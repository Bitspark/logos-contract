// Package replayledger is contract/go's replay adapter for the per-assertion replay accounting
// (#2732 increment 2; vectors/REPLAY-ACCOUNTING.md section 4). A vector replay calls Observe AFTER
// its assertion held, so an observation means the assertion ran; a skipped or deleted assertion
// leaves a missing line, which the central check reads.
//
// Observe appends one JSON line to the file LOGOS_REPLAY_LEDGER names, and does nothing when the
// variable is unset, so a local run is unaffected. The target is this module's, never the caller's.
// The line carries the vector file's sha256, so a receipt written against an older corpus cannot
// satisfy the check (research 0025 row A20). What a valid line is, is decided once, by the central
// check's schema: this adapter only writes it.
package replayledger

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"sync"
	"testing"
)

// Target is the deployment contract/go's replays run in (the manifest's `targets`).
const Target = "go"

// The statuses a line may carry. A skip satisfies no obligation unless the manifest authorizes it.
const (
	Passed            = "passed"
	RefusedAsExpected = "refused_as_expected"
)

var (
	mu     sync.Mutex
	hashes = map[string]string{}
)

// Observe records that the replay of vectors/<file>'s case `kase` held assertion `assertion`.
// A write that fails fails the test: a ledger that silently drops a line reads as a missing replay.
func Observe(t testing.TB, file, kase, assertion, status string) {
	t.Helper()
	ledger := os.Getenv("LOGOS_REPLAY_LEDGER")
	if ledger == "" {
		return
	}
	mu.Lock()
	defer mu.Unlock()
	sum, ok := hashes[file]
	if !ok {
		raw, err := os.ReadFile(filepath.Join(vectorsDir(t), file))
		if err != nil {
			t.Fatalf("replayledger: read vectors/%s: %v", file, err)
		}
		h := sha256.Sum256(raw)
		sum = hex.EncodeToString(h[:])
		hashes[file] = sum
	}
	line, err := json.Marshal(map[string]string{
		"file": file, "case": kase, "assertion": assertion, "target": Target, "status": status,
		"file_sha256": sum,
	})
	if err != nil {
		t.Fatalf("replayledger: encode: %v", err)
	}
	f, err := os.OpenFile(ledger, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		t.Fatalf("replayledger: open %s: %v", ledger, err)
	}
	defer f.Close()
	// One write per line: concurrent test processes append whole lines.
	if _, err := f.Write(append(line, '\n')); err != nil {
		t.Fatalf("replayledger: write %s: %v", ledger, err)
	}
}

// vectorsDir is the repository's vectors/ directory, found by walking up from the test's working
// directory (a package directory) to the first ancestor that holds vectors/replay_obligations.json.
func vectorsDir(t testing.TB) string {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("replayledger: getwd: %v", err)
	}
	for {
		v := filepath.Join(dir, "vectors")
		if _, err := os.Stat(filepath.Join(v, "replay_obligations.json")); err == nil {
			return v
		}
		up := filepath.Dir(dir)
		if up == dir {
			t.Fatalf("replayledger: no vectors/replay_obligations.json above %s", dir)
		}
		dir = up
	}
}
