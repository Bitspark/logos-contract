// Package r3domain reads R3's generated domain and its raise value for contract/go's replays (#2733;
// seat:caa's ruling (B) on 3b-ii). It is kernel/go/internal/r3domain's twin: Go's internal rule keeps
// each module's copy out of the other's reach, as with the replay ledger. The domain's computation is
// rs's replay_manifest::relational_cases, drift-guarded there; go reads the list and never re-derives it.
package r3domain

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

// Domain is file's R3 case ids from vectors/r3_domain.json, joined both ways against cases, the ids
// the replay has (seat:caa's condition 3): an id no case carries, or that two cases carry, fails the
// test. The count is logged.
func Domain(t testing.TB, file string, cases []string) map[string]bool {
	t.Helper()
	var doc struct {
		Files []struct {
			File  string   `json:"file"`
			Cases []string `json:"cases"`
		} `json:"files"`
	}
	read(t, "r3_domain.json", &doc)
	// One record per runs file, its name a value (#2733 3b-ii): exactly one must name file.
	var ids []string
	found := 0
	for _, r := range doc.Files {
		if r.File == file {
			ids, found = r.Cases, found+1
		}
	}
	if found != 1 {
		t.Fatalf("r3domain: vectors/r3_domain.json holds %d records for %s, not exactly one", found, file)
	}
	carried := map[string]int{}
	for _, c := range cases {
		carried[c]++
	}
	out := map[string]bool{}
	for _, id := range ids {
		if n := carried[id]; n != 1 {
			t.Fatalf("r3domain: %s's domain id %q resolves to %d of the replay's cases, not exactly one", file, id, n)
		}
		out[id] = true
	}
	t.Logf("r3 %s: %d domain case(s) of %d", file, len(out), len(cases))
	return out
}

// Raised is the value R3 raises an allowance to, from the declared carrier table
// (vectors/allowances.json).
func Raised(t testing.TB) int {
	t.Helper()
	var table struct {
		Raised int `json:"raised"`
	}
	read(t, "allowances.json", &table)
	if table.Raised <= 0 {
		t.Fatalf("r3domain: vectors/allowances.json has no raised value")
	}
	return table.Raised
}

func read(t testing.TB, name string, into any) {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("r3domain: getwd: %v", err)
	}
	for {
		path := filepath.Join(dir, "vectors", name)
		if raw, err := os.ReadFile(path); err == nil {
			if err := json.Unmarshal(raw, into); err != nil {
				t.Fatalf("r3domain: vectors/%s does not parse: %v", name, err)
			}
			return
		}
		up := filepath.Dir(dir)
		if up == dir {
			t.Fatalf("r3domain: no vectors/%s above the test's directory", name)
		}
		dir = up
	}
}
