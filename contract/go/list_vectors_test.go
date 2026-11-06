// Go replay of the cross-core THEORY-DECISION agreement vector vectors/list.json
// (ADR 0016 ListTheory tri-core). The Rust ListTheory is the decision oracle; this test
// asserts the Go ListTheory reproduces every pinned outcome byte-for-byte. The SAME file
// is replayed in Rust (contract/rs/tests/list_vectors.rs) and TS
// (contract/ts/test/list_vectors.test.ts), so a single oracle pins all three cores — the
// §7 dual-conformance byte-parity proof.
//
// The on-disk vector shape is identical to vectors/term.json (and arithmetic.json), so
// this reuses the arithVectorFile struct and the buildArg / expectOutcome helpers defined
// in arithmetic_vectors_test.go (same package). The {list: [..]} arg shape is handled by
// the shared buildArg. Only the file name and the theory differ.
package contract

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// loadListVectors finds vectors/list.json by walking up from the test's working
// directory (contract/go) to the repo root, mirroring loadTermVectors.
func loadListVectors(t *testing.T) arithVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "list.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/list.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf arithVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

func TestListTheoryVectorDecisions(t *testing.T) {
	vf := loadListVectors(t)
	theory := NewListTheory()
	if len(vf.Decisions) == 0 {
		t.Fatal("no decision vectors loaded")
	}
	for _, d := range vf.Decisions {
		args := make([]core.Value, 0, len(d.Args))
		for _, a := range d.Args {
			args = append(args, buildArg(t, a))
		}
		atom := GroundLiteral{Pred: SymbolFromString(d.Pred), Args: args}
		expectOutcome(t, d.Name, d.Outcome, DecideGround(theory, atom), theory.Decide(atom))
	}
}

func TestListTheoryVectorOwns(t *testing.T) {
	vf := loadListVectors(t)
	theory := NewListTheory()
	for _, name := range vf.Owns.Owned {
		if !theory.Owns(SymbolFromString(name)) {
			t.Errorf("Owns(%q) = false, want true", name)
		}
	}
	for _, name := range vf.Owns.NotOwned {
		if theory.Owns(SymbolFromString(name)) {
			t.Errorf("Owns(%q) = true, want false", name)
		}
	}
}

func TestListTheoryVectorIdentity(t *testing.T) {
	vf := loadListVectors(t)
	id := NewListTheory().Identity()
	if string(id.Id) != vf.Identity.ID {
		t.Errorf("identity Id = %q, want %q", id.Id, vf.Identity.ID)
	}
	if string(id.Version) != vf.Identity.Version {
		t.Errorf("identity Version = %q, want %q", id.Version, vf.Identity.Version)
	}
	if id.ConfigDigest != ([32]byte{}) {
		t.Errorf("identity ConfigDigest = %v, want zero", id.ConfigDigest)
	}
}
