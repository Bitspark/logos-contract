// Go mirror of the Shelf-B lists cross-version BYTE-SUPERSET invariant (issue #494).
//
// ADR 0016 freezes Shelf B per (name@version) and each lists bundle pledges it
// "RE-INCLUDES every prior relation BYTE-IDENTICALLY". That pledge was prose-only: the
// shipped-bundle tests load each lists@1.{0,1,2}.0 INDEPENDENTLY and verify only each
// file's own per-file program_digest, so editing a shared clause in a newer bundle (and
// re-pinning its digest) would silently break the superset and still pass.
//
// This test makes it a theorem: it loads each adjacent pair through the REAL LoadPrelude
// (which recomputes + verifies the program_digest, so a tampered manifest is refused
// before the comparison) and asserts the older bundle's clause-id set is a subset of the
// newer's. The canonical ClauseId is a hash of the frozen account-codec clause bytes, so
// id-subset already implies byte-identical re-inclusion; id-subset + the existing per-file
// digest pins ⟹ the newer bundle is a byte-exact extension of the older. (The Rust mirror
// conformance/rs/tests/lists_version_superset.rs additionally compares the clause body.)
package contract

import (
	"os"
	"path/filepath"
	"testing"
)

// loadListsBundleIDs loads prelude/lists@<version>.json through the real loader and returns
// its clause ids indexed in a set.
func loadListsBundleIDs(t *testing.T, root, version string) map[string]struct{} {
	t.Helper()
	raw, err := os.ReadFile(filepath.Join(root, "prelude", "lists@"+version+".json"))
	if err != nil {
		t.Fatalf("read prelude/lists@%s.json: %v", version, err)
	}
	bundle, err := LoadPrelude(raw)
	if err != nil {
		t.Fatalf("prelude/lists@%s.json did not load: %v", version, err)
	}
	ids := make(map[string]struct{}, len(bundle.Clauses))
	for _, pc := range bundle.Clauses {
		ids[pc.ID.String()] = struct{}{}
	}
	return ids
}

func assertIDSubset(t *testing.T, older, newer map[string]struct{}, olderLabel, newerLabel string) {
	t.Helper()
	if len(older) > len(newer) {
		t.Fatalf("%s (%d) has fewer clauses than %s (%d) — not a superset", newerLabel, len(newer), olderLabel, len(older))
	}
	for id := range older {
		if _, ok := newer[id]; !ok {
			t.Errorf("byte-superset broken: clause %s of %s is ABSENT from %s (a prior relation was dropped or its bytes changed)", id, olderLabel, newerLabel)
		}
	}
}

// TestListsVersionsFormByteSupersetChain asserts lists@1.0.0 ⊆ 1.1.0 ⊆ 1.2.0 (and the
// 1.0.0 ⊆ 1.2.0 end-to-end edge) by canonical clause id.
func TestListsVersionsFormByteSupersetChain(t *testing.T) {
	root := repoRoot(t)
	v100 := loadListsBundleIDs(t, root, "1.0.0")
	v110 := loadListsBundleIDs(t, root, "1.1.0")
	v120 := loadListsBundleIDs(t, root, "1.2.0")

	// The cardinalities the issue verified at HEAD: 4 ⊂ 14 ⊂ 19.
	if len(v100) != 4 || len(v110) != 14 || len(v120) != 19 {
		t.Fatalf("clause counts = %d/%d/%d, want 4/14/19", len(v100), len(v110), len(v120))
	}

	assertIDSubset(t, v100, v110, "lists@1.0.0", "lists@1.1.0")
	assertIDSubset(t, v110, v120, "lists@1.1.0", "lists@1.2.0")
	assertIDSubset(t, v100, v120, "lists@1.0.0", "lists@1.2.0")
}
