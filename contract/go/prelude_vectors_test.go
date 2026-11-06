// Go replay of the cross-core Shelf-B prelude-loader vector vectors/prelude.json (ADR
// 0016 Shelf-B Horn-clause prelude), plus a load of the shipped on-disk bundles
// prelude/sample@1.0.0.json + lists@1.0.0/1.1.0/1.2.0.json, plus the cross-core
// program_digest pin.
//
// Each vector case is a complete prelude manifest plus the PINNED LoadPrelude outcome.
// This replay drives the REAL contract.LoadPrelude over each manifest (the committed file
// is checked against the loader, not trusted blind) and asserts the {ok | err} outcome.
// The SAME vectors/prelude.json is replayed in Rust (contract/rs/tests/prelude_vectors.rs)
// and TS (contract/ts/test/prelude_vectors.test.ts) — the recomputed program_digest is
// byte-identical across {rs,go,ts} (frozen ontos-codec + syntactic VarId), so
// search/check/loader cannot silently diverge.
//
// The trust anchor is DIGEST RE-DERIVATION, not the JSON parser: the digest_mismatch and
// tampered_clause_rejected_by_digest cases pin that a wrong clause set (or a wrong pinned
// digest) is REFUSED, never silently admitted.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"testing"
)

// ----- the on-disk vector shape -----

type preludeVectorFile struct {
	Seam             string           `json:"seam"`
	ProgramPrefixHex string           `json:"program_prefix_hex"`
	ClausePrefixHex  string           `json:"clause_prefix_hex"`
	Cases            []preludeVecCase `json:"cases"`
}

type preludeVecCase struct {
	Name     string          `json:"name"`
	Manifest json.RawMessage `json:"manifest"`
	Outcome  preludeOutcome  `json:"outcome"`
}

type preludeOutcome struct {
	Ok  *preludeOk `json:"ok"`
	Err *string    `json:"err"`
}

type preludeOk struct {
	Name          string   `json:"name"`
	Version       string   `json:"version"`
	ProgramDigest string   `json:"program_digest"`
	ClauseIDs     []string `json:"clause_ids"`
}

// repoRoot walks up from the test's working directory (contract/go) to the repo root,
// mirroring loadTermVectors.
func repoRoot(t *testing.T) string {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for d := dir; ; {
		if _, err := os.Stat(filepath.Join(d, "vectors", "prelude.json")); err == nil {
			return d
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/prelude.json above %s", dir)
		}
		d = parent
	}
}

func loadPreludeVectors(t *testing.T) preludeVectorFile {
	t.Helper()
	raw, err := os.ReadFile(filepath.Join(repoRoot(t), "vectors", "prelude.json"))
	if err != nil {
		t.Fatalf("read vectors/prelude.json: %v", err)
	}
	var vf preludeVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal vectors/prelude.json: %v", err)
	}
	return vf
}

// errVariant maps a *PreludeError back to its cross-core variant tag.
func errVariant(err error) string {
	var pe *PreludeError
	if errors.As(err, &pe) {
		return string(pe.Kind)
	}
	return "<non-prelude-error: " + err.Error() + ">"
}

func assertOk(t *testing.T, name string, want *preludeOk, got *PreludeBundle) {
	t.Helper()
	if got.Name != want.Name {
		t.Errorf("%s: bundle name = %q, want %q", name, got.Name, want.Name)
	}
	if got.Version != want.Version {
		t.Errorf("%s: bundle version = %q, want %q", name, got.Version, want.Version)
	}
	if got.ProgramDigest != want.ProgramDigest {
		t.Errorf("%s: recomputed program_digest = %q, want %q", name, got.ProgramDigest, want.ProgramDigest)
	}
	gotIDs := make([]string, len(got.Clauses))
	for i, pc := range got.Clauses {
		gotIDs[i] = pc.ID.String()
	}
	if len(gotIDs) != len(want.ClauseIDs) {
		t.Fatalf("%s: clause id count = %d, want %d", name, len(gotIDs), len(want.ClauseIDs))
	}
	for i := range gotIDs {
		if gotIDs[i] != want.ClauseIDs[i] {
			t.Errorf("%s: clause id[%d] = %q, want %q", name, i, gotIDs[i], want.ClauseIDs[i])
		}
	}
}

// TestPreludeLoaderVectors replays every vectors/prelude.json case through the REAL
// LoadPrelude, asserting the pinned {ok | err} outcome byte-for-byte (the same oracle
// the Rust and TS loaders replay).
func TestPreludeLoaderVectors(t *testing.T) {
	vf := loadPreludeVectors(t)
	if len(vf.Cases) == 0 {
		t.Fatal("no loader vectors loaded")
	}
	sawOk, sawErr := false, false
	for _, c := range vf.Cases {
		got, err := LoadPrelude(c.Manifest)
		switch {
		case c.Outcome.Ok != nil:
			sawOk = true
			if err != nil {
				t.Errorf("%s: expected ok, got err %v", c.Name, err)
				continue
			}
			assertOk(t, c.Name, c.Outcome.Ok, got)
		case c.Outcome.Err != nil:
			sawErr = true
			if err == nil {
				t.Errorf("%s: expected err %q, got ok %+v", c.Name, *c.Outcome.Err, got)
				continue
			}
			if v := errVariant(err); v != *c.Outcome.Err {
				t.Errorf("%s: error variant = %q, want %q", c.Name, v, *c.Outcome.Err)
			}
		default:
			t.Errorf("%s: outcome is neither ok nor err", c.Name)
		}
	}
	if !sawOk || !sawErr {
		t.Errorf("vectors must cover both ok and err paths (sawOk=%v sawErr=%v)", sawOk, sawErr)
	}
}

// TestPreludeVectorProgramPrefixPin pins the program/clause domain-separator bytes the
// vector commits — a drift in the prefix would change every program_digest, so the
// vector's hex must equal the constants this binding hashes with.
func TestPreludeVectorProgramPrefixPin(t *testing.T) {
	vf := loadPreludeVectors(t)
	if got := hex.EncodeToString(ProgramPrefix); got != vf.ProgramPrefixHex {
		t.Errorf("ProgramPrefix hex = %q, want vector %q", got, vf.ProgramPrefixHex)
	}
	if got := hex.EncodeToString(ClausePrefix); got != vf.ClausePrefixHex {
		t.Errorf("ClausePrefix hex = %q, want vector %q", got, vf.ClausePrefixHex)
	}
}

// TestProgramDigestMatchesRustPin is the cross-core program_digest oracle: building the
// sample bundle's two clauses in Go and hashing them with ProgramDigest must reproduce
// the EXACT hex the Rust loader pins (and that the vector commits) — byte-for-byte.
func TestProgramDigestMatchesRustPin(t *testing.T) {
	// nat(z).  and  nat(s(X)) :- nat(X).  — the sample bundle, built in Go so the test
	// is independent of the on-disk manifest.
	natZ := Fact(NewGoal("nat", Tuple(Atom([]byte("z")))))
	natS := NewClause(
		NewGoal("nat", Tuple(Atom([]byte("s")), Var("X"))),
		NewGoal("nat", Var("X")),
	)
	got := BundleDigest([]Clause{natZ, natS})
	const wantDigest = "cb22fbb4f7fcaf55de33742c2ad0328cc9f964bbb97b62ab508fced396fbb5a7"
	if got != wantDigest {
		t.Fatalf("program_digest\n got  %s\n want %s (Rust pin)", got, wantDigest)
	}
	// Order-independence: the digest sorts the per-clause bytes, so a reversed clause
	// slice yields the SAME digest.
	if rev := BundleDigest([]Clause{natS, natZ}); rev != wantDigest {
		t.Fatalf("program_digest is not order-independent: reversed = %s", rev)
	}
	// And the per-clause canonical ids match the manifest pins.
	if id := CanonicalClauseId(natZ).String(); id != "8c245a7a0ea73dab49ff899cc27254953f7cb321e15a803bf832c174ab2d757c" {
		t.Errorf("nat(z) clause id = %s", id)
	}
	if id := CanonicalClauseId(natS).String(); id != "d02e98ca7fe546344c88c2bc5afdfea44779e90195c9432de6858d5055d46e84" {
		t.Errorf("nat(s(X)):-nat(X) clause id = %s", id)
	}
}

// TestShippedBundlesLoad loads every shipped on-disk prelude bundle through the REAL
// loader (the same files the Rust replay loads): sample@1.0.0 + lists@1.0.0/1.1.0/1.2.0.
// A bundle whose recomputed digest did not match its pinned program_digest would be
// refused here.
func TestShippedBundlesLoad(t *testing.T) {
	root := repoRoot(t)
	cases := []struct {
		file    string
		name    string
		version string
		digest  string // "" = do not pin (just require it loads)
	}{
		{"sample@1.0.0.json", "sample", "1.0.0", "cb22fbb4f7fcaf55de33742c2ad0328cc9f964bbb97b62ab508fced396fbb5a7"},
		{"lists@1.0.0.json", "lists", "1.0.0", "59d7f32b8a3a7d936ce098d15b05d87d03b0727d920cedd2e24891a857176e25"},
		{"lists@1.1.0.json", "lists", "1.1.0", "9451f99428fd18a60eb19c9ef26a72b94b4db5b5a8f755ed851fe159ffcf0e35"},
		{"lists@1.2.0.json", "lists", "1.2.0", "c2cb5164002b89db421463d3d98e057646545a6b25c3b3145ae170443bd1b056"},
	}
	for _, tc := range cases {
		raw, err := os.ReadFile(filepath.Join(root, "prelude", tc.file))
		if err != nil {
			t.Fatalf("read prelude/%s: %v", tc.file, err)
		}
		bundle, err := LoadPrelude(raw)
		if err != nil {
			t.Fatalf("prelude/%s did not load: %v", tc.file, err)
		}
		if bundle.Name != tc.name || bundle.Version != tc.version {
			t.Errorf("prelude/%s: got %s@%s, want %s@%s", tc.file, bundle.Name, bundle.Version, tc.name, tc.version)
		}
		if tc.digest != "" && bundle.ProgramDigest != tc.digest {
			t.Errorf("prelude/%s: program_digest = %s, want %s", tc.file, bundle.ProgramDigest, tc.digest)
		}
		if len(bundle.Clauses) == 0 {
			t.Errorf("prelude/%s: loaded with no clauses", tc.file)
		}
	}
}
