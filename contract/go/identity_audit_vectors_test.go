// Go replay of vectors/identity_audit.json (#767) — the identity-audit surface:
// ComponentIdentity.Equal/IsUnidentified and the CompoundIdentityOf baseline fold,
// which this vector uses to FREEZE the CompoundTheory identity byte layout tri-core.
//
// Every case builds REAL member theories (fixture types over the vector's invented
// `mistfen` vocabulary, declared invented per ADR 0025 — a member named "unidentified"
// is a theory that does NOT implement the Identified seam), constructs a live
// CompoundTheory, and asserts three independently-falsifiable facts per case: the live
// Identity() equals the hand-authored pin; CompoundIdentityOf over the triples equals
// the same pin; and the distinguishability verdict (live vs the all-unidentified
// baseline of the same member count) equals the pinned verdict. Plus the order pin:
// identified_first and identified_second must carry DIFFERENT digests.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

type identityAuditSpec struct {
	Id           string `json:"id"`
	Version      string `json:"version"`
	ConfigDigest string `json:"config_digest"`
}

type identityAuditFile struct {
	Unidentified    identityAuditSpec            `json:"unidentified"`
	Components      map[string]identityAuditSpec `json:"components"`
	CompoundWrapper struct {
		Id      string `json:"id"`
		Version string `json:"version"`
	} `json:"compound_wrapper"`
	Cases []struct {
		Name            string   `json:"name"`
		Members         []string `json:"members"`
		ConfigDigest    string   `json:"config_digest"`
		Distinguishable bool     `json:"distinguishable"`
	} `json:"cases"`
}

func loadIdentityAudit(t *testing.T) identityAuditFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "identity_audit.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read vector: %v", readErr)
			}
			var file identityAuditFile
			if jsonErr := json.Unmarshal(raw, &file); jsonErr != nil {
				t.Fatalf("parse vector: %v", jsonErr)
			}
			return file
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("could not locate vectors/identity_audit.json")
		}
		dir = parent
	}
}

func identityAuditHex32(t *testing.T, s string) [32]byte {
	t.Helper()
	raw, err := hex.DecodeString(s)
	if err != nil || len(raw) != 32 {
		t.Fatalf("config_digest must be 32 hex-encoded bytes, got %q", s)
	}
	var out [32]byte
	copy(out[:], raw)
	return out
}

func identityAuditFrom(t *testing.T, spec identityAuditSpec) ComponentIdentity {
	t.Helper()
	return NewComponentIdentity([]byte(spec.Id), []byte(spec.Version), identityAuditHex32(t, spec.ConfigDigest))
}

// pinnedIdentityTheory is a fixture member carrying an explicit identity (the vector's
// invented mistfen components). Owns nothing — the audit is about identity, not routing.
// test-double: consumer(an explicitly identified theory for the identity audit)
type pinnedIdentityTheory struct{ identity ComponentIdentity }

func (pinnedIdentityTheory) Owns(Symbol) bool                   { return false }
func (pinnedIdentityTheory) Decide(GroundLiteral) TheoryOutcome { return TheoryNotMine{} }
func (p pinnedIdentityTheory) Identity() ComponentIdentity      { return p.identity }

// defaultedIdentityTheory does NOT implement the Identified seam — the unidentified
// reading the audit exists to detect.
// test-double: adversarial(relies on the default identity: the unidentified reading the audit detects)
type defaultedIdentityTheory struct{}

func (defaultedIdentityTheory) Owns(Symbol) bool                   { return false }
func (defaultedIdentityTheory) Decide(GroundLiteral) TheoryOutcome { return TheoryNotMine{} }

func TestIdentityAuditVectorsReplay(t *testing.T) {
	f := loadIdentityAudit(t)
	if len(f.Cases) != 8 {
		t.Fatalf("the pin file carries exactly 8 cases, got %d", len(f.Cases))
	}

	// The plain-component audit primitive, against the vector's triples.
	if !identityAuditFrom(t, f.Unidentified).IsUnidentified() {
		t.Fatal("the vector's unidentified triple must read IsUnidentified")
	}
	for name, spec := range f.Components {
		if identityAuditFrom(t, spec).IsUnidentified() {
			t.Fatalf("component %q must not read IsUnidentified", name)
		}
	}
	// A live component without the Identified seam reads as unidentified.
	if !identityOf(defaultedIdentityTheory{}).IsUnidentified() {
		t.Fatal("a non-Identified live component must read as unidentified")
	}

	configByName := map[string][32]byte{}
	for _, c := range f.Cases {
		pinned := NewComponentIdentity(
			[]byte(f.CompoundWrapper.Id),
			[]byte(f.CompoundWrapper.Version),
			identityAuditHex32(t, c.ConfigDigest),
		)

		// (1) LIVE: real member theories -> CompoundTheory -> Identity().
		liveMembers := make([]Theory, len(c.Members))
		triples := make([]ComponentIdentity, len(c.Members))
		baseline := make([]ComponentIdentity, len(c.Members))
		for i, m := range c.Members {
			baseline[i] = UnidentifiedComponent()
			if m == "unidentified" {
				liveMembers[i] = defaultedIdentityTheory{}
				triples[i] = UnidentifiedComponent()
			} else {
				id := identityAuditFrom(t, f.Components[m])
				liveMembers[i] = pinnedIdentityTheory{identity: id}
				triples[i] = id
			}
		}
		live := NewCompoundTheory(liveMembers...).Identity()
		if !live.Equal(pinned) {
			t.Errorf("case %s: live identity != hand-authored pin", c.Name)
		}

		// (2) The public audit fn over the triples agrees with the same pin.
		if !CompoundIdentityOf(triples).Equal(pinned) {
			t.Errorf("case %s: CompoundIdentityOf != hand-authored pin", c.Name)
		}

		// (3) The audit verdict: live vs the all-unidentified baseline of the same n.
		if got := !live.Equal(CompoundIdentityOf(baseline)); got != c.Distinguishable {
			t.Errorf("case %s: distinguishability %v, pinned %v", c.Name, got, c.Distinguishable)
		}

		configByName[c.Name] = pinned.ConfigDigest
	}

	// Order is identity-bearing: the same member multiset in two orders pins two digests.
	if configByName["identified_first"] == configByName["identified_second"] {
		t.Error("member order must be identity-bearing")
	}
}
