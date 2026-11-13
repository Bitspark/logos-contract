// Go replay of the cross-core agreement vector vectors/compound.json (CompoundTheory
// over [arithmetic, text]). The Rust CompoundTheory is the oracle; this asserts the Go
// CompoundTheory reproduces the routed decisions, the owns union, AND the identity
// config-digest byte-for-byte. The SAME file is replayed in Rust
// (contract/rs/tests/compound_vectors.rs) and TS (contract/ts/test/compound_vectors.test.ts).
//
// The on-disk shape adds a "members" list to the arithmetic/text vector shape, so this
// reuses the arithIdentity/arithOwns/arithDecision types and the buildArg/expectOutcome
// helpers from arithmetic_vectors_test.go (same package).
package contract

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

type compoundVectorFile struct {
	Members   []string        `json:"members"`
	Identity  arithIdentity   `json:"identity"`
	Owns      arithOwns       `json:"owns"`
	Decisions []arithDecision `json:"decisions"`
}

// loadCompoundVectors finds vectors/compound.json by walking up from the test's working
// directory (contract/go) to the repo root, mirroring loadArithVectors.
func loadCompoundVectors(t *testing.T) compoundVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "compound.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/compound.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf compoundVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// buildCompound builds the CompoundTheory the vector names, mapping each member string.
func buildCompound(t *testing.T, members []string) CompoundTheory {
	t.Helper()
	theories := make([]Theory, 0, len(members))
	for _, m := range members {
		switch m {
		case "arithmetic":
			theories = append(theories, NewArithmeticTheory())
		case "text":
			theories = append(theories, NewTextTheory())
		default:
			t.Fatalf("unknown member theory %q", m)
		}
	}
	return NewCompoundTheory(theories...)
}

func TestCompoundTheoryVectorDecisions(t *testing.T) {
	vf := loadCompoundVectors(t)
	theory := buildCompound(t, vf.Members)
	if len(vf.Decisions) == 0 {
		t.Fatal("no decision vectors loaded")
	}
	for _, d := range vf.Decisions {
		args := make([]core.Value, 0, len(d.Args))
		for _, a := range d.Args {
			args = append(args, buildArg(t, a))
		}
		atom := GroundLiteral{Pred: SymbolFromString(d.Pred), Args: args}
		expectOutcome(t, d.Name, d.Outcome, DecideGround(theory, atom))
	}
}

func TestCompoundTheoryVectorOwns(t *testing.T) {
	vf := loadCompoundVectors(t)
	theory := buildCompound(t, vf.Members)
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

func TestCompoundTheoryVectorIdentity(t *testing.T) {
	vf := loadCompoundVectors(t)
	id := buildCompound(t, vf.Members).Identity()
	if string(id.Id) != vf.Identity.ID {
		t.Errorf("identity Id = %q, want %q", id.Id, vf.Identity.ID)
	}
	if string(id.Version) != vf.Identity.Version {
		t.Errorf("identity Version = %q, want %q", id.Version, vf.Identity.Version)
	}
	if got := hex.EncodeToString(id.ConfigDigest[:]); got != vf.Identity.ConfigDigestHex {
		t.Errorf("identity config_digest = %s, want %s", got, vf.Identity.ConfigDigestHex)
	}
}
