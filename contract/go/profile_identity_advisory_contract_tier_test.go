package contract_test

// The CONTRACT-TIER reachability test for the unidentified-component advisory (#815).
//
// It is an EXTERNAL test package (contract_test) importing ONLY
// github.com/Bitspark/logos-contract/contract/go. That is the whole point: it stands where a
// consumer stands — outside the package, with no kernel dependency.
//
// ADR 0026 G2 asks each exposed consumer to self-measure. The advisory originally lived in
// kernel, so a consumer binding only logos-contract could not reach it, and could not be
// given it: contract -> kernel is an UPWARD edge the arch job rejects. That wall was found
// only when a real consumer (thesmos, which binds logos-contract) tried to follow the
// instruction and had to submit a source-level audit instead (#791).
//
// The kernel forms are now aliases of these. A test that imports the kernel CANNOT detect a
// regression of the placement — it would keep passing if the definition moved back up a
// tier, because an alias looks identical from above. Only a test that refuses the kernel
// dependency can.
//
// It replays the SAME vectors/profile_identity_advisory.json as the kernel arms, so
// cross-tier agreement and tri-core agreement are one check rather than two.

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	"github.com/Bitspark/logos-contract/contract/go/completion"
)

// test-double: consumer(an explicitly identified theory for the identity advisory)
type ctTheory struct{ id *contract.ComponentIdentity }

func (ctTheory) Owns(contract.Symbol) bool { return false }
func (ctTheory) DecideGround(contract.GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundDisowned()
}
func (t ctTheory) Identity() contract.ComponentIdentity { return *t.id }

// test-double: adversarial(no identity: the anonymous reading the advisory flags)
type ctAnonTheory struct{}

func (ctAnonTheory) Owns(contract.Symbol) bool { return false }
func (ctAnonTheory) DecideGround(contract.GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundDisowned()
}

// test-double: consumer(an explicitly identified leaf verifier for the identity advisory)
type ctLeaves struct {
	ext *contract.PredicateSet
	id  *contract.ComponentIdentity
}

func (l ctLeaves) Extensional() *contract.PredicateSet { return l.ext }
func (ctLeaves) Verify(contract.GroundLiteral, contract.Evidence, any) contract.LeafOutcome {
	return contract.LeafReject{Code: "vector"}
}
func (l ctLeaves) Identity() contract.ComponentIdentity { return *l.id }

// test-double: adversarial(no identity: the anonymous reading the advisory flags)
type ctAnonLeaves struct{ ext *contract.PredicateSet }

func (l ctAnonLeaves) Extensional() *contract.PredicateSet { return l.ext }
func (ctAnonLeaves) Verify(contract.GroundLiteral, contract.Evidence, any) contract.LeafOutcome {
	return contract.LeafReject{Code: "vector"}
}

// test-double: adversarial(no identity: the anonymous reading the advisory flags)
type ctAnonAdmit struct{}

func (ctAnonAdmit) Admissible(contract.Clause, contract.NodeMeta, any) contract.RuleOutcome {
	return contract.RuleAdmit{}
}

type ctVectors struct {
	Bindings map[string]struct {
		Id           string `json:"id"`
		Version      string `json:"version"`
		ConfigDigest string `json:"config_digest"`
	} `json:"bindings"`
	Cases []struct {
		Name              string   `json:"name"`
		Theory            string   `json:"theory"`
		Leaves            string   `json:"leaves"`
		Admit             string   `json:"admit"`
		AllowUnidentified []string `json:"allow_unidentified"`
		UnidentifiedSlots []string `json:"unidentified_slots"`
	} `json:"cases"`
}

func TestAdvisoryIsReachableAndCorrectFromContractAlone(t *testing.T) {
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var v ctVectors
	for {
		candidate := filepath.Join(dir, "vectors", "profile_identity_advisory.json")
		if raw, readErr := os.ReadFile(candidate); readErr == nil {
			if err := json.Unmarshal(raw, &v); err != nil {
				t.Fatalf("parse %s: %v", candidate, err)
			}
			break
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("could not locate the advisory vector")
		}
		dir = parent
	}
	if len(v.Cases) == 0 {
		t.Fatal("vector must carry cases")
	}

	idFor := func(name string) *contract.ComponentIdentity {
		if name == "anonymous" {
			return nil
		}
		b, ok := v.Bindings[name]
		if !ok {
			t.Fatalf("unknown binding %q", name)
		}
		raw, err := hex.DecodeString(b.ConfigDigest)
		if err != nil || len(raw) != 32 {
			t.Fatalf("binding %q: bad config_digest", name)
		}
		var cfg [32]byte
		copy(cfg[:], raw)
		return &contract.ComponentIdentity{
			Id: []byte(b.Id), Version: []byte(b.Version), ConfigDigest: cfg,
		}
	}

	ext := contract.PredicateSetOf("p/1")

	for _, c := range v.Cases {
		var theory contract.Theory
		if id := idFor(c.Theory); id == nil {
			theory = ctAnonTheory{}
		} else {
			theory = ctTheory{id: id}
		}
		var leaves contract.LeafVerifier[any]
		if id := idFor(c.Leaves); id == nil {
			leaves = ctAnonLeaves{ext: ext}
		} else {
			leaves = ctLeaves{ext: ext, id: id}
		}
		var admit contract.RuleAdmissibility[any]
		switch c.Admit {
		case "anonymous":
			admit = ctAnonAdmit{}
		case "always_admit":
			admit = contract.AlwaysAdmit[any]{}
		default:
			t.Fatalf("case %s: unknown admit binding %q", c.Name, c.Admit)
		}

		profile := &contract.CheckProfile[any]{
			Theory: theory, Leaves: leaves, Admit: admit, Limits: contract.DefaultLimits(),
		}

		allowance := make([]contract.ProfileSlot, 0, len(c.AllowUnidentified))
		for _, s := range c.AllowUnidentified {
			switch s {
			case "theory":
				allowance = append(allowance, contract.ProfileSlotTheory)
			case "leaves":
				allowance = append(allowance, contract.ProfileSlotLeaves)
			case "admit":
				allowance = append(allowance, contract.ProfileSlotAdmit)
			default:
				t.Fatalf("case %s: unknown slot %q", c.Name, s)
			}
		}

		got := contract.UnidentifiedProfileSlotsAllowing(profile, allowance)
		names := make([]string, 0, len(got))
		for _, s := range got {
			names = append(names, s.String())
		}

		// ORDERED — a set comparison would pass under reordering.
		if len(names) != len(c.UnidentifiedSlots) {
			t.Fatalf("case %s: got %v want %v", c.Name, names, c.UnidentifiedSlots)
		}
		for i := range c.UnidentifiedSlots {
			if names[i] != c.UnidentifiedSlots[i] {
				t.Fatalf("case %s: contract-tier advisory must match the shared vector, in fold order: got %v want %v",
					c.Name, names, c.UnidentifiedSlots)
			}
		}

		if len(allowance) == 0 {
			plain := contract.UnidentifiedProfileSlots(profile)
			if len(plain) != len(got) {
				t.Fatalf("case %s: the unallowed form must equal the empty allowance", c.Name)
			}
		}
	}
}
