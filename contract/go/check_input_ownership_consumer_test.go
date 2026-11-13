package contract_test

import (
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	core "github.com/bitspark/ontos/core/go"
)

// test-double: consumer(a verifier that attests exactly one original fact)
type ownedInputLeaves struct {
	fact       contract.GroundLiteral
	during     func()
	duringAtom func(contract.GroundLiteral)
	calls      int
}

func (*ownedInputLeaves) Extensional() *contract.PredicateSet {
	return contract.PredicateSetOf("allowed")
}

func (l *ownedInputLeaves) Verify(atom contract.GroundLiteral, _ contract.Evidence, _ struct{}) contract.LeafOutcome {
	l.calls++
	if !atom.Equal(l.fact) {
		return contract.LeafReject{Code: "not_attested"}
	}
	if l.during != nil {
		l.during()
	}
	if l.duringAtom != nil {
		l.duringAtom(atom)
	}
	return contract.LeafAdmit{}
}

type ownedInputCheck func(contract.Program, contract.GroundLiteral, contract.Derivation, *contract.CheckProfile[struct{}]) contract.Outcome

func ownedInputRoutes() map[string]ownedInputCheck {
	return map[string]ownedInputCheck{
		"check": func(p contract.Program, c contract.GroundLiteral, d contract.Derivation, profile *contract.CheckProfile[struct{}]) contract.Outcome {
			return contract.Check(p, c, d, struct{}{}, profile)
		},
		"cert_context": func(p contract.Program, c contract.GroundLiteral, d contract.Derivation, profile *contract.CheckProfile[struct{}]) contract.Outcome {
			return contract.CheckWithCertContext(p, c, d, struct{}{}, profile, contract.ZeroCertContext())
		},
		"world_memo": func(p contract.Program, c contract.GroundLiteral, d contract.Derivation, profile *contract.CheckProfile[struct{}]) contract.Outcome {
			memo := contract.NewWorldMemo(p, profile, struct{}{}, contract.ZeroCertContext())
			return contract.CheckWithWorldMemo(memo, c, d)
		},
	}
}

func TestPublicCheckerBindsItsProofAndClaimBeforeAttestation(t *testing.T) {
	fact := func(pred, arg string) contract.GroundLiteral {
		return contract.NewGroundLiteral(pred, core.NewAtom([]byte(arg)))
	}
	leaf := func(conclusion contract.GroundLiteral) contract.LeafNode {
		return contract.LeafNode{Conc: conclusion, Evidence: contract.NoEvidence()}
	}
	for name, run := range ownedInputRoutes() {
		for _, spec := range []struct {
			name   string
			claim  contract.GroundLiteral
			change func(contract.Derivation, contract.GroundLiteral)
			accept bool
		}{
			{"matching", fact("allowed", "a"), func(contract.Derivation, contract.GroundLiteral) {}, true},
			{"different_predicate", fact("other", "a"), func(contract.Derivation, contract.GroundLiteral) {}, false},
			{"replace_root", fact("other", "a"), func(d contract.Derivation, c contract.GroundLiteral) {
				d.Nodes[0] = leaf(c)
			}, false},
			{"retarget_claim", fact("allowed", "b"), func(_ contract.Derivation, c contract.GroundLiteral) {
				c.Args[0] = core.NewAtom([]byte("a"))
			}, false},
			{"retarget_matching_claim", fact("allowed", "a"), func(_ contract.Derivation, c contract.GroundLiteral) {
				c.Args[0] = core.NewAtom([]byte("b"))
			}, true},
		} {
			t.Run(name+"/"+spec.name, func(t *testing.T) {
				original := fact("allowed", "a")
				proof := contract.NewDerivation([]contract.Node{leaf(original)}, 0)
				leaves := &ownedInputLeaves{fact: original, during: func() { spec.change(proof, spec.claim) }}
				profile := &contract.CheckProfile[struct{}]{
					Theory: contract.NewCompoundTheory(), Leaves: leaves,
					Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
				}
				out := run(contract.NewMapProgram(), spec.claim, proof, profile)
				if leaves.calls != 1 {
					t.Fatalf("expected one attestation of the original fact, got %d", leaves.calls)
				}
				if out.IsAccept() != spec.accept || (!spec.accept && out.Verdict.Code() != contract.RootConclusionMismatch) {
					t.Fatalf("captured proof and claim: want accept=%v, got %s", spec.accept, out)
				}
			})
		}
	}
}

// test-double: consumer(a fixed program whose lookup exposes a callback boundary)
type ownedInputProgram struct {
	*contract.MapProgram
	onLookup func()
}

func (p *ownedInputProgram) Clause(id contract.ClauseId) (contract.Clause, bool) {
	p.onLookup()
	return p.MapProgram.Clause(id)
}

func TestProofIsBoundBeforeTheFirstProgramLookup(t *testing.T) {
	a, b := contract.NewClauseId("a"), contract.NewClauseId("b")
	original := contract.NewGroundLiteral("derived")
	claim := contract.NewGroundLiteral("other")
	base := contract.NewMapProgram().With(a, contract.Fact(contract.NewGoal("derived"))).
		With(b, contract.Fact(contract.NewGoal("other")))
	for name, run := range ownedInputRoutes() {
		t.Run(name, func(t *testing.T) {
			proof := contract.NewDerivation([]contract.Node{contract.RuleNode{Conc: original, Clause: a}}, 0)
			lookups := 0
			program := &ownedInputProgram{MapProgram: base, onLookup: func() {
				lookups++
				proof.Nodes[0] = contract.RuleNode{Conc: claim, Clause: b}
			}}
			profile := &contract.CheckProfile[struct{}]{
				Theory: contract.NewCompoundTheory(), Leaves: &ownedInputLeaves{},
				Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
			}
			if control := run(base, original, proof, profile); !control.IsAccept() {
				t.Fatalf("matching rule control: %s", control)
			}
			out := run(program, claim, proof, profile)
			if lookups == 0 || out.IsAccept() || out.Verdict.Code() != contract.RootConclusionMismatch {
				t.Fatalf("a lookup changed the proposed root: %s (%d lookups)", out, lookups)
			}
		})
	}
}

func TestMalformedClaimIsRefusedBeforeAttestation(t *testing.T) {
	for name, run := range ownedInputRoutes() {
		t.Run(name, func(t *testing.T) {
			fact := contract.NewGroundLiteral("allowed", core.NewAtom([]byte("a")))
			leaves := &ownedInputLeaves{fact: fact, during: func() { t.Fatal("consulted verifier for malformed input") }}
			profile := &contract.CheckProfile[struct{}]{
				Theory: contract.NewCompoundTheory(), Leaves: leaves,
				Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
			}
			proof := contract.NewDerivation([]contract.Node{contract.LeafNode{Conc: fact, Evidence: contract.NoEvidence()}}, 0)
			claim := contract.NewGroundLiteral("allowed", nil)
			out := run(contract.NewMapProgram(), claim, proof, profile)
			if out.IsAccept() || out.Verdict.Code() != contract.UnknownNodeKind || leaves.calls != 0 {
				t.Fatalf("malformed claim: %s (%d attestations)", out, leaves.calls)
			}
			profile.Limits.MaxNodes = 0
			out = run(contract.NewMapProgram(), claim, proof, profile)
			if out.IsAccept() || out.Verdict.Code() != contract.TooManyNodes || leaves.calls != 0 {
				t.Fatalf("header precedence: %s (%d attestations)", out, leaves.calls)
			}
		})
	}
}

// The verifier attests the incoming fact before changing its own argument.
// That argument must not expose the checker's retained proof storage.
func TestVerifierArgumentCannotRetargetTheCapturedProof(t *testing.T) {
	for name, run := range ownedInputRoutes() {
		for _, matching := range []bool{true, false} {
			label := "mismatched"
			if matching {
				label = "matching"
			}
			t.Run(name+"/"+label, func(t *testing.T) {
				fact := contract.NewGroundLiteral("allowed", core.NewAtom([]byte("a")))
				claim := contract.NewGroundLiteral("allowed", core.NewAtom([]byte("b")))
				if matching {
					claim = fact
				}
				leaves := &ownedInputLeaves{fact: fact, duringAtom: func(atom contract.GroundLiteral) {
					atom.Args[0] = core.NewAtom([]byte("b"))
				}}
				profile := &contract.CheckProfile[struct{}]{
					Theory: contract.NewCompoundTheory(), Leaves: leaves,
					Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
				}
				proof := contract.NewDerivation([]contract.Node{
					contract.LeafNode{Conc: fact, Evidence: contract.NoEvidence()},
				}, 0)
				out := run(contract.NewMapProgram(), claim, proof, profile)
				if leaves.calls != 1 || out.IsAccept() != matching || (!matching && out.Verdict.Code() != contract.RootConclusionMismatch) {
					t.Fatalf("verifier argument alias: %s (%d attestations)", out, leaves.calls)
				}
			})
		}
	}
}
