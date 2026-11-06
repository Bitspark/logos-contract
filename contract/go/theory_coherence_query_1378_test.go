package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// The arm-3 attribution query (issue #1378), Go half of the tri-core surface.
//
// Check rejects an Owns()-yes / Decide()-NotMine theory with the structural code
// PredicatePartitionViolation. That code is correct - the account cannot be verified by this
// profile - but it points a consumer at the PRODUCER for a defect in the verifier's own theory
// binding. Per the #1382 ruling on the sibling arm a new RejectionCode is v1-breaking in all
// three cores, so the attribution is a query rather than vocabulary.
//
// The two that matter are:
//   - TestArm1UnboundTheoryIsNotReportedAsIncoherent - arm 1 also answers NotMine and shares
//     the rejection code, so a query keyed on the outcome alone would conflate them.
//   - TestEmptyResultDoesNotCertifyTheTheoryCoherent - the documented limit, executable.

// --------------------------------- theories ---------------------------------

// Arm 3: Owns says yes, Decide disowns. The defect under test.
// test-double: adversarial(owns a predicate yet decides NotMine: the defect under test)
type tcDisowningTheory struct{}

func (tcDisowningTheory) Owns(pred Symbol) bool { return true }
func (tcDisowningTheory) Decide(atom GroundLiteral) TheoryOutcome {
	return TheoryNotMine{}
}

// A coherent theory: owns it and decides it.
// test-double: consumer(owns every predicate and holds it)
type tcOwningTheory struct{}

func (tcOwningTheory) Owns(pred Symbol) bool { return true }
func (tcOwningTheory) Decide(atom GroundLiteral) TheoryOutcome {
	return TheoryHolds{}
}

// Arm 1: a host binding no theory. Decide also answers NotMine.
// test-double: consumer(owns no predicate: the theory-less host)
type tcUnboundTheory struct{}

func (tcUnboundTheory) Owns(pred Symbol) bool { return false }
func (tcUnboundTheory) Decide(atom GroundLiteral) TheoryOutcome {
	return TheoryNotMine{}
}

// ---------------------------------- harness ----------------------------------

// test-double: consumer(declares a chosen extensional set)
type tcLeaves struct{ extensional *PredicateSet }

func (l tcLeaves) Extensional() *PredicateSet { return l.extensional }
func (tcLeaves) Verify(atom GroundLiteral, evidence Evidence, ctx struct{}) LeafOutcome {
	return LeafReject{Code: "not_a_leaf_test"}
}

func tcAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

func tcLit(pred string, arg string) GroundLiteral {
	return NewGroundLiteral(pred, tcAtom(arg))
}

// pairs is a flat (pred, arg, pred, arg, ...) list, one BuiltinNode each.
func tcDeriv(pairs ...string) Derivation {
	nodes := make([]Node, 0, len(pairs)/2)
	for i := 0; i+1 < len(pairs); i += 2 {
		nodes = append(nodes, BuiltinNode{Conc: tcLit(pairs[i], pairs[i+1])})
	}
	return Derivation{Nodes: nodes, Root: 0}
}

func tcProfile(theory Theory) *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: theory,
		Leaves: tcLeaves{extensional: NewPredicateSet()},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

func tcRender(atoms []GroundLiteral) []string {
	out := make([]string, 0, len(atoms))
	for _, a := range atoms {
		out = append(out, a.Pred.String())
	}
	return out
}

// ----------------------------------- tests -----------------------------------

// The query fires on the defect it is named for, returning the ATOM - incoherence is only
// observable per atom, since Owns is per predicate.
func TestNamesTheAtomAnIncoherentTheoryDisowns(t *testing.T) {
	got := IncoherentBuiltinAtoms(tcDeriv("=:=", "a"), tcProfile(tcDisowningTheory{}))
	if len(got) != 1 || !got[0].Equal(tcLit("=:=", "a")) {
		t.Fatalf("expected exactly the offending atom, got %v", tcRender(got))
	}
}

// A coherent theory yields nothing. Without this the query could be returning every builtin
// atom it sees and every other test here would still pass.
func TestACoherentTheoryYieldsNothing(t *testing.T) {
	got := IncoherentBuiltinAtoms(tcDeriv("=:=", "a"), tcProfile(tcOwningTheory{}))
	if len(got) != 0 {
		t.Fatalf("coherent theory reported as incoherent: %v", tcRender(got))
	}
}

// THE DISCRIMINATING CONTROL. Arm 1 also answers NotMine and Check gives it the SAME
// rejection code. A query keyed on the outcome alone would report arm 1 too - naming a defect
// in a theory the host never bound, which is the misattribution inverted rather than fixed.
func TestArm1UnboundTheoryIsNotReportedAsIncoherent(t *testing.T) {
	got := IncoherentBuiltinAtoms(tcDeriv("=:=", "a"), tcProfile(tcUnboundTheory{}))
	if len(got) != 0 {
		t.Fatalf("arm 1 (no theory owns the predicate) is a HOST CAPABILITY refusal, not an "+
			"incoherent theory - the two share a rejection code and must not share this "+
			"query; got %v", tcRender(got))
	}
}

// Deduplicated on first appearance, in node order.
func TestRepeatedAndDistinctAtomsDedupInNodeOrder(t *testing.T) {
	got := IncoherentBuiltinAtoms(
		tcDeriv("=:=", "a", "<", "b", "=:=", "a"),
		tcProfile(tcDisowningTheory{}),
	)
	if len(got) != 2 || !got[0].Equal(tcLit("=:=", "a")) || !got[1].Equal(tcLit("<", "b")) {
		t.Fatalf("expected [=:=(a) <(b)] deduplicated in node order, got %v", tcRender(got))
	}
}

// THE DOCUMENTED LIMIT, MADE EXECUTABLE. The theory here is the same provably incoherent one
// as the first test, and the query returns empty - because this derivation cites no Builtin
// node for it to disagree on. An empty result is therefore not a coherence certificate.
func TestEmptyResultDoesNotCertifyTheTheoryCoherent(t *testing.T) {
	deriv := Derivation{
		Nodes: []Node{LeafNode{Conc: tcLit("edge", "a"), Evidence: Evidence{}}},
		Root:  0,
	}
	got := IncoherentBuiltinAtoms(deriv, tcProfile(tcDisowningTheory{}))
	if len(got) != 0 {
		t.Fatalf("expected empty: the query can only witness incoherence on atoms the "+
			"derivation cites, and this one cites no Builtin node; got %v", tcRender(got))
	}
}
