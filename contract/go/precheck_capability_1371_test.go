package contract

import (
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// The pre-check capability query (issue #1371 stage 1), Go half of the tri-core surface.
//
// The two that matter are the NEGATIVE ones:
//   - TestEmptyResultDoesNotPromiseAcceptance — an empty result means no capability refusal
//     will occur, NOT that Check will accept.
//   - TestNeverCallsDecideGround — proven by a theory whose DecideGround panics.

// --------------------------------- theories ---------------------------------

// test-double: consumer(owns no predicate: the theory-less host)
type pcUnboundTheory struct{}

func (pcUnboundTheory) Owns(pred Symbol) bool { return false }
func (pcUnboundTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundDisowned()
}

// test-double: consumer(owns every predicate and holds it)
type pcOwningTheory struct{}

func (pcOwningTheory) Owns(pred Symbol) bool { return true }
func (pcOwningTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundHolds()
}

// test-double: consumer(owns exactly one named predicate and holds it)
type pcOwnsOnly struct{ name string }

func (t pcOwnsOnly) Owns(pred Symbol) bool { return pred.String() == t.name }
func (pcOwnsOnly) DecideGround(atom GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundHolds()
}

// Owns everything and PANICS if asked to decide — the query must never call DecideGround.
// test-double: adversarial(panics if asked to decide)
type pcExplodingTheory struct{}

func (pcExplodingTheory) Owns(pred Symbol) bool { return true }
func (pcExplodingTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	panic("the pre-check query must not call DecideGround()")
}

// ---------------------------------- leaves ----------------------------------

// test-double: consumer(declares a chosen extensional set)
type pcLeaves struct{ extensional *PredicateSet }

func (l pcLeaves) Extensional() *PredicateSet { return l.extensional }
func (pcLeaves) Verify(atom GroundLiteral, evidence Evidence, ctx struct{}) LeafOutcome {
	return LeafReject{Code: "not_a_leaf_test"}
}

func pcEmptyLeaves() pcLeaves { return pcLeaves{extensional: NewPredicateSet()} }

func pcLeavesWith(pred string) pcLeaves {
	set := NewPredicateSet()
	set.Insert(SymbolFromString(pred))
	return pcLeaves{extensional: set}
}

// ---------------------------------- harness ----------------------------------

func pcAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

func pcDeriv(preds ...string) Derivation {
	nodes := make([]Node, 0, len(preds))
	for _, p := range preds {
		nodes = append(nodes, BuiltinNode{
			Conc: NewGroundLiteral(p, pcAtom("a"), pcAtom("a")),
		})
	}
	return Derivation{Nodes: nodes, Root: 0}
}

func pcProfile(theory Theory, leaves pcLeaves) *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: theory,
		Leaves: leaves,
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

func pcNames(syms []Symbol) []string {
	out := make([]string, 0, len(syms))
	for _, s := range syms {
		out = append(out, s.String())
	}
	return out
}

func pcEqual(a []string, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// ----------------------------------- tests -----------------------------------

func TestUnboundTheoryNamesThePredicate(t *testing.T) {
	p := pcProfile(pcUnboundTheory{}, pcEmptyLeaves())
	d := pcDeriv("=:=")
	got := pcNames(UnownedBuiltinPredicates(d, p))
	if !pcEqual(got, []string{"=:="}) {
		t.Fatalf("want [=:=], got %v", got)
	}
	if ProfileDecidesAllBuiltins(d, p) {
		t.Fatal("a theory-less host must not report all builtins decidable")
	}
}

func TestBoundTheoryReportsNothing(t *testing.T) {
	p := pcProfile(pcOwningTheory{}, pcEmptyLeaves())
	d := pcDeriv("=:=")
	if got := UnownedBuiltinPredicates(d, p); len(got) != 0 {
		t.Fatalf("want empty, got %v", pcNames(got))
	}
	if !ProfileDecidesAllBuiltins(d, p) {
		t.Fatal("a bound theory must report all builtins decidable")
	}
}

func TestMixedOwnershipNamesOnlyTheUnowned(t *testing.T) {
	p := pcProfile(pcOwnsOnly{name: "=:="}, pcEmptyLeaves())
	d := pcDeriv("=:=", ">", "<")
	got := pcNames(UnownedBuiltinPredicates(d, p))
	if !pcEqual(got, []string{">", "<"}) {
		t.Fatalf("want [> <], got %v", got)
	}
}

// Deduplicated on first appearance, in derivation node order — so the report is
// deterministic for a given derivation rather than merely a set.
func TestDeduplicatedInNodeOrder(t *testing.T) {
	p := pcProfile(pcUnboundTheory{}, pcEmptyLeaves())
	d := pcDeriv(">", "=:=", ">", "<", "=:=")
	got := pcNames(UnownedBuiltinPredicates(d, p))
	if !pcEqual(got, []string{">", "=:=", "<"}) {
		t.Fatalf("want [> =:= <], got %v", got)
	}
}

// THE FORM-33 GUARD. An empty result must NOT be read as "Check will accept".
//
// The theory owns the predicate, so the query is EMPTY — the strongest possible "no
// capability problem" answer — and Check still rejects, because the predicate is also
// extensional (a genuine §4.4 partition overlap). This is what stops the query being
// documented as a verifiability oracle.
func TestEmptyResultDoesNotPromiseAcceptance(t *testing.T) {
	p := pcProfile(pcOwningTheory{}, pcLeavesWith("=:="))
	d := pcDeriv("=:=")

	if got := UnownedBuiltinPredicates(d, p); len(got) != 0 {
		t.Fatalf("precondition: capability query must be clean, got %v", pcNames(got))
	}

	claim := NewGroundLiteral("=:=", pcAtom("a"), pcAtom("a"))
	out := Check(NewMapProgram(), claim, d, struct{}{}, p)

	if out.IsAccept() {
		t.Fatal("expected a structural rejection: an empty capability report does not make an overlapping account valid")
	}
	if out.Verdict.Code() != PredicatePartitionViolation {
		t.Fatalf("want predicate_partition_violation, got %v", out.Verdict.Code())
	}
}

// The query is total and side-effect-free: it consults Owns only. Proven rather than
// asserted — this theory panics if DecideGround is ever reached.
func TestNeverCallsDecideGround(t *testing.T) {
	p := pcProfile(pcExplodingTheory{}, pcEmptyLeaves())
	d := pcDeriv("=:=", ">", "<")
	if got := UnownedBuiltinPredicates(d, p); len(got) != 0 {
		t.Fatalf("want empty, got %v", pcNames(got))
	}
	if !ProfileDecidesAllBuiltins(d, p) {
		t.Fatal("want true")
	}
}

func TestNoBuiltinsReportsNothing(t *testing.T) {
	p := pcProfile(pcUnboundTheory{}, pcEmptyLeaves())
	d := Derivation{Nodes: []Node{}, Root: 0}
	if got := UnownedBuiltinPredicates(d, p); len(got) != 0 {
		t.Fatalf("want empty, got %v", pcNames(got))
	}
}
