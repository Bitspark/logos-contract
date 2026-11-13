// Language-local tests for the Go binding's host-extension band and the two rule-head
// sealing/partition branches — the parts NOT pinned by the shared, cross-language
// oracle.
//
// The shared check.json/account.json vectors are no longer replayed here: that is the
// differential CLI harness (conformance/, ADR 0006), which drives the per-language
// check CLIs as black boxes over the one oracle. This file keeps only the host band
// (builtin_failed / leaf_rejected / rule_inadmissible) + the rule-head branch tests.
package contract

import (
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// =================== the demo_v1 profile (shared by name) ===================
// Implemented identically in each language binding; the JSON pins program +
// derivation + claim + outcome. Context is unit (the empty struct).

// unitCtx is the unit context for the demo_v1 profile.
type unitCtx = struct{}

// ltTheory owns lt: lt(a, b) Holds iff both args are atoms and a < b bytewise.
// Pure, total, config-free.
// test-double: consumer(a less-than theory over atoms)
type ltTheory struct{}

func (ltTheory) Owns(pred Symbol) bool { return pred.Equal(SymbolFromString("lt")) }

func (ltTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	if len(atom.Args) != 2 {
		return completion.TheoryGroundFails("lt_arity")
	}
	a, aok := atom.Args[0].(core.Atom)
	b, bok := atom.Args[1].(core.Atom)
	if aok && bok && bytesLess(a.Bytes(), b.Bytes()) {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("not_less_than")
}

// bytesLess reports lexicographic byte ordering (a < b), matching Rust's slice
// comparison.
func bytesLess(a, b []byte) bool {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	for i := 0; i < n; i++ {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return len(a) < len(b)
}

// edgeLeaves declares edge extensional and admits any edge leaf (trusted facts).
// test-double: consumer(admits any edge leaf)
type edgeLeaves struct {
	extensional *PredicateSet
}

func newEdgeLeaves() edgeLeaves {
	return edgeLeaves{extensional: PredicateSetOf("edge")}
}

func (e edgeLeaves) Extensional() *PredicateSet { return e.extensional }

func (edgeLeaves) Verify(_ GroundLiteral, _ Evidence, _ unitCtx) LeafOutcome {
	return LeafAdmit{}
}

func demoProfile(limits CheckLimits) *CheckProfile[unitCtx] {
	return &CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: newEdgeLeaves(),
		Admit:  AlwaysAdmit[unitCtx]{},
		Limits: limits,
	}
}

// ===== language-local host-extension band tests (NOT in the shared vectors) =====
// The host band's sub-codes are an open set pinned only in a consumer's own suite;
// here we verify the three wrapper codes + that the seam's sub-code reaches detail.

func ltLit(a, b string) GroundLiteral {
	return NewGroundLiteral("lt", ontosValue(a), ontosValue(b))
}

func ontosValue(s string) core.Value { return core.NewAtom([]byte(s)) }

func TestHostBandBuiltinFailed(t *testing.T) {
	// lt(b, a): b > a, so the theory Fails -> builtin_failed, sub-code in detail.
	deriv := NewDerivation([]Node{BuiltinNode{Conc: ltLit("b", "a")}}, 0)
	profile := demoProfile(DefaultLimits())
	got := Check[unitCtx](NewMapProgram(), ltLit("b", "a"), deriv, unitCtx{}, profile)
	if got.IsAccept() {
		t.Fatalf("expected builtin_failed, got accept")
	}
	if got.Verdict.Code().Code() != "builtin_failed" {
		t.Errorf("got code %q want builtin_failed", got.Verdict.Code().Code())
	}
	if got.Verdict.Detail() != "not_less_than" {
		t.Errorf("got detail %q want not_less_than", got.Verdict.Detail())
	}
	if got.Verdict.Code().IsStructural() {
		t.Errorf("builtin_failed must not be structural")
	}
}

// rejectingLeaves always rejects with a custom sub-code.
// test-double: adversarial(rejects every leaf with a custom sub-code)
type rejectingLeaves struct {
	extensional *PredicateSet
}

func (r rejectingLeaves) Extensional() *PredicateSet { return r.extensional }

func (rejectingLeaves) Verify(_ GroundLiteral, _ Evidence, _ unitCtx) LeafOutcome {
	return LeafReject{Code: "no_attestation"}
}

func TestHostBandLeafRejected(t *testing.T) {
	edge := NewGroundLiteral("edge", ontosValue("a"), ontosValue("b"))
	deriv := NewDerivation([]Node{LeafNode{Conc: edge, Evidence: NoEvidence()}}, 0)
	profile := &CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: rejectingLeaves{extensional: PredicateSetOf("edge")},
		Admit:  AlwaysAdmit[unitCtx]{},
		Limits: DefaultLimits(),
	}
	got := Check[unitCtx](NewMapProgram(), edge, deriv, unitCtx{}, profile)
	if got.IsAccept() {
		t.Fatalf("expected leaf_rejected, got accept")
	}
	if got.Verdict.Code().Code() != "leaf_rejected" {
		t.Errorf("got code %q want leaf_rejected", got.Verdict.Code().Code())
	}
	if got.Verdict.Detail() != "no_attestation" {
		t.Errorf("got detail %q want no_attestation", got.Verdict.Detail())
	}
}

// denyAdmit always rejects rule admissibility.
// test-double: adversarial(rejects every otherwise-valid rule)
type denyAdmit struct{}

func (denyAdmit) Admissible(_ Clause, _ NodeMeta, _ unitCtx) RuleOutcome {
	return RuleReject{Code: "placement_mismatch"}
}

func TestHostBandRuleInadmissible(t *testing.T) {
	// program: greet(X) :- edge(X, X).  (intensional head greet, extensional body edge)
	program := NewMapProgram().With(
		NewClauseId("greet_rule"),
		NewClause(
			NewGoal("greet", Var("X")),
			NewGoal("edge", Var("X"), Var("X")),
		),
	)
	edgeAA := NewGroundLiteral("edge", ontosValue("a"), ontosValue("a"))
	greetA := NewGroundLiteral("greet", ontosValue("a"))
	subst := Subst{NewVarId("X"): Atom([]byte("a"))}
	deriv := NewDerivation([]Node{
		LeafNode{Conc: edgeAA, Evidence: NoEvidence()},
		RuleNode{
			Conc:     greetA,
			Clause:   NewClauseId("greet_rule"),
			Subst:    subst,
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	profile := &CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: newEdgeLeaves(),
		Admit:  denyAdmit{},
		Limits: DefaultLimits(),
	}
	got := Check[unitCtx](program, greetA, deriv, unitCtx{}, profile)
	if got.IsAccept() {
		t.Fatalf("expected rule_inadmissible, got accept")
	}
	if got.Verdict.Code().Code() != "rule_inadmissible" {
		t.Errorf("got code %q want rule_inadmissible", got.Verdict.Code().Code())
	}
	if got.Verdict.Detail() != "placement_mismatch" {
		t.Errorf("got detail %q want placement_mismatch", got.Verdict.Detail())
	}
}

// ===== sealing/partition branches on a Rule head (go-local; shared program is clean) =====

func TestRuleHeadCollidesWithExtensionalIsSealed(t *testing.T) {
	// edge_sym: edge(X,Y) :- edge(Y,X). edge is extensional, so a rule concluding it
	// is the §4.2 "rule head collides with an extensional predicate" error.
	program := NewMapProgram().With(
		NewClauseId("edge_sym"),
		NewClause(
			NewGoal("edge", Var("X"), Var("Y")),
			NewGoal("edge", Var("Y"), Var("X")),
		),
	)
	edgeBA := NewGroundLiteral("edge", ontosValue("b"), ontosValue("a"))
	edgeAB := NewGroundLiteral("edge", ontosValue("a"), ontosValue("b"))
	subst := Subst{NewVarId("X"): Atom([]byte("a")), NewVarId("Y"): Atom([]byte("b"))}
	deriv := NewDerivation([]Node{
		LeafNode{Conc: edgeBA, Evidence: NoEvidence()},
		RuleNode{
			Conc:     edgeAB,
			Clause:   NewClauseId("edge_sym"),
			Subst:    subst,
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	profile := demoProfile(DefaultLimits())
	got := Check[unitCtx](program, edgeAB, deriv, unitCtx{}, profile)
	if got.IsAccept() || got.Verdict.Code().Code() != "sealed_violation" {
		t.Fatalf("expected sealed_violation, got %s", got)
	}
}

func TestRuleHeadOwnedByTheoryIsPartitionViolation(t *testing.T) {
	// lt_rule: lt(X,Y) :- edge(X,Y). lt is theory-owned, so a rule concluding it is
	// a §4.4 predicate-partition violation.
	program := NewMapProgram().With(
		NewClauseId("lt_rule"),
		NewClause(
			NewGoal("lt", Var("X"), Var("Y")),
			NewGoal("edge", Var("X"), Var("Y")),
		),
	)
	edgeAB := NewGroundLiteral("edge", ontosValue("a"), ontosValue("b"))
	ltAB := NewGroundLiteral("lt", ontosValue("a"), ontosValue("b"))
	subst := Subst{NewVarId("X"): Atom([]byte("a")), NewVarId("Y"): Atom([]byte("b"))}
	deriv := NewDerivation([]Node{
		LeafNode{Conc: edgeAB, Evidence: NoEvidence()},
		RuleNode{
			Conc:     ltAB,
			Clause:   NewClauseId("lt_rule"),
			Subst:    subst,
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	profile := demoProfile(DefaultLimits())
	got := Check[unitCtx](program, ltAB, deriv, unitCtx{}, profile)
	if got.IsAccept() || got.Verdict.Code().Code() != "predicate_partition_violation" {
		t.Fatalf("expected predicate_partition_violation, got %s", got)
	}
}
