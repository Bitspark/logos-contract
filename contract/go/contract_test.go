// Language-local unit tests mirroring the Rust crate's #[cfg(test)] modules
// (term.rs, literal.rs, reify.rs). These pin the model below the shared-vector
// surface and live only in this binding's suite (per the {rs,go} parity
// discipline). They are NOT cross-core vectors.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

func TestGroundTermRoundTripsThroughValue(t *testing.T) {
	tm := Tuple(Atom([]byte("pair")), Atom([]byte("a")), Atom([]byte("b")))
	if !tm.IsGround() {
		t.Fatal("expected ground")
	}
	v, ok := tm.EraseGround()
	if !ok {
		t.Fatal("erase_ground failed on ground term")
	}
	if !FromValue(v).Equal(tm) {
		t.Errorf("round-trip mismatch: %s != %s", FromValue(v), tm)
	}
}

func TestHoleAtDepthMakesTermNonGround(t *testing.T) {
	// pair(X, "a") — a hole inside a tuple, not a whole-argument variable.
	tm := Tuple(Atom([]byte("pair")), Var("X"), Atom([]byte("a")))
	if tm.IsGround() {
		t.Fatal("expected non-ground")
	}
	if _, ok := tm.EraseGround(); ok {
		t.Fatal("expected erase_ground to fail")
	}
}

func TestVarIdentityIsByID(t *testing.T) {
	if !Var("X").Equal(Var("X")) {
		t.Error("Var(X) should equal Var(X)")
	}
	if Var("X").Equal(Var("Y")) {
		t.Error("Var(X) should not equal Var(Y)")
	}
}

func TestSubstituteThenGroundMatchesExpected(t *testing.T) {
	// edge(X, Y) with {X: a, Y: b}  ==  edge(a, b)
	goal := NewGoal("edge", Var("X"), Var("Y"))
	subst := Subst{NewVarId("X"): Atom([]byte("a")), NewVarId("Y"): Atom([]byte("b"))}
	grounded, ok := goal.Substitute(subst).AsGround()
	if !ok {
		t.Fatal("expected ground after substitute")
	}
	expected := NewGroundLiteral("edge", core.NewAtom([]byte("a")), core.NewAtom([]byte("b")))
	if !grounded.Equal(expected) {
		t.Errorf("got %v want %v", grounded, expected)
	}
}

func TestUnboundVarStaysNonGround(t *testing.T) {
	goal := NewGoal("edge", Var("X"), Var("Y"))
	subst := Subst{NewVarId("X"): Atom([]byte("a"))}
	if _, ok := goal.Substitute(subst).AsGround(); ok {
		t.Fatal("expected non-ground with unbound Y")
	}
}

func TestQuoteReifyRoundTripsTermsWithHoles(t *testing.T) {
	roundTrips := func(term Term) {
		quoted := Quote(term)
		got, ok := Reify(quoted)
		if !ok {
			t.Errorf("reify failed for %s", term)
			return
		}
		if !got.Equal(term) {
			t.Errorf("round-trip mismatch: %s != %s", got, term)
		}
	}
	// pair(X, "a") — a term with a hole at depth, quoted to ground data.
	roundTrips(Tuple(Atom([]byte("pair")), Var("X"), Atom([]byte("a"))))
	roundTrips(Atom([]byte("solo")))
	roundTrips(Var("Y"))
	roundTrips(Tuple())
}

func TestReifyRejectsNonQuotedValues(t *testing.T) {
	// A bare atom is not in the image of quote.
	if _, ok := Reify(core.NewAtom([]byte("x"))); ok {
		t.Error("bare atom should not reify")
	}
	// A wrapper with an unknown tag.
	if _, ok := Reify(core.NewTuple(core.NewAtom([]byte{0x09}), core.NewAtom([]byte("x")))); ok {
		t.Error("unknown-tag wrapper should not reify")
	}
}

// ============ issue #253: term-nesting depth bound (DoS hardening) ============

// deepValue builds a ground core.Value nested `depth` levels deep ITERATIVELY (so the
// fixture itself never recurses): f(f(…f(a)…)).
func deepValue(depth int) core.Value {
	var v core.Value = core.NewAtom([]byte("a"))
	for i := 0; i < depth; i++ {
		v = core.NewTuple(core.NewAtom([]byte("f")), v)
	}
	return v
}

func TestTermDepthLEIsIterativeAndDoesNotOverflow(t *testing.T) {
	// 50_000 levels — FromValue (iterative) builds it, TermDepthLE (iterative)
	// measures it; neither recurses, so neither overflows.
	v := deepValue(50_000)
	tm := FromValue(v)
	if _, ok := tm.(TupleTerm); !ok {
		t.Fatal("expected a deep TupleTerm from FromValue")
	}
	if TermDepthLE(tm, MaxTermDepthDefault) {
		t.Error("a 50_000-deep term must exceed the default bound")
	}
	if !ValueDepthLE(deepValue(MaxTermDepthDefault-1), MaxTermDepthDefault) {
		t.Error("a term at the bound must be within it")
	}
	if ValueDepthLE(deepValue(MaxTermDepthDefault), MaxTermDepthDefault) {
		t.Error("a term one past the bound must exceed it")
	}
}

func TestCheckRejectsOverDeepTermTermTooDeepNotACrash(t *testing.T) {
	// edge(<deep>, b) with a deep first argument. edge is extensional in the demo
	// profile, so a single leaf reaches the depth guard. A recursive check could
	// overflow; the iterative guard rejects it.
	concl := GroundLiteral{Pred: SymbolFromString("edge"), Args: []core.Value{deepValue(50_000), core.NewAtom([]byte("b"))}}
	deriv := NewDerivation([]Node{LeafNode{Conc: concl, Evidence: NoEvidence()}}, 0)
	profile := demoTermDepthProfile(DefaultLimits())
	got := Check[struct{}](NewMapProgram(), concl, deriv, struct{}{}, profile)
	if got.IsAccept() || got.Code().Code() != "term_too_deep" {
		t.Fatalf("expected term_too_deep, got %s", got)
	}
	if !got.Code().IsStructural() {
		t.Error("term_too_deep must be a structural-band code")
	}
}

func TestCheckAcceptsWithinBoundTerm(t *testing.T) {
	// The SAME shape at a shallow, within-bound depth is still accepted (the bound
	// never weakens the accept path).
	arg := deepValue(MaxTermDepthDefault - 2)
	concl := GroundLiteral{Pred: SymbolFromString("edge"), Args: []core.Value{arg, core.NewAtom([]byte("b"))}}
	deriv := NewDerivation([]Node{LeafNode{Conc: concl, Evidence: NoEvidence()}}, 0)
	profile := demoTermDepthProfile(DefaultLimits())
	got := Check[struct{}](NewMapProgram(), concl, deriv, struct{}{}, profile)
	if !got.IsAccept() {
		t.Fatalf("a within-bound term must be accepted, got %s", got)
	}
}

// demoTermDepthProfile is a minimal demo_v1-style profile (edge extensional, lt
// theory, always-admit) for the term-depth tests.
func demoTermDepthProfile(limits CheckLimits) *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: termDepthLtTheory{},
		Leaves: termDepthEdgeLeaves{ext: PredicateSetOf("edge")},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: limits,
	}
}

// test-double: consumer(owns lt for the term-depth profile)
type termDepthLtTheory struct{}

func (termDepthLtTheory) Owns(pred Symbol) bool { return pred.Equal(SymbolFromString("lt")) }
func (termDepthLtTheory) Decide(GroundLiteral) TheoryOutcome {
	return TheoryFails{Code: "not_less_than"}
}

// test-double: consumer(admits any edge leaf)
type termDepthEdgeLeaves struct{ ext *PredicateSet }

func (e termDepthEdgeLeaves) Extensional() *PredicateSet { return e.ext }
func (termDepthEdgeLeaves) Verify(GroundLiteral, Evidence, struct{}) LeafOutcome {
	return LeafAdmit{}
}
