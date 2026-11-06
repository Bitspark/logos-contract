// account-v2 list reification (#277), after #3022 — the Go mirror of contract/rs's
// account_v2_reify tests. Every certified literal claim is EXACT (#3022): a derivation whose
// nodes conclude the REIFIED `list(…)` spelling of a cons-form instance is REFUSED by Check,
// under every term identity, because the reified conclusion is not the instantiated head. The
// cons↔`list` canonicalization stays a bijection (no conflation) and is the PRESENTATION
// equivalence a producer shows a list in, beside the exact fact; the cons-form derivation an
// engine emits is accepted as before.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// ----------------------------- profile + helpers -----------------------------

// noTheory owns nothing (no builtins needed here).
// test-double: consumer(owns no predicate)
type noTheory struct{}

func (noTheory) Owns(Symbol) bool                   { return false }
func (noTheory) Decide(GroundLiteral) TheoryOutcome { return TheoryNotMine{} }

// srcLeaves declares src extensional and admits any src leaf whose argument, AFTER
// cons↔`list` canonicalization, is in its cons-form EDB-of-record — exercising the
// "a reified leaf matches the cons-form EDB" obligation of #277 via the public
// CanonicalizeLists primitive (the SAME bijection Check uses).
// test-double: consumer(a cons-form src EDB matched after list canonicalization)
type srcLeaves struct {
	extensional *PredicateSet
	edbCons     []GroundLiteral
}

func newSrcLeaves(edbCons []GroundLiteral) srcLeaves {
	return srcLeaves{extensional: PredicateSetOf("src"), edbCons: edbCons}
}

func (s srcLeaves) Extensional() *PredicateSet { return s.extensional }

func (s srcLeaves) Verify(atom GroundLiteral, _ Evidence, _ unitCtx) LeafOutcome {
	canon := func(g GroundLiteral) GroundLiteral {
		args := make([]core.Value, len(g.Args))
		for i, a := range g.Args {
			args[i] = CanonicalizeLists(a)
		}
		return GroundLiteral{Pred: g.Pred, Args: args}
	}
	want := canon(atom)
	for _, row := range s.edbCons {
		if canon(row).Equal(want) {
			return LeafAdmit{}
		}
	}
	return LeafReject{Code: "not_in_edb"}
}

func srcProfile(leaves srcLeaves) *CheckProfile[unitCtx] {
	return &CheckProfile[unitCtx]{
		Theory: noTheory{},
		Leaves: leaves,
		Admit:  AlwaysAdmit[unitCtx]{},
		Limits: DefaultLimits(),
	}
}

func av(s string) core.Value { return core.NewAtom([]byte(s)) }
func nilv() core.Value       { return av("[]") }
func consv(head, tail core.Value) core.Value {
	return core.NewTuple(av("."), head, tail)
}

// consList builds a proper cons list [e0, e1, …] right-folded onto [] — the FROZEN form.
func consList(elems ...core.Value) core.Value {
	acc := nilv()
	for i := len(elems) - 1; i >= 0; i-- {
		acc = consv(elems[i], acc)
	}
	return acc
}

// listEmbed builds the ontos/data flat `list` embedding list(e0, …) — the REIFIED form.
func listEmbed(elems ...core.Value) core.Value {
	items := make([]core.Value, 0, len(elems)+1)
	items = append(items, av("list"))
	items = append(items, elems...)
	return core.NewTuple(items...)
}

func gl(pred string, arg core.Value) GroundLiteral {
	return NewGroundLiteral(pred, arg)
}

// wrapProgram is wrap(X) :- src(X). — src extensional, wrap intensional; the grounding
// subst binds X to the cons-form list term (the surface identity).
func wrapProgram() Program {
	return NewMapProgram().With(
		NewClauseId("wrap_rule"),
		NewClause(NewGoal("wrap", Var("X")), NewGoal("src", Var("X"))),
	)
}

// substXConsList is subst {X = <cons-form list term>}.
func substXConsList(elems ...core.Value) Subst {
	return Subst{NewVarId("X"): FromValue(consList(elems...))}
}

// ======================= 1. THE REIFIED SPELLING IS REFUSED (#3022) ========================

func TestReifiedListDerivationIsRefused3022(t *testing.T) {
	elems := []core.Value{av("a"), av("b")}
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(elems...))})

	wrapList := gl("wrap", listEmbed(elems...))
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", listEmbed(elems...)), Evidence: NoEvidence()},
		RuleNode{
			Conc:     wrapList,
			Clause:   NewClauseId("wrap_rule"),
			Subst:    substXConsList(elems...),
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	got := Check[unitCtx](program, wrapList, deriv, unitCtx{}, srcProfile(leaves))
	if got.IsAccept() || got.Code().Code() != "instantiation_mismatch" {
		t.Fatalf("a reified conclusion is not the instantiated head (#3022); got %s", got.String())
	}
}

func TestReifiedRootIsRefusedAgainstConsClaim3022(t *testing.T) {
	elems := []core.Value{av("a"), av("b")}
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(elems...))})
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", listEmbed(elems...)), Evidence: NoEvidence()},
		RuleNode{
			Conc:     gl("wrap", listEmbed(elems...)),
			Clause:   NewClauseId("wrap_rule"),
			Subst:    substXConsList(elems...),
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	consClaim := gl("wrap", consList(elems...))
	got := Check[unitCtx](program, consClaim, deriv, unitCtx{}, srcProfile(leaves))
	if got.IsAccept() || got.Code().Code() != "instantiation_mismatch" {
		t.Fatalf("a reified node is refused at its own head before the root is read (#3022); got %s", got.String())
	}
}

func TestDefaultConsDerivationStillAccepts(t *testing.T) {
	elems := []core.Value{av("a"), av("b")}
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(elems...))})
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", consList(elems...)), Evidence: NoEvidence()},
		RuleNode{
			Conc:     gl("wrap", consList(elems...)),
			Clause:   NewClauseId("wrap_rule"),
			Subst:    substXConsList(elems...),
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	consClaim := gl("wrap", consList(elems...))
	got := Check[unitCtx](program, consClaim, deriv, unitCtx{}, srcProfile(leaves))
	if !got.IsAccept() {
		t.Fatalf("the frozen cons-form derivation must still accept (additive); got %s", got.String())
	}
}

// ================================ 2. REJECT ===============================

func TestReifiedWrongOrderListIsRejected(t *testing.T) {
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(av("a"), av("b")))})
	// subst binds X = [a,b] but the Rule claims wrap(list(b,a)) — a different sequence.
	wrong := gl("wrap", listEmbed(av("b"), av("a")))
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", listEmbed(av("a"), av("b"))), Evidence: NoEvidence()},
		RuleNode{
			Conc:     wrong,
			Clause:   NewClauseId("wrap_rule"),
			Subst:    substXConsList(av("a"), av("b")),
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	got := Check[unitCtx](program, wrong, deriv, unitCtx{}, srcProfile(leaves))
	if got.IsAccept() {
		t.Fatal("a wrong-order reified list was wrongly ACCEPTED (unsound)")
	}
	if got.Code().Code() != "instantiation_mismatch" {
		t.Errorf("got code %q want instantiation_mismatch", got.Code().Code())
	}
}

func TestImproperTailNotConflatedWithProperList(t *testing.T) {
	program := wrapProgram()
	// subst binds X to the IMPROPER cons [a|b] = .(a,b).
	improper := consv(av("a"), av("b"))
	subst := Subst{NewVarId("X"): FromValue(improper)}
	leaves := newSrcLeaves([]GroundLiteral{gl("src", improper)})
	// The Rule DISHONESTLY claims wrap(list(a,b)) (a proper 2-list) for the improper subst.
	dishonest := gl("wrap", listEmbed(av("a"), av("b")))
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", improper), Evidence: NoEvidence()},
		RuleNode{
			Conc:     dishonest,
			Clause:   NewClauseId("wrap_rule"),
			Subst:    subst,
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	got := Check[unitCtx](program, dishonest, deriv, unitCtx{}, srcProfile(leaves))
	if got.IsAccept() {
		t.Fatal("an improper cons claimed as a proper list was wrongly ACCEPTED (unsound)")
	}
	if got.Code().Code() != "instantiation_mismatch" {
		t.Errorf("got code %q want instantiation_mismatch", got.Code().Code())
	}
}

func TestDefaultDistinctConsStillRejects(t *testing.T) {
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(av("a")))})
	deriv := NewDerivation([]Node{
		LeafNode{Conc: gl("src", consList(av("a"))), Evidence: NoEvidence()},
		RuleNode{
			Conc:     gl("wrap", consList(av("a"))),
			Clause:   NewClauseId("wrap_rule"),
			Subst:    substXConsList(av("a")),
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)
	otherClaim := gl("wrap", consList(av("z")))
	got := Check[unitCtx](program, otherClaim, deriv, unitCtx{}, srcProfile(leaves))
	if got.IsAccept() {
		t.Fatal("a distinct cons root matched the claim (unsound)")
	}
	if got.Code().Code() != "root_conclusion_mismatch" {
		t.Errorf("got code %q want root_conclusion_mismatch", got.Code().Code())
	}
}

// ============================ 3. BIJECTION ============================

func TestEmptyListAndNilStayDistinct(t *testing.T) {
	if !CanonicalizeLists(nilv()).Equal(nilv()) {
		t.Error("[] must be left as the bare atom")
	}
	if !CanonicalizeLists(listEmbed()).Equal(listEmbed()) {
		t.Error("list() must be left as the empty embedding")
	}
	if CanonicalizeLists(nilv()).Equal(CanonicalizeLists(listEmbed())) {
		t.Error("[] and list() must NOT canonicalize to the same value")
	}
}

func TestConsAndListAreBijectiveNoConflation(t *testing.T) {
	ab := []core.Value{av("a"), av("b")}
	ba := []core.Value{av("b"), av("a")}
	if !CanonicalizeLists(consList(ab...)).Equal(CanonicalizeLists(listEmbed(ab...))) {
		t.Error("same sequence, two spellings → equal canonical form")
	}
	if !CanonicalizeLists(consList(ab...)).Equal(listEmbed(ab...)) {
		t.Error("cons [a,b] canonicalizes to list(a,b)")
	}
	if CanonicalizeLists(consList(ab...)).Equal(CanonicalizeLists(consList(ba...))) {
		t.Error("distinct sequences must NOT conflate")
	}
	if CanonicalizeLists(consList(av("a"))).Equal(CanonicalizeLists(consList(ab...))) {
		t.Error("a length-1 list must not conflate with a length-2 list")
	}
}

func TestCanonicalizeIsIdempotent(t *testing.T) {
	v := consList(av("a"), av("b"))
	once := CanonicalizeLists(v)
	if !once.Equal(CanonicalizeLists(once)) {
		t.Error("canonicalize must be idempotent")
	}
	already := listEmbed(av("a"))
	if !CanonicalizeLists(already).Equal(already) {
		t.Error("an already-list value is a no-op")
	}
}

func TestImproperConsIsNotReified(t *testing.T) {
	improper := consv(av("a"), av("b"))
	if !CanonicalizeLists(improper).Equal(improper) {
		t.Error("improper cons must be left as the cons tuple")
	}
	if CanonicalizeLists(improper).Equal(listEmbed(av("a"), av("b"))) {
		t.Error("improper cons must not collapse onto a list")
	}
}

func TestNonlistCompoundUntouchedButListFunctorIsASequence(t *testing.T) {
	// f(a, b) is not a list — identity.
	f := core.NewTuple(av("f"), av("a"), av("b"))
	if !CanonicalizeLists(f).Equal(f) {
		t.Error("a non-list compound must be untouched")
	}
	// f([a]) → f(list(a)): the inner cons list reifies, the f-compound does not.
	fWithList := core.NewTuple(av("f"), consList(av("a")))
	expected := core.NewTuple(av("f"), listEmbed(av("a")))
	if !CanonicalizeLists(fWithList).Equal(expected) {
		t.Error("an inner cons list inside a compound must canonicalize")
	}
}

func TestDeepNestedListsCanonicalizeRecursively(t *testing.T) {
	// [[a], [b, c]] in cons form ↔ list(list(a), list(b, c)).
	outerCons := consList(consList(av("a")), consList(av("b"), av("c")))
	expected := listEmbed(listEmbed(av("a")), listEmbed(av("b"), av("c")))
	if !CanonicalizeLists(outerCons).Equal(expected) {
		t.Error("deep nested cons lists must canonicalize recursively")
	}
	outerList := listEmbed(consList(av("a")), listEmbed(av("b"), av("c")))
	if !CanonicalizeLists(outerList).Equal(expected) {
		t.Error("the list-spelling of the same nested sequence must canonicalize to the same")
	}
}

func TestReifiedLeafMatchesConsEdb(t *testing.T) {
	program := wrapProgram()
	leaves := newSrcLeaves([]GroundLiteral{gl("src", consList(av("a"), av("b")))})
	leafList := gl("src", listEmbed(av("a"), av("b")))
	deriv := NewDerivation([]Node{LeafNode{Conc: leafList, Evidence: NoEvidence()}}, 0)
	got := Check[unitCtx](program, leafList, deriv, unitCtx{}, srcProfile(leaves))
	if !got.IsAccept() {
		t.Fatalf("a reified leaf must match the cons-form EDB-of-record; got %s", got.String())
	}

	leaves2 := newSrcLeaves([]GroundLiteral{gl("src", consList(av("a"), av("b")))})
	absent := gl("src", listEmbed(av("z")))
	deriv2 := NewDerivation([]Node{LeafNode{Conc: absent, Evidence: NoEvidence()}}, 0)
	got2 := Check[unitCtx](program, absent, deriv2, unitCtx{}, srcProfile(leaves2))
	if got2.IsAccept() {
		t.Fatal("a leaf absent from the EDB was wrongly admitted")
	}
	if got2.Code().Code() != "leaf_rejected" {
		t.Errorf("got code %q want leaf_rejected", got2.Code().Code())
	}
}
