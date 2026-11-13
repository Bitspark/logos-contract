// #2232 / #2227: the premise-match discipline at the two SPELLING-SENSITIVE premise sites
// (ruled by seat:caa, issuecomment-5811831064). A positive premise that cites a Builtin node, and
// a Neg premise's atom, must EXACTLY equal the grounded body literal. Rule and Leaf premises keep
// #277's account equality. The same inputs are pinned in contract/rs and contract/ts.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

func pmAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

var (
	pmConsA = core.NewTuple(pmAtom("."), pmAtom("a"), pmAtom("[]")) // .(a, []): the list [a], cons form
	pmListA = core.NewTuple(pmAtom("list"), pmAtom("a"))            // list(a): the list [a], reified form
)

// pmLeaves admits exactly its rows (exact identity) and attests their EDB snapshot.
// test-double: consumer(a fixed EDB: admits exactly its rows and attests them)
type pmLeaves struct {
	extensional *PredicateSet
	rows        []GroundLiteral
}

func (l pmLeaves) Extensional() *PredicateSet { return l.extensional }
func (l pmLeaves) Verify(lit GroundLiteral, _ Evidence, _ struct{}) LeafOutcome {
	for _, r := range l.rows {
		if r.Equal(lit) {
			return LeafAdmit{}
		}
	}
	return LeafReject{Code: "not_admitted"}
}
func (l pmLeaves) EdbSnapshot(p Symbol, _ struct{}) (Hash, bool) {
	var rows []GroundLiteral
	for _, r := range l.rows {
		if r.Pred.Equal(p) {
			rows = append(rows, r)
		}
	}
	if len(rows) == 0 {
		return Hash{}, false
	}
	return EdbTableHash(p, rows), true
}

func pmProfile(extensional []string, rows ...GroundLiteral) *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: NewStandardTheory(),
		Leaves: pmLeaves{PredicateSetOf(extensional...), rows},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

func pmVerdict(o Outcome) string {
	if o.IsAccept() {
		return "ACCEPT"
	}
	return o.Verdict.Code().Code()
}

// selfNeq checks self_neq(.(a,[])) from `self_neq(X) :- cand(X), X \== X.`, citing the builtin
// node `\==(.(a,[]), second)`.
func pmSelfNeq(second core.Value) Outcome {
	cand := NewGroundLiteral("cand", pmConsA)
	x := Var("X")
	prog := NewMapProgram().With(NewClauseId("self_neq"),
		NewClauseLits(NewGoal("self_neq", x),
			PosLit(NewGoal("cand", x)),
			PosLit(NewGoal(`\==`, x, x))))
	claim := NewGroundLiteral("self_neq", pmConsA)
	nodes := []Node{
		LeafNode{Conc: cand, Evidence: NoEvidence()},
		BuiltinNode{Conc: NewGroundLiteral(`\==`, pmConsA, second)},
		RuleNode{Conc: claim, Clause: NewClauseId("self_neq"),
			Subst:    Subst{NewVarId("X"): FromValue(pmConsA)},
			Premises: []Premise{PosNode(0), PosNode(1)}, Meta: NoMeta()},
	}
	return Check(prog, claim, NewDerivation(nodes, 2), struct{}{}, pmProfile([]string{"cand"}, cand))
}

// TestPremiseMatch2232BuiltinCitedPremiseIsExact: a Builtin node's truth is the term theory's
// decision on ITS OWN spelling, so it transfers only to that exact spelling.
func TestPremiseMatch2232BuiltinCitedPremiseIsExact(t *testing.T) {
	// A, the control: the honest node is decided false by the theory.
	if got := pmVerdict(pmSelfNeq(pmConsA)); got != "builtin_failed" {
		t.Fatalf(`A: \==(.(a,[]), .(a,[])) = %s, want builtin_failed`, got)
	}
	// B: the node is respelled `list(a)`, true in the theory, cited for `.(a,[]) \== .(a,[])`.
	if got := pmVerdict(pmSelfNeq(pmListA)); got != "instantiation_mismatch" {
		t.Fatalf(`B: \==(.(a,[]), list(a)) for X \== X = %s, want instantiation_mismatch`, got)
	}

	// `lst(X) :- seen(X), is_list(X).` over seen(list(a)), citing is_list(.(a,[])).
	x := Var("X")
	seen := NewGroundLiteral("seen", pmListA)
	lstProg := NewMapProgram().With(NewClauseId("lst"),
		NewClauseLits(NewGoal("lst", x), PosLit(NewGoal("seen", x)), PosLit(NewGoal("is_list", x))))
	lstClaim := NewGroundLiteral("lst", pmListA)
	lst := Check(lstProg, lstClaim, NewDerivation([]Node{
		LeafNode{Conc: seen, Evidence: NoEvidence()},
		BuiltinNode{Conc: NewGroundLiteral("is_list", pmConsA)},
		RuleNode{Conc: lstClaim, Clause: NewClauseId("lst"),
			Subst:    Subst{NewVarId("X"): FromValue(pmListA)},
			Premises: []Premise{PosNode(0), PosNode(1)}, Meta: NoMeta()},
	}, 2), struct{}{}, pmProfile([]string{"seen"}, seen))
	if got := pmVerdict(lst); got != "instantiation_mismatch" {
		t.Fatalf(`is_list(.(a,[])) cited for is_list(list(a)) = %s, want instantiation_mismatch`, got)
	}

	// `same(X,Y) :- l(X), r(Y), X == Y.` over l(.(a,[])), r(list(a)), citing ==(.(a,[]), .(a,[])).
	y := Var("Y")
	l := NewGroundLiteral("l", pmConsA)
	r := NewGroundLiteral("r", pmListA)
	sameProg := NewMapProgram().With(NewClauseId("same"),
		NewClauseLits(NewGoal("same", x, y),
			PosLit(NewGoal("l", x)), PosLit(NewGoal("r", y)), PosLit(NewGoal("==", x, y))))
	sameClaim := NewGroundLiteral("same", pmConsA, pmListA)
	same := Check(sameProg, sameClaim, NewDerivation([]Node{
		LeafNode{Conc: l, Evidence: NoEvidence()},
		LeafNode{Conc: r, Evidence: NoEvidence()},
		BuiltinNode{Conc: NewGroundLiteral("==", pmConsA, pmConsA)},
		RuleNode{Conc: sameClaim, Clause: NewClauseId("same"),
			Subst:    Subst{NewVarId("X"): FromValue(pmConsA), NewVarId("Y"): FromValue(pmListA)},
			Premises: []Premise{PosNode(0), PosNode(1), PosNode(2)}, Meta: NoMeta()},
	}, 3), struct{}{}, pmProfile([]string{"l", "r"}, l, r))
	if got := pmVerdict(same); got != "instantiation_mismatch" {
		t.Fatalf(`==(.(a,[]), .(a,[])) cited for .(a,[]) == list(a) = %s, want instantiation_mismatch`, got)
	}
}

// pmNegation checks `r :- \+ seen(body).` with a NegPremise atom `seen(premise)` against a
// certificate that seals `seen` with exactly `sealed` and the finite domain `domain`.
func pmNegation(body core.Value, sealed []core.Value, premise core.Value, domain []core.Value) Outcome {
	seenSym := SymbolFromString("seen")
	var rows []GroundLiteral
	for _, v := range sealed {
		rows = append(rows, NewGroundLiteral("seen", v))
	}
	prog := NewMapProgram().With(NewClauseId("r"),
		NewClauseLits(NewGoal("r"), NegLit(NewGoal("seen", FromValue(body)))))
	claim := NewGroundLiteral("r")
	pin := Hash{1}
	cert := ClosedModelCert{
		Scope:       NewStratumPrefix(0, []Symbol{seenSym}),
		ProgramHash: ProgramDigestOf(prog),
		ProfileHash: pin, CtxHash: pin, TheoryConfigHash: pin,
		EdbSnapshotHashes: []Hash{EdbTableHash(seenSym, rows)},
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("v"), domain)},
		Extensions:        []RelationTable{NewRelationTable(seenSym, 1, rows)},
		LimitsDecl:        CertSizeDecl{CertFacts: uint64(len(rows)), DomainValues: uint64(len(domain))},
	}
	cert.LimitsDecl.CertBytes = CertEncodedBytes(cert) // #2524: an honest cert declares its measured bytes
	nodes := []Node{RuleNode{
		Conc: claim, Clause: NewClauseId("r"), Subst: Subst{},
		Premises: []Premise{NegPremise{
			Atom: NewGroundLiteral("seen", premise), Cert: NewCertId(0), Nonmember: DirectLookup}},
		Meta: NoMeta(),
	}}
	deriv := NewDerivationWithClosedWorld(nodes, 0, []ClosedModelCert{cert})
	profile := &CheckProfile[struct{}]{
		Theory: NewCompoundTheory(),
		Leaves: pmLeaves{PredicateSetOf("seen"), rows},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	return CheckWithCertContext(prog, claim, deriv, struct{}{}, profile,
		NewCertContext(ProgramDigestOf(prog), pin, pin, pin))
}

// TestPremiseMatch2227NegPremiseAtomIsExact: absence is looked up by exact membership, so the
// Neg premise atom must be the exact grounded body literal.
func TestPremiseMatch2227NegPremiseAtomIsExact(t *testing.T) {
	b := pmAtom("b")
	vs := func(v ...core.Value) []core.Value { return v }
	cases := []struct {
		name string
		got  Outcome
		want string
	}{
		{"A honest negation (control)", pmNegation(pmConsA, vs(b), pmConsA, vs(pmConsA, b)), "ACCEPT"},
		{"B present, exact spelling (control)", pmNegation(pmConsA, vs(pmConsA), pmConsA, vs(pmConsA)), "neg_atom_present"},
		{"C present, premise respelled list(a)", pmNegation(pmConsA, vs(pmConsA), pmListA, vs(pmConsA, pmListA)), "instantiation_mismatch"},
		{"D reverse spelling", pmNegation(pmListA, vs(pmListA), pmConsA, vs(pmListA, pmConsA)), "instantiation_mismatch"},
	}
	for _, c := range cases {
		if got := pmVerdict(c.got); got != c.want {
			t.Errorf("%s: %s, want %s", c.name, got, c.want)
		}
	}
}
