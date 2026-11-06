// #2256: the exact cone (ruled by seat:caa, issuecomment-5813063113). After #2242 a Leaf- or
// Rule-cited positive premise still matches by account equality, so the substitution can carry the
// other list spelling into a spelling-sensitive judgment of the same rule instance, or of a higher
// one through a derived fact. A rule instance whose clause is spelling-sensitive (a Neg literal, a
// count literal, or any builtin literal) must be exact-grounded: every positive premise equals its
// cited node's underlying exact fact (a Rule node's instantiated head, not its conclusion label),
// and every cited node is exact-grounded. #3022 (seat:caa's ruling) then made every certified
// literal claim exact: every comparison site is structural for every clause, so the exact cone holds
// by construction, and the positive-only rows #2256 left on #277's account equality are refused too.
// The same inputs are pinned in contract/rs and contract/ts.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

var (
	lpListX = core.NewTuple(pmAtom("list"), pmAtom("x"))            // list(x)
	lpConsX = core.NewTuple(pmAtom("."), pmAtom("x"), pmAtom("[]")) // .(x, []), the same list
	lpPin   = Hash{1}
)

func lpLeaf(g GroundLiteral) Node { return LeafNode{Conc: g, Evidence: NoEvidence()} }

// lpRun checks claim under leaves that admit exactly rows. With a domain, the derivation carries
// one certificate sealing `member` exactly as rows hold it, with that finite domain.
func lpRun(prog *MapProgram, claim GroundLiteral, nodes []Node, root int, ext []string, rows []GroundLiteral, domain []core.Value) Outcome {
	profile := &CheckProfile[struct{}]{
		Theory: NewStandardTheory(),
		Leaves: pmLeaves{PredicateSetOf(ext...), rows},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	if domain == nil {
		return Check(prog, claim, NewDerivation(nodes, uint64(root)), struct{}{}, profile)
	}
	member := SymbolFromString("member")
	var sealed []GroundLiteral
	for _, r := range rows {
		if r.Pred.Equal(member) {
			sealed = append(sealed, r)
		}
	}
	cert := ClosedModelCert{
		Scope:       NewStratumPrefix(0, []Symbol{member}),
		ProgramHash: ProgramDigestOf(prog),
		ProfileHash: lpPin, CtxHash: lpPin, TheoryConfigHash: lpPin,
		EdbSnapshotHashes: []Hash{EdbTableHash(member, sealed)},
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("v"), domain)},
		Extensions:        []RelationTable{NewRelationTable(member, 1, sealed)},
		LimitsDecl: CertSizeDecl{CertFacts: uint64(len(sealed)), DomainValues: uint64(len(domain)),
			RuleGroundings: 1000, JoinSteps: 10000, CertBytes: 4096},
	}
	deriv := NewDerivationWithClosedWorld(nodes, uint64(root), []ClosedModelCert{cert})
	return CheckWithCertContext(prog, claim, deriv, struct{}{}, profile,
		NewCertContext(ProgramDigestOf(prog), lpPin, lpPin, lpPin))
}

// lpN: `unlisted :- name(X), \+ member(X).` over name(nameRow), member(list(a)), X bound to x, the
// Neg atom member(negArg).
func lpN(nameRow, x, negArg core.Value, domain ...core.Value) Outcome {
	X := Var("X")
	prog := NewMapProgram().With(NewClauseId("unlisted"), NewClauseLits(NewGoal("unlisted"),
		PosLit(NewGoal("name", X)), NegLit(NewGoal("member", X))))
	rows := []GroundLiteral{NewGroundLiteral("name", nameRow), NewGroundLiteral("member", pmListA)}
	nodes := []Node{
		lpLeaf(rows[0]),
		RuleNode{Conc: NewGroundLiteral("unlisted"), Clause: NewClauseId("unlisted"), Subst: Subst{NewVarId("X"): FromValue(x)},
			Premises: []Premise{PosNode(0),
				NegPremise{Atom: NewGroundLiteral("member", negArg), Cert: NewCertId(0), Nonmember: DirectLookup}},
			Meta: NoMeta()},
	}
	return lpRun(prog, NewGroundLiteral("unlisted"), nodes, 1, []string{"name", "member"}, rows, domain)
}

// lpR: `conflict :- dep(R1), rev(R2), R1 \== R2.` over dep(list(x)), rev(revRow), R1 = list(x), R2
// bound to r2, the builtin node \==(list(x), neArg).
func lpR(revRow, r2, neArg core.Value) Outcome {
	r1v, r2v := Var("R1"), Var("R2")
	prog := NewMapProgram().With(NewClauseId("conflict"), NewClauseLits(NewGoal("conflict"),
		PosLit(NewGoal("dep", r1v)), PosLit(NewGoal("rev", r2v)), PosLit(NewGoal(`\==`, r1v, r2v))))
	rows := []GroundLiteral{NewGroundLiteral("dep", lpListX), NewGroundLiteral("rev", revRow)}
	nodes := []Node{
		lpLeaf(rows[0]), lpLeaf(rows[1]),
		BuiltinNode{Conc: NewGroundLiteral(`\==`, lpListX, neArg)},
		RuleNode{Conc: NewGroundLiteral("conflict"), Clause: NewClauseId("conflict"),
			Subst:    Subst{NewVarId("R1"): FromValue(lpListX), NewVarId("R2"): FromValue(r2)},
			Premises: []Premise{PosNode(0), PosNode(1), PosNode(2)}, Meta: NoMeta()},
	}
	return lpRun(prog, NewGroundLiteral("conflict"), nodes, 3, []string{"dep", "rev"}, rows, nil)
}

// lpLaunder: `name2(X) :- name(X).` then `unlisted :- name2(X), \+ member(X).` over name(list(a)),
// member(list(a)), X bound to x in both. With whole = false only the positive-only intermediate
// is checked, as the root, with no certificate.
func lpLaunder(x core.Value, whole bool) Outcome {
	X := Var("X")
	prog := NewMapProgram().
		With(NewClauseId("name2"), NewClauseLits(NewGoal("name2", X), PosLit(NewGoal("name", X)))).
		With(NewClauseId("unlisted"), NewClauseLits(NewGoal("unlisted"),
			PosLit(NewGoal("name2", X)), NegLit(NewGoal("member", X))))
	rows := []GroundLiteral{NewGroundLiteral("name", pmListA), NewGroundLiteral("member", pmListA)}
	name2 := NewGroundLiteral("name2", x)
	nodes := []Node{
		lpLeaf(rows[0]),
		RuleNode{Conc: name2, Clause: NewClauseId("name2"), Subst: Subst{NewVarId("X"): FromValue(x)},
			Premises: []Premise{PosNode(0)}, Meta: NoMeta()},
	}
	ext := []string{"name", "member"}
	if !whole {
		return lpRun(prog, name2, nodes, 1, ext, rows, nil)
	}
	nodes = append(nodes, RuleNode{Conc: NewGroundLiteral("unlisted"), Clause: NewClauseId("unlisted"),
		Subst: Subst{NewVarId("X"): FromValue(x)},
		Premises: []Premise{PosNode(1),
			NegPremise{Atom: NewGroundLiteral("member", x), Cert: NewCertId(0), Nonmember: DirectLookup}},
		Meta: NoMeta()})
	return lpRun(prog, NewGroundLiteral("unlisted"), nodes, 2, ext, rows, []core.Value{pmListA, pmConsA})
}

// lpCount: `n(N) :- name(X), count(member where arg0 = X) = N.` over name(list(a)), member(list(a)),
// X bound to x, the premise claiming k rows.
func lpCount(x core.Value, k int64) Outcome {
	X, N := Var("X"), Var("N")
	member := SymbolFromString("member")
	prog := NewMapProgram().With(NewClauseId("n"), Clause{Head: NewGoal("n", N), Body: []BodyLit{
		PosLit(NewGoal("name", X)),
		CountLitBody(CountLit{Pred: NewPredicateRef(member, 1), Filter: []CountFilterEntry{{Pos: 0, Term: X}},
			Project: Rows(), Count: N}),
	}})
	rows := []GroundLiteral{NewGroundLiteral("name", pmListA), NewGroundLiteral("member", pmListA)}
	claim := NewGroundLiteral("n", intV(k))
	nodes := []Node{
		lpLeaf(rows[0]),
		RuleNode{Conc: claim, Clause: NewClauseId("n"),
			Subst: Subst{NewVarId("X"): FromValue(x), NewVarId("N"): FromValue(intV(k))},
			Premises: []Premise{PosNode(0), CountPremise{Pred: NewPredicateRef(member, 1),
				Filter: []GroundFilterEntry{{Pos: 0, Value: x}}, Project: Rows(), K: intV(k), Cert: NewCertId(0)}},
			Meta: NoMeta()},
	}
	return lpRun(prog, claim, nodes, 1, []string{"name", "member"}, rows, []core.Value{pmListA, pmConsA})
}

// lpJoin and lpHidden are #2226's positive-only rows, refused since #3022.
func lpJoin() Outcome {
	X := Var("X")
	prog := NewMapProgram().With(NewClauseId("twin"), NewClauseLits(NewGoal("twin", X),
		PosLit(NewGoal("left", X)), PosLit(NewGoal("right", X))))
	rows := []GroundLiteral{NewGroundLiteral("left", pmConsA), NewGroundLiteral("right", pmListA)}
	claim := NewGroundLiteral("twin", pmConsA)
	nodes := []Node{lpLeaf(rows[0]), lpLeaf(rows[1]),
		RuleNode{Conc: claim, Clause: NewClauseId("twin"), Subst: Subst{NewVarId("X"): FromValue(pmConsA)},
			Premises: []Premise{PosNode(0), PosNode(1)}, Meta: NoMeta()}}
	return lpRun(prog, claim, nodes, 2, []string{"left", "right"}, rows, nil)
}

func lpHidden() Outcome {
	prog := NewMapProgram().With(NewClauseId("allowed"), NewClauseLits(NewGoal("allowed"),
		PosLit(NewGoal("seen", FromValue(pmListA)))))
	rows := []GroundLiteral{NewGroundLiteral("seen", pmConsA)}
	nodes := []Node{lpLeaf(rows[0]),
		RuleNode{Conc: NewGroundLiteral("allowed"), Clause: NewClauseId("allowed"), Subst: Subst{},
			Premises: []Premise{PosNode(0)}, Meta: NoMeta()}}
	return lpRun(prog, NewGroundLiteral("allowed"), nodes, 1, []string{"seen"}, rows, nil)
}

func TestLeafPremiseRoute2256ExactCone(t *testing.T) {
	a, c := pmListA, pmConsA
	cases := []struct {
		name string
		got  Outcome
		want string
	}{
		// Rejected: a respelled binding reaches a spelling-sensitive judgment.
		{"N1 X = .(a,[]) via leaf name(list(a)), Neg member(.(a,[]))", lpN(a, c, c, a, c), "instantiation_mismatch"},
		{"R1 R2 = .(x,[]) via leaf rev(list(x)), \\==(list(x), .(x,[]))", lpR(lpListX, lpConsX, lpConsX), "instantiation_mismatch"},
		{"L laundered through the positive-only name2", lpLaunder(c, true), "instantiation_mismatch"},
		{"C count over a respelled X", lpCount(c, 0), "instantiation_mismatch"},
		// Rejected since #3022: a positive-only rule's respelled premise is no longer account-equal.
		{"L's positive-only intermediate alone", lpLaunder(c, false), "instantiation_mismatch"},
		{"#2226 join", lpJoin(), "instantiation_mismatch"},
		{"#2226 hidden", lpHidden(), "instantiation_mismatch"},
		// Unchanged.
		{"N0 exact spelling, present", lpN(a, a, a, a), "neg_atom_present"},
		{"N3 #2227's form, Neg atom respelled", lpN(a, a, c, a, c), "instantiation_mismatch"},
		{"R0 exact spelling, \\== fails", lpR(lpListX, lpListX, lpListX), "builtin_failed"},
		{"R2 #2232's form, builtin node respelled", lpR(lpListX, lpListX, lpConsX), "instantiation_mismatch"},
		// Stay accepted: the rule does not reach them.
		{"N4 mixed EDB, honest exact binding", lpN(c, c, c, a, c), "ACCEPT"},
		{"R3 mixed EDB, honest exact binding", lpR(lpConsX, lpConsX, lpConsX), "ACCEPT"},
		{"L's positive-only intermediate, honest exact binding", lpLaunder(a, false), "ACCEPT"},
		{"C honest count", lpCount(a, 1), "ACCEPT"},
	}
	for _, tc := range cases {
		if got := pmVerdict(tc.got); got != tc.want {
			t.Errorf("%s: %s (%s), want %s", tc.name, got, tc.got.Detail(), tc.want)
		}
	}
}
