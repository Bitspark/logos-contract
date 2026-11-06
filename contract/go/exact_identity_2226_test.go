// #2226's rows, after #3022. #2226 added the exact term identity beside the default reify_lists,
// whose label-tolerant sites ACCEPTED the issue's join, head, hidden and nested diag rows and a root
// respelled against its claim. #3022 (seat:caa's ruling) makes every certified literal claim exact:
// every comparison site is structural under EVERY identity, so all five are refused under both, and
// ctl-same (every spelling alike) is accepted under both. The same inputs are pinned in contract/rs,
// contract/go and contract/ts.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// eiFixture is one row: the program, the claim, the derivation (root last), the extensional
// predicates, and the leaf rows admitted.
type eiFixture struct {
	prog  *MapProgram
	claim GroundLiteral
	nodes []Node
	ext   []string
	rows  []GroundLiteral
}

func eiRun(f eiFixture, identity TermIdentity) Outcome {
	limits := DefaultLimits()
	limits.TermIdentity = identity
	profile := &CheckProfile[struct{}]{
		Theory: NewCompoundTheory(),
		Leaves: pmLeaves{PredicateSetOf(f.ext...), f.rows},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: limits,
	}
	return Check(f.prog, f.claim, NewDerivation(f.nodes, uint64(len(f.nodes)-1)), struct{}{}, profile)
}

func eiVerdict(o Outcome) string {
	if o.IsAccept() {
		return "ACCEPT"
	}
	return o.Code().Code()
}

func eiRule(conc GroundLiteral, id string, s Subst, prem ...uint64) Node {
	return RuleNode{Conc: conc, Clause: NewClauseId(id), Subst: s, Premises: PosPremises(prem...), Meta: NoMeta()}
}

func eiX(v core.Value) Subst { return Subst{NewVarId("X"): FromValue(v)} }

// eiTwin: twin(X) :- left(X), right(X). over left(.(a,[])) and right(rightArg).
func eiTwin(rightArg core.Value) eiFixture {
	X := Var("X")
	rows := []GroundLiteral{NewGroundLiteral("left", pmConsA), NewGroundLiteral("right", rightArg)}
	claim := NewGroundLiteral("twin", pmConsA)
	return eiFixture{
		prog:  NewMapProgram().With(NewClauseId("twin"), NewClause(NewGoal("twin", X), NewGoal("left", X), NewGoal("right", X))),
		claim: claim,
		nodes: []Node{lpLeaf(rows[0]), lpLeaf(rows[1]), eiRule(claim, "twin", eiX(pmConsA), 0, 1)},
		ext:   []string{"left", "right"},
		rows:  rows,
	}
}

// eiCopy: copy(X) :- seen(X). over seen(.(a,[])), X = .(a,[]), the node concluding nodeArg and the
// claim claimArg.
func eiCopy(nodeArg, claimArg core.Value) eiFixture {
	X := Var("X")
	rows := []GroundLiteral{NewGroundLiteral("seen", pmConsA)}
	return eiFixture{
		prog:  NewMapProgram().With(NewClauseId("copy"), NewClause(NewGoal("copy", X), NewGoal("seen", X))),
		claim: NewGroundLiteral("copy", claimArg),
		nodes: []Node{lpLeaf(rows[0]), eiRule(NewGroundLiteral("copy", nodeArg), "copy", eiX(pmConsA), 0)},
		ext:   []string{"seen"},
		rows:  rows,
	}
}

// eiHidden: allowed :- seen(list(a)). over seen(.(a,[])); the conclusion shows neither spelling.
func eiHidden() eiFixture {
	rows := []GroundLiteral{NewGroundLiteral("seen", pmConsA)}
	return eiFixture{
		prog:  NewMapProgram().With(NewClauseId("allowed"), NewClause(NewGoal("allowed"), NewGoal("seen", FromValue(pmListA)))),
		claim: NewGroundLiteral("allowed"),
		nodes: []Node{lpLeaf(rows[0]), eiRule(NewGroundLiteral("allowed"), "allowed", Subst{}, 0)},
		ext:   []string{"seen"},
		rows:  rows,
	}
}

// eiDiag: diag(X) :- pair(p(X, X)). over the single fact pair(p(.(a,[]), list(a))): X bound to
// two trees inside one nested term.
func eiDiag() eiFixture {
	X := Var("X")
	rows := []GroundLiteral{NewGroundLiteral("pair", core.NewTuple(pmAtom("p"), pmConsA, pmListA))}
	claim := NewGroundLiteral("diag", pmConsA)
	return eiFixture{
		prog:  NewMapProgram().With(NewClauseId("diag"), NewClause(NewGoal("diag", X), NewGoal("pair", Tuple(Atom([]byte("p")), X, X)))),
		claim: claim,
		nodes: []Node{lpLeaf(rows[0]), eiRule(claim, "diag", eiX(pmConsA), 0)},
		ext:   []string{"pair"},
		rows:  rows,
	}
}

func TestEveryIdentityRefusesEveryRespelling3022(t *testing.T) {
	cases := []struct {
		id    string
		f     eiFixture
		exact string
	}{
		{"ctl-same", eiTwin(pmConsA), "ACCEPT"},
		{"join", eiTwin(pmListA), "instantiation_mismatch"},
		{"head", eiCopy(pmListA, pmListA), "instantiation_mismatch"},
		{"hidden", eiHidden(), "instantiation_mismatch"},
		{"diag", eiDiag(), "instantiation_mismatch"},
		{"root", eiCopy(pmConsA, pmListA), "root_conclusion_mismatch"},
	}
	for _, c := range cases {
		for _, identity := range []TermIdentity{TermIdentityReifyLists, TermIdentityExact} {
			if got := eiVerdict(eiRun(c.f, identity)); got != c.exact {
				t.Errorf("%s under %s: got %s, want %s", c.id, identity.Tag(), got, c.exact)
			}
		}
	}
}

func TestTheDefaultTermIdentityIsReifyLists2226(t *testing.T) {
	if DefaultLimits().TermIdentity != TermIdentityReifyLists {
		t.Fatal("DefaultLimits must use the reify_lists identity")
	}
	var zero TermIdentity
	if zero != TermIdentityReifyLists {
		t.Fatal("the zero value must be reify_lists, so a CheckLimits literal keeps the default")
	}
	if TermIdentityReifyLists.Tag() != "reify_lists" || TermIdentityExact.Tag() != "exact" {
		t.Fatal("tags")
	}
}
