// #3022 step 4 (research 0028 A8), the negative witness uabszqyzof asked for on #3037: a
// closed-model certificate's closure reads a theory-owned body literal through theoryTruth, and a
// theory that OWNS the predicate but disowns the atom (completion.TheoryGroundDisowned, the v1
// NotMine) is refused predicate_partition_violation, never read as false. Both polarities are
// planted, each against its control, a theory that decides Fails, which is what NotMine used to be
// read as. The same four cases are pinned in
// contract/rs (tests/closure_theory_not_mine_3022.rs) and contract/ts
// (test/closure_theory_not_mine_3022.test.ts).
//
//   - positive: `r(X) :- d(X), q(X).` over d(a), r sealed EMPTY. Read as false, NotMine leaves the
//     body false, so the empty table looked closed and the certificate was accepted.
//   - negated: `r(X) :- d(X).` and `r(X) :- d(X), \+ q(X).` over d(a), r sealed {r(a)}. Read as
//     false, NotMine made `\+ q(a)` TRUE, and the certificate was accepted.
package contract

import (
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// test-double: consumer(owns q and decides it with one fixed outcome)
type ctnmTheory struct{ outcome completion.TheoryGround }

func (ctnmTheory) Owns(p Symbol) bool { return p.Equal(SymbolFromString("q")) }
func (t ctnmTheory) DecideGround(GroundLiteral) completion.TheoryGround {
	return t.outcome
}

// test-double: consumer(admits every leaf and attests d's one-row EDB snapshot)
type ctnmLeaves struct{ extensional *PredicateSet }

func (l ctnmLeaves) Extensional() *PredicateSet { return l.extensional }
func (ctnmLeaves) Verify(GroundLiteral, Evidence, struct{}) LeafOutcome {
	return LeafAdmit{}
}
func (ctnmLeaves) EdbSnapshot(p Symbol, _ struct{}) (Hash, bool) {
	if !p.Equal(SymbolFromString("d")) {
		return Hash{}, false
	}
	return EdbTableHash(p, []GroundLiteral{ctnmLit("d")}), true
}

func ctnmLit(pred string) GroundLiteral {
	return NewGroundLiteral(pred, core.NewAtom([]byte("a")))
}

// ctnmChain verifies one certificate sealing {d, r} (d = {d(a)}, r = rRows, with edges) over
// program, under a theory that decides q with outcome.
func ctnmChain(program *MapProgram, rRows []GroundLiteral, edges []SupportEdge, outcome completion.TheoryGround) Outcome {
	d, r := SymbolFromString("d"), SymbolFromString("r")
	pin := Hash{7}
	cert := ClosedModelCert{
		Scope:             NewStratumPrefix(0, []Symbol{d, r}),
		ProgramHash:       ProgramDigestOf(program),
		ProfileHash:       pin,
		CtxHash:           pin,
		TheoryConfigHash:  pin,
		EdbSnapshotHashes: []Hash{EdbTableHash(d, []GroundLiteral{ctnmLit("d")})},
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("v"), []core.Value{core.NewAtom([]byte("a"))})},
		Extensions: []RelationTable{
			NewRelationTable(d, 1, []GroundLiteral{ctnmLit("d")}),
			NewRelationTable(r, 1, rRows),
		},
		Supports: SupportWitness{Edges: edges},
		LimitsDecl: CertSizeDecl{CertFacts: uint64(1 + len(rRows)), DomainValues: 1, SupportEdges: uint64(len(edges)),
			RuleGroundings: 1_000, JoinSteps: 10_000},
	}
	cert.LimitsDecl.CertBytes = CertEncodedBytes(cert)
	profile := &CheckProfile[struct{}]{
		Theory: ctnmTheory{outcome},
		Leaves: ctnmLeaves{PredicateSetOf("d")},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	return CheckClosedModelChain(program, []ClosedModelCert{cert}, struct{}{}, profile,
		NewCertContext(ProgramDigestOf(program), pin, pin, pin))
}

// The positive polarity: q(a) filters the only clause, and r is sealed empty.
func ctnmPositive(outcome completion.TheoryGround) Outcome {
	x := Var("X")
	program := NewMapProgram().With(NewClauseId("r_q"),
		NewClauseLits(NewGoal("r", x), PosLit(NewGoal("d", x)), PosLit(NewGoal("q", x))))
	return ctnmChain(program, nil, nil, outcome)
}

// The negated polarity: `\+ q(a)` filters the second clause, and r(a) is sealed, supported by the
// first.
func ctnmNegated(outcome completion.TheoryGround) Outcome {
	x := Var("X")
	program := NewMapProgram().
		With(NewClauseId("r_d"), NewClauseLits(NewGoal("r", x), PosLit(NewGoal("d", x)))).
		With(NewClauseId("r_not_q"), NewClauseLits(NewGoal("r", x), PosLit(NewGoal("d", x)), NegLit(NewGoal("q", x))))
	edge := SupportEdge{
		Fact:     ctnmLit("r"),
		Clause:   NewClauseId("r_d"),
		Subst:    Subst{NewVarId("X"): FromValue(core.NewAtom([]byte("a")))},
		BodyRefs: []SupportRef{LowerStratumRef{Cert: NewCertId(0), Atom: ctnmLit("d")}},
		Rank:     1,
	}
	return ctnmChain(program, []GroundLiteral{ctnmLit("r")}, []SupportEdge{edge}, outcome)
}

func ctnmVerdict(o Outcome) string {
	if o.IsAccept() {
		return "accept"
	}
	return o.Verdict.Code().Code()
}

func TestClosureTheoryDisowningIsRefusedInEitherPolarity3022(t *testing.T) {
	fails := completion.TheoryGroundFails("q_does_not_hold")
	for _, c := range []struct {
		name string
		got  Outcome
		want string
	}{
		{"positive control: q decides Fails", ctnmPositive(fails), "accept"},
		{"positive witness: q owned, decides NotMine", ctnmPositive(completion.TheoryGroundDisowned()), "predicate_partition_violation"},
		{"negated control: q decides Fails", ctnmNegated(fails), "accept"},
		{"negated witness: q owned, decides NotMine", ctnmNegated(completion.TheoryGroundDisowned()), "predicate_partition_violation"},
		// Go alone can return an outcome no constructor built (the zero TheoryGround); rs's enum and
		// ts's union cannot.
		{"positive witness: q owned, returns no outcome", ctnmPositive(completion.TheoryGround{}), "predicate_partition_violation"},
		{"negated witness: q owned, returns no outcome", ctnmNegated(completion.TheoryGround{}), "predicate_partition_violation"},
	} {
		if got := ctnmVerdict(c.got); got != c.want {
			t.Errorf("%s: %s (%s), want %s", c.name, got, c.got.Verdict.Detail(), c.want)
		}
	}
}
