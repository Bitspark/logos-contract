// ADR 0023 — certifiable aggregation (count / count_distinct): the go checker oracle
// tests (Phase 1-2). A structural mirror of the Rust oracle (contract/rs/tests/
// aggregation.rs): build a sealed, exact ClosedModelCert over a small relation, cite it
// from a CountPremise, and assert the go checker re-derives the count byte-identically.
//
// ACCEPT: a correct count (rows matching a filter) and a correct count_distinct (distinct
// projected attr, null() excluded).
// REJECT: a wrong k → count_mismatch; a count over a same/higher stratum →
// count_stratum_not_lower; a projection attr / filter position / arity out of range →
// count_attr_out_of_range; a stale EDB → the existing cert_edb_mismatch gate still fires.
package contract

import (
	"math/big"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ================================= test profile =================================

// test-double: consumer(owns no predicate)
type aggNoTheory struct{}

func (aggNoTheory) Owns(Symbol) bool { return false }
func (aggNoTheory) Decide(GroundLiteral) TheoryOutcome {
	return TheoryFails{Code: "no_theory"}
}

// aggLeaves attests a fixed EDB-of-record snapshot for each extensional predicate (so the
// §3.6 EDB-binding gate can bind the sealed table to the live EDB). Implements both
// LeafVerifier and EdbSnapshotProvider.
// test-double: consumer(a fixed EDB with attested snapshots)
type aggLeaves struct {
	extensional *PredicateSet
	edb         map[string][]GroundLiteral
}

func newAggLeaves(preds []string, edb map[string][]GroundLiteral) *aggLeaves {
	return &aggLeaves{extensional: PredicateSetOf(preds...), edb: edb}
}

func (l *aggLeaves) Extensional() *PredicateSet { return l.extensional }
func (l *aggLeaves) Verify(GroundLiteral, Evidence, struct{}) LeafOutcome {
	return LeafAdmit{}
}
func (l *aggLeaves) EdbSnapshot(pred Symbol, _ struct{}) (Hash, bool) {
	if rows, ok := l.edb[pred.String()]; ok {
		return EdbTableHash(pred, rows), true
	}
	if l.extensional.Contains(pred) {
		return EdbTableHash(pred, nil), true
	}
	return Hash{}, false
}

// ============================ value / literal helpers ===========================

func aggV(s string) core.Value { return core.NewAtom([]byte(s)) }

// nullValue is the canonical null() marker (nullary compound Tuple[Atom("null")]).
func nullValue() core.Value { return core.NewTuple(core.NewAtom([]byte("null"))) }

// intV is the int ground value n (the count-result embedding k binds).
func intV(n int64) core.Value { return data.EncodeInt(big.NewInt(n)) }

func aggObs(o, p string, val core.Value) GroundLiteral {
	return NewGroundLiteral("obs", aggV(o), aggV(p), val)
}

func aggSym(s string) Symbol { return SymbolFromString(s) }

func aggBoundContext(program CompleteProgram) CertContext {
	return NewCertContext(ProgramDigestOf(program),
		Hash{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
		Hash{2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2},
		Hash{3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3})
}

func aggBindCert(cert *ClosedModelCert, program CompleteProgram) {
	cx := aggBoundContext(program)
	cert.ProgramHash = cx.ProgramHash
	cert.ProfileHash = cx.ProfileHash
	cert.CtxHash = cx.CtxHash
	cert.TheoryConfigHash = cx.TheoryConfigHash
}

// ================================ the program ===================================

const cEligibleCount = "eligible_count_rule"
const cEligibleDistinct = "eligible_distinct_rule"

// obsEdb is the EDB-of-record for obs (the sealed relation we count over):
//
//	obs(o1,p1,x), obs(o1,p2,x), obs(o1,p3,y), obs(o1,p4,null()), obs(o2,p1,z)
//
// For O=o1: 4 rows; distinct non-null V = {x, y} → 2.
func obsEdb() []GroundLiteral {
	return []GroundLiteral{
		aggObs("o1", "p1", aggV("x")),
		aggObs("o1", "p2", aggV("x")),
		aggObs("o1", "p3", aggV("y")),
		aggObs("o1", "p4", nullValue()),
		aggObs("o2", "p1", aggV("z")),
	}
}

func aggBaseProgram() *MapProgram {
	countClause := Clause{
		Head: NewGoal("eligible_count", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Rows(),
			Count:   Var("N"),
		})},
	}
	distinctClause := Clause{
		Head: NewGoal("eligible_distinct", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Distinct(2),
			Count:   Var("N"),
		})},
	}
	return NewMapProgram().
		With(NewClauseId(cEligibleCount), countClause).
		With(NewClauseId(cEligibleDistinct), distinctClause)
}

func aggProfile() *CheckProfile[struct{}] {
	edb := map[string][]GroundLiteral{"obs": obsEdb()}
	return &CheckProfile[struct{}]{
		Theory: aggNoTheory{},
		Leaves: newAggLeaves([]string{"obs"}, edb),
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

// aggValidCert is the valid sealed certificate for the prefix {obs} (level 0): obs = the
// live EDB snapshot. obs is a PURE EDB leaf, exempt from support, bound by the §3.6 gate.
func aggValidCert() ClosedModelCert {
	domain := NewFiniteDomain(aggSym("u"), []core.Value{
		aggV("o1"), aggV("o2"), aggV("p1"), aggV("p2"), aggV("p3"), aggV("p4"),
		aggV("x"), aggV("y"), aggV("z"), nullValue(),
	})
	cert := ClosedModelCert{
		Scope:      NewStratumPrefix(0, []Symbol{aggSym("obs")}),
		Domains:    []FiniteDomain{domain},
		Extensions: []RelationTable{NewRelationTable(aggSym("obs"), 3, obsEdb())},
		Supports:   SupportWitness{},
		Closure:    ClosureWitness{},
		LimitsDecl: CertSizeDecl{
			CertFacts:      5,
			DomainValues:   10,
			SupportEdges:   0,
			RuleGroundings: 1000,
			JoinSteps:      10000,
			CertBytes:      8192,
		},
	}
	aggBindCert(&cert, aggBaseProgram())
	return cert
}

func aggCountDerivation(clauseID, headPred string, project ProjectSpec, k int64, cert ClosedModelCert) Derivation {
	subst := Subst{
		NewVarId("O"): Atom([]byte("o1")),
		NewVarId("N"): FromValue(intV(k)),
	}
	node := RuleNode{
		Conc:   NewGroundLiteral(headPred, aggV("o1")),
		Clause: NewClauseId(clauseID),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV("o1")}},
			Project: project,
			K:       intV(k),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}
	return NewDerivationWithClosedWorld([]Node{node}, 0, []ClosedModelCert{cert})
}

func aggRun(t *testing.T, program *MapProgram, claim GroundLiteral, deriv Derivation) Outcome {
	t.Helper()
	cx := aggBoundContext(program)
	return CheckWithCertContext[struct{}](program, claim, deriv, struct{}{}, aggProfile(), cx)
}

func assertReject(t *testing.T, outcome Outcome, expected string) {
	t.Helper()
	if outcome.IsAccept() {
		t.Fatalf("expected reject %s, got Accept", expected)
	}
	if got := outcome.Code().Code(); got != expected {
		t.Fatalf("expected %s, got %s (%s)", expected, got, outcome.Detail())
	}
}

// =================================== ACCEPT ===================================

func TestAggAcceptCountRowsMatchingFilter(t *testing.T) {
	deriv := aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 4, aggValidCert())
	out := aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_count", aggV("o1")), deriv)
	if !out.IsAccept() {
		t.Fatalf("expected Accept, got %s (%s)", out.Code().Code(), out.Detail())
	}
}

func TestAggAcceptCountDistinctExcludesNull(t *testing.T) {
	deriv := aggCountDerivation(cEligibleDistinct, "eligible_distinct", Distinct(2), 2, aggValidCert())
	out := aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_distinct", aggV("o1")), deriv)
	if !out.IsAccept() {
		t.Fatalf("expected Accept, got %s (%s)", out.Code().Code(), out.Detail())
	}
}

// =================================== REJECT ===================================

func TestAggRejectCountMismatchWrongKRows(t *testing.T) {
	deriv := aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 3, aggValidCert()) // actually 4
	assertReject(t, aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_count", aggV("o1")), deriv), "count_mismatch")
}

func TestAggRejectCountMismatchWrongKDistinct(t *testing.T) {
	deriv := aggCountDerivation(cEligibleDistinct, "eligible_distinct", Distinct(2), 3, aggValidCert()) // actually 2
	assertReject(t, aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_distinct", aggV("o1")), deriv), "count_mismatch")
}

// TestAggRejectCountStratumNotLowerHeadSealed seals eligible_count alongside obs (so the
// head predicate is in the lower scope). The sealed-scope clause carries a count → the
// §3.2 scope-closure gate rejects (cert_scope_incomplete), subsuming the per-premise
// count_stratum_not_lower for this malformed shape. Either way the unsound same-stratum
// count is REJECTED. Mirrors the Rust reject_count_stratum_not_lower.
func TestAggRejectCountStratumNotLower(t *testing.T) {
	program := aggBaseProgram()
	cert := aggValidCert()
	cert.Scope = NewStratumPrefix(0, []Symbol{aggSym("obs"), aggSym("eligible_count")})
	cert.Extensions = append(cert.Extensions, NewRelationTable(aggSym("eligible_count"), 1, nil))
	aggBindCert(&cert, program)
	deriv := aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 4, cert)
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_count", aggV("o1")), deriv, struct{}{}, aggProfile(), cx)
	assertReject(t, out, "cert_scope_incomplete")
}

// TestAggRejectCountStratumNotLowerHeadSealed is the per-premise variant: r is a pure EDB
// leaf; the citing rule concludes r(o1) while counting r — head predicate r IS in the
// sealed scope. The sealed-scope clause carries a count → §3.2 rejects first; the
// per-premise count_stratum_not_lower is the backstop. Mirrors the Rust test.
func TestAggRejectCountStratumNotLowerHeadSealed(t *testing.T) {
	rClause := Clause{
		Head: NewGoal("r", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("r"), 1),
			Filter:  nil,
			Project: Rows(),
			Count:   Var("N"),
		})},
	}
	program := NewMapProgram().With(NewClauseId("r_self_count"), rClause)
	edb := map[string][]GroundLiteral{"r": {NewGroundLiteral("r", aggV("o1"))}}
	prof := &CheckProfile[struct{}]{
		Theory: aggNoTheory{},
		Leaves: newAggLeaves([]string{"r"}, edb),
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	cert := ClosedModelCert{
		Scope:      NewStratumPrefix(0, []Symbol{aggSym("r")}),
		Domains:    []FiniteDomain{NewFiniteDomain(aggSym("u"), []core.Value{aggV("o1")})},
		Extensions: []RelationTable{NewRelationTable(aggSym("r"), 1, []GroundLiteral{NewGroundLiteral("r", aggV("o1"))})},
		Supports:   SupportWitness{},
		Closure:    ClosureWitness{},
		LimitsDecl: CertSizeDecl{CertFacts: 1, DomainValues: 1, SupportEdges: 0, RuleGroundings: 100, JoinSteps: 100, CertBytes: 512},
	}
	aggBindCert(&cert, program)
	subst := Subst{NewVarId("O"): Atom([]byte("o1")), NewVarId("N"): FromValue(intV(1))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("r", aggV("o1")),
		Clause: NewClauseId("r_self_count"),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("r"), 1),
			Filter:  nil,
			Project: Rows(),
			K:       intV(1),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{cert})
	cx := NewCertContext(ProgramDigestOf(program), aggBoundContext(program).ProfileHash, aggBoundContext(program).CtxHash, aggBoundContext(program).TheoryConfigHash)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("r", aggV("o1")), deriv, struct{}{}, prof, cx)
	assertReject(t, out, "cert_scope_incomplete")
}

func TestAggRejectCountAttrOutOfRange(t *testing.T) {
	program := aggBaseProgram().With(NewClauseId("eligible_bad_attr"), Clause{
		Head: NewGoal("eligible_bad", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Distinct(5), // obs arity = 3
			Count:   Var("N"),
		})},
	})
	cert := aggValidCert()
	aggBindCert(&cert, program)
	subst := Subst{NewVarId("O"): Atom([]byte("o1")), NewVarId("N"): FromValue(intV(2))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("eligible_bad", aggV("o1")),
		Clause: NewClauseId("eligible_bad_attr"),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV("o1")}},
			Project: Distinct(5),
			K:       intV(2),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{cert})
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_bad", aggV("o1")), deriv, struct{}{}, aggProfile(), cx)
	assertReject(t, out, "count_attr_out_of_range")
}

func TestAggRejectCountFilterPositionOutOfRange(t *testing.T) {
	program := aggBaseProgram().With(NewClauseId("eligible_bad_filter"), Clause{
		Head: NewGoal("eligible_bad", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []CountFilterEntry{{Pos: 7, Term: Var("O")}}, // obs arity 3
			Project: Rows(),
			Count:   Var("N"),
		})},
	})
	cert := aggValidCert()
	aggBindCert(&cert, program)
	subst := Subst{NewVarId("O"): Atom([]byte("o1")), NewVarId("N"): FromValue(intV(0))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("eligible_bad", aggV("o1")),
		Clause: NewClauseId("eligible_bad_filter"),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []GroundFilterEntry{{Pos: 7, Value: aggV("o1")}},
			Project: Rows(),
			K:       intV(0),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{cert})
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_bad", aggV("o1")), deriv, struct{}{}, aggProfile(), cx)
	assertReject(t, out, "count_attr_out_of_range")
}

// TestAggRejectCountWrongArity (#581) — the PredicateRef names obs with arity 2, but the
// sealed obs table has arity 3. A wrong arity must be rejected, never silently counted.
func TestAggRejectCountWrongArity(t *testing.T) {
	program := aggBaseProgram().With(NewClauseId("eligible_bad_arity"), Clause{
		Head: NewGoal("eligible_bad", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 2), // sealed obs is arity 3
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Rows(),
			Count:   Var("N"),
		})},
	})
	cert := aggValidCert()
	aggBindCert(&cert, program)
	subst := Subst{NewVarId("O"): Atom([]byte("o1")), NewVarId("N"): FromValue(intV(4))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("eligible_bad", aggV("o1")),
		Clause: NewClauseId("eligible_bad_arity"),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 2),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV("o1")}},
			Project: Rows(),
			K:       intV(4),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{cert})
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_bad", aggV("o1")), deriv, struct{}{}, aggProfile(), cx)
	assertReject(t, out, "count_attr_out_of_range")
}

// TestAggRejectStaleEdbCertEdbMismatch — the sealed obs table OMITS a live EDB fact, so
// the existing §3.6 EDB gate (cert_edb_mismatch) fires before the count is recomputed.
func TestAggRejectStaleEdbCertEdbMismatch(t *testing.T) {
	cert := aggValidCert()
	cert.Extensions = []RelationTable{NewRelationTable(aggSym("obs"), 3, []GroundLiteral{
		aggObs("o1", "p1", aggV("x")),
		aggObs("o1", "p2", aggV("x")),
		aggObs("o1", "p3", aggV("y")),
		// obs(o1,p4,null()) and obs(o2,p1,z) OMITTED
	})}
	cert.LimitsDecl.CertFacts = 3
	aggBindCert(&cert, aggBaseProgram())
	deriv := aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 4, cert)
	assertReject(t, aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_count", aggV("o1")), deriv), "cert_edb_mismatch")
}

// TestAggRejectCountMismatchFilterApplied — the filter selects O=o2 (1 obs row); claiming
// 4 (the o1 count) is wrong for o2, proving the filter is genuinely applied.
func TestAggRejectCountMismatchFilterApplied(t *testing.T) {
	program := aggBaseProgram()
	subst := Subst{NewVarId("O"): Atom([]byte("o2")), NewVarId("N"): FromValue(intV(4))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("eligible_count", aggV("o2")),
		Clause: NewClauseId(cEligibleCount),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV("o2")}}, // o2 has only 1 obs row
			Project: Rows(),
			K:       intV(4), // claims 4 — wrong, actual is 1
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{aggValidCert()})
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_count", aggV("o2")), deriv, struct{}{}, aggProfile(), cx)
	assertReject(t, out, "count_mismatch")
}

// TestAggAcceptCountFilterAppliedO2 — the filter applied to o2 gives 1 row; claiming k=1
// accepts (the positive companion to the filter-applied reject).
func TestAggAcceptCountFilterAppliedO2(t *testing.T) {
	program := aggBaseProgram()
	subst := Subst{NewVarId("O"): Atom([]byte("o2")), NewVarId("N"): FromValue(intV(1))}
	deriv := NewDerivationWithClosedWorld([]Node{RuleNode{
		Conc:   NewGroundLiteral("eligible_count", aggV("o2")),
		Clause: NewClauseId(cEligibleCount),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV("o2")}},
			Project: Rows(),
			K:       intV(1),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}}, 0, []ClosedModelCert{aggValidCert()})
	cx := aggBoundContext(program)
	out := CheckWithCertContext[struct{}](program, NewGroundLiteral("eligible_count", aggV("o2")), deriv, struct{}{}, aggProfile(), cx)
	if !out.IsAccept() {
		t.Fatalf("expected Accept, got %s (%s)", out.Code().Code(), out.Detail())
	}
}

// TestAggRejectCountCertOutOfRange — the cited cert index does not exist.
func TestAggRejectCountCertOutOfRange(t *testing.T) {
	deriv := aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 4, aggValidCert())
	deriv.ClosedWorld = nil
	assertReject(t, aggRun(t, aggBaseProgram(), NewGroundLiteral("eligible_count", aggV("o1")), deriv), "cert_out_of_range")
}

// ===================== #587: sum / min / max integer folds =====================
//
// A separate score(obj, val) fixture with INTEGER values in column 1, mirroring the
// Rust oracle's #587 section (contract/rs/tests/aggregation.rs):
//
//	score("g1",3), score("g1",7), score("g1",1), score("g2_unused",99)
//
// For O=g1: 3 matching rows; sum = 11, min = 1, max = 7. An "empty_grp" object is in the
// domain but has NO score rows, so min/max of it is undefined (agg_empty_undefined) and
// its sum is 0.

const cScoreSum = "score_sum_rule"
const cScoreMin = "score_min_rule"
const cScoreMax = "score_max_rule"

// scoreRow builds score(obj, int(val)) — a 2-ary relation with an integer column 1.
func scoreRow(obj string, val int64) GroundLiteral {
	return NewGroundLiteral("score", aggV(obj), intV(val))
}

// scoreRowVal builds score(obj, v) with an arbitrary (possibly non-int) column value —
// used by the non-int reject fixture.
func scoreRowVal(obj string, v core.Value) GroundLiteral {
	return NewGroundLiteral("score", aggV(obj), v)
}

func scoreEdb() []GroundLiteral {
	return []GroundLiteral{
		scoreRow("g1", 3),
		scoreRow("g1", 7),
		scoreRow("g1", 1),
		scoreRow("g2_unused", 99),
	}
}

// scoreProgram pins one clause per aggregate over score(obj, val), folding column 1.
func scoreProgram() *MapProgram {
	mk := func(headPred string, project ProjectSpec) Clause {
		return Clause{
			Head: NewGoal(headPred, Var("O")),
			Body: []BodyLit{CountLitBody(CountLit{
				Pred:    NewPredicateRef(aggSym("score"), 2),
				Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
				Project: project,
				Count:   Var("N"),
			})},
		}
	}
	return NewMapProgram().
		With(NewClauseId(cScoreSum), mk("score_sum", Sum(1))).
		With(NewClauseId(cScoreMin), mk("score_min", Min(1))).
		With(NewClauseId(cScoreMax), mk("score_max", Max(1)))
}

func scoreProfile(edb []GroundLiteral) *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: aggNoTheory{},
		Leaves: newAggLeaves([]string{"score"}, map[string][]GroundLiteral{"score": edb}),
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

// scoreCert is the valid sealed cert over {score} = edb. score is a pure EDB leaf bound by
// the §3.6 gate. The domain carries every object + every integer value used (so a count
// filter value is in-domain) plus empty_grp (an object with no rows).
func scoreCert(program CompleteProgram, edb []GroundLiteral) ClosedModelCert {
	domain := NewFiniteDomain(aggSym("u"), []core.Value{
		aggV("g1"), aggV("g2_unused"), aggV("empty_grp"),
		intV(1), intV(3), intV(7), intV(99),
	})
	cert := ClosedModelCert{
		Scope:      NewStratumPrefix(0, []Symbol{aggSym("score")}),
		Domains:    []FiniteDomain{domain},
		Extensions: []RelationTable{NewRelationTable(aggSym("score"), 2, edb)},
		Supports:   SupportWitness{},
		Closure:    ClosureWitness{},
		LimitsDecl: CertSizeDecl{
			CertFacts: uint64(len(edb)), DomainValues: 7, SupportEdges: 0,
			RuleGroundings: 1000, JoinSteps: 10000, CertBytes: 8192,
		},
	}
	aggBindCert(&cert, program)
	return cert
}

// scoreDeriv cites a CountPremise folding column 1 of score for object obj, claiming k.
func scoreDeriv(clauseID, headPred, obj string, project ProjectSpec, k int64, cert ClosedModelCert) Derivation {
	subst := Subst{
		NewVarId("O"): Atom([]byte(obj)),
		NewVarId("N"): FromValue(intV(k)),
	}
	node := RuleNode{
		Conc:   NewGroundLiteral(headPred, aggV(obj)),
		Clause: NewClauseId(clauseID),
		Subst:  subst,
		Premises: []Premise{CountPremise{
			Pred:    NewPredicateRef(aggSym("score"), 2),
			Filter:  []GroundFilterEntry{{Pos: 0, Value: aggV(obj)}},
			Project: project,
			K:       intV(k),
			Cert:    NewCertId(0),
		}},
		Meta: NoMeta(),
	}
	return NewDerivationWithClosedWorld([]Node{node}, 0, []ClosedModelCert{cert})
}

func scoreRun(t *testing.T, program *MapProgram, edb []GroundLiteral, claim GroundLiteral, deriv Derivation) Outcome {
	t.Helper()
	cx := aggBoundContext(program)
	return CheckWithCertContext[struct{}](program, claim, deriv, struct{}{}, scoreProfile(edb), cx)
}

// ----- ACCEPT: integer sum / min / max -----

func TestAggAcceptSumIntColumn(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreSum, "score_sum", "g1", Sum(1), 11, scoreCert(prog, edb)) // 3+7+1
	if out := scoreRun(t, prog, edb, NewGroundLiteral("score_sum", aggV("g1")), deriv); !out.IsAccept() {
		t.Fatalf("expected Accept (sum=11), got %s (%s)", out.Code().Code(), out.Detail())
	}
}

func TestAggAcceptMinIntColumn(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreMin, "score_min", "g1", Min(1), 1, scoreCert(prog, edb))
	if out := scoreRun(t, prog, edb, NewGroundLiteral("score_min", aggV("g1")), deriv); !out.IsAccept() {
		t.Fatalf("expected Accept (min=1), got %s (%s)", out.Code().Code(), out.Detail())
	}
}

func TestAggAcceptMaxIntColumn(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreMax, "score_max", "g1", Max(1), 7, scoreCert(prog, edb))
	if out := scoreRun(t, prog, edb, NewGroundLiteral("score_max", aggV("g1")), deriv); !out.IsAccept() {
		t.Fatalf("expected Accept (max=7), got %s (%s)", out.Code().Code(), out.Detail())
	}
}

// Empty sum is 0 (folding empty_grp, which has no rows).
func TestAggAcceptEmptySumIsZero(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreSum, "score_sum", "empty_grp", Sum(1), 0, scoreCert(prog, edb))
	if out := scoreRun(t, prog, edb, NewGroundLiteral("score_sum", aggV("empty_grp")), deriv); !out.IsAccept() {
		t.Fatalf("expected Accept (empty sum=0), got %s (%s)", out.Code().Code(), out.Detail())
	}
}

// ----- REJECT: empty min / max are undefined -----

func TestAggRejectEmptyMinUndefined(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	// empty_grp has no score rows; min of an empty set is agg_empty_undefined regardless of k.
	deriv := scoreDeriv(cScoreMin, "score_min", "empty_grp", Min(1), 0, scoreCert(prog, edb))
	assertReject(t, scoreRun(t, prog, edb, NewGroundLiteral("score_min", aggV("empty_grp")), deriv), "agg_empty_undefined")
}

func TestAggRejectEmptyMaxUndefined(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreMax, "score_max", "empty_grp", Max(1), 0, scoreCert(prog, edb))
	assertReject(t, scoreRun(t, prog, edb, NewGroundLiteral("score_max", aggV("empty_grp")), deriv), "agg_empty_undefined")
}

// ----- REJECT: tampered sum (claim 99, real 11) -----

func TestAggRejectTamperedSumCountMismatch(t *testing.T) {
	prog := scoreProgram()
	edb := scoreEdb()
	deriv := scoreDeriv(cScoreSum, "score_sum", "g1", Sum(1), 99, scoreCert(prog, edb)) // real sum is 11
	assertReject(t, scoreRun(t, prog, edb, NewGroundLiteral("score_sum", aggV("g1")), deriv), "count_mismatch")
}

// ----- REJECT: non-int column folded by sum -----

// TestAggRejectNonIntColumnSum folds a column whose values are NOT canonical ints (atoms).
// v1 sum/min/max are integer-only, so a non-int read is count_attr_out_of_range.
func TestAggRejectNonIntColumnSum(t *testing.T) {
	prog := scoreProgram()
	// score(g1, <atom>) — column 1 is a bare atom, not an int embedding.
	edb := []GroundLiteral{scoreRowVal("g1", aggV("not_a_number"))}
	domain := NewFiniteDomain(aggSym("u"), []core.Value{aggV("g1"), aggV("not_a_number")})
	cert := ClosedModelCert{
		Scope:      NewStratumPrefix(0, []Symbol{aggSym("score")}),
		Domains:    []FiniteDomain{domain},
		Extensions: []RelationTable{NewRelationTable(aggSym("score"), 2, edb)},
		Supports:   SupportWitness{},
		Closure:    ClosureWitness{},
		LimitsDecl: CertSizeDecl{CertFacts: 1, DomainValues: 2, SupportEdges: 0, RuleGroundings: 100, JoinSteps: 100, CertBytes: 512},
	}
	aggBindCert(&cert, prog)
	// Claim is irrelevant: the non-int read rejects before the k comparison.
	deriv := scoreDeriv(cScoreSum, "score_sum", "g1", Sum(1), 0, cert)
	assertReject(t, scoreRun(t, prog, edb, NewGroundLiteral("score_sum", aggV("g1")), deriv), "count_attr_out_of_range")
}

// TestAggCountClauseRoundTrips — a Count clause round-trips through ClauseValue →
// ClauseFromValue (the account codec mirror), and a wrong-arity ref produces a DISTINCT
// clause id (the #581 arity is load-bearing in the bytes).
func TestAggCountClauseRoundTrips(t *testing.T) {
	clause := Clause{
		Head: NewGoal("eligible", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 3),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Distinct(2),
			Count:   Var("N"),
		})},
	}
	value := ClauseValue(clause)
	got, ok := ClauseFromValue(value)
	if !ok {
		t.Fatalf("ClauseFromValue failed to decode the count clause")
	}
	if CanonicalClauseId(got) != CanonicalClauseId(clause) {
		t.Fatalf("round-trip changed the clause id")
	}
	// Arity is load-bearing: obs/3 and obs/2 produce distinct ids.
	clause2 := Clause{
		Head: NewGoal("eligible", Var("O")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(aggSym("obs"), 2),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("O")}},
			Project: Distinct(2),
			Count:   Var("N"),
		})},
	}
	if CanonicalClauseId(clause) == CanonicalClauseId(clause2) {
		t.Fatalf("expected obs/3 and obs/2 count clauses to have distinct ids")
	}
}
