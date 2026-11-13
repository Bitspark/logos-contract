// ADR 0023 — certifiable aggregation (count / count_distinct): the TS checker oracle
// tests (Phase 1-2). A structural mirror of the Rust oracle (contract/rs/tests/
// aggregation.rs): build a sealed, exact ClosedModelCert over a small relation, cite it
// from a CountPremise, and assert the TS checker re-derives the count byte-identically.
//
// ACCEPT: a correct count (rows matching a filter) and a correct count_distinct (distinct
// projected attr, null() excluded).
// REJECT: a wrong k → count_mismatch; a count over a same/higher stratum →
// count_stratum_not_lower; a projection attr / filter position / arity out of range →
// count_attr_out_of_range; a stale EDB → the existing cert_edb_mismatch gate still fires.

import { strict as assert } from "node:assert";
import { test } from "node:test";

import { Atom, Tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";

import {
  AlwaysAdmit,
  BodyLit,
  CertContext,
  checkWithCertContext,
  checkWithWorldMemo,
  type CheckProfile,
  ClosedModelCert,
  CountLit,
  CountPremise,
  Clause,
  ClauseId,
  type CountFilterEntry,
  defaultLimits,
  Derivation,
  type Evidence,
  FiniteDomain,
  type GroundFilterEntry,
  Goal,
  GroundLiteral,
  type Hash,
  type LeafOutcome,
  LeafOutcome as LeafOutcomeOps,
  type LeafVerifier,
  MapProgram,
  NodeMeta,
  type Outcome,
  PredicateRef,
  PredicateSet,
  ProjectSpec,
  programDigest,
  RelationTable,
  RuleNode,
  StratumPrefix,
  Subst,
  Symbol,
  Term,
  type Theory,
  TheoryGround,
  edbTableHash,
  Evidence as EvidenceOps,
  LeafNode,
  WorldMemo,
  VarId,
} from "../src/index.js";

// ================================= test profile =================================

// test-double: consumer(owns no predicate)
class NoTheory implements Theory {
  owns(_pred: Symbol): boolean {
    return false;
  }
  decideGround(_atom: GroundLiteral): TheoryGround {
    return TheoryGround.fails("no_theory");
  }
}

// AggLeaves attests a fixed EDB-of-record snapshot for each extensional predicate (so the
// §3.6 EDB-binding gate can bind the sealed table to the live EDB).
// test-double: consumer(a fixed EDB with attested snapshots)
class AggLeaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #edb: Map<string, GroundLiteral[]>;
  constructor(preds: string[], edb: Map<string, GroundLiteral[]>) {
    this.#extensional = PredicateSet.from(preds);
    this.#edb = edb;
  }
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcomeOps.Admit;
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    const key = new TextDecoder().decode(pred.bytes());
    const rows = this.#edb.get(key);
    if (rows !== undefined) return edbTableHash(pred, rows);
    if (this.#extensional.contains(pred)) return edbTableHash(pred, []);
    return undefined;
  }
}

// ============================ value / literal helpers ===========================

function av(s: string): Value {
  return new Atom(new TextEncoder().encode(s));
}
/** The canonical null() marker (nullary compound Tuple[Atom("null")]). */
function nullValue(): Value {
  return new Tuple([new Atom(new TextEncoder().encode("null"))]);
}
/** The int ground value n (the count-result embedding k binds). */
function intV(n: number): Value {
  return encodeInt(BigInt(n));
}
function obs(o: string, p: string, val: Value): GroundLiteral {
  return GroundLiteral.of("obs", [av(o), av(p), val]);
}
function sym(s: string): Symbol {
  return Symbol.of(s);
}

const PROFILE_PIN: Hash = new Uint8Array(32).fill(0x11);
const CTX_PIN: Hash = new Uint8Array(32).fill(0x22);
const THEORY_PIN: Hash = new Uint8Array(32).fill(0x33);

function boundContext(program: MapProgram): CertContext {
  const digest = programDigest(program.iter().map(([, clause]) => clause));
  return CertContext.of(digest, PROFILE_PIN, CTX_PIN, THEORY_PIN);
}

// ================================ the program ===================================

const C_ELIGIBLE_COUNT = "eligible_count_rule";
const C_ELIGIBLE_DISTINCT = "eligible_distinct_rule";

// The EDB-of-record for obs:
//   obs(o1,p1,x), obs(o1,p2,x), obs(o1,p3,y), obs(o1,p4,null()), obs(o2,p1,z)
// For O=o1: 4 rows; distinct non-null V = {x, y} → 2.
function obsEdb(): GroundLiteral[] {
  return [
    obs("o1", "p1", av("x")),
    obs("o1", "p2", av("x")),
    obs("o1", "p3", av("y")),
    obs("o1", "p4", nullValue()),
    obs("o2", "p1", av("z")),
  ];
}

function countFilter(...entries: CountFilterEntry[]): CountFilterEntry[] {
  return entries;
}

function baseProgram(): MapProgram {
  const countClause = new Clause(Goal.of("eligible_count", [Term.var("O")]), [
    BodyLitCount(new PredicateRef(sym("obs"), 3), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.rows()),
  ]);
  const distinctClause = new Clause(Goal.of("eligible_distinct", [Term.var("O")]), [
    BodyLitCount(new PredicateRef(sym("obs"), 3), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.distinct(2)),
  ]);
  return new MapProgram().with(new ClauseId(C_ELIGIBLE_COUNT), countClause).with(new ClauseId(C_ELIGIBLE_DISTINCT), distinctClause);
}

// BodyLitCount builds a count body literal whose count slot is the head var N.
function BodyLitCount(pred: PredicateRef, filter: CountFilterEntry[], project: ProjectSpec): BodyLit {
  return BodyLit.count(new CountLit(pred, filter, project, Term.var("N")));
}

function aggProfile(): CheckProfile<void> {
  const edb = new Map<string, GroundLiteral[]>([["obs", obsEdb()]]);
  return { theory: new NoTheory(), leaves: new AggLeaves(["obs"], edb), admit: new AlwaysAdmit<void>(), limits: defaultLimits() };
}

// validCert is the valid sealed certificate for the prefix {obs} (level 0): obs = the live
// EDB snapshot. obs is a PURE EDB leaf, exempt from support, bound by the §3.6 gate.
function validCert(program: MapProgram): ClosedModelCert {
  const cx = boundContext(program);
  return new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("obs")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [
      FiniteDomain.of(sym("u"), [av("o1"), av("o2"), av("p1"), av("p2"), av("p3"), av("p4"), av("x"), av("y"), av("z"), nullValue()]),
    ],
    extensions: [RelationTable.of(sym("obs"), 3, obsEdb())],
    supports: [],
    limitsDecl: { certFacts: 5, domainValues: 10, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
}

function countSubst(k: number): Subst {
  return new Subst([
    [VarId.of("O"), Term.atom(new TextEncoder().encode("o1"))],
    [VarId.of("N"), Term.fromValue(intV(k))],
  ]);
}

function countPremise(pred: PredicateRef, filter: GroundFilterEntry[], project: ProjectSpec, k: number): CountPremise {
  return new CountPremise(pred, filter, project, intV(k), 0);
}

function countDerivation(clauseID: string, headPred: string, project: ProjectSpec, k: number, cert: ClosedModelCert): Derivation {
  const node = new RuleNode(
    GroundLiteral.of(headPred, [av("o1")]),
    new ClauseId(clauseID),
    countSubst(k),
    [countPremise(new PredicateRef(sym("obs"), 3), [{ pos: 0, value: av("o1") }], project, k)],
    NodeMeta.none(),
  );
  return new Derivation([node], 0, [cert]);
}

function run(program: MapProgram, claim: GroundLiteral, deriv: Derivation): Outcome {
  return checkWithCertContext(program, claim, deriv, undefined, aggProfile(), boundContext(program));
}

function assertReject(outcome: Outcome, expected: string): void {
  assert.equal(outcome.verdict.kind, "reject", `expected reject ${expected}, got ${outcome.verdict.kind}`);
  if (outcome.verdict.kind === "reject") {
    assert.equal(outcome.verdict.code, expected, `expected ${expected}, got ${outcome.verdict.code} (${outcome.verdict.detail})`);
  }
}

// =================================== ACCEPT ===================================

test("accept count rows matching filter", () => {
  const program = baseProgram();
  const deriv = countDerivation(C_ELIGIBLE_COUNT, "eligible_count", ProjectSpec.rows(), 4, validCert(program));
  const out = run(program, GroundLiteral.of("eligible_count", [av("o1")]), deriv);
  assert.equal(out.verdict.kind, "accept", out.verdict.kind === "reject" ? `${out.verdict.code} (${out.verdict.detail})` : "");
});

test("accept count_distinct excludes null", () => {
  const program = baseProgram();
  const deriv = countDerivation(C_ELIGIBLE_DISTINCT, "eligible_distinct", ProjectSpec.distinct(2), 2, validCert(program));
  const out = run(program, GroundLiteral.of("eligible_distinct", [av("o1")]), deriv);
  assert.equal(out.verdict.kind, "accept", out.verdict.kind === "reject" ? `${out.verdict.code} (${out.verdict.detail})` : "");
});

// =================================== REJECT ===================================

test("reject count_mismatch wrong k (rows)", () => {
  const program = baseProgram();
  const deriv = countDerivation(C_ELIGIBLE_COUNT, "eligible_count", ProjectSpec.rows(), 3, validCert(program)); // actually 4
  assertReject(run(program, GroundLiteral.of("eligible_count", [av("o1")]), deriv), "count_mismatch");
});

test("reject count_mismatch wrong k (distinct)", () => {
  const program = baseProgram();
  const deriv = countDerivation(C_ELIGIBLE_DISTINCT, "eligible_distinct", ProjectSpec.distinct(2), 3, validCert(program)); // actually 2
  assertReject(run(program, GroundLiteral.of("eligible_distinct", [av("o1")]), deriv), "count_mismatch");
});

test("reject count_stratum_not_lower (head sealed alongside obs)", () => {
  const program = baseProgram();
  const cx = boundContext(program);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("obs"), sym("eligible_count")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(sym("u"), [av("o1"), av("o2"), av("p1"), av("p2"), av("p3"), av("p4"), av("x"), av("y"), av("z"), nullValue()])],
    extensions: [RelationTable.of(sym("obs"), 3, obsEdb()), RelationTable.of(sym("eligible_count"), 1, [])],
    supports: [],
    limitsDecl: { certFacts: 5, domainValues: 10, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
  const deriv = countDerivation(C_ELIGIBLE_COUNT, "eligible_count", ProjectSpec.rows(), 4, cert);
  // The sealed-scope clause carries a count → §3.2 rejects cert_scope_incomplete, subsuming
  // the per-premise count_stratum_not_lower; either way the unsound same-stratum count fails.
  assertReject(run(program, GroundLiteral.of("eligible_count", [av("o1")]), deriv), "cert_scope_incomplete");
});

test("reject count_attr_out_of_range (distinct attr >= arity)", () => {
  const program = baseProgram().with(
    new ClauseId("eligible_bad_attr"),
    new Clause(Goal.of("eligible_bad", [Term.var("O")]), [
      BodyLitCount(new PredicateRef(sym("obs"), 3), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.distinct(5)),
    ]),
  );
  const cx = boundContext(program);
  const cert = validCertFor(program, cx);
  const node = new RuleNode(
    GroundLiteral.of("eligible_bad", [av("o1")]),
    new ClauseId("eligible_bad_attr"),
    countSubst(2),
    [countPremise(new PredicateRef(sym("obs"), 3), [{ pos: 0, value: av("o1") }], ProjectSpec.distinct(5), 2)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [cert]);
  assertReject(checkWithCertContext(program, GroundLiteral.of("eligible_bad", [av("o1")]), deriv, undefined, aggProfile(), cx), "count_attr_out_of_range");
});

test("reject count_attr_out_of_range (filter position >= arity)", () => {
  const program = baseProgram().with(
    new ClauseId("eligible_bad_filter"),
    new Clause(Goal.of("eligible_bad", [Term.var("O")]), [
      BodyLitCount(new PredicateRef(sym("obs"), 3), countFilter({ pos: 7, term: Term.var("O") }), ProjectSpec.rows()),
    ]),
  );
  const cx = boundContext(program);
  const cert = validCertFor(program, cx);
  const node = new RuleNode(
    GroundLiteral.of("eligible_bad", [av("o1")]),
    new ClauseId("eligible_bad_filter"),
    countSubst(0),
    [countPremise(new PredicateRef(sym("obs"), 3), [{ pos: 7, value: av("o1") }], ProjectSpec.rows(), 0)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [cert]);
  assertReject(checkWithCertContext(program, GroundLiteral.of("eligible_bad", [av("o1")]), deriv, undefined, aggProfile(), cx), "count_attr_out_of_range");
});

// #581 — the PredicateRef names obs with arity 2, but the sealed obs table has arity 3.
test("reject count wrong arity (count_attr_out_of_range)", () => {
  const program = baseProgram().with(
    new ClauseId("eligible_bad_arity"),
    new Clause(Goal.of("eligible_bad", [Term.var("O")]), [
      BodyLitCount(new PredicateRef(sym("obs"), 2), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.rows()),
    ]),
  );
  const cx = boundContext(program);
  const cert = validCertFor(program, cx);
  const node = new RuleNode(
    GroundLiteral.of("eligible_bad", [av("o1")]),
    new ClauseId("eligible_bad_arity"),
    countSubst(4),
    [countPremise(new PredicateRef(sym("obs"), 2), [{ pos: 0, value: av("o1") }], ProjectSpec.rows(), 4)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [cert]);
  assertReject(checkWithCertContext(program, GroundLiteral.of("eligible_bad", [av("o1")]), deriv, undefined, aggProfile(), cx), "count_attr_out_of_range");
});

test("reject stale EDB (cert_edb_mismatch)", () => {
  const program = baseProgram();
  const cx = boundContext(program);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("obs")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(sym("u"), [av("o1"), av("o2"), av("p1"), av("p2"), av("p3"), av("p4"), av("x"), av("y"), av("z"), nullValue()])],
    // obs(o1,p4,null()) and obs(o2,p1,z) OMITTED → stale vs the attested snapshot.
    extensions: [RelationTable.of(sym("obs"), 3, [obs("o1", "p1", av("x")), obs("o1", "p2", av("x")), obs("o1", "p3", av("y"))])],
    supports: [],
    limitsDecl: { certFacts: 3, domainValues: 10, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
  const deriv = countDerivation(C_ELIGIBLE_COUNT, "eligible_count", ProjectSpec.rows(), 4, cert);
  assertReject(run(program, GroundLiteral.of("eligible_count", [av("o1")]), deriv), "cert_edb_mismatch");
});

test("reject count_mismatch — filter genuinely applied (o2 has 1 row, claim 4)", () => {
  const program = baseProgram();
  const cx = boundContext(program);
  const subst = new Subst([[VarId.of("O"), Term.atom(new TextEncoder().encode("o2"))], [VarId.of("N"), Term.fromValue(intV(4))]]);
  const node = new RuleNode(
    GroundLiteral.of("eligible_count", [av("o2")]),
    new ClauseId(C_ELIGIBLE_COUNT),
    subst,
    [new CountPremise(new PredicateRef(sym("obs"), 3), [{ pos: 0, value: av("o2") }], ProjectSpec.rows(), intV(4), 0)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [validCertFor(program, cx)]);
  assertReject(checkWithCertContext(program, GroundLiteral.of("eligible_count", [av("o2")]), deriv, undefined, aggProfile(), cx), "count_mismatch");
});

test("accept count — filter applied to o2 gives 1 row, claim 1", () => {
  const program = baseProgram();
  const cx = boundContext(program);
  const subst = new Subst([[VarId.of("O"), Term.atom(new TextEncoder().encode("o2"))], [VarId.of("N"), Term.fromValue(intV(1))]]);
  const node = new RuleNode(
    GroundLiteral.of("eligible_count", [av("o2")]),
    new ClauseId(C_ELIGIBLE_COUNT),
    subst,
    [new CountPremise(new PredicateRef(sym("obs"), 3), [{ pos: 0, value: av("o2") }], ProjectSpec.rows(), intV(1), 0)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [validCertFor(program, cx)]);
  const out = checkWithCertContext(program, GroundLiteral.of("eligible_count", [av("o2")]), deriv, undefined, aggProfile(), cx);
  assert.equal(out.verdict.kind, "accept", out.verdict.kind === "reject" ? `${out.verdict.code} (${out.verdict.detail})` : "");
});

test("reject cert_out_of_range — cited cert index does not exist", () => {
  const program = baseProgram();
  const cert = validCert(program);
  const node = new RuleNode(
    GroundLiteral.of("eligible_count", [av("o1")]),
    new ClauseId(C_ELIGIBLE_COUNT),
    countSubst(4),
    [countPremise(new PredicateRef(sym("obs"), 3), [{ pos: 0, value: av("o1") }], ProjectSpec.rows(), 4)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, []); // empty closedWorld
  void cert;
  assertReject(run(program, GroundLiteral.of("eligible_count", [av("o1")]), deriv), "cert_out_of_range");
});

test("count clause round-trips and arity is load-bearing in the id", async () => {
  const { canonicalClauseId, clauseValue, clauseFromValue } = await import("../src/account.js");
  const clause = new Clause(Goal.of("eligible", [Term.var("O")]), [
    BodyLitCount(new PredicateRef(sym("obs"), 3), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.distinct(2)),
  ]);
  const decoded = clauseFromValue(clauseValue(clause));
  assert.notEqual(decoded, undefined);
  assert.equal(canonicalClauseId(decoded!).asStr(), canonicalClauseId(clause).asStr());
  // obs/3 and obs/2 produce distinct ids.
  const clause2 = new Clause(Goal.of("eligible", [Term.var("O")]), [
    BodyLitCount(new PredicateRef(sym("obs"), 2), countFilter({ pos: 0, term: Term.var("O") }), ProjectSpec.distinct(2)),
  ]);
  assert.notEqual(canonicalClauseId(clause).asStr(), canonicalClauseId(clause2).asStr());
});

// ====================== #587 — integer sum / min / max folds ======================
// A second relation score(obj, val) whose column 1 is a sealed integer. The aggregate folds
// it exactly over BigInt. v1 is INTEGER-only, SET semantics over the proven-exact rows; empty
// sum = 0; empty min/max REJECT (agg_empty_undefined); a non-int column is ill-typed
// (count_attr_out_of_range). A structural mirror of the Rust oracle's #587 section.

const C_SCORE_SUM = "score_sum_rule";
const C_SCORE_MIN = "score_min_rule";
const C_SCORE_MAX = "score_max_rule";

// score(obj, val) with an int val column (or a non-int for the ill-typed test).
function score(obj: string, val: Value): GroundLiteral {
  return GroundLiteral.of("score", [av(obj), val]);
}

// EDB-of-record for score: g1 has int values {3, 7, 1} (set semantics over distinct facts).
// sum over g1 = 3+7+1 = 11; min = 1; max = 7. g2_unused has one unrelated row.
function scoreEdb(): GroundLiteral[] {
  return [score("g1", intV(3)), score("g1", intV(7)), score("g1", intV(1)), score("g2_unused", intV(99))];
}

function scoreProgram(): MapProgram {
  const mk = (head: string, project: ProjectSpec): Clause =>
    new Clause(Goal.of(head, [Term.var("G")]), [
      BodyLit.count(new CountLit(new PredicateRef(sym("score"), 2), countFilter({ pos: 0, term: Term.var("G") }), project, Term.var("N"))),
    ]);
  return new MapProgram()
    .with(new ClauseId(C_SCORE_SUM), mk("score_sum", ProjectSpec.sum(1)))
    .with(new ClauseId(C_SCORE_MIN), mk("score_min", ProjectSpec.min(1)))
    .with(new ClauseId(C_SCORE_MAX), mk("score_max", ProjectSpec.max(1)));
}

function scoreProfile(): CheckProfile<void> {
  const edb = new Map<string, GroundLiteral[]>([["score", scoreEdb()]]);
  return { theory: new NoTheory(), leaves: new AggLeaves(["score"], edb), admit: new AlwaysAdmit<void>(), limits: defaultLimits() };
}

function scoreCertWithDomain(domainVals: Value[]): ClosedModelCert {
  const cx = boundContext(scoreProgram());
  return new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("score")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(sym("u"), domainVals)],
    extensions: [RelationTable.of(sym("score"), 2, scoreEdb())],
    supports: [],
    limitsDecl: { certFacts: 4, domainValues: domainVals.length, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
}

function scoreCert(): ClosedModelCert {
  return scoreCertWithDomain([av("g1"), av("g2_unused"), intV(3), intV(7), intV(1), intV(99)]);
}

// The cert + domain that includes an in-domain group atom empty_grp with no rows.
function scoreCertEmptyGroup(): ClosedModelCert {
  return scoreCertWithDomain([av("g1"), av("g2_unused"), av("empty_grp"), intV(3), intV(7), intV(1), intV(99)]);
}

// <head>(g) :- agg(score(g, V), V, k), citing the score cert.
function foldDerivation(clauseID: string, headPred: string, group: string, project: ProjectSpec, k: number, cert: ClosedModelCert): Derivation {
  const subst = new Subst([
    [VarId.of("G"), Term.atom(new TextEncoder().encode(group))],
    [VarId.of("N"), Term.fromValue(intV(k))],
  ]);
  const node = new RuleNode(
    GroundLiteral.of(headPred, [av(group)]),
    new ClauseId(clauseID),
    subst,
    [new CountPremise(new PredicateRef(sym("score"), 2), [{ pos: 0, value: av(group) }], project, intV(k), 0)],
    NodeMeta.none(),
  );
  return new Derivation([node], 0, [cert]);
}

function runFold(claimPred: string, group: string, deriv: Derivation): Outcome {
  const program = scoreProgram();
  return checkWithCertContext(program, GroundLiteral.of(claimPred, [av(group)]), deriv, undefined, scoreProfile(), boundContext(program));
}

test("accept integer sum: 3 + 7 + 1 = 11 over the sealed g1 column", () => {
  const deriv = foldDerivation(C_SCORE_SUM, "score_sum", "g1", ProjectSpec.sum(1), 11, scoreCert());
  const out = runFold("score_sum", "g1", deriv);
  assert.equal(out.verdict.kind, "accept", out.verdict.kind === "reject" ? `${out.verdict.code} (${out.verdict.detail})` : "");
});

test("accept integer min / max over the sealed g1 column: min = 1, max = 7", () => {
  const dmin = foldDerivation(C_SCORE_MIN, "score_min", "g1", ProjectSpec.min(1), 1, scoreCert());
  const omin = runFold("score_min", "g1", dmin);
  assert.equal(omin.verdict.kind, "accept", omin.verdict.kind === "reject" ? `${omin.verdict.code} (${omin.verdict.detail})` : "");
  const dmax = foldDerivation(C_SCORE_MAX, "score_max", "g1", ProjectSpec.max(1), 7, scoreCert());
  const omax = runFold("score_max", "g1", dmax);
  assert.equal(omax.verdict.kind, "accept", omax.verdict.kind === "reject" ? `${omax.verdict.code} (${omax.verdict.detail})` : "");
});

test("accept empty sum = 0: no score rows match the in-domain group empty_grp", () => {
  const deriv = foldDerivation(C_SCORE_SUM, "score_sum", "empty_grp", ProjectSpec.sum(1), 0, scoreCertEmptyGroup());
  const out = runFold("score_sum", "empty_grp", deriv);
  assert.equal(out.verdict.kind, "accept", out.verdict.kind === "reject" ? `${out.verdict.code} (${out.verdict.detail})` : "");
});

test("reject empty min: min of an empty set is undefined (agg_empty_undefined)", () => {
  // k is irrelevant — the empty fold rejects BEFORE the k comparison.
  const deriv = foldDerivation(C_SCORE_MIN, "score_min", "empty_grp", ProjectSpec.min(1), 0, scoreCertEmptyGroup());
  assertReject(runFold("score_min", "empty_grp", deriv), "agg_empty_undefined");
});

test("reject empty max: symmetric to min (agg_empty_undefined)", () => {
  const deriv = foldDerivation(C_SCORE_MAX, "score_max", "empty_grp", ProjectSpec.max(1), 0, scoreCertEmptyGroup());
  assertReject(runFold("score_max", "empty_grp", deriv), "agg_empty_undefined");
});

test("reject a tampered sum: claim 99 when the real sum is 11 (count_mismatch)", () => {
  const deriv = foldDerivation(C_SCORE_SUM, "score_sum", "g1", ProjectSpec.sum(1), 99, scoreCert());
  assertReject(runFold("score_sum", "g1", deriv), "count_mismatch");
});

test("reject a tampered max: claim 8 when the real max is 7 (count_mismatch)", () => {
  const deriv = foldDerivation(C_SCORE_MAX, "score_max", "g1", ProjectSpec.max(1), 8, scoreCert());
  assertReject(runFold("score_max", "g1", deriv), "count_mismatch");
});

test("reject a sum over a NON-INT column: fold column 0 (the group atom) (count_attr_out_of_range)", () => {
  const bad = new Clause(Goal.of("score_bad", [Term.var("G")]), [
    BodyLit.count(new CountLit(new PredicateRef(sym("score"), 2), countFilter({ pos: 0, term: Term.var("G") }), ProjectSpec.sum(0), Term.var("N"))),
  ]);
  const program = scoreProgram().with(new ClauseId("score_bad_rule"), bad);
  const cx = boundContext(program);
  // Bind the cert to THIS (augmented) program's digest, not score_program's.
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("score")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(sym("u"), [av("g1"), av("g2_unused"), intV(3), intV(7), intV(1), intV(99)])],
    extensions: [RelationTable.of(sym("score"), 2, scoreEdb())],
    supports: [],
    limitsDecl: { certFacts: 4, domainValues: 6, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
  const subst = new Subst([
    [VarId.of("G"), Term.atom(new TextEncoder().encode("g1"))],
    [VarId.of("N"), Term.fromValue(intV(0))],
  ]);
  const node = new RuleNode(
    GroundLiteral.of("score_bad", [av("g1")]),
    new ClauseId("score_bad_rule"),
    subst,
    [new CountPremise(new PredicateRef(sym("score"), 2), [{ pos: 0, value: av("g1") }], ProjectSpec.sum(0), intV(0), 0)],
    NodeMeta.none(),
  );
  const deriv = new Derivation([node], 0, [cert]);
  assertReject(checkWithCertContext(program, GroundLiteral.of("score_bad", [av("g1")]), deriv, undefined, scoreProfile(), cx), "count_attr_out_of_range");
});

// validCertFor builds the valid {obs} cert bound to an already-computed context (for the
// augmented programs whose digest differs from the base program's).
function validCertFor(program: MapProgram, cx: CertContext): ClosedModelCert {
  return new ClosedModelCert({
    scope: StratumPrefix.of(0, [sym("obs")]),
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(sym("u"), [av("o1"), av("o2"), av("p1"), av("p2"), av("p3"), av("p4"), av("x"), av("y"), av("z"), nullValue()])],
    extensions: [RelationTable.of(sym("obs"), 3, obsEdb())],
    supports: [],
    limitsDecl: { certFacts: 5, domainValues: 10, supportEdges: 0, ruleGroundings: 1000, joinSteps: 10000, certBytes: 8192 },
  });
  void program;
}

// ========================= #2569: the checker's world memo =========================
// The ts rung of #2565 term 1, ported from contract/rs/tests/negation.rs `world_memo_2565` onto
// this fixture: WorldMemo verifies a closed world once for a run of derivations citing it, and
// every verdict through it is the fresh checkWithCertContext verdict.

function memoClaim(): GroundLiteral {
  return GroundLiteral.of("eligible_count", [av("o1")]);
}

function memoDeriv(cert: ClosedModelCert): Derivation {
  return countDerivation(C_ELIGIBLE_COUNT, "eligible_count", ProjectSpec.rows(), 4, cert);
}

function memoFresh(program: MapProgram, prof: CheckProfile<void>, claim: GroundLiteral, deriv: Derivation): Outcome {
  return checkWithCertContext(program, claim, deriv, undefined, prof, boundContext(program));
}

type CertParams = ConstructorParameters<typeof ClosedModelCert>[0];

function certWith(program: MapProgram, change: Partial<CertParams>): ClosedModelCert {
  const c = validCert(program);
  return new ClosedModelCert({
    scope: c.scope,
    programHash: c.programHash,
    profileHash: c.profileHash,
    ctxHash: c.ctxHash,
    theoryConfigHash: c.theoryConfigHash,
    edbSnapshotHashes: c.edbSnapshotHashes,
    domains: c.domains,
    extensions: c.extensions,
    supports: c.supports,
    limitsDecl: c.limitsDecl,
    ...change,
  });
}

/** One change each to the valid certificate: a table row, a domain value, a pin, a size declaration. */
function memoMutations(program: MapProgram): { what: string; cert: ClosedModelCert }[] {
  const rows = obsEdb();
  rows[0] = obs("o1", "p1", av("y"));
  const pin = new Uint8Array(validCert(program).programHash);
  pin[0] = pin[0]! ^ 1;
  return [
    { what: "a table row", cert: certWith(program, { extensions: [RelationTable.of(sym("obs"), 3, rows)] }) },
    {
      what: "a domain value",
      cert: certWith(program, {
        domains: [
          FiniteDomain.of(sym("u"), [av("o1"), av("o2"), av("p1"), av("p2"), av("p3"), av("p4"), av("x"), av("y"), nullValue()]),
        ],
      }),
    },
    { what: "a pin", cert: certWith(program, { programHash: pin }) },
    { what: "a size declaration", cert: certWith(program, { limitsDecl: { ...validCert(program).limitsDecl, certFacts: 6 } }) },
  ];
}

test("#2569: a world cited by many answers is verified once", () => {
  const program = baseProgram();
  const memo = new WorldMemo(program, aggProfile(), undefined, boundContext(program));
  const deriv = memoDeriv(validCert(program));
  for (let i = 0; i < 5; i++) {
    assert.equal(checkWithWorldMemo(memo, memoClaim(), deriv).verdict.kind, "accept", `answer ${i}`);
  }
  assert.equal(memo.certificatesVerified, 1, "five answers citing one certificate verify it once");
});

test("a verifier can change the producer's pin without changing the memo's verified world", () => {
  const program = baseProgram();
  const cert = certWith(program, { profileHash: PROFILE_PIN.slice() });
  const deriv = memoDeriv(cert);
  const profile = aggProfile();
  const stable = profile.leaves;
  // test-double: consumer(attests the fixed EDB while changing only the producer's pin)
  const leaves: LeafVerifier<void> = {
    extensional: () => stable.extensional(),
    verify: (literal, ev, ctx) => stable.verify(literal, ev, ctx),
    edbSnapshot(pred, ctx) {
      cert.profileHash.fill(0);
      return stable.edbSnapshot!(pred, ctx);
    },
  };
  const memo = new WorldMemo(program, { ...profile, leaves }, undefined, boundContext(program));
  assert.equal(checkWithWorldMemo(memo, memoClaim(), deriv).verdict.kind, "accept");
  const fresh = memoFresh(program, profile, memoClaim(), deriv);
  assertReject(fresh, "cert_context_mismatch");
  assert.deepEqual(checkWithWorldMemo(memo, memoClaim(), deriv).verdict, fresh.verdict);
  assert.equal(memo.certificatesVerified, 2);
});

test("a consumer cannot inject a valid world status or alter the memo's bound pins", () => {
  const program = baseProgram();
  const profile = aggProfile();
  const context = { ...boundContext(program), profileHash: PROFILE_PIN.slice() };
  class InjectedMemo extends WorldMemo<void> {
    statuses() { return [{ kind: "valid" }]; }
  }
  const memo = new InjectedMemo(program, profile, undefined, context);
  const valid = memoDeriv(validCert(program));
  context.profileHash.fill(0);
  memo.certContext.profileHash.fill(0);
  assert.equal(checkWithWorldMemo(memo, memoClaim(), valid).verdict.kind, "accept");
  const invalid = memoDeriv(certWith(program, { profileHash: new Uint8Array(32) }));
  const expected = memoFresh(program, profile, memoClaim(), invalid);
  assertReject(expected, "cert_context_mismatch");
  assert.deepEqual(checkWithWorldMemo(memo, memoClaim(), invalid).verdict, expected.verdict);
  assert.equal(memo.certificatesVerified, 2);
  assert.equal(Reflect.get(WorldMemo.prototype, "statuses"), undefined);
});

test("#2569: a changed certificate is a miss with the fresh verdict", () => {
  const program = baseProgram();
  const prof = aggProfile();
  const memo = new WorldMemo(program, prof, undefined, boundContext(program));
  const valid = memoDeriv(validCert(program));
  assert.equal(checkWithWorldMemo(memo, memoClaim(), valid).verdict.kind, "accept");
  // The control, exact: which single changes a fresh check rejects. The size declaration above the
  // real size is a change the checker ACCEPTS, and it must miss all the same: the memo keys on the
  // certificate, never on the verdict.
  const rejecting = new Set(["a table row", "a domain value", "a pin"]);
  for (const m of memoMutations(program)) {
    const before = memo.certificatesVerified;
    const deriv = memoDeriv(m.cert);
    const expected = memoFresh(program, prof, memoClaim(), deriv);
    assert.deepEqual(checkWithWorldMemo(memo, memoClaim(), deriv).verdict, expected.verdict, `${m.what}: the memo's verdict is not the fresh one`);
    assert.equal(memo.certificatesVerified, before + 1, `${m.what}: a changed certificate must miss`);
    assert.equal(
      expected.verdict.kind !== "accept",
      rejecting.has(m.what),
      `${m.what}: the control's expected verdict, ${JSON.stringify(expected)}`,
    );
    assert.equal(checkWithWorldMemo(memo, memoClaim(), valid).verdict.kind, "accept", `${m.what}: the valid world after it`);
  }
});

// A certificate is frozen, but its hashes' bytes and its size declaration are not. An edit in place
// to a certificate already checked must be a miss with the fresh verdict, never a hit on identity.
test("#2569: an in-place edit of a checked certificate is a miss", () => {
  const program = baseProgram();
  const prof = aggProfile();
  const edits: { what: string; edit: (c: ClosedModelCert) => void }[] = [
    {
      what: "a pin's bytes",
      edit: (c) => {
        c.programHash[0] = c.programHash[0]! ^ 1;
      },
    },
    {
      what: "the size declaration",
      edit: (c) => {
        (c.limitsDecl as { certFacts: number }).certFacts = 4;
      },
    },
  ];
  for (const e of edits) {
    const memo = new WorldMemo(program, prof, undefined, boundContext(program));
    const cert = certWith(program, { limitsDecl: { ...validCert(program).limitsDecl } });
    const deriv = memoDeriv(cert);
    assert.equal(checkWithWorldMemo(memo, memoClaim(), deriv).verdict.kind, "accept", `${e.what}: the valid world`);
    e.edit(cert);
    const expected = memoFresh(program, prof, memoClaim(), deriv);
    assert.notEqual(expected.verdict.kind, "accept", `${e.what}: control, the edited certificate must be rejected fresh`);
    assert.deepEqual(checkWithWorldMemo(memo, memoClaim(), deriv).verdict, expected.verdict, `${e.what}: the memo's verdict`);
    assert.equal(memo.certificatesVerified, 2, `${e.what}: an in-place edit must miss`);
  }
});

// Limits are the one bound input checked rather than assumed: a limit changed through the profile
// the memo holds re-verifies, and so does changing it back.
test("#2569: a limit changed through the bound profile is a miss", () => {
  const program = baseProgram();
  const prof = aggProfile();
  const memo = new WorldMemo(program, prof, undefined, boundContext(program));
  const deriv = memoDeriv(validCert(program));
  assert.equal(checkWithWorldMemo(memo, memoClaim(), deriv).verdict.kind, "accept", "the loose limits");
  const loose = prof.limits;
  const writable = prof as { limits: typeof loose };
  writable.limits = { ...loose, maxCertFacts: 4 }; // the valid certificate seals five facts
  const tight = memoFresh(program, prof, memoClaim(), deriv);
  assert.notEqual(tight.verdict.kind, "accept", "control: the tighter limit must reject");
  assert.deepEqual(checkWithWorldMemo(memo, memoClaim(), deriv).verdict, tight.verdict, "tightened");
  writable.limits = loose;
  assert.equal(checkWithWorldMemo(memo, memoClaim(), deriv).verdict.kind, "accept", "loosened again");
  assert.equal(memo.certificatesVerified, 3, "each change of limits re-verifies");
});

test("#2569: a mixed sequence through one memo is the fresh sequence", () => {
  const program = baseProgram();
  const prof = aggProfile();
  const memo = new WorldMemo(program, prof, undefined, boundContext(program));
  const row = obs("o1", "p1", av("x"));
  const positive = new Derivation([new LeafNode(row, EvidenceOps.none())], 0);
  const valid = memoDeriv(validCert(program));
  const [tableRow, domain, pin] = memoMutations(program).map((m) => memoDeriv(m.cert));
  const steps: [GroundLiteral, Derivation][] = [
    [memoClaim(), valid], // miss 1
    [row, positive], // no world: the slot is not touched
    [memoClaim(), valid], // hit
    [memoClaim(), tableRow!], // miss 2
    [memoClaim(), valid], // miss 3
    [row, positive], // no world
    [memoClaim(), domain!], // miss 4
    [memoClaim(), domain!], // hit
    [memoClaim(), valid], // miss 5
    [memoClaim(), pin!], // miss 6
    [memoClaim(), valid], // miss 7
  ];
  steps.forEach(([claim, deriv], i) => {
    assert.deepEqual(checkWithWorldMemo(memo, claim, deriv).verdict, memoFresh(program, prof, claim, deriv).verdict, `step ${i}`);
  });
  assert.equal(memoFresh(program, prof, row, positive).verdict.kind, "accept", "the positive control accepts");
  assert.equal(memo.certificatesVerified, 7, "seven misses, two hits, and positive answers never evict the world");
});
