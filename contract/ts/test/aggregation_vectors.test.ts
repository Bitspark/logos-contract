/*
 * Aggregation-family conformance vectors (ADR 0023 certifiable count / count_distinct,
 * Phase 5, #585, epic #579). This replays vectors/aggregation.json — the SAME
 * hand-authored rs oracle the rs and go cores replay — asserting every case's `outcome`
 * against the TS checkWithCertContext over the closed-model-cert machinery. One oracle
 * (rs, per the #464 lesson) pins all three cores byte-identically.
 *
 * The aggregation_v1 profile (mirrored across cores): NO theory (NoTheory owns nothing),
 * EDB leaves = the top-level `extensional` set with `edbSnapshot` recomputed over the
 * top-level `edb` rows, AlwaysAdmit, unit context. The bound context is DERIVED from the
 * live program (recomputed programDigest) + fixed non-zero pins; each cert auto-binds to
 * it. Certs are named in a top-level `certs` map, selected per case by `cert` (a key, or
 * null ⇒ no cert supplied).
 *
 * THE CORE GUARANTEE pinned tri-core is `tamper_wrong_k_over_valid_cert`: a derivation
 * claiming a wrong k over an otherwise VALID cert MUST be rejected count_mismatch.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { Atom, Tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";
import {
  AlwaysAdmit,
  BigDecimal,
  BodyLit,
  CertContext,
  checkWithCertContext,
  checkWithWorldMemo,
  Clause,
  ClauseId,
  ClosedModelCert,
  CountLit,
  CountPremise,
  type CountFilterEntry,
  Derivation,
  type Evidence,
  edbTableHash,
  FiniteDomain,
  Goal,
  type GroundFilterEntry,
  GroundLiteral,
  type Hash,
  type LeafOutcome,
  LeafOutcome as LeafOutcomeOps,
  type LeafVerifier,
  MapProgram,
  type Node,
  NodeMeta,
  Outcome,
  PredicateRef,
  PredicateSet,
  ProjectSpec,
  programDigest,
  RelationTable,
  RuleNode,
  StratumPrefix,
  type Subst,
  type SupportEdge,
  SupportEdge as SupportEdgeClass,
  type SupportRef,
  SupportRef as SupportRefOps,
  Symbol,
  Term,
  type Theory,
  TheoryOutcome,
  type CheckProfile,
  defaultLimits,
  CHECK_BUDGETS,
  eachBudgetRaised,
  type CheckLimits,
  WorldMemo,
} from "../src/index.js";
import { assertLengthReading2605 } from "./support/cert_len_2605.js";
import { r3Domain, r3Raised } from "./support/r3_domain.js";

// ------------------------------- locate the oracle -------------------------------

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "aggregation.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/aggregation.json above ${dir}`);
    dir = parent;
  }
}

function loadVectors(): any {
  return JSON.parse(fs.readFileSync(path.join(repoRoot(), "vectors", "aggregation.json"), "utf8"));
}

// ------------------------------- the aggregation_v1 profile -----------------------

// test-double: consumer(owns no predicate)
class NoTheory implements Theory {
  owns(_pred: Symbol): boolean {
    return false;
  }
  decide(_atom: GroundLiteral): TheoryOutcome {
    return TheoryOutcome.Fails("no_theory");
  }
}

const PROFILE_PIN: Hash = new Uint8Array(32).fill(0x01);
const CTX_PIN: Hash = new Uint8Array(32).fill(0x02);
const THEORY_PIN: Hash = new Uint8Array(32).fill(0x03);

// test-double: consumer(the vector EDB with attested snapshots)
class AggLeaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #snapshots = new Map<string, Hash>();
  constructor(extensional: string[], edb: Record<string, any[]>) {
    this.#extensional = PredicateSet.from(extensional);
    for (const [pred, rows] of Object.entries(edb)) {
      this.#snapshots.set(pred, edbTableHash(Symbol.of(pred), rows.map(groundFromJson)));
    }
  }
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcomeOps.Admit;
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    const key = new TextDecoder().decode(pred.bytes());
    if (this.#snapshots.has(key)) return this.#snapshots.get(key);
    if (this.#extensional.contains(pred)) return edbTableHash(pred, []);
    return undefined;
  }
}

// -------------------------------- authoring notation -----------------------------

function termFromJson(j: any): Term {
  if (typeof j.atom_str === "string") return Term.atom(new TextEncoder().encode(j.atom_str));
  if (typeof j.var === "string") return Term.var(j.var);
  if (typeof j.int === "number") return Term.fromValue(encodeInt(BigInt(j.int)));
  // #2813: the canonical ontos decimal embedding (#331, the term.json notation), for the frozen
  // decimal-column rows and the non-int k row.
  if (typeof j.decimal === "string") {
    const d = BigDecimal.fromString(j.decimal);
    if (d === undefined) throw new Error(`decimal ${JSON.stringify(j.decimal)} is not a decimal literal`);
    return Term.fromValue(d.toTerm());
  }
  if (Array.isArray(j.tuple)) return Term.tuple(j.tuple.map(termFromJson));
  throw new Error(`term must be atom_str/var/int/decimal/tuple: ${JSON.stringify(j)}`);
}

function groundValue(j: any): Value {
  const v = Term.eraseGround(termFromJson(j));
  if (v === undefined) throw new Error("value must be ground");
  return v;
}

function goalFromJson(j: any): Goal {
  return new Goal(Symbol.of(String(j.pred)), ((j.args as any[]) ?? []).map(termFromJson));
}

function groundFromJson(j: any): GroundLiteral {
  const g = goalFromJson(j).asGround();
  if (g === undefined) throw new Error("ground literal must be ground in the vector");
  return g;
}

function projectFromJson(j: any): ProjectSpec {
  if (j === "rows") return ProjectSpec.rows();
  if (typeof j.distinct === "number") return ProjectSpec.distinct(j.distinct);
  // #587 integer folds.
  if (typeof j.sum === "number") return ProjectSpec.sum(j.sum);
  if (typeof j.min === "number") return ProjectSpec.min(j.min);
  if (typeof j.max === "number") return ProjectSpec.max(j.max);
  throw new Error(`project must be 'rows' or {distinct|sum|min|max:<attr>}: ${JSON.stringify(j)}`);
}

function predRefFromJson(j: any): PredicateRef {
  return new PredicateRef(Symbol.of(String(j.name)), Number(j.arity));
}

function bodyLitFromJson(j: any): BodyLit {
  if (j !== null && typeof j === "object" && j.count_lit !== undefined) {
    const c = j.count_lit;
    const filter: CountFilterEntry[] = ((c.filter as any[]) ?? []).map((e) => {
      if (typeof e.var === "string") return { pos: Number(e.pos), term: Term.var(e.var) };
      if (typeof e.atom_str === "string") return { pos: Number(e.pos), term: Term.atom(new TextEncoder().encode(e.atom_str)) };
      throw new Error(`count_lit filter entry must bind a var/atom_str: ${JSON.stringify(e)}`);
    });
    return BodyLit.count(new CountLit(predRefFromJson(c.pred), filter, projectFromJson(c.project), termFromJson(c.count)));
  }
  return BodyLit.pos(goalFromJson(j));
}

function substFromJson(j: any): Subst {
  const subst: Subst = new Map();
  for (const [name, term] of Object.entries(j)) subst.set(name, termFromJson(term));
  return subst;
}

function premiseFromJson(j: any): number | CountPremise {
  if (typeof j === "number") return j;
  const c = j.count;
  const filter: GroundFilterEntry[] = ((c.filter as any[]) ?? []).map((e) => ({ pos: Number(e.pos), value: groundValue(e.value) }));
  return new CountPremise(predRefFromJson(c.pred), filter, projectFromJson(c.project), premiseK(c.k), Number(c.cert));
}

// A count premise's k: a bare int (the canonical int embedding) or, #2813, any value in the term
// notation (a non-int claim). Any other shape, or a missing k, is a vector error, never a default.
function premiseK(k: unknown): Value {
  if (typeof k === "number" && Number.isSafeInteger(k)) return encodeInt(BigInt(k));
  if (k !== null && typeof k === "object" && !Array.isArray(k)) return groundValue(k);
  throw new Error(`count k must be an int or a term object, got ${JSON.stringify(k)}`);
}

function nodeFromJson(j: any): Node {
  const conclusion = groundFromJson(j.conclusion);
  switch (j.kind) {
    case "rule":
      return new RuleNode(
        conclusion,
        ClauseId.of(String(j.clause)),
        substFromJson(j.subst),
        ((j.premises as any[]) ?? []).map(premiseFromJson),
        NodeMeta.none(),
      );
    default:
      throw new Error(`unknown node kind ${JSON.stringify(j.kind)}`);
  }
}

function programFromJson(j: any): MapProgram {
  const program = new MapProgram();
  for (const [id, clause] of Object.entries<any>(j)) {
    program.insert(ClauseId.of(id), new Clause(goalFromJson(clause.head), (clause.body as any[]).map(bodyLitFromJson)));
  }
  return program;
}

// Verbatim constructors, NOT `.of` — the loader must carry the vector's collection
// order exactly as authored, or a non-canonical case (issue #839) is silently
// repaired before it can reach the gate it exists to pin.
function verbatimStratumPrefix(level: number, predicates: Symbol[]): StratumPrefix {
  const s = Object.create(StratumPrefix.prototype);
  s.level = level;
  s.predicates = Object.freeze(predicates);
  return Object.freeze(s) as StratumPrefix;
}

function verbatimFiniteDomain(typeTag: Symbol, values: Value[]): FiniteDomain {
  const d = Object.create(FiniteDomain.prototype);
  d.typeTag = typeTag;
  d.values = Object.freeze(values);
  return Object.freeze(d) as FiniteDomain;
}

function verbatimRelationTable(pred: Symbol, arity: number, rows: GroundLiteral[]): RelationTable {
  const t = Object.create(RelationTable.prototype);
  t.pred = pred;
  t.arity = arity;
  t.rows = Object.freeze(rows);
  return Object.freeze(t) as RelationTable;
}

// #2258 L3.3b: a stacked cert carries support edges, whose refs may cite a lower cert.
function supportRefFromJson(j: any): SupportRef {
  if (j.same_stratum !== undefined) {
    return SupportRefOps.sameStratum(groundFromJson(j.same_stratum.fact), Number(j.same_stratum.rank));
  }
  if (j.lower_stratum !== undefined) {
    return SupportRefOps.lowerStratum(Number(j.lower_stratum.cert), groundFromJson(j.lower_stratum.atom));
  }
  if (j.builtin !== undefined) return SupportRefOps.builtin(groundFromJson(j.builtin.atom));
  if (j.neg_lower !== undefined) return SupportRefOps.negLower(Number(j.neg_lower.cert), groundFromJson(j.neg_lower.atom));
  if (j.count_lower !== undefined) return SupportRefOps.countLower(Number(j.count_lower.cert));
  throw new Error(`support ref must be same_stratum/lower_stratum/builtin/neg_lower/count_lower: ${JSON.stringify(j)}`);
}

function supportEdgeFromJson(j: any): SupportEdge {
  return new SupportEdgeClass(
    groundFromJson(j.fact),
    ClauseId.of(String(j.clause)),
    substFromJson(j.subst),
    (j.body_refs as any[]).map(supportRefFromJson),
    Number(j.rank),
  );
}

function certFromJson(j: any, cx: CertContext): ClosedModelCert {
  const scope = verbatimStratumPrefix(Number(j.scope.level), (j.scope.predicates as any[]).map((p) => Symbol.of(String(p))));
  const domains: FiniteDomain[] = (j.domains as any[]).map((d) =>
    verbatimFiniteDomain(Symbol.of(String(d.type_tag)), (d.values as any[]).map(groundValue)),
  );
  const extensions: RelationTable[] = (j.extensions as any[]).map((t) =>
    verbatimRelationTable(Symbol.of(String(t.pred)), Number(t.arity), (t.rows as any[]).map(groundFromJson)),
  );
  const ld = j.limits_decl;
  return new ClosedModelCert({
    scope,
    programHash: cx.programHash,
    profileHash: cx.profileHash,
    ctxHash: cx.ctxHash,
    theoryConfigHash: cx.theoryConfigHash,
    edbSnapshotHashes: [],
    domains,
    extensions,
    supports: ((j.supports as any[]) ?? []).map(supportEdgeFromJson),
    partialScope:
      j.partial_scope === undefined
        ? undefined
        : verbatimStratumPrefix(
            Number(j.partial_scope.level),
            (j.partial_scope.predicates as any[]).map((p) => Symbol.of(String(p))),
          ),
    limitsDecl: {
      certFacts: Number(ld.cert_facts),
      domainValues: Number(ld.domain_values),
      supportEdges: Number(ld.support_edges),
      ruleGroundings: Number(ld.rule_groundings),
      joinSteps: Number(ld.join_steps),
      certBytes: Number(ld.cert_bytes),
    },
  });
}

// ------------------------------------ the test -----------------------------------

const doc = loadVectors();
const program = programFromJson(doc.program);
const leaves = new AggLeaves((doc.extensional as string[]) ?? [], (doc.edb as Record<string, any[]>) ?? {});
const recomputed: Hash = programDigest(program.iter().map(([, clause]) => clause));
const ctx = CertContext.of(recomputed, PROFILE_PIN, CTX_PIN, THEORY_PIN);
const profile: CheckProfile<void> = { theory: new NoTheory(), leaves, admit: new AlwaysAdmit<void>(), limits: defaultLimits() };

// Fail loud if the case array is empty — an empty `for` registers zero tests and the
// suite would pass green, silently dropping the aggregation family from the TS contract.
assert(doc.cases.length > 0, "no aggregation cases loaded");

// #2569 control: at least one case must reach the memo's verification, or the miss-then-hit
// assertion below would hold of a memo that never filled.
let memoizedWorlds = 0;

const domain = r3Domain("aggregation.json", doc.cases.map((c: { name: string }) => c.name));
const raised = r3Raised();

/**
 * A case's `limits`: every key a checker budget by the name `CHECK_BUDGETS` gives it, read by one
 * reader (#3376's class); an absent key keeps its default, and an unknown one fails.
 */
function caseLimits(name: string, raw: Record<string, unknown> | undefined): CheckLimits {
  let limits: CheckLimits = defaultLimits();
  for (const [key, value] of Object.entries(raw ?? {})) {
    const budget = CHECK_BUDGETS.find(([wire]) => wire === key);
    assert.ok(budget !== undefined, `case ${name}: unknown budget ${key}`);
    limits = { ...limits, [budget[1]]: Number(value) };
  }
  return limits;
}

for (const c of doc.cases) {
  test(`aggregation vector: ${c.name}`, () => {
    const claim = groundFromJson(c.claim);
    const nodes: Node[] = (c.derivation.nodes as any[]).map(nodeFromJson);
    // #2258 L3.3b: `certs` names the closed world as an ORDERED list (index = position).
    const closedWorld: ClosedModelCert[] = Array.isArray(c.certs)
      ? (c.certs as string[]).map((key) => certFromJson(doc.certs[key], ctx))
      : typeof c.cert === "string"
        ? [certFromJson(doc.certs[c.cert], ctx)]
        : [];
    // #2605 (seat:caa's condition 3): the length reading equals the encoding it measures.
    closedWorld.forEach((cert, i) => assertLengthReading2605(`${c.name} certificate ${i}`, cert));
    const deriv = new Derivation(nodes, Number(c.derivation.root), closedWorld);

    // An optional per-case `limits` override (issue #253): a case pins a budget; absent keys keep
    // their defaults.
    const caseProfile: CheckProfile<void> = { ...profile, limits: caseLimits(c.name, c.limits) };

    const got = checkWithCertContext(program, claim, deriv, undefined, caseProfile, ctx);
    const gotOutcome = Outcome.isAccept(got) ? "accept" : { reject: (got as { code: string }).code };
    assert.deepEqual(gotOutcome, c.outcome, `case ${c.name}: detail=${(got as any).detail ?? ""}`);

    // R3 (#2733, the checker's arm): an accepted case stays accepted under each raised budget,
    // alone and together, to the declared table's value.
    if (domain.has(c.name)) {
      for (const rb of eachBudgetRaised(caseProfile.limits, raised)) {
        const again = checkWithCertContext(program, claim, deriv, undefined, { ...caseProfile, limits: rb.limits }, ctx);
        assert.deepEqual(again, got, `case ${c.name}: raising ${rb.name} changed the verdict`);
      }
    }

    // #2569: the memoized check gives the same verdict on its miss and on its hit, and the hit
    // verifies nothing.
    const memo = new WorldMemo(program, caseProfile, undefined, ctx);
    for (const pass of [0, 1]) {
      assert.deepEqual(checkWithWorldMemo(memo, claim, deriv), got, `case ${c.name}: memo pass ${pass}`);
    }
    if (memo.certificatesVerified === closedWorld.length && closedWorld.length > 0) {
      memoizedWorlds += 1;
    } else {
      assert.equal(memo.certificatesVerified, 0, `case ${c.name}: memo verified ${memo.certificatesVerified}, want 0 or ${closedWorld.length}`);
    }
  });
}

test("#2569 control: some aggregation case reaches the memo's verification", () => {
  assert.ok(memoizedWorlds > 0, "no case filled the memo: the miss-then-hit check is vacuous");
});
