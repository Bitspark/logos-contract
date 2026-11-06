/*
 * Negation-family conformance vectors (ADR 0007 certifiable stratified negation). This
 * replays vectors/negation.json — the SAME hand-authored oracle the rs/go cores replay
 * through the differential CLI harness — asserting every case's `outcome` against the
 * TS `check` / `checkWithCertContext` over the closed-model cert machinery.
 *
 * The negation_v1 profile (mirrored across cores): the `lt` theory (lt(a,b) Holds iff
 * a<b bytewise), EDB leaves = the top-level `extensional` set with `edbSnapshot`
 * recomputed over the top-level `edb` rows, AlwaysAdmit, unit context. The bound
 * context is DERIVED from the live program (recomputed programDigest) + fixed non-zero
 * pins; each cert auto-binds to it unless it sets an explicit pin. A `plain_check:true`
 * case calls the plain check() (unbound zero context); a case may override pins via
 * `cert_context`.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";
import {
  AlwaysAdmit,
  BodyLit,
  CertContext,
  check,
  checkClosedModelChain,
  checkWithCertContext,
  checkWithWorldMemo,
  Clause,
  ClauseId,
  ClosedModelCert,
  type CountFilterEntry,
  CountLit,
  CountPremise,
  Derivation,
  edbTableHash,
  Evidence,
  FiniteDomain,
  Goal,
  type GroundFilterEntry,
  GroundLiteral,
  type Hash,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  NegPremise,
  type Node,
  NodeMeta,
  Outcome,
  PredicateSet,
  programDigest,
  PredicateRef,
  type Premise,
  ProjectSpec,
  RelationTable,
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
  type CertSizeDecl,
  type CheckLimits,
  type CheckProfile,
  defaultLimits,
  BuiltinNode,
  LeafNode,
  RuleNode,
  WorldMemo,
} from "../src/index.js";
import { assertLengthReading2605 } from "./support/cert_len_2605.js";

// ------------------------------- locate the oracle -------------------------------

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "negation.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/negation.json above ${dir}`);
    dir = parent;
  }
}

function loadVectors(): any {
  const file = path.join(repoRoot(), "vectors", "negation.json");
  return JSON.parse(fs.readFileSync(file, "utf8"));
}

// ------------------------------- the negation_v1 profile -------------------------

function bytesLess(a: Uint8Array, b: Uint8Array): boolean {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const x = a[i]!;
    const y = b[i]!;
    if (x !== y) return x < y;
  }
  return a.length < b.length;
}

// test-double: consumer(a less-than theory over atoms)
class LtTheory implements Theory {
  owns(pred: Symbol): boolean {
    return pred.equals(Symbol.of("lt"));
  }
  decide(atom: GroundLiteral): TheoryOutcome {
    const args = atom.args;
    if (args.length !== 2) return TheoryOutcome.Fails("lt_arity");
    const a = args[0]!;
    const b = args[1]!;
    if (a.kind === "atom" && b.kind === "atom" && bytesLess(a.bytes(), b.bytes())) {
      return TheoryOutcome.Holds;
    }
    return TheoryOutcome.Fails("not_less_than");
  }
}

const PROFILE_PIN: Hash = new Uint8Array(32).fill(0x11);
const CTX_PIN: Hash = new Uint8Array(32).fill(0x22);
const THEORY_PIN: Hash = new Uint8Array(32).fill(0x33);

// test-double: consumer(the negation vector EDB with snapshots)
class EdbLeaves implements LeafVerifier<void> {
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
    return LeafOutcome.Admit;
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    return this.#snapshots.get(new TextDecoder().decode(pred.bytes()));
  }
}

function negationProfile(leaves: LeafVerifier<void>, limits: CheckLimits): CheckProfile<void> {
  return { theory: new LtTheory(), leaves, admit: new AlwaysAdmit<void>(), limits };
}

// -------------------------------- authoring notation -----------------------------

function hexToBytes(hex: string): Uint8Array {
  if (hex.length % 2 !== 0) throw new Error(`odd-length hex: ${hex}`);
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i += 1) out[i] = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  return out;
}

function hexToHash(hex: string): Hash {
  const bytes = hexToBytes(hex);
  assert.equal(bytes.length, 32, "hash must be 32 bytes");
  return bytes;
}

function termFromJson(j: any): Term {
  if (typeof j.atom === "string") return Term.atom(hexToBytes(j.atom));
  if (typeof j.atom_str === "string") return Term.atom(new TextEncoder().encode(j.atom_str));
  if (Array.isArray(j.tuple)) return Term.tuple(j.tuple.map(termFromJson));
  if (typeof j.var === "string") return Term.var(j.var);
  throw new Error(`term must be atom/atom_str/tuple/var: ${JSON.stringify(j)}`);
}

function goalFromJson(j: any): Goal {
  return new Goal(Symbol.of(String(j.pred)), (j.args as any[]).map(termFromJson));
}

function bodyLitFromJson(j: any): BodyLit {
  if (j !== null && typeof j === "object" && j.neg !== undefined) return BodyLit.neg(goalFromJson(j.neg));
  // ADR 0023 count body literal — the aggregation vectors' `count_lit` form, admitted here for
  // ADR 0030 G2's count-over-partial case (the first count premise in negation.json).
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

/** `{name, arity}` — the counted predicate of a count premise / literal (ADR 0023). */
function predRefFromJson(j: any): PredicateRef {
  return new PredicateRef(Symbol.of(String(j.name)), Number(j.arity));
}

/** `"rows"` or `{distinct|sum|min|max: <attr>}` (ADR 0023, #587). */
function projectFromJson(j: any): ProjectSpec {
  if (j === "rows") return ProjectSpec.rows();
  if (typeof j.distinct === "number") return ProjectSpec.distinct(j.distinct);
  if (typeof j.sum === "number") return ProjectSpec.sum(j.sum);
  if (typeof j.min === "number") return ProjectSpec.min(j.min);
  if (typeof j.max === "number") return ProjectSpec.max(j.max);
  throw new Error(`project must be 'rows' or {distinct|sum|min|max:<attr>}: ${JSON.stringify(j)}`);
}

function groundFromJson(j: any): GroundLiteral {
  const g = goalFromJson(j).asGround();
  if (g === undefined) throw new Error("ground literal must be ground in the vector");
  return g;
}

function groundTermValue(j: any): Value {
  const v = Term.eraseGround(termFromJson(j));
  if (v === undefined) throw new Error("value must be ground");
  return v;
}

function substFromJson(j: any): Subst {
  const subst: Subst = new Map();
  for (const [varName, term] of Object.entries(j)) subst.set(varName, termFromJson(term));
  return subst;
}

function premiseFromJson(j: any): Premise {
  if (j !== null && typeof j === "object" && j.neg !== undefined) {
    return new NegPremise(groundFromJson(j.neg.atom), Number(j.neg.cert), j.neg.nonmember ?? "direct_lookup");
  }
  // ADR 0023 count premise (`{count: {pred, filter, project, k, cert}}`), admitted here for
  // ADR 0030 G2's count-over-partial case.
  if (j !== null && typeof j === "object" && j.count !== undefined) {
    const c = j.count;
    const filter: GroundFilterEntry[] = ((c.filter as any[]) ?? []).map((e) => ({ pos: Number(e.pos), value: groundTermValue(e.value) }));
    return new CountPremise(predRefFromJson(c.pred), filter, projectFromJson(c.project), encodeInt(BigInt(c.k)), Number(c.cert));
  }
  return Number(j);
}

function nodeFromJson(j: any): Node {
  const conclusion = groundFromJson(j.conclusion);
  switch (j.kind) {
    case "rule":
      return new RuleNode(
        conclusion,
        ClauseId.of(String(j.clause)),
        substFromJson(j.subst),
        (j.premises as any[]).map(premiseFromJson),
        NodeMeta.none(),
      );
    case "builtin":
      return new BuiltinNode(conclusion);
    case "leaf":
      return new LeafNode(conclusion, Evidence.none());
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

function supportRefFromJson(j: any): SupportRef {
  if (j.same_stratum !== undefined) {
    return SupportRefOps.sameStratum(groundFromJson(j.same_stratum.fact), Number(j.same_stratum.rank));
  }
  if (j.lower_stratum !== undefined) {
    return SupportRefOps.lowerStratum(Number(j.lower_stratum.cert), groundFromJson(j.lower_stratum.atom));
  }
  if (j.builtin !== undefined) return SupportRefOps.builtin(groundFromJson(j.builtin.atom));
  if (j.neg_lower !== undefined) {
    return SupportRefOps.negLower(Number(j.neg_lower.cert), groundFromJson(j.neg_lower.atom));
  }
  throw new Error(`bad support ref: ${JSON.stringify(j)}`);
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

function certSizeDeclFromJson(j: any): CertSizeDecl {
  return {
    certFacts: Number(j.cert_facts),
    domainValues: Number(j.domain_values),
    supportEdges: Number(j.support_edges),
    ruleGroundings: Number(j.rule_groundings),
    joinSteps: Number(j.join_steps),
    certBytes: Number(j.cert_bytes),
  };
}

// Verbatim constructors, NOT `.of`: the loader must carry the vector's collection
// order exactly as authored, or a non-canonical case (issue #839) is silently
// repaired before it can reach the gate it exists to pin. `.of` is unreachable for
// this (it canonicalizes by design), so the loader builds through the prototype —
// the same shape a plain-JS caller could hand the checker.
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

function certFromJson(j: any, programHash: Hash): ClosedModelCert {
  const scope = verbatimStratumPrefix(Number(j.scope.level), (j.scope.predicates as any[]).map((p) => Symbol.of(String(p))));
  const domains: FiniteDomain[] = (j.domains as any[]).map((d) =>
    verbatimFiniteDomain(Symbol.of(String(d.type_tag)), (d.values as any[]).map(groundTermValue)),
  );
  const extensions: RelationTable[] = (j.extensions as any[]).map((t) =>
    verbatimRelationTable(Symbol.of(String(t.pred)), Number(t.arity), (t.rows as any[]).map(groundFromJson)),
  );
  const supports: SupportEdge[] = (j.supports as any[]).map(supportEdgeFromJson);
  return new ClosedModelCert({
    scope,
    programHash: j.program_hash !== undefined ? hexToHash(String(j.program_hash)) : programHash,
    profileHash: j.profile_hash !== undefined ? hexToHash(String(j.profile_hash)) : PROFILE_PIN,
    ctxHash: j.ctx_hash !== undefined ? hexToHash(String(j.ctx_hash)) : CTX_PIN,
    theoryConfigHash: j.theory_config_hash !== undefined ? hexToHash(String(j.theory_config_hash)) : THEORY_PIN,
    edbSnapshotHashes: [],
    domains,
    extensions,
    supports,
    limitsDecl: certSizeDeclFromJson(j.limits_decl),
    // ADR 0029 D10: the slice seal, read from the vector when present. TypeScript absorbs an
    // absent optional as silently as Go's nil, so this line is what makes a slice-sealed case
    // exercise the branch at all.
    ...(j.decomposition_witness !== undefined
      ? { decompositionWitness: hexToHash(String(j.decomposition_witness)) }
      : {}),
    // ADR 0030 D1: the partial sub-scope, read VERBATIM (order preserved) so a non-canonical
    // vector is refused by the checker rather than repaired by the walker.
    ...(j.partial_scope !== undefined
      ? {
          partialScope: verbatimStratumPrefix(
            Number(j.partial_scope.level),
            (j.partial_scope.predicates as any[]).map((p) => Symbol.of(String(p))),
          ),
        }
      : {}),
  });
}

function limitsFromJson(j: any): CheckLimits {
  let limits = defaultLimits();
  if (!j) return limits;
  const num = (k: string) => (j[k] !== undefined ? Number(j[k]) : undefined);
  const set = <K extends keyof CheckLimits>(k: K, v: number | undefined) => {
    if (v !== undefined) limits = { ...limits, [k]: v };
  };
  set("maxNodes", num("max_nodes"));
  set("maxDepth", num("max_depth"));
  set("maxTermDepth", num("max_term_depth"));
  set("maxCertBytes", num("max_cert_bytes"));
  set("maxCertFacts", num("max_cert_facts"));
  set("maxDomainValues", num("max_domain_values"));
  set("maxSupportEdges", num("max_support_edges"));
  set("maxRuleGroundings", num("max_rule_groundings"));
  set("maxJoinSteps", num("max_join_steps"));
  return limits;
}

// ------------------------------------ the test -----------------------------------

const doc = loadVectors();
const program = programFromJson(doc.program);
const leaves = new EdbLeaves((doc.extensional as string[]) ?? [], (doc.edb as Record<string, any[]>) ?? {});
const recomputed: Hash = programDigest(program.iter().map(([, clause]) => clause));

// Fail loud if the case array is empty / mis-keyed: an empty `for` registers zero
// tests and the suite would pass green, silently dropping the negation family from the
// TS parity contract (the last unguarded JSON-replay; #487). The rs/go replays already
// guard their loops the same way.
assert(doc.cases.length > 0, "no negation cases loaded");

for (const c of doc.cases) {
  test(`negation vector: ${c.name}`, () => {
    const claim = groundFromJson(c.claim);
    const nodes: Node[] = (c.derivation.nodes as any[]).map(nodeFromJson);
    const closedWorld: ClosedModelCert[] = ((c.derivation.closed_world as any[]) ?? []).map((cj: any) =>
      certFromJson(cj, recomputed),
    );
    // #2605 (seat:caa's condition 3): the length reading equals the encoding it measures.
    closedWorld.forEach((cert, i) => assertLengthReading2605(`${c.name} certificate ${i}`, cert));
    const deriv = new Derivation(nodes, Number(c.derivation.root), closedWorld);
    const profile = negationProfile(leaves, limitsFromJson(c.limits));

    let got: Outcome;
    if (c.plain_check === true) {
      got = check(program, claim, deriv, undefined, profile);
    } else {
      const cc = c.cert_context ?? {};
      const base = CertContext.of(
        cc.program_hash !== undefined ? hexToHash(String(cc.program_hash)) : recomputed,
        cc.profile_hash !== undefined ? hexToHash(String(cc.profile_hash)) : PROFILE_PIN,
        cc.ctx_hash !== undefined ? hexToHash(String(cc.ctx_hash)) : CTX_PIN,
        cc.theory_config_hash !== undefined ? hexToHash(String(cc.theory_config_hash)) : THEORY_PIN,
      );
      // ADR 0029 D10: a case that declares its decomposition binds the context to it.
      const context =
        cc.decomposition_witness !== undefined
          ? CertContext.withDecomposition(base, hexToHash(String(cc.decomposition_witness)))
          : base;
      got = checkWithCertContext(program, claim, deriv, undefined, profile, context);

      // #2569: the memoized check gives the same verdict on its miss and on its hit, and the hit
      // verifies nothing: the world is verified in full once, or never (a precheck refused).
      const memo = new WorldMemo(program, profile, undefined, context);
      for (const pass of [0, 1]) {
        assert.deepEqual(checkWithWorldMemo(memo, claim, deriv), got, `case ${c.name}: memo pass ${pass}`);
      }
      assert.ok(
        memo.certificatesVerified === 0 || memo.certificatesVerified === closedWorld.length,
        `case ${c.name}: memo verified ${memo.certificatesVerified}, want 0 or ${closedWorld.length}`,
      );
    }

    const gotOutcome = Outcome.isAccept(got) ? "accept" : { reject: (got as { code: string }).code };
    assert.deepEqual(gotOutcome, c.outcome, `case ${c.name}: detail=${(got as any).detail ?? ""}`);
  });
}

// ------------------- #2313: the same vectors through checkClosedModelChain -------------------
//
// Design 0008 §1.4.3: a certificate chain that no derivation cites is verified by the verification
// a Neg-cited cert already passes. Two claims per case, both counted so neither passes vacuously:
// a case the oracle ACCEPTS verifies its closed_world as a chain, and a case the oracle rejects
// with a code only verifyCert produces rejects the chain with the SAME code. Mirrors the go replay
// (closed_model_chain_2313_test.go).

const CHAIN_CERT_INTERNAL_CODES = new Set([
  "cert_budget_exceeded",
  "cert_size_exceeded",
  "cert_decl_mismatch",
  "cert_context_mismatch",
  "cert_unsupported",
  "cert_not_closed",
  "cert_scope_incomplete",
  "cert_edb_mismatch",
  "cert_partial_scope_invalid",
]);

function chainContext(c: any): CertContext {
  const cc = c.cert_context ?? {};
  const base = CertContext.of(
    cc.program_hash !== undefined ? hexToHash(String(cc.program_hash)) : recomputed,
    cc.profile_hash !== undefined ? hexToHash(String(cc.profile_hash)) : PROFILE_PIN,
    cc.ctx_hash !== undefined ? hexToHash(String(cc.ctx_hash)) : CTX_PIN,
    cc.theory_config_hash !== undefined ? hexToHash(String(cc.theory_config_hash)) : THEORY_PIN,
  );
  return cc.decomposition_witness !== undefined
    ? CertContext.withDecomposition(base, hexToHash(String(cc.decomposition_witness)))
    : base;
}

function chainCerts(c: any): ClosedModelCert[] {
  return ((c.derivation.closed_world as any[]) ?? []).map((cj: any) => certFromJson(cj, recomputed));
}

test("#2313 chain: the negation vectors replay through checkClosedModelChain", () => {
  let accepted = 0;
  let certRejected = 0;
  for (const c of doc.cases) {
    if (c.plain_check === true) continue; // a plain check runs under the zero context by design
    const certs = chainCerts(c);
    if (certs.length === 0) continue; // an all-positive case cites no cert: no chain to verify
    const got = checkClosedModelChain(program, certs, undefined, negationProfile(leaves, limitsFromJson(c.limits)), chainContext(c));
    if (c.outcome === "accept") {
      accepted += 1;
      assert.ok(Outcome.isAccept(got), `case ${c.name}: its closed_world must verify as a chain; got ${JSON.stringify(got)}`);
    } else if (CHAIN_CERT_INTERNAL_CODES.has(c.outcome.reject)) {
      certRejected += 1;
      assert.equal((got as { code?: string }).code, c.outcome.reject, `case ${c.name}: ${JSON.stringify(got)}`);
    }
  }
  assert.ok(accepted > 0 && certRejected > 0, `the replay is vacuous: ${accepted} accepted, ${certRejected} cert-rejected`);
});

test("#2313 chain: an empty chain is refused by name, never accepted vacuously", () => {
  const got = checkClosedModelChain(program, [], undefined, negationProfile(leaves, limitsFromJson(undefined)), CertContext.of(recomputed, PROFILE_PIN, CTX_PIN, THEORY_PIN));
  assert.equal((got as { code?: string }).code, "cert_out_of_range");
  assert.match((got as { detail?: string }).detail ?? "", /empty certificate chain/);
});

// #2759 (seat:caa's design gate): check admits an open compound in a sealed scope inside the
// CONSTRUCTOR-ACYCLIC fragment and refuses one outside it, re-deriving the fragment from the bound
// program, and the refusal NAMES the cycle: the function-free gate it replaced rejected both with the
// same code, so the code alone cannot tell them apart. The Go twin is constructor_acyclic_2759_test.go.
function chain2759(name: string): unknown {
  const c = doc.cases.find((k: any) => k.name === name);
  assert.ok(c, `vectors/negation.json carries no case ${name}`);
  return checkClosedModelChain(program, chainCerts(c), undefined, negationProfile(leaves, limitsFromJson(c.limits)), chainContext(c));
}

test("#2759 chain: a constructor-acyclic sealed scope verifies", () => {
  const got = chain2759("round3_structural_subterm_closed_accept_2759");
  assert.ok(Outcome.isAccept(got as any), `r(box(box(X))) :- e(box(X)) constructs on no cycle; got ${JSON.stringify(got)}`);
});

test("#2759 chain: a constructor-cyclic sealed scope is refused by name", () => {
  const got = chain2759("constructor_cycle_stratum_rejects_2759") as { code?: string; detail?: string };
  assert.equal(got.code, "cert_scope_incomplete");
  assert.match(got.detail ?? "", /"nat" constructs an open compound/);
  assert.match(got.detail ?? "", /dependency cycle through "nat"/);
});

test("#2313 chain: an unbound context refuses the chain", () => {
  const c = doc.cases.find((k: any) => k.outcome === "accept" && k.plain_check !== true && chainCerts(k).length > 0);
  assert.ok(c, "no accepted case with a closed_world to test the unbound context against");
  const got = checkClosedModelChain(program, chainCerts(c), undefined, negationProfile(leaves, limitsFromJson(c.limits)), CertContext.zero());
  assert.equal((got as { code?: string }).code, "cert_context_unbound");
});

// ------------- #3424: where a certificate's scope level is inert, and where it is read -------------
//
// Research 0035 lane 8 (row B17). `level` is not read for a single certificate with a full scope.
// Since #1708 a partial scope must sit at its certificate's own level, and since #2344 stacked
// certificates are verified in level order and a certificate reads only a strictly lower seal.
// There, a wrong level changes the verdict. The fixtures are this file's own cases, replayed with
// only the certificates' scope levels changed. Mirrors contract/go/scope_level_consulted_3424_test.go
// and the rs cases (negation.rs, adr0030_partial_scope_guard.rs, stacked_scope_level_3424.rs).

function replayWithLevels(name: string, levels: number[]): string {
  const c = doc.cases.find((k: any) => k.name === name);
  assert.ok(c, `vectors/negation.json carries no case ${name}`);
  assert.ok(c.plain_check !== true && c.cert_context === undefined && c.limits === undefined, `${name} needs a setup this replay does not make`);
  const certs = (c.derivation.closed_world as any[]) ?? [];
  assert.equal(certs.length, levels.length, `${name} has ${certs.length} certificates`);
  const world = certs.map((cj: any, i: number) => certFromJson({ ...cj, scope: { ...cj.scope, level: levels[i] } }, recomputed));
  const deriv = new Derivation((c.derivation.nodes as any[]).map(nodeFromJson), Number(c.derivation.root), world);
  const context = CertContext.of(recomputed, PROFILE_PIN, CTX_PIN, THEORY_PIN);
  const got = checkWithCertContext(program, groundFromJson(c.claim), deriv, undefined, negationProfile(leaves, limitsFromJson(undefined)), context);
  return Outcome.isAccept(got) ? "accept" : `reject:${(got as { code: string }).code}`;
}

test("#3424: a single certificate with a full scope does not read its level", () => {
  for (const level of [1, 0, 7]) {
    assert.equal(replayWithLevels("accept_negation_of_absent_atom", [level]), "accept", `level ${level}`);
  }
});

test("#3424: a certificate's level is read once it carries a partial scope", () => {
  const name = "adr0030_lower_bound_table_not_closed_but_marked_partial";
  assert.equal(replayWithLevels(name, [1]), "accept", "control: the partial scope's own level");
  for (const level of [0, 7]) {
    assert.equal(replayWithLevels(name, [level]), "reject:cert_partial_scope_invalid", `level ${level} under a level-1 partial scope`);
  }
});

test("#3424: stacked certificates are verified in level order, and read only a strictly lower seal", () => {
  const upperFirst = "stacked_2258_the_order_of_the_world_does_not_matter_accepts"; // [upper, base]
  assert.equal(replayWithLevels("stacked_2258_the_edb_sealed_once_below_accepts", [1, 2]), "accept", "control: the base listed first");
  assert.equal(replayWithLevels(upperFirst, [2, 1]), "accept", "the upper certificate listed first is still verified after the base");
  // the base at the upper's level, or above it: in either order the upper has no strictly lower seal
  const baseFirst = "stacked_2258_the_edb_sealed_once_below_accepts"; // [base, upper]
  for (const [name, levels] of [[upperFirst, [1, 1]], [upperFirst, [2, 3]], [baseFirst, [1, 1]], [baseFirst, [3, 2]]] as const) {
    assert.equal(replayWithLevels(name, [...levels]), "reject:cert_scope_incomplete", `${name} at levels ${levels}`);
  }
});
