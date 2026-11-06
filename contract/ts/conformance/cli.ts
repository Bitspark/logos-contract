// Conformance CLI (ts) — a dev/CI artifact, NOT part of the published package
// (files=["dist/src"] excludes dist/conformance). Implements the `conformance v1`
// protocol (ADR 0006): `cli.js <family>` reads the family's vector JSON on stdin and
// writes one NDJSON line per case to stdout, in input order, baking in the demo_v1
// profile and ignoring any expected outcome/id in the input. The language-agnostic
// harness (conformance/harness.mjs) drives this and the rs/go CLIs as black boxes and
// asserts each line against the hand-authored oracle.
//
//   check   : in  {program, cases:[{name, claim, derivation, limits?}]}
//             out {"name":…,"outcome":"accept"|{"reject":"<code>"}}
//   account : in  {clauses:[{name, head, body}]}
//             out {"name":…,"id":"<hex>"}
//
// The theory-decision families (arithmetic, list, term, text, compound) share one shape:
//   <theory> : in  {identity, owns, decisions:[{name, pred, args}]}
//              out one {"name":…,"outcome":"holds"|{"fails":"<code>"}} line per decision,
//                   then {"name":"__identity__","outcome":"<config_digest_hex>"} pinning the
//                   theory's identity config digest (zero for the single theories, the
//                   ordered-membership digest for compound).

import { readFileSync } from "node:fs";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { encodeInt, encodeText, encodeList } from "@bitspark/ontos-data";
import {
  AlwaysAdmit,
  ArithmeticTheory,
  type CountFilterEntry,
  CountLit,
  CountPremise,
  type GroundFilterEntry,
  PredicateRef,
  ProjectSpec,
  BigDecimal,
  BodyLit,
  canonicalClauseId,
  CertContext,
  check,
  checkWithCertContext,
  Clause,
  ClauseId,
  ClosedModelCert,
  ComponentIdentity,
  CompoundTheory,
  decideGround,
  DecisionCompletion,
  Derivation,
  edbTableHash,
  Evidence,
  FiniteDomain,
  Goal,
  GroundLiteral,
  type Hash,
  LeafOutcome,
  type LeafVerifier,
  ListTheory,
  MapProgram,
  type NegPremise,
  NegPremise as NegPremiseClass,
  type Node,
  NodeMeta,
  Outcome,
  PredicateSet,
  programDigest,
  RelationTable,
  type Premise,
  StratumPrefix,
  type Subst,
  type SupportEdge,
  SupportEdge as SupportEdgeClass,
  type SupportRef,
  SupportRef as SupportRefOps,
  Symbol,
  Term,
  TermTheory,
  TextTheory,
  type Theory,
  TheoryOutcome,
  type CertSizeDecl,
  type CheckLimits,
  type CheckProfile,
  defaultLimits,
  BuiltinNode,
  LeafNode,
  RuleNode,
} from "../src/index.js";

// =================== demo_v1 profile (baked in) ===================
// Mirrors contract/ts/test/vectors.test.ts.

function bytesLess(a: Uint8Array, b: Uint8Array): boolean {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const x = a[i]!;
    const y = b[i]!;
    if (x !== y) return x < y;
  }
  return a.length < b.length;
}

class LtTheory implements Theory {
  owns(pred: Symbol): boolean {
    return pred.equals(Symbol.of("lt"));
  }
  /** #3142: every lt decision completes (a byte comparison). */
  completion(_pred: Symbol): DecisionCompletion {
    return DecisionCompletion.StopsAreTyped;
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

class EdgeLeaves implements LeafVerifier<void> {
  readonly #extensional = PredicateSet.from(["edge"]);
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcome.Admit;
  }
}

/**
 * A case's `limits` object, read ONE way by every family (#3376): each of the nine checker budgets
 * is optional, and an absent key keeps its default. Two readers of this one object disagreed until
 * #3376 (the check family read an absent max_nodes or max_depth as NaN, which disables the cap),
 * which is research 0022's class, one decision computed twice.
 */
function limitsFromJson(raw: any): CheckLimits {
  const base = defaultLimits();
  if (!raw) return base;
  const pick = (key: string, current: number): number =>
    raw[key] !== undefined ? Number(raw[key]) : current;
  return {
    ...base,
    maxNodes: pick("max_nodes", base.maxNodes),
    maxDepth: pick("max_depth", base.maxDepth),
    maxTermDepth: pick("max_term_depth", base.maxTermDepth),
    maxCertBytes: pick("max_cert_bytes", base.maxCertBytes),
    maxCertFacts: pick("max_cert_facts", base.maxCertFacts),
    maxDomainValues: pick("max_domain_values", base.maxDomainValues),
    maxSupportEdges: pick("max_support_edges", base.maxSupportEdges),
    maxRuleGroundings: pick("max_rule_groundings", base.maxRuleGroundings),
    maxJoinSteps: pick("max_join_steps", base.maxJoinSteps),
  };
}

function demoProfile(limits: CheckLimits): CheckProfile<void> {
  return {
    theory: new LtTheory(),
    leaves: new EdgeLeaves(),
    admit: new AlwaysAdmit<void>(),
    limits,
  };
}

// ===================== authoring notation -> contract types ====================

function hexToBytes(hex: string): Uint8Array {
  if (hex.length % 2 !== 0) throw new Error(`odd-length hex: ${hex}`);
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i += 1) {
    out[i] = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

function termFromJson(j: any): Term {
  if (typeof j.atom === "string") return Term.atom(hexToBytes(j.atom));
  if (typeof j.atom_str === "string") return Term.atom(new TextEncoder().encode(j.atom_str));
  if (Array.isArray(j.tuple)) return Term.tuple(j.tuple.map(termFromJson));
  if (typeof j.var === "string") return Term.var(j.var);
  if (j.nest !== undefined) {
    // #2731: {nest: {functor, times, leaf}} is functor(functor(...leaf...)), `times` levels around
    // `leaf`, expanded by a loop, so a term past any JSON parser's nesting limit is authored flat.
    let t = termFromJson(j.nest.leaf);
    for (let i = 0; i < Number(j.nest.times); i++) {
      t = Term.tuple([Term.atom(new TextEncoder().encode(j.nest.functor)), t]);
    }
    return t;
  }
  throw new Error(`term must be atom/atom_str/tuple/var/nest: ${JSON.stringify(j)}`);
}

function goalFromJson(j: any): Goal {
  const pred = Symbol.of(String(j.pred));
  const args: Term[] = (j.args as any[]).map(termFromJson);
  return new Goal(pred, args);
}

// A body-literal authoring form: a bare goal {pred, args} is positive (so existing
// all-positive check.json/account.json bodies decode byte-identically), and
// {neg: <goal>} is a negated body literal (ADR 0007). Mirrors Rust's body_lit_from_json.
function bodyLitFromJson(j: any): BodyLit {
  if (j !== null && typeof j === "object" && j.neg !== undefined) {
    return BodyLit.neg(goalFromJson(j.neg));
  }
  // ADR 0023 count body literal (`count_lit`), admitted in the negation family for ADR 0030 G2.
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

function groundFromJson(j: any): GroundLiteral {
  const g = goalFromJson(j).asGround();
  if (g === undefined) throw new Error("conclusion/claim must be ground in the vector");
  return g;
}

function substFromJson(j: any): Subst {
  const subst: Subst = new Map();
  for (const [varName, term] of Object.entries(j)) {
    subst.set(varName, termFromJson(term));
  }
  return subst;
}

function nodeFromJson(j: any): Node {
  const conclusion = groundFromJson(j.conclusion);
  switch (j.kind) {
    case "rule":
      return new RuleNode(
        conclusion,
        ClauseId.of(String(j.clause)),
        substFromJson(j.subst),
        (j.premises as any[]).map((n) => Number(n)),
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
    const head = goalFromJson(clause.head);
    const body: BodyLit[] = (clause.body as any[]).map(bodyLitFromJson);
    program.insert(ClauseId.of(id), new Clause(head, body));
  }
  return program;
}

// ================================ families ===================================

function runCheck(doc: any): void {
  const program = programFromJson(doc.program);
  for (const c of doc.cases) {
    const claim = groundFromJson(c.claim);
    const nodes: Node[] = (c.derivation.nodes as any[]).map(nodeFromJson);
    const deriv = new Derivation(nodes, Number(c.derivation.root));
    const limits = limitsFromJson(c.limits);
    const got = check(program, claim, deriv, undefined, demoProfile(limits));
    const outcome = Outcome.isAccept(got) ? "accept" : { reject: (got as { code: string }).code };
    process.stdout.write(`${JSON.stringify({ name: c.name, outcome })}\n`);
  }
}

function runAccount(doc: any): void {
  for (const c of doc.clauses) {
    const head = goalFromJson(c.head);
    // Body literals may be bare goals (Pos) or {neg: <goal>} (Neg); existing
    // all-positive account vectors decode byte-identically.
    const body: BodyLit[] = (c.body as any[]).map(bodyLitFromJson);
    const id = canonicalClauseId(new Clause(head, body)).asStr();
    process.stdout.write(`${JSON.stringify({ name: c.name, id })}\n`);
  }
}

// ============================= negation family (ADR 0007) ==========================
//
// The negation_v1 profile: the `lt` theory (above), EDB leaves = the top-level
// `extensional` set with `edbSnapshot` recomputed over the top-level `edb` rows, the
// AlwaysAdmit rule policy, and a unit context. The bound context is DERIVED from the
// live program: programHash = recomputed programDigest; the other three pins are FIXED
// non-zero sentinels (a cert is auto-bound to them unless it sets an explicit pin). A
// case with `plain_check:true` calls the plain check() (unbound zero context); a case
// may override pins via `cert_context`. See vectors/negation.json's `note`.

/** Fixed non-zero sentinel pins for the negation_v1 bound context (any non-zero works). */
const PROFILE_PIN: Hash = new Uint8Array(32).fill(0x11);
const CTX_PIN: Hash = new Uint8Array(32).fill(0x22);
const THEORY_PIN: Hash = new Uint8Array(32).fill(0x33);

function hexToHash(hex: string): Hash {
  const bytes = hexToBytes(hex);
  if (bytes.length !== 32) throw new Error(`hash must be 32 bytes (64 hex chars), got ${bytes.length}`);
  return bytes;
}

/** A LeafVerifier over the negation_v1 EDB-of-record: extensional set + per-pred snapshot. */
class EdbLeaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #snapshots = new Map<string, Hash>();
  constructor(extensional: string[], edb: Record<string, any[]>) {
    this.#extensional = PredicateSet.from(extensional);
    for (const [pred, rows] of Object.entries(edb)) {
      const ground = rows.map((r) => groundFromJson(r));
      const sym = Symbol.of(pred);
      this.#snapshots.set(predKey(sym), edbTableHash(sym, ground));
    }
  }
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcome.Admit;
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    return this.#snapshots.get(predKey(pred));
  }
}

/** A predicate's identity is its bytes (#2763): the snapshot map is keyed by their hex, never by
 * decoded text, which merges names that differ only in an ill-formed byte. */
function predKey(pred: Symbol): string {
  return Array.from(pred.bytes(), (b) => b.toString(16).padStart(2, "0")).join("");
}

// The negation_v1 profile's theory: lt for the builtin support refs, and since #3126 the standard
// arithmetic theory beside it, so vectors/theory_not_decided.json can state a literal the theory
// does not decide. No negation-family vector names an arithmetic predicate as a relation, so the
// verdicts of negation.json and exact_claims.json do not move.
function negationProfile(leaves: LeafVerifier<void>, limits: CheckLimits): CheckProfile<void> {
  return {
    theory: new CompoundTheory([new LtTheory(), new ArithmeticTheory()]),
    leaves,
    admit: new AlwaysAdmit<void>(),
    limits,
  };
}

/** A Rule premise: a bare int (Pos node index) or {neg:{atom,cert,nonmember}} (Neg). */
function premiseFromJson(j: any): Premise {
  if (j !== null && typeof j === "object" && j.neg !== undefined) {
    const neg = j.neg;
    const atom = groundFromJson(neg.atom);
    const cert = Number(neg.cert);
    return new NegPremiseClass(atom, cert, neg.nonmember ?? "direct_lookup");
  }
  // ADR 0023 count premise (`{count: {pred, filter, project, k, cert}}`) — the aggregation
  // vectors' authoring form, admitted in the negation family for ADR 0030 G2's
  // count-over-partial case. Mirrors Rust's premise_from_json.
  if (j !== null && typeof j === "object" && j.count !== undefined) {
    const c = j.count;
    const filter: GroundFilterEntry[] = ((c.filter as any[]) ?? []).map((e) => {
      const v = Term.eraseGround(termFromJson(e.value));
      if (v === undefined) throw new Error(`count premise filter value must be ground: ${JSON.stringify(e)}`);
      return { pos: Number(e.pos), value: v };
    });
    return new CountPremise(predRefFromJson(c.pred), filter, projectFromJson(c.project), encodeInt(BigInt(c.k)), Number(c.cert));
  }
  return Number(j);
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

function negNodeFromJson(j: any): Node {
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

function supportRefFromJson(j: any): SupportRef {
  if (j.same_stratum !== undefined) {
    return SupportRefOps.sameStratum(groundFromJson(j.same_stratum.fact), Number(j.same_stratum.rank));
  }
  if (j.lower_stratum !== undefined) {
    return SupportRefOps.lowerStratum(Number(j.lower_stratum.cert), groundFromJson(j.lower_stratum.atom));
  }
  if (j.builtin !== undefined) {
    return SupportRefOps.builtin(groundFromJson(j.builtin.atom));
  }
  if (j.neg_lower !== undefined) {
    return SupportRefOps.negLower(Number(j.neg_lower.cert), groundFromJson(j.neg_lower.atom));
  }
  if (j.count_lower !== undefined) {
    return SupportRefOps.countLower(Number(j.count_lower.cert));
  }
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

/**
 * Build one `ClosedModelCert` from its JSON. The four pins default to the bound context
 * (programHash = recomputed digest; the fixed non-zero sentinels) — i.e. the cert is
 * auto-bound — UNLESS the JSON sets an explicit program/profile/ctx/theory hash (the
 * mismatch cases), which overrides that pin.
 */
// Verbatim constructors, NOT `.of`: the harness must carry the vector's collection
// order exactly as authored, or a non-canonical case (issue #839) is silently
// repaired before it can reach the gate it exists to pin. `.of` canonicalizes by
// design, so the loader builds through the prototype — the same shape a plain-JS
// caller could hand the checker.
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
  const scope = verbatimStratumPrefix(
    Number(j.scope.level),
    (j.scope.predicates as any[]).map((p) => Symbol.of(String(p))),
  );
  const domains: FiniteDomain[] = (j.domains as any[]).map((d) =>
    verbatimFiniteDomain(
      Symbol.of(String(d.type_tag)),
      (d.values as any[]).map((v) => {
        const g = Term.eraseGround(termFromJson(v));
        if (g === undefined) throw new Error("domain value must be ground");
        return g;
      }),
    ),
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

function runNegation(doc: any): void {
  const program = programFromJson(doc.program);
  const leaves = new EdbLeaves((doc.extensional as string[]) ?? [], (doc.edb as Record<string, any[]>) ?? {});
  // The recomputed live program digest — the programHash a bound context pins.
  const clauses = program.iter().map(([, clause]) => clause);
  const recomputed: Hash = programDigest(clauses);

  for (const c of doc.cases) {
    const claim = groundFromJson(c.claim);
    const nodes: Node[] = (c.derivation.nodes as any[]).map(negNodeFromJson);
    const closedWorld: ClosedModelCert[] = ((c.derivation.closed_world as any[]) ?? []).map((cj) =>
      certFromJson(cj, recomputed),
    );
    const deriv = new Derivation(nodes, Number(c.derivation.root), closedWorld);

    const limits = limitsFromJson(c.limits);
    const profile = negationProfile(leaves, limits);

    let got: Outcome;
    if (c.plain_check === true) {
      // The plain check() supplies a zero (unbound) context.
      got = check(program, claim, deriv, undefined, profile);
    } else {
      // The bound context, derived from the live program + fixed pins, with optional
      // per-case overrides.
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
    }
    const outcome = Outcome.isAccept(got) ? "accept" : { reject: (got as { code: string }).code };
    process.stdout.write(`${JSON.stringify({ name: c.name, outcome })}\n`);
  }
}

// ===================== theory-decision families (ADR 0006 / #95, #154) ==============
// arithmetic / list / term / text / compound — each drives a standard checkable Theory's
// decide over the shared vectors/<family>.json `decisions` array. buildTheoryArg mirrors
// the unit replays' buildArg (contract/ts/test/arithmetic_vectors.test.ts) byte-for-byte,
// so the black-box CLI agrees with the in-process oracle.

const utf8Encoder = new TextEncoder();

// buildTheoryArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/{arithmetic,list,term,text,compound}.json (and the
// Go/Rust builders) EXACTLY:
//
//   {"int": N}                 -> the ontos-data int embedding of N
//   {"bigint": "<digits>"}     -> the int embedding of a value beyond JSON int range
//   {"decimal": "<d.dddd>"}    -> the ontos-data decimal embedding of that decimal literal (#331)
//   {"text": "<s>"}            -> the ontos-data utf8-text embedding
//   {"atom": "<utf8>"}         -> a bare Atom of those UTF-8 bytes
//   {"op": "<op>", "args": []} -> an operator compound Tuple(Atom(op), arg..)
//   {"list": [..]}             -> the ontos-data list embedding of the encoded children
//   {"tuple": [..]}            -> a raw Tuple of the encoded children
function buildTheoryArg(raw: any): Value {
  if (raw === null || typeof raw !== "object") {
    throw new Error(`arg is not an object: ${JSON.stringify(raw)}`);
  }
  if ("int" in raw) return encodeInt(BigInt(raw.int as number | bigint));
  if ("bigint" in raw) return encodeInt(BigInt(raw.bigint as string));
  if ("decimal" in raw) {
    const d = BigDecimal.fromString(raw.decimal as string);
    if (d === undefined) throw new Error(`decimal ${JSON.stringify(raw.decimal)} is not a decimal literal`);
    return d.toTerm();
  }
  if ("text" in raw) return encodeText(raw.text as string);
  if ("atom" in raw) return valueAtom(utf8Encoder.encode(raw.atom as string));
  if ("op" in raw) {
    const args = (raw.args as any[]) ?? [];
    return valueTuple([valueAtom(utf8Encoder.encode(raw.op as string)), ...args.map(buildTheoryArg)]);
  }
  if ("list" in raw) return encodeList((raw.list as any[]).map(buildTheoryArg));
  if ("tuple" in raw) return valueTuple((raw.tuple as any[]).map(buildTheoryArg));
  throw new Error(`unrecognized arg shape: ${JSON.stringify(raw)}`);
}

// theoryByName builds the contract Theory the family names. compound composes [arithmetic,
// text] in that order (mirroring buildCompound in compound_vectors.test.ts).
function theoryByName(name: string): Theory {
  switch (name) {
    case "arithmetic":
      return new ArithmeticTheory();
    case "list":
      return new ListTheory();
    case "term":
      return new TermTheory();
    case "text":
      return new TextTheory();
    case "compound":
      return new CompoundTheory([new ArithmeticTheory(), new TextTheory()]);
    default:
      throw new Error(`unknown theory family ${JSON.stringify(name)}`);
  }
}

function hexOf(bytes: Uint8Array): string {
  return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

function runTheory(name: string, doc: any): void {
  const theory = theoryByName(name);
  for (const d of doc.decisions as any[]) {
    const args = (d.args as any[]).map(buildTheoryArg);
    // #3126: the ground verdict, which can say "not decided" ({"not_completed": <kind>}).
    const got = decideGround(theory, GroundLiteral.of(String(d.pred), args));
    let outcome: unknown;
    if (got.kind === "completed") {
      outcome = got.value.kind === "holds" ? "holds" : { fails: got.value.code };
    } else if (got.kind === "not_completed" && got.cause.kind !== "inconsistent_theory") {
      outcome = { not_completed: got.cause.kind };
    } else {
      // The decision vectors only carry owned predicates, so a routed atom is never disowned; if
      // it is, the vector or the owns set is wrong.
      throw new Error(`${name} ${JSON.stringify(d.name)}: theory does not own predicate ${JSON.stringify(d.pred)}`);
    }
    process.stdout.write(`${JSON.stringify({ name: d.name, outcome })}\n`);
  }
  // Pin the theory's identity config digest as a synthetic case so the harness asserts the
  // composed/ordered identity (the compound digest commits to membership AND order),
  // uniformly across every theory family. identity() is an optional SPI member (absent =
  // unidentified); every standard theory implements it.
  const id = theory.identity?.() ?? ComponentIdentity.unidentified();
  const digest = hexOf(id.configDigest);
  process.stdout.write(`${JSON.stringify({ name: "__identity__", outcome: digest })}\n`);
}

const family = process.argv[2];
const input = readFileSync(0, "utf8");
if (family === "check") {
  runCheck(JSON.parse(input));
} else if (family === "account") {
  runAccount(JSON.parse(input));
} else if (family === "negation") {
  runNegation(JSON.parse(input));
} else if (
  family === "arithmetic" ||
  family === "list" ||
  family === "term" ||
  family === "text" ||
  family === "compound"
) {
  // The arithmetic theory vector carries integers beyond Number.MAX_SAFE_INTEGER (e.g.
  // i64::MAX); recover each integer literal losslessly from its JSON source text as a
  // bigint (the Node 24 source-text reviver), exactly as the TS unit replay loads it.
  // encodeInt takes a bigint, so int args round-trip with full precision. Scoped to the
  // theory families so the existing three families parse byte-for-byte as before.
  const reviver = (_key: string, value: unknown, context?: { source: string }): unknown => {
    if (typeof value === "number" && typeof context?.source === "string" && /^-?\d+$/.test(context.source)) {
      return BigInt(context.source);
    }
    return value;
  };
  runTheory(family, JSON.parse(input, reviver));
} else {
  process.stderr.write(
    `usage: cli <check|account|negation|arithmetic|list|term|text|compound> (got ${JSON.stringify(family)})\n`,
  );
  process.exit(2);
}
