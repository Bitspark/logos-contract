/*
 * TS replay of vectors/annotated_closed_model.json (ADR 0031 D5; #1821 P9 I5a, rulings Q14 and Q15),
 * the hand-authored oracle that rs (contract/rs/tests/annotated_closed_model_vectors.rs) and go
 * (contract/go/annotated_closed_model_vectors_test.go) replay too. Every case runs
 * checkAnnotatedClosedModel and compares the outcome kind, the code, the row where the vector names
 * one, the law and the unattested tables.
 *
 * The program, the negation_v1 profile (the lt theory; EDB leaves = `extensional`, the `edb` rows the
 * snapshot) and each cert in negation.json's notation are built as test/negation_vectors.test.ts
 * builds them, the cert bound to the context derived from the live program. Elements use
 * vectors/semiring.json's value grammar, read as test/semiring_vectors.test.ts reads it. The
 * semirings: counting and tropical are the core ones; stopping is semiring.json's fixture; fold_order
 * is this vector's test semiring, defined below.
 *
 * R3 (the vector declares `relational: runs` on the accepted cases): each accepted case keeps its
 * verdict under every checker budget raised, alone and together (eachBudgetRaised).
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { Atom, Tuple, atom, tuple, type Value } from "@bitspark/ontos-core";
import { encode } from "@bitspark/ontos-codec";
import { encodeInt } from "@bitspark/ontos-data";

import {
  AlwaysAdmit,
  AnnotatedClosedModelCert,
  type AnnotatedOutcome,
  AnnotatedTable,
  annotatedClosedModelCertAsValue,
  annotatedClosedModelCertFromValue,
  BodyLit,
  CertContext,
  type CertSizeDecl,
  type CheckLimits,
  type CheckProfile,
  checkAnnotatedClosedModel,
  Clause,
  ClauseId,
  ClosedModelCert,
  ComponentIdentity,
  DecodeError,
  defaultLimits,
  edbTableHash,
  Evidence,
  FiniteDomain,
  Goal,
  GroundLiteral,
  type Hash,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  newCountingSemiring,
  newTropicalSemiring,
  PredicateSet,
  programDigest,
  RelationTable,
  type Semiring,
  SemiringAnswer,
  semiringIdentity,
  StratumPrefix,
  Subst,
  type SupportEdge,
  SupportEdge as SupportEdgeClass,
  type SupportRef,
  SupportRef as SupportRefOps,
  Symbol,
  Term,
  type Theory,
  TheoryGround,
  VarId,
} from "../src/index.js";
import { eachBudgetRaised, r3Domain, r3Raised } from "./support/r3_domain.js";

const VECTOR_FILE = "annotated_closed_model.json";

function loadVectors(): any {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", VECTOR_FILE);
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8"));
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/${VECTOR_FILE} above ${dir}`);
    dir = parent;
  }
}

const utf8 = new TextEncoder();

function text(sym: Symbol): string {
  return new TextDecoder().decode(sym.bytes());
}

// ------------------------------- the negation_v1 profile -------------------------------

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
  decideGround(lit: GroundLiteral): TheoryGround {
    const args = lit.args;
    if (args.length !== 2) return TheoryGround.fails("lt_arity");
    const a = args[0]!;
    const b = args[1]!;
    if (a.kind === "atom" && b.kind === "atom" && bytesLess(a.bytes(), b.bytes())) {
      return TheoryGround.holds();
    }
    return TheoryGround.fails("not_less_than");
  }
}

const PROFILE_PIN: Hash = new Uint8Array(32).fill(0x11);
const CTX_PIN: Hash = new Uint8Array(32).fill(0x22);
const THEORY_PIN: Hash = new Uint8Array(32).fill(0x33);

// test-double: consumer(the annotated vector EDB with snapshots)
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
    return this.#snapshots.get(text(pred));
  }
}

// ---------------------------- negation.json's authoring notation ----------------------------

function termFromJson(j: any): Term {
  if (typeof j.atom_str === "string") return Term.atom(utf8.encode(j.atom_str));
  if (Array.isArray(j.tuple)) return Term.tuple(j.tuple.map(termFromJson));
  if (typeof j.var === "string") return Term.var(j.var);
  throw new Error(`term must be atom_str/tuple/var: ${JSON.stringify(j)}`);
}

function goalFromJson(j: any): Goal {
  return new Goal(Symbol.of(String(j.pred)), (j.args as any[]).map(termFromJson));
}

function bodyLitFromJson(j: any): BodyLit {
  if (j !== null && typeof j === "object" && j.neg !== undefined) return BodyLit.neg(goalFromJson(j.neg));
  return BodyLit.pos(goalFromJson(j));
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
  const subst: Subst = new Subst();
  for (const [varName, term] of Object.entries(j)) subst.set(new VarId(varName), termFromJson(term));
  return subst;
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

// Verbatim constructors, as the negation replay builds them: the row order is the vector's, so
// `annotations[i].elements[j]` stays bound to the row the vector authored it for.
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

function prefixFromJson(j: any): StratumPrefix {
  return verbatimStratumPrefix(Number(j.level), (j.predicates as any[]).map((p) => Symbol.of(String(p))));
}

function certFromJson(j: any, programHash: Hash): ClosedModelCert {
  for (const pin of ["program_hash", "profile_hash", "ctx_hash", "theory_config_hash", "decomposition_witness"]) {
    assert.equal(j[pin], undefined, `this replay binds every cert to the derived context; a ${pin} needs support here`);
  }
  return new ClosedModelCert({
    scope: prefixFromJson(j.scope),
    programHash,
    profileHash: PROFILE_PIN,
    ctxHash: CTX_PIN,
    theoryConfigHash: THEORY_PIN,
    edbSnapshotHashes: [],
    domains: (j.domains as any[]).map((d) =>
      verbatimFiniteDomain(Symbol.of(String(d.type_tag)), (d.values as any[]).map(groundTermValue)),
    ),
    extensions: (j.extensions as any[]).map((t) =>
      verbatimRelationTable(Symbol.of(String(t.pred)), Number(t.arity), (t.rows as any[]).map(groundFromJson)),
    ),
    supports: (j.supports as any[]).map(supportEdgeFromJson),
    limitsDecl: certSizeDeclFromJson(j.limits_decl),
    ...(j.partial_scope !== undefined && j.partial_scope !== null ? { partialScope: prefixFromJson(j.partial_scope) } : {}),
  });
}

// ------------------------------ semiring.json's value grammar ------------------------------

/** The ontos value an element of the vector's structural grammar denotes. */
function element(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) throw new Error(`element is not an object: ${JSON.stringify(raw)}`);
  const obj = raw as Record<string, unknown>;
  if ("int" in obj) return encodeInt(BigInt(obj["int"] as number));
  if ("decimal" in obj) {
    const [m, e] = obj["decimal"] as [number, number];
    return tuple([atom(utf8.encode("decimal")), encodeInt(BigInt(m)), encodeInt(BigInt(e))]);
  }
  if ("atom" in obj) return atom(utf8.encode(obj["atom"] as string));
  if ("tuple" in obj) return tuple((obj["tuple"] as unknown[]).map(element));
  throw new Error(`unrecognized element shape: ${JSON.stringify(raw)}`);
}

// ------------------------------------- the semirings -------------------------------------

/** semiring.json's stopping fixture: Counting's carrier and laws, every operation on elements stopped. */
function stoppingFixture(): Semiring {
  const counting = newCountingSemiring();
  const stopOr = (counted: SemiringAnswer): SemiringAnswer => (counted.kind === "element" ? SemiringAnswer.capacity() : counted);
  return {
    declaredIdentity: () => ComponentIdentity.of(utf8.encode("fixture/stopping-semiring"), utf8.encode("1"), new Uint8Array(32)),
    laws: () => counting.laws(),
    zero: () => counting.zero(),
    one: () => counting.one(),
    isElement: (v) => counting.isElement(v),
    add: (a, b) => stopOr(counting.add(a, b)),
    mul: (a, b) => stopOr(counting.mul(a, b)),
  };
}

function concat(a: Uint8Array, b: Uint8Array): Uint8Array {
  const out = new Uint8Array(a.length + b.length);
  out.set(a, 0);
  out.set(b, a.length);
  return out;
}

/**
 * This vector's TEST semiring, never registered: declared identity (fixture/fold-order, 1, 32 zero
 * bytes), no law declared, every Atom an element, zero and one the empty atom, and add(x, y) and
 * mul(x, y) both the atom of x's bytes then y's bytes. Its add is order-sensitive on purpose: it pins
 * the canonical grounding order (#1821 Q15 condition 3), and its mul pins body order.
 */
function foldOrderFixture(): Semiring {
  const empty = atom(new Uint8Array(0));
  const join = (a: Value, b: Value): SemiringAnswer =>
    a instanceof Atom && b instanceof Atom ? SemiringAnswer.element(atom(concat(a.bytes(), b.bytes()))) : SemiringAnswer.notAnElement();
  return {
    declaredIdentity: () => ComponentIdentity.of(utf8.encode("fixture/fold-order"), utf8.encode("1"), new Uint8Array(32)),
    laws: () => ({ idempotent: false, bounded: false, monotone: false, commutative: false, supportsRetraction: false }),
    zero: () => empty,
    one: () => empty,
    isElement: (v) => v instanceof Atom,
    add: join,
    mul: join,
  };
}

function semiringNamed(name: string): Semiring {
  switch (name) {
    case "counting":
      return newCountingSemiring();
    case "tropical":
      return newTropicalSemiring();
    case "stopping":
      return stoppingFixture();
    case "fold_order":
      return foldOrderFixture();
    default:
      throw new Error(`${VECTOR_FILE} names an unknown semiring ${name}`);
  }
}

// --------------------------------------- the replay ---------------------------------------

const doc = loadVectors();
assert.equal(doc.profile, "negation_v1", "the vector's profile is negation_v1");
const program = programFromJson(doc.program);
const leaves = new EdbLeaves((doc.extensional as string[]) ?? [], (doc.edb as Record<string, any[]>) ?? {});
const recomputed: Hash = programDigest(program.iter().map(([, clause]) => clause));
const context = CertContext.of(recomputed, PROFILE_PIN, CTX_PIN, THEORY_PIN);
const cases: any[] = doc.cases;
assert.ok(cases.length >= 14, `${VECTOR_FILE} carries ${cases.length} cases, fewer than 14`);

function profileWith(limits: CheckLimits): CheckProfile<void> {
  return { theory: new LtTheory(), leaves, admit: new AlwaysAdmit<void>(), limits };
}

function annotatedFromJson(c: any): AnnotatedClosedModelCert {
  const tables = (c.annotations as any[]).map(
    (t) => new AnnotatedTable(Symbol.of(String(t.pred)), (t.elements as unknown[]).map(element)),
  );
  return new AnnotatedClosedModelCert(certFromJson(c.cert, recomputed), semiringIdentity(semiringNamed(String(c.cert_semiring))), tables);
}

function run(c: any, annotated: AnnotatedClosedModelCert, limits: CheckLimits): AnnotatedOutcome {
  return checkAnnotatedClosedModel(program, annotated, undefined, profileWith(limits), context, semiringNamed(String(c.semiring)));
}

/** An outcome as plain data, for comparison and for a readable failure. */
function describe(o: AnnotatedOutcome): Record<string, unknown> {
  switch (o.kind) {
    case "accept":
      return { kind: o.kind, law: o.law ?? null, unattested: o.unattested.map(text) };
    case "reject_cert":
      return { kind: o.kind, code: o.code, detail: o.detail };
    case "reject":
      return {
        kind: o.kind,
        code: o.code,
        row: o.row === undefined ? null : { pred: text(o.row.pred), index: o.row.index },
        detail: o.detail,
      };
    default:
      throw new Error(`an outcome of no known kind: ${JSON.stringify(o)}`);
  }
}

/** Compare kind, code, row (where the vector names one), law and unattested; the name that ran. */
function assertExpected(c: any, got: AnnotatedOutcome): string {
  const where = `case ${c.name}: got ${JSON.stringify(describe(got))}`;
  const want = c.expected ?? {};
  assert.equal(got.kind, c.outcome, where);
  if (got.kind === "accept") {
    assert.equal(got.law ?? null, want.law, where);
    assert.deepEqual(got.unattested.map(text), want.unattested, where);
    return "accept";
  }
  assert.equal(got.code, want.code, where);
  if (want.row !== undefined) {
    assert.ok(got.kind === "reject" && got.row !== undefined, `${where}: the vector names a row`);
    if (got.kind === "reject" && got.row !== undefined) {
      assert.equal(text(got.row.pred), want.row.pred, where);
      assert.equal(got.row.index, want.row.index, where);
    }
  }
  return `${got.kind}:${got.code}`;
}

const domain = r3Domain(VECTOR_FILE, cases.map((c) => String(c.name)));
const raised = r3Raised();
const ran = new Set<string>();
let replayed = 0;

for (const c of cases) {
  test(`annotated closed model vector: ${c.name}`, () => {
    const annotated = annotatedFromJson(c);
    const limits = defaultLimits();
    const got = run(c, annotated, limits);
    ran.add(assertExpected(c, got));
    replayed += 1;

    // The annotated wire is closed and round-trips: decoding what it wrote re-encodes to the same bytes.
    const wire = annotatedClosedModelCertAsValue(annotated);
    const again = annotatedClosedModelCertAsValue(annotatedClosedModelCertFromValue(wire));
    assert.deepEqual(encode(again), encode(wire), `case ${c.name}: the annotated wire round-trips`);

    // R3 (#2733, the checker's arm): an accepted case keeps its verdict under each raised budget.
    if (domain.has(c.name)) {
      for (const rb of eachBudgetRaised(limits, raised)) {
        assert.deepEqual(describe(run(c, annotated, rb.limits)), describe(got), `case ${c.name}: raising ${rb.name} changed the verdict`);
      }
    }
  });
}

test(`${VECTOR_FILE}: every case ran, and every expected kind and code occurred`, () => {
  assert.equal(replayed, cases.length, "a case did not complete");
  const expected = new Set(cases.map((c) => (c.outcome === "accept" ? "accept" : `${c.outcome}:${c.expected.code}`)));
  assert.deepEqual([...ran].sort(), [...expected].sort());
  assert.ok(ran.has("accept") && [...ran].some((n) => n.startsWith("reject:")) && [...ran].some((n) => n.startsWith("reject_cert:")));
});

test(`${VECTOR_FILE}: the annotated decoder refuses every other shape`, () => {
  const c = cases.find((k) => k.outcome === "accept");
  assert.ok(c !== undefined, "no accepted case to build a wire from");
  const wire = annotatedClosedModelCertAsValue(annotatedFromJson(c));
  assert.ok(wire instanceof Tuple);
  const [tag, cert, identity, tables] = wire.items();
  assert.ok(identity instanceof Tuple && tables instanceof Tuple);
  const [id, version] = identity.items();
  const refused = (what: string, v: Value): void => {
    assert.throws(() => annotatedClosedModelCertFromValue(v), DecodeError, what);
  };
  refused("not a tuple", atom(utf8.encode("annotated_closed_model_cert")));
  refused("a wrong tag", tuple([atom(utf8.encode("closed_model_cert")), cert!, identity, tables]));
  refused("a wrong arity", tuple([tag!, cert!, identity]));
  refused("an identity of arity 2", tuple([tag!, cert!, tuple([id!, version!]), tables]));
  refused("a 31-byte config digest", tuple([tag!, cert!, tuple([id!, version!, atom(new Uint8Array(31))]), tables]));
  refused("an uppercase-hex config digest", tuple([tag!, cert!, tuple([id!, version!, atom(new Uint8Array(64).fill(0x41))]), tables]));
  refused("an annotated table of arity 3", tuple([tag!, cert!, identity, tuple([tuple([atom(utf8.encode("p")), tuple([]), tuple([])])])]));
  refused("a non-atom predicate", tuple([tag!, cert!, identity, tuple([tuple([tuple([]), tuple([])])])]));
  refused("elements that are not a tuple", tuple([tag!, cert!, identity, tuple([tuple([atom(utf8.encode("p")), atom(utf8.encode("x"))])])]));
  // The control: the unaltered wire decodes.
  assert.ok(annotatedClosedModelCertFromValue(wire) instanceof AnnotatedClosedModelCert);
});
