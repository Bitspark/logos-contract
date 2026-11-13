/*
 * TS replay of the cross-core agreement vector vectors/semiring.json (ADR 0031 D1, D2, G3;
 * v2 §14.3). The SAME file is replayed by Rust (contract/rs/tests/semiring_vectors.rs) and Go
 * (contract/go/semiring_vectors_test.go). Every core builds the core semiring Counting and the
 * four fixture semirings the vector's note defines, and must reproduce each semiring's
 * declared identity, laws, computed identity digest, zero and one; the element test; every
 * add/mul row; and every audit verdict, witness included. The product semiring (P9 I7) is
 * replayed the same way over its `products`, `product_ops` and `product_audits` sections.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { Atom, Tuple, atom, equals, tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";

import {
  auditSemiring,
  BigDecimal,
  ComponentIdentity,
  LAW_BITS,
  lawBits,
  type LawDeclaration,
  lawIsVacuous,
  type LawTally,
  SemiringAnswer,
  newCountingSemiring,
  newProbabilitySemiring,
  newProductSemiring,
  newProvenanceSemiring,
  newTropicalSemiring,
  productSemiringPrefix,
  type Semiring,
  SEMIRING_AUDIT_ORDER,
  SEMIRING_AUDIT_SAMPLE_LIMIT,
  semiringIdentity,
  semiringIdentityOf,
  semiringIdentityPrefix,
} from "../src/index.js";

type Json = Record<string, unknown>;

function loadSemiringVectors(): Json {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "semiring.json");
    if (fs.existsSync(candidate)) {
      return JSON.parse(fs.readFileSync(candidate, "utf8")) as Json;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/semiring.json above ${dir}`);
    }
    dir = parent;
  }
}

const utf8 = new TextEncoder();

/** The ontos value an object of the vector's structural grammar denotes. */
function value(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) {
    throw new Error(`value is not an object: ${JSON.stringify(raw)}`);
  }
  const obj = raw as Json;
  if ("int" in obj) return encodeInt(BigInt(obj["int"] as number));
  if ("bigint" in obj) return encodeInt(BigInt(obj["bigint"] as string));
  if ("decimal" in obj) {
    const [m, e] = obj["decimal"] as [number, number];
    return tuple([atom(utf8.encode("decimal")), encodeInt(BigInt(m)), encodeInt(BigInt(e))]);
  }
  if ("atom" in obj) return atom(utf8.encode(obj["atom"] as string));
  if ("tuple" in obj) return tuple((obj["tuple"] as unknown[]).map(value));
  throw new Error(`unrecognized value shape: ${JSON.stringify(raw)}`);
}

function rows(v: Json, section: string): Json[] {
  const r = v[section];
  assert.ok(Array.isArray(r), `${section} is an array`);
  return r as Json[];
}

function hex(bytes: Uint8Array): string {
  return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

function sameValues(a: readonly Value[], b: readonly Value[]): boolean {
  return a.length === b.length && a.every((x, i) => equals(x, b[i]!));
}

// ---- the fixture semirings, as the vector's note defines them ----

const TRUE = atom(utf8.encode("true"));
const FALSE = atom(utf8.encode("false"));

function truth(v: Value): boolean | undefined {
  if (equals(v, TRUE)) return true;
  if (equals(v, FALSE)) return false;
  return undefined;
}

/** boolean (⊕ or), or left_add (⊕ the left projection), over {false, true}. */
function booleanFixture(id: string, leftAdd: boolean): Semiring {
  return {
    declaredIdentity: () => ComponentIdentity.of(utf8.encode(id), utf8.encode("1"), new Uint8Array(32)),
    laws: () => ({ idempotent: true, bounded: true, monotone: true, commutative: true, supportsRetraction: false }),
    zero: () => FALSE,
    one: () => TRUE,
    isElement: (v) => truth(v) !== undefined,
    add: (a, b) => {
      const x = truth(a);
      const y = truth(b);
      if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
      return SemiringAnswer.element((leftAdd ? x : x || y) ? TRUE : FALSE);
    },
    mul: (a, b) => {
      const x = truth(a);
      const y = truth(b);
      if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
      return SemiringAnswer.element(x && y ? TRUE : FALSE);
    },
  };
}

function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a[i] !== b[i]) return a[i]! - b[i]!;
  }
  return a.length - b.length;
}

/** string_set's element, or undefined: a Tuple of Atoms strictly increasing by bytes. */
function words(v: Value): Uint8Array[] | undefined {
  if (!(v instanceof Tuple)) return undefined;
  const out: Uint8Array[] = [];
  for (const item of v.items()) {
    if (!(item instanceof Atom)) return undefined;
    const w = item.bytes();
    const prev = out[out.length - 1];
    if (prev !== undefined && compareBytes(prev, w) >= 0) return undefined;
    out.push(w);
  }
  return out;
}

function wordSet(ws: Uint8Array[]): Value {
  const sorted = [...ws].sort(compareBytes);
  const items: Value[] = [];
  let prev: Uint8Array | undefined;
  for (const w of sorted) {
    if (prev !== undefined && compareBytes(prev, w) === 0) continue;
    items.push(atom(w));
    prev = w;
  }
  return tuple(items);
}

function concat(a: Uint8Array, b: Uint8Array): Uint8Array {
  const out = new Uint8Array(a.length + b.length);
  out.set(a, 0);
  out.set(b, a.length);
  return out;
}

/** string_set: finite sets of atoms, ⊕ union, ⊗ pairwise concatenation. */
function stringSetFixture(): Semiring {
  return {
    declaredIdentity: () =>
      ComponentIdentity.of(utf8.encode("fixture/string-set-semiring"), utf8.encode("1"), new Uint8Array(32)),
    laws: () => ({ idempotent: true, bounded: false, monotone: true, commutative: true, supportsRetraction: false }),
    zero: () => wordSet([]),
    one: () => wordSet([new Uint8Array(0)]),
    isElement: (v) => words(v) !== undefined,
    add: (a, b) => {
      const x = words(a);
      const y = words(b);
      return x === undefined || y === undefined ? SemiringAnswer.notAnElement() : SemiringAnswer.element(wordSet([...x, ...y]));
    },
    mul: (a, b) => {
      const x = words(a);
      const y = words(b);
      if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
      const out: Uint8Array[] = [];
      for (const p of x) for (const q of y) out.push(concat(p, q));
      return SemiringAnswer.element(wordSet(out));
    },
  };
}

/**
 * counting_declared_idempotent (Counting with idempotent also declared), or stopping
 * (Counting's carrier, every operation on elements stopped at the capacity bound).
 */
function countingVariant(declaredIdempotent: boolean, stopping: boolean): Semiring {
  const counting = newCountingSemiring();
  const stopOr = (counted: SemiringAnswer): SemiringAnswer =>
    counted.kind === "element" && stopping ? SemiringAnswer.capacity() : counted;
  return {
    declaredIdentity: () =>
      stopping
        ? ComponentIdentity.of(utf8.encode("fixture/stopping-semiring"), utf8.encode("1"), new Uint8Array(32))
        : counting.declaredIdentity(),
    laws: () => ({ ...counting.laws(), idempotent: declaredIdempotent }),
    zero: () => counting.zero(),
    one: () => counting.one(),
    isElement: (v) => counting.isElement(v),
    add: (a, b) => stopOr(counting.add(a, b)),
    mul: (a, b) => stopOr(counting.mul(a, b)),
  };
}

/** noisy_or's carrier: a canonical decimal in [0, 1]. */
function unit(v: Value): BigDecimal | undefined {
  const d = BigDecimal.fromTerm(v);
  if (d === undefined || d.isNegative() || d.cmp(BigDecimal.fromBigInt(1n)) > 0) return undefined;
  return d;
}

/** noisy_or: decimals in [0, 1], ⊕ a + b - ab, ⊗ ab. Not distributive, so not a semiring. */
function noisyOrFixture(): Semiring {
  return {
    declaredIdentity: () =>
      ComponentIdentity.of(utf8.encode("fixture/noisy-or-semiring"), utf8.encode("1"), new Uint8Array(32)),
    laws: () => ({ idempotent: false, bounded: false, monotone: true, commutative: true, supportsRetraction: false }),
    zero: () => BigDecimal.zero().toTerm(),
    one: () => BigDecimal.fromBigInt(1n).toTerm(),
    isElement: (v) => unit(v) !== undefined,
    add: (a, b) => {
      const x = unit(a);
      const y = unit(b);
      if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
      const sum = x.add(y);
      const product = x.mul(y);
      if (!sum.ok || !product.ok) return SemiringAnswer.capacity();
      const result = sum.value.sub(product.value);
      return result.ok ? SemiringAnswer.element(result.value.toTerm()) : SemiringAnswer.capacity();
    },
    mul: (a, b) => {
      const x = unit(a);
      const y = unit(b);
      if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
      const product = x.mul(y);
      return product.ok ? SemiringAnswer.element(product.value.toTerm()) : SemiringAnswer.capacity();
    },
  };
}

/** The semiring a vector row names, built from this core's own code. */
function semiring(name: string, kind: string): Semiring {
  switch (`${kind}/${name}`) {
    case "core/counting":
      return newCountingSemiring();
    case "fixture/counting_declared_idempotent":
      return countingVariant(true, false);
    case "fixture/stopping":
      return countingVariant(false, true);
    case "fixture/boolean":
      return booleanFixture("fixture/boolean-semiring", false);
    case "fixture/left_add":
      return booleanFixture("fixture/left-projection-add", true);
    case "fixture/string_set":
      return stringSetFixture();
    case "core/tropical":
      return newTropicalSemiring();
    case "core/probability":
      return newProbabilitySemiring();
    case "core/provenance":
      return newProvenanceSemiring();
    case "fixture/noisy_or":
      return noisyOrFixture();
    default:
      throw new Error(`vectors/semiring.json names an unknown ${kind} semiring ${name}`);
  }
}

function semiringNamed(v: Json, name: string): Semiring {
  const row = rows(v, "semirings").find((r) => r["name"] === name);
  assert.ok(row !== undefined, `no semiring named ${name}`);
  return semiring(name, row["kind"] as string);
}

function lawsOf(raw: unknown): LawDeclaration {
  const j = raw as Json;
  return {
    idempotent: j["idempotent"] as boolean,
    bounded: j["bounded"] as boolean,
    monotone: j["monotone"] as boolean,
    commutative: j["commutative"] as boolean,
    supportsRetraction: j["supports_retraction"] as boolean,
  };
}

test("semiring.json: the metadata is the contract's", () => {
  const v = loadSemiringVectors();
  assert.deepEqual(utf8.encode(v["identity_prefix"] as string), semiringIdentityPrefix());
  assert.equal(v["audit_sample_limit"], SEMIRING_AUDIT_SAMPLE_LIMIT);
  assert.deepEqual(v["audit_order"], [...SEMIRING_AUDIT_ORDER]);
  const bits = v["law_bits"] as Json;
  assert.deepEqual(bits, {
    idempotent: LAW_BITS.idempotent,
    bounded: LAW_BITS.bounded,
    monotone: LAW_BITS.monotone,
    commutative: LAW_BITS.commutative,
    supports_retraction: LAW_BITS.supportsRetraction,
  });
});

/**
 * Compare `s` with a `semirings` or `products` row: its declared identity, laws, laws_byte, computed
 * identity, zero and one. Returns the computed identity digest as hex.
 */
function assertIdentityRow(row: Json, s: Semiring): string {
  const name = row["name"] as string;
  const declared = s.declaredIdentity();
  const want = row["declared_identity"] as Json;
  assert.deepEqual(declared.id, utf8.encode(want["id"] as string), `${name}: id`);
  assert.deepEqual(declared.version, utf8.encode(want["version"] as string), `${name}: version`);
  assert.equal(hex(declared.configDigest), want["config_digest"], `${name}: config digest`);
  const laws = s.laws();
  assert.deepEqual({ ...laws }, lawsOf(row["laws"]), `${name}: laws`);
  assert.equal(lawBits(laws), row["laws_byte"], `${name}: laws_byte`);
  const identity = semiringIdentity(s);
  assert.ok(identity.equals(semiringIdentityOf(declared, laws)), `${name}: one fold`);
  assert.deepEqual(identity.id, declared.id, `${name}: the identity keeps the id`);
  assert.deepEqual(identity.version, declared.version, `${name}: and the version`);
  assert.equal(hex(identity.configDigest), row["identity_digest_hex"], `${name}: identity digest`);
  assert.ok(equals(s.zero(), value(row["zero"])), `${name}: zero`);
  assert.ok(equals(s.one(), value(row["one"])), `${name}: one`);
  return hex(identity.configDigest);
}

test("semiring.json: every semiring reproduces its identity, laws, zero and one", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "semirings");
  assert.ok(table.length > 0, "the semirings table is not empty");
  for (const row of table) {
    assertIdentityRow(row, semiring(row["name"] as string, row["kind"] as string));
  }
});

test("semiring.json: every element row holds", () => {
  const v = loadSemiringVectors();
  for (const row of rows(v, "elements")) {
    const s = semiringNamed(v, row["semiring"] as string);
    assert.equal(s.isElement(value(row["value"])), row["expected"], row["name"] as string);
  }
});

/** Run an `ops` or `product_ops` row's operation on `s` and compare the answer to its `expected`. */
function assertOpRow(row: Json, s: Semiring): void {
  const name = row["name"] as string;
  const a = value(row["a"]);
  const b = value(row["b"]);
  const op = row["op"];
  assert.ok(op === "add" || op === "mul", `${name}: unknown op ${String(op)}`);
  const got = op === "add" ? s.add(a, b) : s.mul(a, b);
  const expected = row["expected"];
  if (expected === "not_an_element") {
    assert.equal(got.kind, "not_an_element", name);
  } else if (typeof expected === "object" && expected !== null && "stopped" in expected) {
    const stopped = (expected as Json)["stopped"] as Json;
    assert.equal(got.kind, "stopped", name);
    if (got.kind === "stopped") {
      assert.deepEqual({ ...got.cause }, { kind: stopped["kind"], scope: stopped["scope"] }, name);
    }
  } else {
    assert.ok(got.kind === "element" && equals(got.value, value(expected)), name);
  }
}

test("semiring.json: every operation row holds", () => {
  const v = loadSemiringVectors();
  for (const row of rows(v, "ops")) {
    assertOpRow(row, semiringNamed(v, row["semiring"] as string));
  }
});

/** A verdict's tallies as plain records. */
function tallies(laws: readonly LawTally[]): Json[] {
  return laws.map((t) => ({ law: t.law, decided: t.decided, undecided: t.undecided }));
}

/** Audit `s` over an `audits` or `product_audits` row's samples and compare the verdict to the row's. */
function assertAuditRow(row: Json, s: Semiring): void {
  const name = row["name"] as string;
  const got = auditSemiring(s, (row["samples"] as unknown[]).map(value));
  const verdict = row["verdict"] as Json;
  if ("no_counterexample" in verdict) {
    const pass = verdict["no_counterexample"] as Json;
    assert.equal(got.kind, "no_counterexample", `${name}: ${got.kind}`);
    if (got.kind === "no_counterexample") {
      assert.ok(!got.laws.some(lawIsVacuous), `${name}: no law is vacuous`);
      assert.deepEqual(tallies(got.laws), pass["laws"], `${name}: laws`);
    }
  } else if ("vacuous" in verdict) {
    const vacuous = verdict["vacuous"] as Json;
    assert.equal(got.kind, "vacuous", `${name}: ${got.kind}`);
    if (got.kind === "vacuous") {
      assert.ok(got.laws.some(lawIsVacuous), `${name}: a law is vacuous`);
      assert.deepEqual(tallies(got.laws), vacuous["laws"], `${name}: laws`);
    }
  } else if ("counterexample" in verdict) {
    const refuted = verdict["counterexample"] as Json;
    assert.equal(got.kind, "counterexample", name);
    if (got.kind === "counterexample") {
      assert.equal(got.law, refuted["law"], `${name}: law`);
      const witness = (refuted["witness"] as unknown[]).map(value);
      assert.ok(sameValues(got.witness, witness), `${name}: witness`);
    }
  } else if ("sample_limit" in verdict) {
    const limit = verdict["sample_limit"] as Json;
    assert.equal(got.kind, "sample_limit", name);
    if (got.kind === "sample_limit") {
      assert.equal(got.given, limit["given"], `${name}: given`);
      assert.equal(got.limit, limit["limit"], `${name}: limit`);
    }
  } else {
    assert.fail(`${name}: unknown verdict ${JSON.stringify(verdict)}`);
  }
}

test("semiring.json: every audit row reproduces its verdict", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "audits");
  assert.ok(table.length > 0, "the audits table is not empty");
  for (const row of table) {
    assertAuditRow(row, semiringNamed(v, row["semiring"] as string));
  }
});

test("semiring.json: every decimal_parts row holds", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "decimal_parts");
  assert.ok(table.length > 0, "the decimal_parts table is not empty");
  for (const row of table) {
    const name = row["name"] as string;
    const [m, e] = row["parts"] as [number, number];
    const built = BigDecimal.fromParts(BigInt(m), BigInt(e));
    const expected = row["expected"];
    if (expected === "out_of_band") {
      assert.equal(built, undefined, name);
    } else {
      assert.ok(built !== undefined && equals(built.toTerm(), value(expected)), name);
    }
  }
});

test("semiring.json: every decimal_decode row holds", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "decimal_decode");
  assert.ok(table.length > 0, "the decimal_decode table is not empty");
  for (const row of table) {
    const name = row["name"] as string;
    const decoded = BigDecimal.fromTerm(value(row["value"]));
    const expected = row["expected"];
    if (expected === "not_a_canonical_decimal") {
      assert.equal(decoded, undefined, name);
    } else {
      assert.ok(decoded !== undefined && equals(decoded.toTerm(), value(expected)), name);
    }
  }
});

// ---- the product semiring (v2 §14.2, P9 I7; rulings Q23-Q28 on #1821) ----

/** Each declarable law's wire name, as its LawDeclaration field. */
const LAW_FIELDS: Readonly<Record<string, keyof LawDeclaration>> = {
  idempotent: "idempotent",
  bounded: "bounded",
  monotone: "monotone",
  commutative: "commutative",
  supports_retraction: "supportsRetraction",
};

/**
 * A test-only wrapper over `product` whose laws() also declare each law `also` names; everything
 * else delegates. An unknown law name is refused.
 */
function declaringAlso(product: Semiring, also: readonly string[]): Semiring {
  const fields = also.map((law) => {
    const field = LAW_FIELDS[law];
    if (field === undefined) throw new Error(`vectors/semiring.json declares an unknown law ${law}`);
    return field;
  });
  return {
    declaredIdentity: () => product.declaredIdentity(),
    laws: () => {
      const laws: Record<keyof LawDeclaration, boolean> = { ...product.laws() };
      for (const field of fields) laws[field] = true;
      return laws;
    },
    zero: () => product.zero(),
    one: () => product.one(),
    isElement: (x) => product.isElement(x),
    add: (a, b) => product.add(a, b),
    mul: (a, b) => product.mul(a, b),
  };
}

/**
 * The product a `products` row names, built from this core's own code: its two core members in
 * order, and for the one fixture the declared-more wrapper. An unknown member, kind or fixture is
 * refused, never skipped.
 */
function productOf(row: Json): Semiring {
  const name = row["name"] as string;
  const members = row["members"] as string[];
  assert.equal(members.length, 2, `${name}: a product names two members`);
  const product = newProductSemiring(semiring(members[0]!, "core"), semiring(members[1]!, "core"));
  const kind = row["kind"] as string;
  if (kind === "core") {
    assert.equal(row["declares_also"], undefined, `${name}: a core product declares no more than its members`);
    return product;
  }
  if (kind === "fixture" && name === "counting_x_tropical_declared_bounded") {
    return declaringAlso(product, row["declares_also"] as string[]);
  }
  throw new Error(`vectors/semiring.json names an unknown ${kind} product ${name}`);
}

function productNamed(v: Json, name: string): Semiring {
  const row = rows(v, "products").find((r) => r["name"] === name);
  assert.ok(row !== undefined, `no product named ${name}`);
  return productOf(row);
}

test("semiring.json: every product reproduces its identity, laws, zero and one, and the order is identity", () => {
  const v = loadSemiringVectors();
  assert.deepEqual(utf8.encode(v["product_identity_prefix"] as string), productSemiringPrefix());
  const cores = rows(v, "semirings")
    .filter((r) => r["kind"] === "core")
    .map((r) => r["name"] as string);
  assert.equal(cores.length, 4, "the four core semirings");
  const digests = new Map<string, string>();
  for (const row of rows(v, "products")) {
    const digest = assertIdentityRow(row, productOf(row));
    if (row["kind"] !== "core") continue;
    const pair = (row["members"] as string[]).join(" x ");
    assert.ok(!digests.has(pair), `the products table carries ${pair} once`);
    digests.set(pair, digest);
  }
  assert.equal(digests.size, 16, "the products table carries the sixteen ordered core pairs");
  for (const a of cores) {
    for (const b of cores) {
      const ab = digests.get(`${a} x ${b}`);
      assert.ok(ab !== undefined, `the products table carries ${a} x ${b}`);
      if (a !== b) assert.notEqual(ab, digests.get(`${b} x ${a}`), `${a} x ${b} and ${b} x ${a} are different identities`);
    }
  }
});

test("semiring.json: every product operation row holds", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "product_ops");
  assert.ok(table.length > 0, "the product_ops table is not empty");
  for (const row of table) {
    assertOpRow(row, productNamed(v, row["product"] as string));
  }
});

test("semiring.json: every product audit row reproduces its verdict", () => {
  const v = loadSemiringVectors();
  const table = rows(v, "product_audits");
  assert.ok(table.length > 0, "the product_audits table is not empty");
  for (const row of table) {
    assertAuditRow(row, productNamed(v, row["product"] as string));
  }
});
