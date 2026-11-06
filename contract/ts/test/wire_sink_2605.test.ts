// #2605, the ts rung of #2602 (seat:caa's four conditions for lever A): wire_sink.ts's length
// reading against the codec whose framing it restates, and its value reading against the pre-#2605
// tree (sortedMap's substitution order).

import test from "node:test";
import assert from "node:assert/strict";

import { atom, tuple, type Atom, type Tuple, type Value } from "@bitspark/ontos-core";
import { encode } from "@bitspark/ontos-codec";

import {
  ClauseId,
  ClosedModelCert,
  FiniteDomain,
  GroundLiteral,
  RelationTable,
  StratumPrefix,
  SupportEdge,
  Symbol,
  Term,
  bytesAtom,
  certEncodedBytes,
  closedModelCertAsValue,
  digestAtom,
  intAtom,
  quote,
  sortedMap,
  substAsValue,
  type CertSizeDecl,
  type SupportRef,
  type Subst,
} from "../src/index.js";
import { measureLen, utf8Len, writeSubst } from "../src/wire_sink.js";
import { assertLengthReading2605 } from "./support/cert_len_2605.js";

const enc = new TextEncoder();

// The lengths the uvarint's width changes at (1|2 bytes at 127|128, 2|3 at 16383|16384), plus
// 255|256, where the codec order of two lengths is NOT their numeric order: uvarint(256) =
// 0x80 0x02 sorts before uvarint(255) = 0xFF 0x01.
const EDGES = [0, 1, 127, 128, 255, 256, 16383, 16384];

const encLen = (v: Value): number => encode(v).length;

test("#2605 condition 2: the length reading is exact at every uvarint boundary", () => {
  for (const n of EDGES) {
    const str = "x".repeat(n);
    assert.equal(measureLen((w) => w.atomStr(str)), encLen(atom(enc.encode(str))), `an atom of ${n} bytes`);
    assert.equal(measureLen((w) => w.atomBytes(enc.encode(str))), encLen(atom(enc.encode(str))), `atom bytes ${n}`);
    const empties = Array.from({ length: n }, () => atom(new Uint8Array()));
    const measured = measureLen((w) => {
      w.tupleBegin(n);
      for (let i = 0; i < n; i++) w.atomStr("");
      w.tupleEnd();
    });
    assert.equal(measured, encLen(tuple(empties)), `a tuple of arity ${n}`);
    const v = tuple([atom(enc.encode(str)), tuple(empties)]);
    assert.equal(measureLen((w) => w.value(v)), encLen(v), `a verbatim value at ${n}`);
    assert.equal(measureLen((w) => w.quotedValue(v)), encLen(quote(Term.fromValue(v))), `a quoted value at ${n}`);
    const term = Term.tuple([Term.atom(enc.encode(str)), Term.var(str), Term.tuple(Array.from({ length: n }, () => Term.var("v")))]);
    assert.equal(measureLen((w) => w.quotedTerm(term)), encLen(quote(term)), `a quoted term at ${n}`);
    assert.equal(measureLen((w) => w.int(n)), encLen(intAtom(n)), `the int ${n}`);
  }
  for (const n of [2 ** 32, 2 ** 52, Number.MAX_SAFE_INTEGER]) {
    assert.equal(measureLen((w) => w.int(n)), encLen(intAtom(n)), `the int ${n}`);
  }
  const d = Uint8Array.from({ length: 32 }, (_, i) => (i * 7) & 0xff);
  assert.equal(measureLen((w) => w.digest(d)), encLen(digestAtom(d)), "a digest");
});

test("#2605: a string's UTF-8 length is TextEncoder's, lone surrogates included", () => {
  for (const s of ["", "a", "é", "€", "😀", "a😀b", "\ud800", "\udc00", "a\ud800b", "\ud800\ud800", "\udc00\ud800", "x\ud83d"]) {
    assert.equal(utf8Len(s), enc.encode(s).length, JSON.stringify(s));
  }
});

// Names crossing every order trap: Z before AB (shorter first), 256 before 255, and a two-byte
// UTF-8 name ordered by its bytes ("ab" = 61 62 before "é" = C3 A9).
const NAMES = ["AB", "Z", "c".repeat(255), "d".repeat(256), "a".repeat(127), "b".repeat(128), "é", "ab"];

function subst2605(): Subst {
  const s: Subst = new Map();
  NAMES.forEach((name, i) => s.set(name, Term.tuple([Term.atom([i]), Term.var(name)])));
  return s;
}

test("#2605 condition 1: a substitution reads in codec order, exactly as sortedMap did", () => {
  const subst = subst2605();
  const want = encode(sortedMap(Array.from(subst, ([name, term]) => [bytesAtom(enc.encode(name)), quote(term)] as const)));
  const value = substAsValue(subst);
  assert.deepEqual(encode(value), want, "the value reading moved from sortedMap's");
  assert.equal(value.kind, "tuple");
  const order = (value as Tuple).items().map((entry) => new TextDecoder().decode(((entry as Tuple).at(0) as Atom).bytes()));
  assert.deepEqual(
    order.map((n) => enc.encode(n).length),
    [1, 2, 2, 2, 127, 128, 256, 255],
    "codec order: by uvarint(len), then bytes",
  );
  assert.deepEqual(order.slice(1, 4), ["AB", "ab", "é"]);
  assert.equal(measureLen((w) => writeSubst(w, subst)), want.length, "the substitution's length");
});

function hash(seed: number): Uint8Array {
  return Uint8Array.from({ length: 32 }, (_, i) => (seed + i) & 0xff);
}

// A synthetic certificate whose walk reaches every node the shape has: all five SupportRef tags,
// nested domain values, a substitution across the order traps, and the four trailing-slot shapes
// (0 neither, 1 a slice-seal pin, 2 a partial scope with the none marker, 3 both).
function cert2605(rows: number, trailing: number, certBytes = 123456): ClosedModelCert {
  const lit = (i: number): GroundLiteral =>
    new GroundLiteral(Symbol.of("p"), [intAtom(i), tuple([atom(enc.encode("k")), atom(enc.encode("y".repeat(i % 300)))])]);
  const subst = subst2605();
  const table: GroundLiteral[] = [];
  const edges: SupportEdge[] = [];
  for (let i = 0; i < rows; i++) {
    table.push(lit(i));
    const refs: SupportRef[] = [
      { kind: "same_stratum", fact: lit(i + 1), rank: i },
      { kind: "lower_stratum", cert: 0, atom: lit(i) },
      { kind: "builtin", atom: lit(i) },
      { kind: "neg_lower", cert: 1, atom: lit(i) },
      { kind: "count_lower", cert: i },
    ];
    edges.push(new SupportEdge(lit(i), ClauseId.of("c".repeat(1 + (i % 200))), subst, refs, i));
  }
  const limitsDecl: CertSizeDecl = {
    certFacts: rows,
    domainValues: 3,
    supportEdges: rows,
    ruleGroundings: 4,
    joinSteps: 5,
    certBytes,
  };
  return new ClosedModelCert({
    scope: StratumPrefix.of(3, [Symbol.of("p"), Symbol.of("q")]),
    programHash: hash(1),
    profileHash: hash(2),
    ctxHash: hash(3),
    theoryConfigHash: hash(4),
    edbSnapshotHashes: [hash(5), hash(6)],
    domains: [FiniteDomain.of(Symbol.of("t"), [atom(enc.encode("a")), tuple([atom(new Uint8Array()), tuple([intAtom(7)])]), intAtom(2 ** 40)])],
    extensions: [RelationTable.of(Symbol.of("p"), 2, table)],
    supports: edges,
    limitsDecl,
    decompositionWitness: trailing & 1 ? hash(9) : undefined,
    partialScope: trailing & 2 ? StratumPrefix.of(1, [Symbol.of("q")]) : undefined,
  });
}

test("#2605 conditions 1 and 3: every shape measures to its encoding, and each trailing branch is reached", () => {
  [10, 11, 12, 12].forEach((arity, trailing) => {
    const cert = cert2605(40, trailing);
    assertLengthReading2605(`synthetic trailing ${trailing}`, cert);
    const value = closedModelCertAsValue(cert);
    assert.equal(value.kind === "tuple" ? value.length : -1, arity, `trailing shape ${trailing}`);
  });
  assert.equal(certEncodedBytes(cert2605(3, 0, 0)), certEncodedBytes(cert2605(3, 0, Number.MAX_SAFE_INTEGER)), "certBytes leaked into the measure");
});
