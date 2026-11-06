/*
 * TS replay of the cross-core program-(de)serialization byte-pin vector
 * vectors/program_serde.json (logos-contract §10, issue #310).
 *
 * Each case rebuilds a MapProgram from the vector's (id, head, body) clause set (authored
 * in a deliberately NON-sorted insertion order), drives the REAL programToValue /
 * programFromValue, and asserts:
 *   - the ontos-codec-v1 bytes of programToValue(p) equal the pinned program_bytes_hex
 *     (the canonical, insertion-order-independent encoding), and
 *   - programFromValue(programToValue(p)) round-trips back to the same program.
 *
 * The SAME file is replayed in Rust (contract/rs/tests/program_serde_vectors.rs) and Go
 * (contract/go/program_serde_vectors_test.go), so one byte-pin oracle pins all three cores
 * — the frozen ontos-codec + the syntactic §2a quote tags + the canonical (sorted-by-id)
 * clause order pin the SAME bytes across {rs,go,ts}.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom as valueAtom, tuple as valueTuple } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";

import {
  BodyLit,
  Clause,
  ClauseId,
  clauseBytes,
  clauseValue,
  Goal,
  MapProgram,
  PROGRAM_SERDE_VERSION,
  ProgramSerdeDecodeError,
  ProgramSerdeEncodeError,
  programBytes,
  programFromValue,
  programToValue,
  Symbol,
  Term,
} from "../src/index.js";

// ----- the on-disk vector shape -----

interface TermJson {
  atom?: string;
  atom_str?: string;
  int?: number;
  tuple?: TermJson[];
  var?: string;
}
interface GoalJson {
  pred: string;
  args: TermJson[];
}
type BodyLitJson = GoalJson | { neg: GoalJson };
interface ClauseJson {
  id: string;
  head: GoalJson;
  body: BodyLitJson[];
  clause_bytes_hex: string;
}
interface ProgramSerdeFile {
  empty_program: { program_bytes_hex: string };
  program: {
    clauses: ClauseJson[];
    canonical_clause_order: string[];
    program_bytes_hex: string;
  };
}

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "program_serde.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/program_serde.json above ${dir}`);
    dir = parent;
  }
}

function loadVectors(): ProgramSerdeFile {
  const file = path.join(repoRoot(), "vectors", "program_serde.json");
  return JSON.parse(fs.readFileSync(file, "utf8")) as ProgramSerdeFile;
}

function hexToBytes(s: string): Uint8Array {
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i += 1) out[i] = parseInt(s.slice(i * 2, i * 2 + 2), 16);
  return out;
}

function toHex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}

function buildTerm(j: TermJson): Term {
  if (j.atom !== undefined) return Term.atom(hexToBytes(j.atom));
  if (j.atom_str !== undefined) return Term.atom(new TextEncoder().encode(j.atom_str));
  if (j.int !== undefined) return Term.fromValue(encodeInt(BigInt(j.int)));
  if (j.tuple !== undefined) return Term.tuple(j.tuple.map(buildTerm));
  if (j.var !== undefined) return Term.var(j.var);
  throw new Error(`unrecognized term shape: ${JSON.stringify(j)}`);
}

function buildGoal(j: GoalJson): Goal {
  return new Goal(Symbol.of(j.pred), j.args.map(buildTerm));
}

function buildBodyLit(j: BodyLitJson): BodyLit {
  if ("neg" in j) return BodyLit.neg(buildGoal(j.neg));
  return BodyLit.pos(buildGoal(j));
}

function buildClause(c: ClauseJson): Clause {
  return new Clause(buildGoal(c.head), c.body.map(buildBodyLit));
}

function buildProgram(clauses: ClauseJson[]): MapProgram {
  const p = new MapProgram();
  for (const c of clauses) p.insert(ClauseId.of(c.id), buildClause(c));
  return p;
}

test("empty program canonical bytes match the pin", () => {
  const vf = loadVectors();
  assert.equal(toHex(programBytes(new MapProgram())), vf.empty_program.program_bytes_hex);
});

test("per-clause account bytes match the pins", () => {
  const vf = loadVectors();
  for (const c of vf.program.clauses) {
    assert.equal(toHex(clauseBytes(buildClause(c))), c.clause_bytes_hex, `clause_bytes for ${c.id}`);
  }
});

test("program canonical bytes match the pin and round-trip", () => {
  const vf = loadVectors();
  assert.equal(vf.program.clauses.length > 0, true, "no program clauses loaded");
  const program = buildProgram(vf.program.clauses);

  // 1. Canonical bytes match the pin (insertion-order-independent encoding).
  assert.equal(toHex(programBytes(program)), vf.program.program_bytes_hex, "program canonical bytes");

  // 2. Round-trip: programFromValue(programToValue(p)) == p (compare per-clause bytes).
  const back = programFromValue(programToValue(program));
  for (const id of vf.program.canonical_clause_order) {
    const want = program.clause(ClauseId.of(id));
    const got = back.clause(ClauseId.of(id));
    assert.notEqual(want, undefined, `original missing ${id}`);
    assert.notEqual(got, undefined, `round-trip missing ${id}`);
    assert.equal(toHex(clauseBytes(got!)), toHex(clauseBytes(want!)), `round-trip clause ${id}`);
  }
  assert.equal(back.size(), program.size(), "round-trip clause count");
});

test("MapProgram.iter matches the canonical clause order (count + order)", () => {
  // Drive the public ordered enumeration (MapProgram.iter / size) over the vector program
  // — built in a deliberately NON-sorted insertion order — and assert the (id) order it
  // yields equals the pinned canonical_clause_order (the same sorted-by-id order the
  // serializer emits and the Rust/Go bindings reproduce). The cross-core proof that the new
  // iteration order is byte-identical tri-core (issue #368).
  const vf = loadVectors();
  const program = buildProgram(vf.program.clauses);

  assert.equal(program.size(), vf.program.clauses.length, "size mismatch");
  const entries = program.iter();
  assert.equal(entries.length, vf.program.canonical_clause_order.length, "iter count mismatch");
  const iterIds = entries.map(([id]) => id.asStr());
  assert.deepEqual(iterIds, vf.program.canonical_clause_order, "iter order must equal canonical order");
  // The clause paired with each id is the one clause(id) returns.
  for (const [id, clause] of entries) {
    const looked = program.clause(id);
    assert.notEqual(looked, undefined, `iter id ${id.asStr()} not found via clause()`);
    assert.equal(toHex(clauseBytes(looked!)), toHex(clauseBytes(clause)), `iter clause ${id.asStr()} differs`);
  }
});

test("MapProgram.iter is insertion-order independent", () => {
  const idsOf = (order: string[]): string[] => {
    const p = new MapProgram();
    for (const id of order) p.insert(ClauseId.of(id), Clause.fact(Goal.of(id, [])));
    return p.iter().map(([id]) => id.asStr());
  };
  const want = ["A", "a", "aa", "m", "z"]; // byte-lex: 'A'(0x41) < 'a'(0x61) < "aa" < 'm' < 'z'
  assert.deepEqual(idsOf(["z", "a", "m", "aa", "A"]), want);
  assert.deepEqual(idsOf(["A", "aa", "m", "z", "a"]), want);
});

test("serialization is insertion-order independent", () => {
  const mk = (order: string[]): MapProgram => {
    const p = new MapProgram();
    for (const id of order) p.insert(ClauseId.of(id), Clause.fact(Goal.of(id, [])));
    return p;
  };
  const a = mk(["z", "a", "m"]);
  const b = mk(["a", "m", "z"]);
  assert.equal(toHex(programBytes(a)), toHex(programBytes(b)));
});

test("programFromValue rejects all five malformed decode modes", () => {
  const enc = (s: string) => new TextEncoder().encode(s);
  const isDecode = (kind: ProgramSerdeDecodeError["detail"]["kind"]) => (e: unknown) =>
    e instanceof ProgramSerdeDecodeError && e.detail.kind === kind;

  // not_a_tuple.
  assert.throws(() => programFromValue(valueAtom(enc("x"))), isDecode("not_a_tuple"));
  // bad_version.
  assert.throws(() => programFromValue(valueTuple([valueAtom(enc("wrong"))])), isDecode("bad_version"));
  // bad_entry (a non-tuple entry).
  assert.throws(
    () => programFromValue(valueTuple([valueAtom(PROGRAM_SERDE_VERSION), valueAtom(enc("bad"))])),
    isDecode("bad_entry"),
  );
  // bad_clause (an entry whose clause value is not a quoted clause term).
  assert.throws(
    () =>
      programFromValue(
        valueTuple([
          valueAtom(PROGRAM_SERDE_VERSION),
          valueTuple([valueAtom(enc("id")), valueAtom(enc("not-a-clause"))]),
        ]),
      ),
    isDecode("bad_clause"),
  );
  // duplicate_clause_id (two entries share an id).
  const one = clauseValue(Clause.fact(Goal.of("p", [])));
  assert.throws(
    () =>
      programFromValue(
        valueTuple([
          valueAtom(PROGRAM_SERDE_VERSION),
          valueTuple([valueAtom(enc("same")), one]),
          valueTuple([valueAtom(enc("same")), one]),
        ]),
      ),
    isDecode("duplicate_clause_id"),
  );
});

test("programToValue rejects a reserved predicate symbol (NEG_TAG collision)", () => {
  // A POSITIVE body literal whose predicate is the reserved NEG_TAG byte 0x00 with exactly
  // one arg would encode byte-identically to a Neg literal — a silent Pos→Neg flip. The
  // encoder MUST reject it (never emit ambiguous bytes). The HEAD is checked too.
  const nulPred = Symbol.of(new Uint8Array([0x00]));
  const reservedArg = Term.atom(new TextEncoder().encode("a"));

  const bodyOffender = new MapProgram();
  bodyOffender.insert(
    ClauseId.of("c1"),
    new Clause(Goal.of("p", []), [BodyLit.pos(new Goal(nulPred, [reservedArg]))]),
  );
  assert.throws(
    () => programToValue(bodyOffender),
    (e: unknown) => e instanceof ProgramSerdeEncodeError && e.clauseId === "c1" && e.predicateHex === "00",
  );
  assert.throws(() => programBytes(bodyOffender), (e: unknown) => e instanceof ProgramSerdeEncodeError);

  const headOffender = new MapProgram();
  headOffender.insert(ClauseId.of("c2"), Clause.fact(new Goal(nulPred, [reservedArg])));
  assert.throws(() => programToValue(headOffender), (e: unknown) => e instanceof ProgramSerdeEncodeError);
});
