/*
 * TS replay of the cross-core THEORY-DECISION agreement vector vectors/arithmetic.json
 * (issue #95 / TS sibling #154). The Rust ArithmeticTheory is the decision oracle;
 * this test asserts the TS ArithmeticTheory reproduces every pinned outcome
 * byte-for-byte. The SAME file is replayed in Rust (core/rs/tests/arithmetic_vectors.rs)
 * and Go (contract/go/arithmetic_vectors_test.go), so a single oracle pins all three
 * cores — the byte-parity proof the issue requires.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { Atom, Tuple, atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeDecimal, encodeInt, encodeText } from "@bitspark/ontos-data";
import { encode } from "@bitspark/ontos-codec";

import {
  ArithmeticTheory,
  BigDecimal,
  GroundLiteral,
  Symbol,
  type TheoryGround,
} from "../src/index.js";

// ----- the on-disk vector shape -----

interface ArithVectorFile {
  readonly identity: { readonly id: string; readonly version: string; readonly config_digest_hex: string };
  readonly owns: { readonly owned: readonly string[]; readonly not_owned: readonly string[] };
  readonly decisions: readonly ArithDecision[];
  /** #2679: the literal parser against the value domain. */
  readonly decimal_spellings: {
    readonly rows: readonly {
      readonly name: string;
      readonly prefix: string;
      readonly zeros: number | bigint;
      readonly suffix: string;
      readonly parses: readonly [number | bigint, number | bigint] | null;
    }[];
  };
}

interface ArithDecision {
  readonly name: string;
  readonly pred: string;
  readonly args: readonly unknown[];
  readonly outcome: unknown;
}

// loadArithVectors finds vectors/arithmetic.json by walking up from this test file's
// directory to the repo root, mirroring how the Go replay walks up from contract/go
// and the Rust replay includes it relative to the crate.
function loadArithVectors(): ArithVectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "arithmetic.json");
    if (fs.existsSync(candidate)) {
      const text = fs.readFileSync(candidate, "utf8");
      // Integers in the vector (e.g. i64::MAX = 9223372036854775807) exceed JS
      // Number.MAX_SAFE_INTEGER, so a plain JSON.parse would silently round them.
      // Recover each integer literal losslessly from its source text as a bigint
      // (the JSON source-text reviver; CI + dev are Node 24). `context` is typed
      // optional so the reviver stays assignable to the 2-arg reviver type.
      const reviver = (_key: string, value: unknown, context?: { source: string }): unknown => {
        if (typeof value === "number" && typeof context?.source === "string" && /^-?\d+$/.test(context.source)) {
          return BigInt(context.source);
        }
        return value;
      };
      return JSON.parse(text, reviver) as ArithVectorFile;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/arithmetic.json above ${dir}`);
    }
    dir = parent;
  }
}

const utf8 = new TextEncoder();

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/arithmetic.json (and the Go/Rust replay builders):
//
//   {"int": N}                 -> the ontos-data int embedding of N
//   {"bigint": "<digits>"}     -> the int embedding of a value beyond JSON int range
//   {"decimal": "<d.dddd>"}    -> the ontos-data decimal embedding of that decimal literal (#331)
//   {"text": "<s>"}            -> the ontos-data utf8-text embedding
//   {"atom": "<utf8>"}         -> a bare Atom of those UTF-8 bytes
//   {"op": "<op>", "args": []} -> an operator compound Tuple(Atom(op), arg..)
//   {"tuple": [..]}            -> a raw Tuple of the encoded children
function buildArg(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) {
    throw new Error(`arg is not an object: ${JSON.stringify(raw)}`);
  }
  const obj = raw as Record<string, unknown>;
  if ("int" in obj) {
    return encodeInt(BigInt(obj["int"] as number | bigint));
  }
  if ("bigint" in obj) {
    return encodeInt(BigInt(obj["bigint"] as string));
  }
  if ("decimal" in obj) {
    const d = BigDecimal.fromString(obj["decimal"] as string);
    if (d === undefined) {
      throw new Error(`decimal ${JSON.stringify(obj["decimal"])} is not a decimal literal`);
    }
    return d.toTerm();
  }
  if ("text" in obj) {
    return encodeText(obj["text"] as string);
  }
  if ("atom" in obj) {
    return atom(utf8.encode(obj["atom"] as string));
  }
  if ("op" in obj) {
    const args = (obj["args"] as unknown[]) ?? [];
    return tuple([atom(utf8.encode(obj["op"] as string)), ...args.map(buildArg)]);
  }
  if ("tuple" in obj) {
    return tuple((obj["tuple"] as unknown[]).map(buildArg));
  }
  throw new Error(`unrecognized arg shape: ${JSON.stringify(raw)}`);
}

// expectOutcome decodes the pinned outcome ("holds" | {"fails": "<code>"} | {"not_completed":
// "<kind>"}, #3126) and asserts the ground verdict matches it judgment-for-judgment.
function expectOutcome(name: string, raw: unknown, got: TheoryGround): void {
  if (typeof raw === "string") {
    assert.equal(raw, "holds", `${name}: unknown string outcome ${JSON.stringify(raw)}`);
    assert.equal(got.kind === "completed" && got.value.kind === "holds", true, `${name}: want Holds, got ${JSON.stringify(got)}`);
    return;
  }
  const notCompleted = (raw as { not_completed?: unknown })?.not_completed;
  if (typeof notCompleted === "string") {
    assert.equal(
      got.kind === "not_completed" && got.cause.kind === notCompleted,
      true,
      `${name}: want NotCompleted(${notCompleted}), got ${JSON.stringify(got)}`,
    );
    return;
  }
  const fails = (raw as { fails?: unknown })?.fails;
  assert.equal(
    typeof fails === "string" && fails.length > 0,
    true,
    `${name}: outcome is none of "holds", {"fails": code}, {"not_completed": kind}: ${JSON.stringify(raw)}`,
  );
  assert.equal(
    got.kind === "completed" && got.value.kind === "fails",
    true,
    `${name}: want Fails{${String(fails)}}, got ${JSON.stringify(got)}`,
  );
  if (got.kind === "completed" && got.value.kind === "fails") {
    assert.equal(got.value.code, fails, `${name}: want fail code ${String(fails)}, got ${got.value.code}`);
  }
}

// ----- the replay -----

test("ArithmeticTheory reproduces every pinned vector decision byte-for-byte", () => {
  const vf = loadArithVectors();
  const theory = new ArithmeticTheory();
  assert.equal(vf.decisions.length > 0, true, "no decision vectors loaded");
  for (const d of vf.decisions) {
    const args = d.args.map(buildArg);
    const atom = GroundLiteral.of(d.pred, args);
    expectOutcome(d.name, d.outcome, theory.decideGround(atom));
  }
});

test("ArithmeticTheory.owns matches the pinned owned / not-owned sets", () => {
  const vf = loadArithVectors();
  const theory = new ArithmeticTheory();
  for (const name of vf.owns.owned) {
    assert.equal(theory.owns(Symbol.of(name)), true, `owns(${JSON.stringify(name)}) = false, want true`);
  }
  for (const name of vf.owns.not_owned) {
    assert.equal(theory.owns(Symbol.of(name)), false, `owns(${JSON.stringify(name)}) = true, want false`);
  }
});

test("ArithmeticTheory.identity matches the pinned component identity", () => {
  const vf = loadArithVectors();
  const id = new ArithmeticTheory().identity();
  assert.equal(new TextDecoder().decode(id.id), vf.identity.id, "identity id mismatch");
  assert.equal(new TextDecoder().decode(id.version), vf.identity.version, "identity version mismatch");
  assert.equal(id.configDigest.length, 32, "config digest must be 32 bytes");
  assert.equal(
    id.configDigest.every((b) => b === 0),
    true,
    "config digest must be all-zero",
  );
  // the vector pins the zero digest as 64 hex zeros
  assert.equal(vf.identity.config_digest_hex, "0".repeat(64), "vector config_digest_hex must be zero");
});

// #2679 (seat:caa's ruling (a)): BigDecimal.fromString returns through the one limit-checked
// constructor, so a spelling whose VALUE lies outside the domain is refused and one at the bound
// parses. The spellings are 65 KB, so the vector carries their recipe.
test("#2679: the decimal-literal parser refuses a spelling outside the value domain", () => {
  const rows = loadArithVectors().decimal_spellings.rows;
  assert.equal(rows.length, 5, "anti-vacuity: the spelling rows");
  const hex = (v: Value): string => Buffer.from(encode(v)).toString("hex");
  for (const row of rows) {
    // The loader reads JSON integers as bigint, so the count is converted explicitly.
    const got = BigDecimal.fromString(row.prefix + "0".repeat(Number(row.zeros)) + row.suffix);
    if (row.parses === null) {
      assert.equal(got, undefined, `${row.name}: parsed, want refused`);
      continue;
    }
    assert.ok(got !== undefined, `${row.name}: refused, want a value`);
    assert.equal(hex(got.toTerm()), hex(encodeDecimal(BigInt(row.parses[0]), BigInt(row.parses[1]))), row.name);
  }
});
