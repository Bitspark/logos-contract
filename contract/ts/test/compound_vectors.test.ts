/*
 * TS replay of the cross-core agreement vector vectors/compound.json (CompoundTheory
 * over [arithmetic, text]). The Rust CompoundTheory is the oracle; this asserts the TS
 * CompoundTheory reproduces the routed decisions, the owns union, AND the identity
 * config-digest byte-for-byte. The SAME file is replayed in Rust
 * (contract/rs/tests/compound_vectors.rs) and Go (contract/go/compound_vectors_test.go),
 * so one oracle pins the compound's routing + digest scheme across all three cores.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt, encodeText } from "@bitspark/ontos-data";

import {
  ArithmeticTheory,
  CompoundTheory,
  GroundLiteral,
  Symbol,
  type Theory,
  TheoryGround,
  TextTheory,
} from "../src/index.js";

// ----- the on-disk vector shape (the arithmetic/text shape + a `members` list) -----

interface CompoundVectorFile {
  readonly members: readonly string[];
  readonly identity: { readonly id: string; readonly version: string; readonly config_digest_hex: string };
  readonly owns: { readonly owned: readonly string[]; readonly not_owned: readonly string[] };
  readonly decisions: readonly CompoundDecision[];
}

interface CompoundDecision {
  readonly name: string;
  readonly pred: string;
  readonly args: readonly unknown[];
  readonly outcome: unknown;
}

function loadCompoundVectors(): CompoundVectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "compound.json");
    if (fs.existsSync(candidate)) {
      return JSON.parse(fs.readFileSync(candidate, "utf8")) as CompoundVectorFile;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/compound.json above ${dir}`);
    }
    dir = parent;
  }
}

const utf8 = new TextEncoder();

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching vectors/compound.json (and the Go/Rust replay builders): {int}, {atom},
// {op}, {text}, {tuple}.
function buildArg(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) {
    throw new Error(`arg is not an object: ${JSON.stringify(raw)}`);
  }
  const obj = raw as Record<string, unknown>;
  if ("int" in obj) {
    return encodeInt(BigInt(obj["int"] as number | bigint));
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

// buildCompound builds the CompoundTheory the vector names.
function buildCompound(members: readonly string[]): CompoundTheory {
  const theories: Theory[] = members.map((m) => {
    switch (m) {
      case "arithmetic":
        return new ArithmeticTheory();
      case "text":
        return new TextTheory();
      default:
        throw new Error(`unknown member theory ${JSON.stringify(m)}`);
    }
  });
  return new CompoundTheory(theories);
}

function expectOutcome(name: string, raw: unknown, got: TheoryGround): void {
  if (typeof raw === "string") {
    assert.equal(raw, "holds", `${name}: unknown string outcome ${JSON.stringify(raw)}`);
    assert.deepEqual(got, TheoryGround.holds(), `${name}: want Holds, got ${JSON.stringify(got)}`);
    return;
  }
  const fails = (raw as { fails?: unknown })?.fails;
  assert.equal(
    typeof fails === "string" && fails.length > 0,
    true,
    `${name}: outcome is neither "holds" nor {"fails": code}: ${JSON.stringify(raw)}`,
  );
  assert.deepEqual(
    got,
    TheoryGround.fails(String(fails)),
    `${name}: want Fails{${String(fails)}}, got ${JSON.stringify(got)}`,
  );
}

function toHex(bytes: Uint8Array): string {
  let s = "";
  for (const b of bytes) s += b.toString(16).padStart(2, "0");
  return s;
}

// ----- the replay -----

test("CompoundTheory routes every pinned vector decision to the owning member", () => {
  const vf = loadCompoundVectors();
  const theory = buildCompound(vf.members);
  assert.equal(vf.decisions.length > 0, true, "no decision vectors loaded");
  for (const d of vf.decisions) {
    const args = d.args.map(buildArg);
    const got = theory.decideGround(GroundLiteral.of(d.pred, args));
    expectOutcome(d.name, d.outcome, got);
  }
});

test("CompoundTheory.owns is the union of the members' predicates", () => {
  const vf = loadCompoundVectors();
  const theory = buildCompound(vf.members);
  for (const name of vf.owns.owned) {
    assert.equal(theory.owns(Symbol.of(name)), true, `owns(${JSON.stringify(name)}) = false, want true`);
  }
  for (const name of vf.owns.not_owned) {
    assert.equal(theory.owns(Symbol.of(name)), false, `owns(${JSON.stringify(name)}) = true, want false`);
  }
});

test("CompoundTheory.identity matches the pinned membership digest", () => {
  const vf = loadCompoundVectors();
  const id = buildCompound(vf.members).identity();
  assert.equal(new TextDecoder().decode(id.id), vf.identity.id, "identity id mismatch");
  assert.equal(new TextDecoder().decode(id.version), vf.identity.version, "identity version mismatch");
  assert.equal(id.configDigest.length, 32, "config digest must be 32 bytes");
  assert.equal(
    toHex(id.configDigest),
    vf.identity.config_digest_hex,
    "identity config_digest must match the length-prefixed SHA-256 over the ordered member identities",
  );
});
