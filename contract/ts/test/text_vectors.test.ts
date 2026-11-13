/*
 * TS replay of the cross-core THEORY-DECISION agreement vector vectors/text.json
 * (ADR 0016 TextTheory tri-core). The Rust TextTheory is the decision oracle; this
 * test asserts the TS TextTheory reproduces every pinned outcome byte-for-byte. The
 * SAME file is replayed in Rust (contract/rs/tests/text_vectors.rs) and Go
 * (contract/go/text_vectors_test.go), so a single oracle pins all three cores — the §7
 * dual-conformance byte-parity proof.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeText } from "@bitspark/ontos-data";

import { GroundLiteral, Symbol, TextTheory, TheoryGround } from "../src/index.js";

// ----- the on-disk vector shape -----

interface TextVectorFile {
  readonly identity: { readonly id: string; readonly version: string; readonly config_digest_hex: string };
  readonly owns: { readonly owned: readonly string[]; readonly not_owned: readonly string[] };
  readonly decisions: readonly TextDecision[];
}

interface TextDecision {
  readonly name: string;
  readonly pred: string;
  readonly args: readonly unknown[];
  readonly outcome: unknown;
}

// loadTextVectors finds vectors/text.json by walking up from this test file's directory
// to the repo root, mirroring the Go replay (which walks up from contract/go) and the
// Rust replay (which includes it relative to the crate).
function loadTextVectors(): TextVectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "text.json");
    if (fs.existsSync(candidate)) {
      return JSON.parse(fs.readFileSync(candidate, "utf8")) as TextVectorFile;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/text.json above ${dir}`);
    }
    dir = parent;
  }
}

const utf8 = new TextEncoder();

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/text.json (and the Go/Rust replay builders):
//
//   {"text": "<s>"}            -> the ontos-data utf8-text embedding (a Tuple)
//   {"atom": "<utf8>"}         -> a bare Atom of those UTF-8 bytes (the oracle's path)
//   {"tuple": [..]}            -> a raw Tuple of the encoded children
function buildArg(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) {
    throw new Error(`arg is not an object: ${JSON.stringify(raw)}`);
  }
  const obj = raw as Record<string, unknown>;
  if ("text" in obj) {
    return encodeText(obj["text"] as string);
  }
  if ("atom" in obj) {
    return atom(utf8.encode(obj["atom"] as string));
  }
  if ("tuple" in obj) {
    return tuple((obj["tuple"] as unknown[]).map(buildArg));
  }
  throw new Error(`unrecognized arg shape: ${JSON.stringify(raw)}`);
}

// expectOutcome decodes the pinned outcome ("holds" | {"fails": "<code>"}) and asserts
// the actual TheoryGround matches it judgment-for-judgment.
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

// ----- the replay -----

test("TextTheory reproduces every pinned vector decision byte-for-byte", () => {
  const vf = loadTextVectors();
  const theory = new TextTheory();
  assert.equal(vf.decisions.length > 0, true, "no decision vectors loaded");
  for (const d of vf.decisions) {
    const args = d.args.map(buildArg);
    const got = theory.decideGround(GroundLiteral.of(d.pred, args));
    expectOutcome(d.name, d.outcome, got);
  }
});

test("TextTheory.owns matches the pinned owned / not-owned sets", () => {
  const vf = loadTextVectors();
  const theory = new TextTheory();
  for (const name of vf.owns.owned) {
    assert.equal(theory.owns(Symbol.of(name)), true, `owns(${JSON.stringify(name)}) = false, want true`);
  }
  for (const name of vf.owns.not_owned) {
    assert.equal(theory.owns(Symbol.of(name)), false, `owns(${JSON.stringify(name)}) = true, want false`);
  }
});

test("TextTheory.identity matches the pinned component identity", () => {
  const vf = loadTextVectors();
  const id = new TextTheory().identity();
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
