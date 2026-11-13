/*
 * TS replay of the cross-core THEORY-DECISION agreement vector vectors/list.json
 * (ADR 0016 ListTheory tri-core). The Rust ListTheory is the decision oracle; this test
 * asserts the TS ListTheory reproduces every pinned outcome byte-for-byte. The SAME file
 * is replayed in Rust (contract/rs/tests/list_vectors.rs) and Go
 * (contract/go/list_vectors_test.go), so a single oracle pins all three cores — the §7
 * dual-conformance byte-parity proof.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt, encodeList } from "@bitspark/ontos-data";

import { GroundLiteral, Symbol, ListTheory, TheoryGround } from "../src/index.js";

// ----- the on-disk vector shape -----

interface ListVectorFile {
  readonly identity: { readonly id: string; readonly version: string; readonly config_digest_hex: string };
  readonly owns: { readonly owned: readonly string[]; readonly not_owned: readonly string[] };
  readonly decisions: readonly ListDecision[];
}

interface ListDecision {
  readonly name: string;
  readonly pred: string;
  readonly args: readonly unknown[];
  readonly outcome: unknown;
}

// loadListVectors finds vectors/list.json by walking up from this test file's directory to
// the repo root, mirroring the Go replay (which walks up from contract/go) and the Rust
// replay (which includes it relative to the crate).
function loadListVectors(): ListVectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "list.json");
    if (fs.existsSync(candidate)) {
      return JSON.parse(fs.readFileSync(candidate, "utf8")) as ListVectorFile;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/list.json above ${dir}`);
    }
    dir = parent;
  }
}

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/list.json (and the Go/Rust replay builders):
//
//   {"atom": "<utf8>"}  -> a bare Atom of those UTF-8 bytes
//   {"int": N}          -> the ontos-data int embedding of N (a Tuple)
//   {"list": [..]}      -> the ontos-data list embedding of the encoded children
//   {"tuple": [..]}     -> a raw Tuple of the encoded children (cons cells / non-lists)
function buildArg(raw: unknown): Value {
  if (typeof raw !== "object" || raw === null) {
    throw new Error(`arg is not an object: ${JSON.stringify(raw)}`);
  }
  const obj = raw as Record<string, unknown>;
  if ("atom" in obj) {
    return atom(new TextEncoder().encode(obj["atom"] as string));
  }
  if ("int" in obj) {
    return encodeInt(BigInt(obj["int"] as number));
  }
  if ("list" in obj) {
    return encodeList((obj["list"] as unknown[]).map(buildArg));
  }
  if ("tuple" in obj) {
    return tuple((obj["tuple"] as unknown[]).map(buildArg));
  }
  throw new Error(`unrecognized arg shape: ${JSON.stringify(raw)}`);
}

// expectOutcome decodes the pinned outcome ("holds" | {"fails": "<code>"}) and asserts the
// actual TheoryGround matches it judgment-for-judgment.
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

test("ListTheory reproduces every pinned vector decision byte-for-byte", () => {
  const vf = loadListVectors();
  const theory = new ListTheory();
  assert.equal(vf.decisions.length > 0, true, "no decision vectors loaded");
  for (const d of vf.decisions) {
    const args = d.args.map(buildArg);
    const got = theory.decideGround(GroundLiteral.of(d.pred, args));
    expectOutcome(d.name, d.outcome, got);
  }
});

test("ListTheory.owns matches the pinned owned / not-owned sets", () => {
  const vf = loadListVectors();
  const theory = new ListTheory();
  for (const name of vf.owns.owned) {
    assert.equal(theory.owns(Symbol.of(name)), true, `owns(${JSON.stringify(name)}) = false, want true`);
  }
  for (const name of vf.owns.not_owned) {
    assert.equal(theory.owns(Symbol.of(name)), false, `owns(${JSON.stringify(name)}) = true, want false`);
  }
});

test("ListTheory.identity matches the pinned component identity", () => {
  const vf = loadListVectors();
  const id = new ListTheory().identity();
  assert.equal(new TextDecoder().decode(id.id), vf.identity.id, "identity id mismatch");
  assert.equal(new TextDecoder().decode(id.version), vf.identity.version, "identity version mismatch");
  assert.equal(id.configDigest.length, 32, "config digest must be 32 bytes");
  assert.equal(
    id.configDigest.every((b) => b === 0),
    true,
    "config digest must be all-zero",
  );
  assert.equal(vf.identity.config_digest_hex, "0".repeat(64), "vector config_digest_hex must be zero");
});
