/*
 * TS replay of the cross-core THEORY-DECISION agreement vector vectors/term.json
 * (ADR 0016 TermTheory tri-core). The Rust TermTheory is the decision oracle; this test
 * asserts the TS TermTheory reproduces every pinned outcome byte-for-byte. The SAME file
 * is replayed in Rust (contract/rs/tests/term_vectors.rs) and Go
 * (contract/go/term_vectors_test.go), so a single oracle pins all three cores — the §7
 * dual-conformance byte-parity proof.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";

import { BigDecimal, GroundLiteral, Symbol, TermTheory, type TheoryOutcome } from "../src/index.js";

// ----- the on-disk vector shape -----

interface TermVectorFile {
  readonly identity: { readonly id: string; readonly version: string; readonly config_digest_hex: string };
  readonly owns: { readonly owned: readonly string[]; readonly not_owned: readonly string[] };
  readonly decisions: readonly TermDecision[];
}

interface TermDecision {
  readonly name: string;
  readonly pred: string;
  readonly args: readonly unknown[];
  readonly outcome: unknown;
}

// loadTermVectors finds vectors/term.json by walking up from this test file's directory to
// the repo root, mirroring the Go replay (which walks up from contract/go) and the Rust
// replay (which includes it relative to the crate).
function loadTermVectors(): TermVectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "term.json");
    if (fs.existsSync(candidate)) {
      return JSON.parse(fs.readFileSync(candidate, "utf8")) as TermVectorFile;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`could not locate vectors/term.json above ${dir}`);
    }
    dir = parent;
  }
}

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/term.json (and the Go/Rust replay builders):
//
//   {"atom": "<utf8>"}      -> a bare Atom of those UTF-8 bytes
//   {"int": N}              -> the ontos-data int embedding of N (a Tuple)
//   {"decimal": "<d.dddd>"} -> the ontos-data decimal embedding of that decimal literal (#331)
//   {"tuple": [..]}         -> a raw Tuple of the encoded children
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
  if ("decimal" in obj) {
    const d = BigDecimal.fromString(obj["decimal"] as string);
    if (d === undefined) {
      throw new Error(`decimal ${JSON.stringify(obj["decimal"])} is not a decimal literal`);
    }
    return d.toTerm();
  }
  if ("tuple" in obj) {
    return tuple((obj["tuple"] as unknown[]).map(buildArg));
  }
  throw new Error(`unrecognized arg shape: ${JSON.stringify(raw)}`);
}

// expectOutcome decodes the pinned outcome ("holds" | {"fails": "<code>"}) and asserts the
// actual TheoryOutcome matches it judgment-for-judgment.
function expectOutcome(name: string, raw: unknown, got: TheoryOutcome): void {
  if (typeof raw === "string") {
    assert.equal(raw, "holds", `${name}: unknown string outcome ${JSON.stringify(raw)}`);
    assert.equal(got.kind, "holds", `${name}: want Holds, got ${JSON.stringify(got)}`);
    return;
  }
  const fails = (raw as { fails?: unknown })?.fails;
  assert.equal(
    typeof fails === "string" && fails.length > 0,
    true,
    `${name}: outcome is neither "holds" nor {"fails": code}: ${JSON.stringify(raw)}`,
  );
  assert.equal(got.kind, "fails", `${name}: want Fails{${String(fails)}}, got ${JSON.stringify(got)}`);
  if (got.kind === "fails") {
    assert.equal(got.code, fails, `${name}: want fail code ${String(fails)}, got ${got.code}`);
  }
}

// ----- the replay -----

test("TermTheory reproduces every pinned vector decision byte-for-byte", () => {
  const vf = loadTermVectors();
  const theory = new TermTheory();
  assert.equal(vf.decisions.length > 0, true, "no decision vectors loaded");
  for (const d of vf.decisions) {
    const args = d.args.map(buildArg);
    const got = theory.decide(GroundLiteral.of(d.pred, args));
    expectOutcome(d.name, d.outcome, got);
  }
});

test("TermTheory.owns matches the pinned owned / not-owned sets", () => {
  const vf = loadTermVectors();
  const theory = new TermTheory();
  for (const name of vf.owns.owned) {
    assert.equal(theory.owns(Symbol.of(name)), true, `owns(${JSON.stringify(name)}) = false, want true`);
  }
  for (const name of vf.owns.not_owned) {
    assert.equal(theory.owns(Symbol.of(name)), false, `owns(${JSON.stringify(name)}) = true, want false`);
  }
});

test("TermTheory.identity matches the pinned component identity", () => {
  const vf = loadTermVectors();
  const id = new TermTheory().identity();
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
