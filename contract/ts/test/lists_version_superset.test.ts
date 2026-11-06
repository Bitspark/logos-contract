/*
 * TS mirror of the Shelf-B lists cross-version BYTE-SUPERSET invariant (issue #494).
 *
 * ADR 0016 freezes Shelf B per (name@version) and each lists bundle pledges it
 * "RE-INCLUDES every prior relation BYTE-IDENTICALLY". That pledge was prose-only: the
 * shipped-bundle tests load each lists@1.{0,1,2}.0 INDEPENDENTLY and verify only each
 * file's own per-file program_digest, so editing a shared clause in a newer bundle (and
 * re-pinning its digest) would silently break the superset and still pass.
 *
 * This test makes it a theorem: it loads each adjacent pair through the REAL loadPrelude
 * (which recomputes + verifies the program_digest, so a tampered manifest is refused
 * before the comparison) and asserts the older bundle's clause-id set is a subset of the
 * newer's. The canonical clause id is a hash of the frozen account-codec clause bytes, so
 * id-subset already implies byte-identical re-inclusion; id-subset + the existing per-file
 * digest pins ⟹ the newer bundle is a byte-exact extension of the older. (The Rust mirror
 * conformance/rs/tests/lists_version_superset.rs additionally compares the clause body.)
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { loadPrelude } from "../src/index.js";

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "prelude.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/prelude.json above ${dir}`);
    dir = parent;
  }
}

function loadListsBundleIds(root: string, version: string): Set<string> {
  const raw = fs.readFileSync(path.join(root, "prelude", `lists@${version}.json`), "utf8");
  const bundle = loadPrelude(raw);
  return new Set(bundle.clauses.map((c) => c.id.asStr()));
}

function assertIdSubset(older: Set<string>, newer: Set<string>, olderLabel: string, newerLabel: string): void {
  assert.ok(
    older.size <= newer.size,
    `${newerLabel} (${newer.size}) has fewer clauses than ${olderLabel} (${older.size}) — not a superset`,
  );
  for (const id of older) {
    assert.ok(
      newer.has(id),
      `byte-superset broken: clause ${id} of ${olderLabel} is ABSENT from ${newerLabel} (a prior relation was dropped or its bytes changed)`,
    );
  }
}

test("lists@1.0.0 ⊆ 1.1.0 ⊆ 1.2.0 form a byte-identical superset chain", () => {
  const root = repoRoot();
  const v100 = loadListsBundleIds(root, "1.0.0");
  const v110 = loadListsBundleIds(root, "1.1.0");
  const v120 = loadListsBundleIds(root, "1.2.0");

  // The cardinalities the issue verified at HEAD: 4 ⊂ 14 ⊂ 19.
  assert.equal(v100.size, 4, "lists@1.0.0 clause count");
  assert.equal(v110.size, 14, "lists@1.1.0 clause count");
  assert.equal(v120.size, 19, "lists@1.2.0 clause count");

  assertIdSubset(v100, v110, "lists@1.0.0", "lists@1.1.0");
  assertIdSubset(v110, v120, "lists@1.1.0", "lists@1.2.0");
  assertIdSubset(v100, v120, "lists@1.0.0", "lists@1.2.0");
});
