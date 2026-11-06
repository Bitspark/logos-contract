/*
 * #3057: the injective escape is Symbol's canonical rendering, so it lives beside Symbol in the
 * contract tier (seat:caa's ruling on #2984, site 3). This replays vectors/identity_bytes.json's
 * escaped_name section against the contract's own escapedName, so the contract tier can render a
 * name injectively without the kernel. kernel/ts/test/identity_bytes_2763.test.ts replays the same
 * rows through the kernel's re-export. The same rows are replayed at the contract tier in rs
 * (contract/rs/tests/escaped_name_3057.rs) and go (contract/go/escaped_name_3057_test.go).
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { escapedName } from "../src/index.js";

interface EscapeCase {
  readonly name: string;
  readonly bytes_hex: string;
  readonly rendered: string;
  readonly collides_with?: string;
}

// Walks up from this test file's directory to the repo root, mirroring loadTextVectors.
function loadEscapeCases(): readonly EscapeCase[] {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "identity_bytes.json");
    if (fs.existsSync(candidate)) {
      const file = JSON.parse(fs.readFileSync(candidate, "utf8")) as { escaped_name: { cases: readonly EscapeCase[] } };
      return file.escaped_name.cases;
    }
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/identity_bytes.json above ${dir}`);
    dir = parent;
  }
}

function unhex(s: string): Uint8Array {
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(s.slice(2 * i, 2 * i + 2), 16);
  return out;
}

test("#3057 vector [escaped_name] at the contract tier: every row renders exactly, and no pair collides", () => {
  const cases = loadEscapeCases();
  assert.ok(cases.length > 0, "the escaped_name section carries rows");
  const rendered = new Map<string, string>();
  for (const c of cases) {
    const got = escapedName(unhex(c.bytes_hex));
    assert.equal(got, c.rendered, `[escaped_name/${c.name}] rendered differently`);
    rendered.set(c.name, got);
  }
  for (const c of cases) {
    if (c.collides_with === undefined) continue;
    assert.notEqual(rendered.get(c.name), rendered.get(c.collides_with), `[escaped_name/${c.name}] renders as ${c.collides_with} does`);
  }
});
