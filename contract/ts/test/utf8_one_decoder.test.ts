// #2682: ts turns bytes into text in ONE place (src/utf8.ts), and this guard keeps it that way.
//
// A platform `TextDecoder` strips a leading UTF-8 BOM by default, so ts read different text from rs
// and go wherever a site built its own decoder: a BOM-prefixed tag matched a known tag, two subst
// keys collided, a BOM-prefixed atom had a shorter name. The fix routes every site through
// UTF8_STRICT / UTF8_LOSSY. This test fails on any `new TextDecoder(` elsewhere in contract/ts/src or
// kernel/ts/src, so a new site cannot bring the platform default back unobserved.
//
// ⛔ NO EXCLUSION. #2682 shipped this guard with exactly one, `kernel/ts/src/wasm/` (the #2361
// carve-out, whose sites needed a pre-merge guest refresh), and #2690 routed those sites and
// emptied the list. The list is kept, capped at ONE and required to name an open follow-up, so a
// future carve-out can take the same two-step path; a second exclusion, or one that no longer
// matches a site, fails this test.

import { strict as assert } from "node:assert";
import fs from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { UTF8_LOSSY, UTF8_STRICT } from "../src/utf8.js";

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "derivation_wire.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate the repo root above ${dir}`);
    dir = parent;
  }
}

/** The ONE module allowed to construct a decoder. */
const HOME = "contract/ts/src/utf8.ts";
/** Allowed exclusions, each naming its follow-up issue. At most one (#2682's scope ruling). */
const EXCLUSIONS: readonly { dir: string; issue: string }[] = [];
const ROOTS = ["contract/ts/src"];

function tsFiles(dir: string): string[] {
  const out: string[] = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) out.push(...tsFiles(p));
    else if (e.name.endsWith(".ts")) out.push(p);
  }
  return out;
}

/** Every `new TextDecoder(` site under the roots, as repo-relative `path:line`. */
function sites(root: string): string[] {
  const hits: string[] = [];
  for (const r of ROOTS) {
    for (const f of tsFiles(path.join(root, r))) {
      const rel = path.relative(root, f).split(path.sep).join("/");
      fs.readFileSync(f, "utf8")
        .split("\n")
        .forEach((line, i) => {
          if (line.includes("new TextDecoder(")) hits.push(`${rel}:${i + 1}`);
        });
    }
  }
  return hits;
}

test("#2682: no `new TextDecoder(` outside src/utf8.ts, save ONE excluded directory with an open follow-up", () => {
  const root = repoRoot();
  const all = sites(root);
  // POSITIVE CONTROL, and it is fatal: the scan must find utf8.ts's own two decoders, or it read
  // nothing and every assertion below would pass on an empty set.
  assert.equal(
    all.filter((s) => s.startsWith(`${HOME}:`)).length,
    2,
    `the scan did not find ${HOME}'s two decoders; it is not reading the tree (found ${all.length} sites)`,
  );
  assert.ok(EXCLUSIONS.length <= 1, `at most ONE exclusion is allowed (#2682's scope ruling); found ${EXCLUSIONS.length}`);
  for (const ex of EXCLUSIONS) {
    assert.match(ex.issue, /^#\d+$/, `exclusion ${ex.dir} must name its follow-up issue`);
    assert.ok(
      all.some((s) => s.startsWith(ex.dir)),
      `exclusion ${ex.dir} (${ex.issue}) matches no site any more: its sites were routed, so DELETE the exclusion`,
    );
  }
  const offenders = all.filter((s) => !s.startsWith(`${HOME}:`) && !EXCLUSIONS.some((ex) => s.startsWith(ex.dir)));
  assert.deepEqual(offenders, [], "decode through UTF8_STRICT / UTF8_LOSSY (src/utf8.ts), never a new TextDecoder");
});

test("#2682: the shared decoders KEEP a leading BOM, as rs and go read exact bytes", () => {
  const bomA = Uint8Array.of(0xef, 0xbb, 0xbf, 0x61);
  // Control: the platform default strips it, which is the behaviour this module exists to refuse.
  assert.equal([...new TextDecoder().decode(bomA)].length, 1, "control: a default TextDecoder strips the BOM");
  assert.equal(UTF8_STRICT.decode(bomA), "﻿a");
  assert.equal(UTF8_LOSSY.decode(bomA), "﻿a");
  assert.throws(() => UTF8_STRICT.decode(Uint8Array.of(0xff)), TypeError, "strict refuses ill-formed UTF-8");
  assert.equal(UTF8_LOSSY.decode(Uint8Array.of(0xff)), "�", "lossy replaces ill-formed UTF-8 with U+FFFD");
});
