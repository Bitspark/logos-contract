// TS replay of vectors/reify.json (#3102): §2a's reify decision, pinned as a shared fact.
//
// Before #3102 go's Reify accepted a quoted variable whose name is not UTF-8 (Tuple[Atom(0x02),
// Atom(0xFF)] reified to a variable), while rs and ts refused it. The three cores decode one
// untrusted input, so their agreement is replayed from one hand-authored file (the same file
// contract/rs/tests/reify_vectors.rs and contract/go/reify_vectors_test.go replay) rather than
// claimed in a comment.

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { decode, encode } from "@bitspark/ontos-codec";
import { atom as valueAtom, tuple as valueTuple } from "@bitspark/ontos-core";

import { Term, TermAtom, TermTuple, TermVar, VarId, VarIdError, quote, reify } from "../src/index.js";

interface Row {
  name: string;
  value_hex: string;
  term?: unknown;
}

type ReifyFile = Record<string, unknown>;

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "reify.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/reify.json above ${dir}`);
    dir = parent;
  }
}

function vectors(): ReifyFile {
  return JSON.parse(fs.readFileSync(path.join(repoRoot(), "vectors", "reify.json"), "utf8")) as ReifyFile;
}

function section(file: ReifyFile, key: string): Row[] {
  const rows = file[key];
  assert.ok(Array.isArray(rows), `section ${key} is not an array`);
  assert.ok(rows.length > 0, `section ${key} is empty: a replay over no rows proves nothing`);
  return rows as Row[];
}

function hexToBytes(hex: string): Uint8Array {
  return new Uint8Array(Buffer.from(hex, "hex"));
}

/** The term a row describes: {"var": name}, {"atom_hex": bytes} or {"tuple": [terms]}. */
function described(name: string, desc: unknown): Term {
  assert.ok(desc !== null && typeof desc === "object" && !Array.isArray(desc), `${name}: a term is an object`);
  const entries = Object.entries(desc as Record<string, unknown>);
  assert.equal(entries.length, 1, `${name}: a term is an object with one key`);
  const [kind, body] = entries[0]!;
  switch (kind) {
    case "var":
      assert.equal(typeof body, "string", `${name}: var is a string`);
      return new TermVar(new VarId(body as string));
    case "atom_hex":
      assert.equal(typeof body, "string", `${name}: atom_hex is a string`);
      return new TermAtom(hexToBytes(body as string));
    case "tuple":
      assert.ok(Array.isArray(body), `${name}: tuple is an array`);
      return new TermTuple((body as unknown[]).map((kid) => described(name, kid)));
    default:
      throw new Error(`${name}: unknown term kind ${kind}`);
  }
}

test("vectors/reify.json: every row reifies, or is refused, as the file says (#3102)", () => {
  const file = vectors();
  for (const key of Object.keys(file)) {
    assert.ok(
      ["spec", "note", "refused", "reifies", "var_names"].includes(key),
      `vectors/reify.json carries a section ${key} this replay has no reader for`,
    );
  }

  const failures: string[] = [];
  for (const row of section(file, "refused")) {
    const got = reify(decode(hexToBytes(row.value_hex)));
    if (got !== undefined) {
      failures.push(`refused/${row.name}: reify ACCEPTED it; the value is outside quote's image`);
    }
  }
  for (const row of section(file, "reifies")) {
    const raw = hexToBytes(row.value_hex);
    const got = reify(decode(raw));
    if (got === undefined) {
      failures.push(`reifies/${row.name}: reify refused a value in quote's image`);
      continue;
    }
    if (!got.equals(described(row.name, row.term))) {
      failures.push(`reifies/${row.name}: reify gave a different term`);
    }
    const again = Buffer.from(encode(quote(got))).toString("hex");
    if (again !== row.value_hex) {
      failures.push(`reifies/${row.name}: quote re-encodes to ${again}, want ${row.value_hex}`);
    }
  }
  failures.push(...replayVarNames3115(file));
  assert.deepEqual(failures, []);
});

interface VarNameRow {
  name: string;
  name_hex: string;
  in_domain: boolean;
  utf16: boolean;
}

/**
 * Generalized UTF-8 (WTF-8) to a JS string: UTF-8's rules, except that a surrogate code point may
 * appear as three bytes, as long as a high surrogate is not directly followed by a low one (that
 * pair has to be the four-byte form). `undefined` when the bytes are not WTF-8, so no JS string
 * holds that name.
 */
function wtf8ToString(b: Uint8Array): string | undefined {
  let out = "";
  let prevHigh = false;
  for (let i = 0; i < b.length; ) {
    const b0 = b[i]!;
    let n: number;
    let cp: number;
    if (b0 < 0x80) [n, cp] = [1, b0];
    else if (b0 >= 0xc2 && b0 <= 0xdf) [n, cp] = [2, b0 & 0x1f];
    else if (b0 >= 0xe0 && b0 <= 0xef) [n, cp] = [3, b0 & 0x0f];
    else if (b0 >= 0xf0 && b0 <= 0xf4) [n, cp] = [4, b0 & 0x07];
    else return undefined;
    if (i + n > b.length) return undefined;
    for (let k = 1; k < n; k += 1) {
      const c = b[i + k]!;
      if ((c & 0xc0) !== 0x80) return undefined;
      cp = (cp << 6) | (c & 0x3f);
    }
    if ((n === 3 && cp < 0x800) || (n === 4 && (cp < 0x10000 || cp > 0x10ffff))) return undefined;
    const isHigh = cp >= 0xd800 && cp <= 0xdbff;
    const isLow = cp >= 0xdc00 && cp <= 0xdfff;
    if (isLow && prevHigh) return undefined;
    out += String.fromCodePoint(cp);
    prevHigh = isHigh;
    i += n;
  }
  return out;
}

/**
 * `var_names` (#3115): each row's name as WTF-8 bytes. Where those bytes are WTF-8, ts holds the
 * name as a string, and `new VarId`, `VarId.of` and `Term.var` must accept it iff `in_domain`,
 * throwing a `VarIdError` that names it otherwise. An accepted name round-trips, and quote writes
 * exactly `name_hex`. Where they are not WTF-8 (`utf16` false), no ts string holds the name.
 */
function replayVarNames3115(file: ReifyFile): string[] {
  const rows = file["var_names"];
  assert.ok(Array.isArray(rows) && rows.length > 0, "var_names is an empty or missing section");
  const failures: string[] = [];
  for (const row of rows as VarNameRow[]) {
    const s = wtf8ToString(hexToBytes(row.name_hex));
    if ((s !== undefined) !== row.utf16) {
      failures.push(`var_names/${row.name}: the row says utf16=${row.utf16}, but the bytes' WTF-8 reading says ${s !== undefined}`);
      continue;
    }
    if (s === undefined) continue; // unrepresentable in ts, as the row says
    for (const [form, f] of [
      ["new VarId", () => new VarId(s)],
      ["VarId.of", () => VarId.of(s)],
      ["Term.var", () => Term.var(s)],
    ] as const) {
      let refused: unknown;
      try {
        f();
      } catch (e) {
        refused = e;
      }
      if ((refused === undefined) !== row.in_domain) {
        failures.push(`var_names/${row.name}: ${form} refused=${refused !== undefined}, want accepted=${row.in_domain}`);
      } else if (refused !== undefined && !(refused instanceof VarIdError && refused.varName === s)) {
        failures.push(`var_names/${row.name}: ${form} refused without a VarIdError naming it`);
      }
    }
    if (!row.in_domain) continue;
    const v = new TermVar(new VarId(s));
    const q = quote(v);
    const back = reify(q);
    if (back === undefined || !back.equals(v)) failures.push(`var_names/${row.name}: reify(quote(v)) is not v`);
    const want = Buffer.from(encode(valueTuple([valueAtom([0x02]), valueAtom(hexToBytes(row.name_hex))]))).toString("hex");
    if (Buffer.from(encode(q)).toString("hex") !== want) {
      failures.push(`var_names/${row.name}: quote does not write exactly name_hex`);
    }
  }
  return failures;
}
