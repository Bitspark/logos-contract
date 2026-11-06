// TS replay of vectors/edb_snapshot_set.json (#2279): edbTableHash reads its rows as a SET.
// Every case is an equivalence over hashes, so no digest is authored in the vector.

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom } from "@bitspark/ontos-core";

import {
  edbTableHash,
  GroundLiteral,
  type Hash,
  hashEquals,
  RelationTable,
  Symbol as LSymbol,
} from "../src/index.js";

function load(): any {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "edb_snapshot_set.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8"));
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/edb_snapshot_set.json");
    dir = parent;
  }
}

const v = load();
const pred = LSymbol.of(String(v.pred));

function rows(names: readonly string[]): GroundLiteral[] {
  return names.map((n) => {
    const args = v.rows[n];
    if (!Array.isArray(args)) throw new Error(`row ${n} is not in \`rows\``);
    return GroundLiteral.of(
      pred,
      args.map((a: string) => atom(new TextEncoder().encode(a))),
    );
  });
}

function hash(names: readonly string[]): Hash {
  return edbTableHash(pred, rows(names));
}

test("#2279: every equal group hashes equal", () => {
  assert.ok(v.equal.length > 0, "the vector must carry equal groups");
  for (const g of v.equal) {
    const first = hash(g.lists[0]);
    for (const list of g.lists.slice(1)) {
      assert.ok(hashEquals(hash(list), first), `${g.name}: ${JSON.stringify(list)} hashes differently`);
    }
  }
});

test("#2279: every differ pair hashes differently", () => {
  assert.ok(v.differ.length > 0, "the vector must carry differ pairs, or a constant hash passes");
  for (const p of v.differ) {
    assert.ok(!hashEquals(hash(p.lists[0]), hash(p.lists[1])), p.name);
  }
});

test("#2279: a snapshot equals the hash over its sealed table", () => {
  for (const list of v.table_agrees) {
    const rs = rows(list);
    const table = RelationTable.of(pred, Number(v.arity), rs);
    assert.ok(table.isCanonical(), `${JSON.stringify(list)}: the sealed table is canonical`);
    assert.ok(
      hashEquals(edbTableHash(pred, rs), edbTableHash(pred, table.rows)),
      `${JSON.stringify(list)}: the snapshot of the rows and the hash over the table they seal differ`,
    );
  }
});
