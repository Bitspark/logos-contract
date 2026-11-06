/*
 * TS replay of vectors/account-v2-list.json (#2732 increment 1). The spec records the reify-aware
 * account-v2 check as tri-core (docs/spec/logos-contract.md §9), yet until this file only rs replayed
 * the vector. Like the rs oracle (conformance/rs/tests/list_reification_vectors.rs) and the go twin
 * (contract/go/account_v2_list_vectors_test.go), each case is rebuilt from code and the committed
 * file is checked against it: the file is checked, not trusted. The case NAMES are read from the
 * file, so a case added there with no builder here fails, and a builder here with no case fails.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encode } from "@bitspark/ontos-codec";

import { canonicalizeLists, quote, Term } from "../src/index.js";
import { observe } from "./support/replay_ledger.js";

/** This replay's vector file, as its ledger lines name it (#2732 increment 2). */
const FILE = "account-v2-list.json";

interface AccountV2ListFile {
  readonly fixtures: readonly { readonly name: string; readonly cons_wire_hex: string; readonly list_wire_hex: string }[];
  readonly check_correspondence: {
    readonly account_equal: readonly { readonly case: string }[];
    readonly account_distinct: readonly { readonly case: string }[];
  };
}

function loadAccountV2List(): AccountV2ListFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "account-v2-list.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8")) as AccountV2ListFile;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/account-v2-list.json above ${dir}`);
    dir = parent;
  }
}

const enc = new TextEncoder();
const hex = (b: Uint8Array): string => Array.from(b, (x) => x.toString(16).padStart(2, "0")).join("");
const av = (s: string): Value => atom(enc.encode(s));
const nil = (): Value => av("[]");
const cons = (head: Value, tail: Value): Value => tuple([av("."), head, tail]);
/** A PROPER cons list, right-folded onto []. */
const consList = (...elems: Value[]): Value => elems.reduceRight<Value>((acc, e) => cons(e, acc), nil());
/** The `list` embedding Tuple[Atom("list"), e0, …], built directly: the oracle must not use the transform it checks. */
const listEmbed = (...elems: Value[]): Value => tuple([av("list"), ...elems]);
/** The account's reading of the ground claim p(arg): Tuple[Atom(p), quote(arg)]. */
const claimWireHex = (arg: Value): string => hex(encode(tuple([av("p"), quote(Term.fromValue(arg))])));

test("#2732 account-v2-list: every fixture's cons and canonicalized wire hex match the oracle", () => {
  const f = loadAccountV2List();
  const builders = new Map<string, Value>([
    ["proper_pair", consList(av("a"), av("b"))],
    ["proper_singleton", consList(av("a"))],
    ["empty_nil", nil()],
    ["improper_tail", cons(av("a"), av("b"))],
    ["nested_list", consList(consList(av("a")), av("b"))],
  ]);
  assert.equal(f.fixtures.length, builders.size, `fixtures in the file vs builders here (${[...builders.keys()]})`);
  for (const fx of f.fixtures) {
    const arg = builders.get(fx.name);
    assert.ok(arg !== undefined, `fixture ${fx.name} has no builder here`);
    assert.equal(claimWireHex(arg), fx.cons_wire_hex, `[${fx.name}] cons wire hex`);
    observe(FILE, fx.name, "cons_wire_hex", "passed");
    assert.equal(claimWireHex(canonicalizeLists(arg)), fx.list_wire_hex, `[${fx.name}] canonicalized (list) wire hex`);
    observe(FILE, fx.name, "list_wire_hex", "passed");
  }
});

test("#2732 account-v2-list: account_equal pairs canonicalize to one value, account_distinct pairs never do", () => {
  const f = loadAccountV2List();
  const ab = [av("a"), av("b")];
  const equal = new Map<string, readonly [Value, Value]>([
    ["proper_pair_cons_vs_list", [consList(...ab), listEmbed(...ab)]],
    ["singleton_cons_vs_list", [consList(av("a")), listEmbed(av("a"))]],
    ["nested_cons_vs_list", [consList(consList(av("a")), av("b")), listEmbed(listEmbed(av("a")), av("b"))]],
  ]);
  const distinct = new Map<string, readonly [Value, Value]>([
    ["wrong_order", [listEmbed(...ab), listEmbed(av("b"), av("a"))]],
    ["empty_nil_vs_empty_list", [nil(), listEmbed()]],
    ["proper_vs_improper", [listEmbed(...ab), cons(av("a"), av("b"))]],
  ]);
  const same = (a: Value, b: Value): boolean => hex(encode(canonicalizeLists(a))) === hex(encode(canonicalizeLists(b)));
  const check = (section: string, cases: readonly { readonly case: string }[], oracle: Map<string, readonly [Value, Value]>, want: boolean): void => {
    assert.equal(cases.length, oracle.size, `${section}: cases in the file vs builders here (${[...oracle.keys()]})`);
    for (const c of cases) {
      const pair = oracle.get(c.case);
      assert.ok(pair !== undefined, `${section} case ${c.case} has no builder here`);
      assert.equal(same(pair[0], pair[1]), want, `${section} [${c.case}]`);
      observe(FILE, c.case, "outcome", "passed");
    }
  };
  check("account_equal", f.check_correspondence.account_equal, equal, true);
  check("account_distinct", f.check_correspondence.account_distinct, distinct, false);
});
