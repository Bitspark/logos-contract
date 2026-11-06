// #3115: a VarId's name is UTF-8 text (§2a), which for a JS string means well-formed UTF-16: no lone
// surrogate. Every construction holds to it.
//
// Before #3115 `new VarId("\ud800")` was accepted, and `quote` wrote the lone surrogate as U+FFFD:
// `VarId("\ud800")`, `VarId("\udfff")` and `VarId("�")` quoted to ONE byte string, so reify
// returned a different variable and those clauses shared a ClauseId. The law, over listed names and
// generated strings:
//   - a name is accepted iff it is well-formed UTF-16 (stated here from the spec, not imported);
//   - `new VarId`, `VarId.of` and `Term.var` refuse by name, with a `VarIdError` naming it;
//   - every accepted name round-trips through quote/reify, two distinct names never quote to the
//     same bytes, and the subst codec reads back what it writes;
//   - a `Subst` key that is not a name is refused by name before anything is written (the interim
//     #3288 removes when it retypes the key).

import test from "node:test";
import assert from "node:assert/strict";

import { encode } from "@bitspark/ontos-codec";

import { Term, TermVar, VarId, VarIdError, quote, reify, substAsValue, substFromValue } from "../src/index.js";

function inDomain(s: string): boolean {
  for (let i = 0; i < s.length; i += 1) {
    const u = s.charCodeAt(i);
    if (u >= 0xdc00 && u <= 0xdfff) return false;
    if (u >= 0xd800 && u <= 0xdbff) {
      const n = s.charCodeAt(i + 1);
      if (!(n >= 0xdc00 && n <= 0xdfff)) return false;
      i += 1;
    }
  }
  return true;
}

const LISTED: readonly string[] = [
  "X", "é", "😀", "�", "", "퟿", "", "\u{10ffff}",
  "\ud800", "\udfff", "a\ud800b", "\udc00\ud800", "X\ud800", "\ud800\ud800",
];

/** Strings over code units weighted towards the surrogate ranges, seeded, so both verdicts occur. */
function generated(n: number): string[] {
  const units = [0x61, 0x5a, 0x30, 0x00, 0x7f, 0xe9, 0xfffd, 0xd7ff, 0xd800, 0xdbff, 0xdc00, 0xdfff, 0xe000];
  let seed = 3115;
  const next = () => {
    seed = (seed * 1103515245 + 12345) >>> 0;
    return seed >>> 8;
  };
  const out: string[] = [];
  for (let i = 0; i < n; i += 1) {
    const len = next() % 7;
    let s = "";
    for (let j = 0; j < len; j += 1) s += String.fromCharCode(units[next() % units.length]!);
    out.push(s);
  }
  return out;
}

function refusal(f: () => unknown): VarIdError | undefined {
  try {
    f();
    return undefined;
  } catch (e) {
    if (e instanceof VarIdError) return e;
    throw e;
  }
}

const hex = (v: Parameters<typeof encode>[0]) => Buffer.from(encode(v)).toString("hex");

test("#3115: VarId construction holds to the §2a domain, and every accepted name round-trips", () => {
  const byQuote = new Map<string, string>();
  let accepted = 0;
  let refused = 0;
  for (const name of [...LISTED, ...generated(3000)]) {
    const label = JSON.stringify(name);
    const ok = inDomain(name);
    for (const [form, f] of [
      ["new VarId", () => new VarId(name)],
      ["VarId.of", () => VarId.of(name)],
      ["Term.var", () => Term.var(name)],
    ] as const) {
      const err = refusal(f);
      assert.equal(err === undefined, ok, `${form}(${label}): refused=${err !== undefined}, but §2a says in-domain=${ok}`);
      if (err !== undefined) assert.equal(err.varName, name, `${form}(${label}) refused without naming it`);
    }
    if (!ok) {
      refused += 1;
      assert.throws(
        () => substAsValue(new Map([[name, Term.atom(new Uint8Array([0x61]))]])),
        (e: unknown) => e instanceof VarIdError && e.varName === name,
        `a Subst key ${label} that is not a name must be refused by name`,
      );
      continue;
    }
    accepted += 1;
    const v = new TermVar(new VarId(name));
    const q = quote(v);
    const back = reify(q);
    assert.ok(back !== undefined && back.equals(v), `${label}: reify(quote(v)) is not v`);
    const bytes = hex(q);
    const prior = byQuote.get(bytes);
    assert.ok(prior === undefined || prior === name, `${label} and ${JSON.stringify(prior)} quote to the same bytes`);
    byQuote.set(bytes, name);
    const subst = substFromValue(substAsValue(new Map([[name, Term.atom(new Uint8Array([0x61]))]])));
    assert.equal(subst.size, 1, `${label}: the subst codec does not read back its own subst`);
    assert.ok(subst.has(name), `${label}: the subst codec read back a different key`);
  }
  assert.ok(accepted >= 100 && refused >= 100, `control: both verdicts must occur often; accepted ${accepted}, refused ${refused}`);
});
