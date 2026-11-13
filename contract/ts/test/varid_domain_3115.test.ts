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
//   - a `Subst` key is a `VarId` (#3288): a string is not a key, in the types or at run time, so a
//     name outside §2a cannot reach the subst codec at all. That replaced #3115's interim refusal in
//     `writeSubst`.

import test from "node:test";
import assert from "node:assert/strict";

import { encode } from "@bitspark/ontos-codec";

import {
  Subst, Term, TermVar, VarId, VarIdError, captureSubst, defaultLimits, quote, reify, substAsValue, substFromValue,
} from "../src/index.js";

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
    assert.throws(
      () => new Subst().set(name as unknown as VarId, Term.atom(new Uint8Array([0x61]))),
      (e: unknown) => e instanceof TypeError && /a Subst key is a VarId/.test(e.message),
      `the string ${label} must not be accepted as a Subst key`,
    );
    if (!ok) {
      refused += 1;
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
    const subst = substFromValue(substAsValue(new Subst([[new VarId(name), Term.atom(new Uint8Array([0x61]))]])));
    assert.equal(subst.size, 1, `${label}: the subst codec does not read back its own subst`);
    assert.ok(subst.has(new VarId(name)), `${label}: the subst codec read back a different key`);
    assert.equal([...subst.keys()][0]!.asStr(), name, `${label}: the key read back is not the name written`);
  }
  assert.ok(accepted >= 100 && refused >= 100, `control: both verdicts must occur often; accepted ${accepted}, refused ${refused}`);
});

test("#3288: a Subst key is a VarId; a string, a look-alike or an asStr override cannot become a key", () => {
  const a = Term.atom(new Uint8Array([0x61]));
  // @ts-expect-error a string is not a Subst key (#3288): the types refuse it before run time does.
  assert.throws(() => new Subst().set("X", a), TypeError);
  // @ts-expect-error neither does the constructor take string-keyed entries.
  assert.throws(() => new Subst([["X", a]]), TypeError);

  // An object shaped like a VarId is not one: the brand is VarId's private name, not its methods.
  const lookAlike = Object.create(VarId.prototype) as VarId;
  assert.throws(() => new Subst().set(lookAlike, a), TypeError, "a look-alike without VarId's brand became a key");
  assert.throws(() => new Subst().set({ asStr: () => "\ud800" } as unknown as VarId, a), TypeError);

  // A subclass passes the constructor's test with its real name; an asStr override cannot swap in
  // another (here a lone surrogate) for the key or for what the codec writes.
  class Lying extends VarId {
    override asStr(): string {
      return "\ud800";
    }
  }
  const subst = new Subst([[new Lying("Y"), a]]);
  assert.ok(subst.has(new VarId("Y")), "the key is the subclass's real name");
  const key = [...subst.keys()][0]!;
  assert.equal(Object.getPrototypeOf(key), VarId.prototype, "the key is stored as a plain VarId");
  assert.equal(key.asStr(), "Y");
  const back = substFromValue(substAsValue(subst));
  assert.ok(back.has(new VarId("Y")) && back.size === 1, "the codec wrote the real name");

  // A VarId's identity is its name: two VarId objects of one name are one key, as in rs and go.
  const twice = new Subst([[new VarId("Z"), a], [new VarId("Z"), Term.atom(new Uint8Array([0x62]))]]);
  assert.equal(twice.size, 1, "two VarIds of one name made two keys");
  assert.ok(twice.get(VarId.of("Z"))!.equals(Term.atom(new Uint8Array([0x62]))), "the later binding replaces the earlier");
  assert.ok(twice.equals(new Subst([[VarId.of("Z"), Term.atom(new Uint8Array([0x62]))]])));
  assert.ok(!twice.equals(new Subst([[VarId.of("Z"), a]])), "equals reads the bound terms");
});

test("#3288: capture reads only a Subst's own entries; a forged substitution or key is refused, never captured", () => {
  // capture.ts no longer tests a key's name: every key reaching it passed VarId's constructor. That
  // rests on run-time facts, not on the types, and each is pinned here (research 0050 row 26).
  const a = Term.atom(new Uint8Array([0x61]));
  const limits = defaultLimits();

  // The brand checks cannot be replaced: both classes are frozen.
  assert.throws(() => Object.defineProperty(VarId, Symbol.hasInstance, { value: () => true }), TypeError);
  assert.throws(() => Object.defineProperty(Subst, Symbol.hasInstance, { value: () => true }), TypeError);
  assert.throws(() => Object.defineProperty(VarId.prototype, "asStr", { value: () => "\ud800" }), TypeError);

  // Not a Subst: a string-keyed Map, and an object built on Subst's prototype without its storage.
  const notSubsts: unknown[] = [new Map([["\ud800", a]]), Object.create(Subst.prototype)];
  for (const forged of notSubsts) {
    const r = captureSubst(forged as Subst, limits);
    assert.equal(r.kind, "reject", "a forged substitution was captured");
    if (r.kind === "reject") assert.equal(r.code, "unknown_node_kind");
  }

  // A subclass whose iterator yields a forged key: capture copies the storage through Subst's own
  // frozen iterator, so the forged entry never reaches the captured value.
  const forgedKey = { asStr: () => "\ud800" } as unknown as VarId;
  class Lying extends Subst {
    override *entries(): IterableIterator<[VarId, Term]> {
      yield [forgedKey, a];
    }
    override [Symbol.iterator](): IterableIterator<[VarId, Term]> {
      return this.entries();
    }
  }
  const lying = new Lying();
  lying.set(VarId.of("X"), a);
  const r = captureSubst(lying, limits);
  assert.equal(r.kind, "captured");
  if (r.kind === "captured") {
    assert.deepEqual([...r.value.keys()].map((k) => k.asStr()), ["X"], "capture read the subclass's iterator");
    assert.equal(Object.getPrototypeOf(r.value), Subst.prototype, "the captured substitution is a plain Subst");
  }
});
