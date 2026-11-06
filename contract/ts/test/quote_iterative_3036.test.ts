// #3036, the class behind #3014: quote and reify walk with an explicit work stack, never the JS call
// stack, so how deep a term they handle is not a property of the V8 tier or the runner. A recursive
// walker's safe depth moves with both (#3014 measured ~2,390 unoptimized, ~2,970 optimized), and
// that made a required context flake.
//
// NEGATIVE WITNESS (seat:caa's done-when 4): the recursive quote throws RangeError on the
// 100,000-level term below, under any tier; the iterative one quotes it and reify reads it back.
import { test } from "node:test";
import assert from "node:assert/strict";
import { Atom, Tuple, atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { quote, reify, Term, valueDepthLe } from "../src/index.js";

const DEEP = 100_000;
const atom = (s: string): Term => Term.atom(new TextEncoder().encode(s));

function nested(depth: number): Term {
  let t = atom("a");
  for (let i = 1; i < depth; i++) t = Term.tuple([atom("f"), t]);
  return t;
}

test("#3036: quote and reify handle a 100,000-level term, with no call stack per level", () => {
  const t = nested(DEEP);
  const v = quote(t);
  // quote wraps each level as Tuple[tag, payload]: a tuple level is two value levels, the atom one.
  const depth = 2 * DEEP;
  assert.ok(valueDepthLe(v, depth) && !valueDepthLe(v, depth - 1), "the quoted value keeps every level");
  // Walk the spine iteratively: every level is the tuple tag 0x01 over [f, rest], down to the atom.
  let cur: Value = v;
  let levels = 0;
  for (;;) {
    assert.ok(cur instanceof Tuple && cur.length === 2, `level ${levels} is a [tag, payload] pair`);
    const [tag, payload] = cur.items();
    const t0 = (tag as Atom).bytes()[0];
    levels += 1;
    if (t0 === 0x00) break;
    assert.equal(t0, 0x01, `level ${levels} is a tuple`);
    const kids = (payload as Tuple).items();
    assert.equal(kids.length, 2);
    cur = kids[1]!;
  }
  assert.equal(levels, DEEP);
  const back = reify(v);
  assert.ok(back !== undefined, "reify reads the quoted value back");
  assert.ok(Term.depthLe(back, DEEP) && !Term.depthLe(back, DEEP - 1), "reify keeps every level");
});

// The frozen v1 byte form is unchanged: a hand-written expected value, never quote's own output.
test("#3036: quote keeps the frozen v1 shape: atom 0x00, tuple 0x01, var 0x02", () => {
  const enc = (s: string) => new TextEncoder().encode(s);
  const t = Term.tuple([atom("f"), Term.var("X"), Term.tuple([atom("g")])]);
  const expected = valueTuple([
    valueAtom([0x01]),
    valueTuple([
      valueTuple([valueAtom([0x00]), valueAtom(enc("f"))]),
      valueTuple([valueAtom([0x02]), valueAtom(enc("X"))]),
      valueTuple([valueAtom([0x01]), valueTuple([valueTuple([valueAtom([0x00]), valueAtom(enc("g"))])])]),
    ]),
  ]);
  assert.ok(sameValue(quote(t), expected));
  const back = reify(expected);
  assert.ok(back !== undefined && sameValue(quote(back), expected), "reify is quote's inverse on its image");
});

function sameValue(a: Value, b: Value): boolean {
  if (a instanceof Atom && b instanceof Atom) {
    const x = a.bytes();
    const y = b.bytes();
    return x.length === y.length && x.every((c, i) => c === y[i]);
  }
  if (a instanceof Tuple && b instanceof Tuple) {
    return a.length === b.length && a.items().every((c, i) => sameValue(c, b.items()[i]!));
  }
  return false;
}
