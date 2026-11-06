// #2366: the ts term walks are iterative, so a long surface list cannot overflow the
// JS call stack. A list nests one level per element, and the recursive walks threw a
// RangeError at about 2,464 elements (isGround) and 9,600 (eraseGround), lists rs
// answers. N is well past both.

import test from "node:test";
import assert from "node:assert/strict";
import { Term, type Subst } from "../src/index.js";

const N = 20_000;
const enc = new TextEncoder();

/** `[a, a, …, a | tail]` as cons cells, one nesting level per element. */
function list(n: number, tail: Term): Term {
  let l = tail;
  for (let i = 0; i < n; i += 1) {
    l = Term.tuple([Term.atom(enc.encode(".")), Term.atom(enc.encode("a")), l]);
  }
  return l;
}

const nil = Term.atom(enc.encode("[]"));

test("isGround walks a 20,000-element list without overflowing", () => {
  assert.equal(Term.isGround(list(N, nil)), true);
  assert.equal(Term.isGround(list(N, Term.var("T"))), false, "a variable at the bottom is found");
});

test("eraseGround erases a 20,000-element list, and fromValue restores it", () => {
  const ground = list(N, nil);
  const value = Term.eraseGround(ground);
  assert.ok(value !== undefined, "a ground term erases");
  assert.ok(Term.fromValue(value).equals(ground), "the round trip is the same term");
  assert.equal(Term.eraseGround(list(N, Term.var("T"))), undefined, "a non-ground term does not");
});

test("substitute grounds the variable at the bottom of a 20,000-element list", () => {
  const subst: Subst = new Map([["T", nil]]);
  const out = Term.substitute(list(N, Term.var("T")), subst);
  assert.equal(Term.isGround(out), true);
  assert.ok(out.equals(list(N, nil)));
});

test("equals compares two 20,000-element lists and finds a difference at the bottom", () => {
  assert.ok(list(N, nil).equals(list(N, nil)));
  assert.equal(list(N, nil).equals(list(N, Term.atom(enc.encode("x")))), false);
  assert.equal(list(N, nil).equals(list(N - 1, nil)), false, "a shorter list differs");
});
