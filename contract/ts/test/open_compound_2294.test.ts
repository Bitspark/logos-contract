// #2294 (ruled seat:caa): Term.isOpenCompound, the ONE classification of "compound" the
// function-free fragment excludes. The same rows as contract/rs/tests/open_compound_2294.rs.
import { test } from "node:test";
import assert from "node:assert/strict";

import { Term } from "../src/index.js";

const atom = (s: string): Term => Term.atom(new TextEncoder().encode(s));
const f = (t: Term): Term => Term.tuple([atom("f"), t]);
const g = (t: Term): Term => Term.tuple([atom("g"), t]);

test("#2294: only a tuple with a variable is an open compound", () => {
  const rows: [string, Term, boolean][] = [
    ["an atom", atom("a"), false],
    ["a variable", Term.var("X"), false],
    ["a string", Term.tuple([atom("utf8-text"), atom("a")]), false],
    ["f(a)", f(atom("a")), false],
    ["f(g(a))", f(g(atom("a"))), false],
    ["f(X)", f(Term.var("X")), true],
    ["f(g(X))", f(g(Term.var("X"))), true],
  ];
  for (const [name, term, open] of rows) {
    assert.equal(Term.isOpenCompound(term), open, name);
  }
});
