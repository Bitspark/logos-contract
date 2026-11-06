/*
 * The contract↔guest standard-theory SYNC GUARD, TS arm (#574).
 *
 * newStandardTheory() is the consumer-facing gate Theory a TS CHECK consumer binds into its
 * CheckProfile to certify a search that uses the wasm guest's builtins. It MUST own EXACTLY
 * the predicate set the guest's rs standard_theory() evaluates IN SEARCH — otherwise a
 * perfectly-formed Builtin node routes to NO owner under check() and silently fails to
 * certify (the root of #574). TS has no native search engine and cannot reach the rs guest
 * binding from a unit test, so this arm pins the owned set against the rs SOURCE OF TRUTH
 * enumerated below (arithmetic.rs / text.rs / term_theory.rs / list_theory.rs). The rs arm
 * (app/wasm/rs) compares the contract helper to the guest's local standard_theory() owns
 * directly; together they fence the helper from drifting away from the guest tri-core.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { newArithmeticTheory, newCompoundTheory, newListTheory, newStandardTheory, newTermTheory, newTextTheory, Symbol } from "../src/index.js";

const utf8 = new TextEncoder();
const sym = (s: string): Symbol => new Symbol(utf8.encode(s));

// The EXACT predicate set newStandardTheory() owns — the union of the four standard
// theories' owned relations, copied verbatim from the rs source of truth:
//   - ArithmeticTheory (contract/rs/src/arithmetic.rs): is =:= =\= < > >= =<
//   - TextTheory       (contract/rs/src/text.rs):       contains starts_with ends_with
//   - TermTheory       (contract/rs/src/term_theory.rs): atom atomic compound is_list number
//     (recognizers) + == \== @< @> @=< @>= (standard-order comparisons) + =.. (univ)
//     + = \= true fail false (unification + control constants, 1.1.0 / #1611)
//   - ListTheory       (contract/rs/src/list_theory.rs): length nth0 last
const STANDARD_OWNED = [
  // ArithmeticTheory
  "is", "=:=", "=\\=", "<", ">", ">=", "=<",
  // TextTheory
  "contains", "starts_with", "ends_with",
  // TermTheory recognizers
  "atom", "atomic", "compound", "is_list", "number",
  // TermTheory standard-order comparisons
  "==", "\\==", "@<", "@>", "@=<", "@>=",
  // TermTheory univ, unification and the control constants (#1611)
  "=..", "=", "\\=", "true", "fail", "false",
  // ListTheory
  "length", "nth0", "last",
];

// Predicates NO standard theory may claim — non-builtin heads/leaves and expression
// operators (which are sub-terms, never goals).
const STANDARD_NOT_OWNED = ["reach", "edge", "p", "differ", "five", "concat", "+", "-", "foo"];

test("newStandardTheory() owns exactly the rs guest's standard_theory() predicate set (#574)", () => {
  const theory = newStandardTheory();

  for (const name of STANDARD_OWNED) {
    assert.equal(theory.owns(sym(name)), true, `newStandardTheory().owns(${JSON.stringify(name)}) must be true`);
  }
  for (const name of STANDARD_NOT_OWNED) {
    assert.equal(theory.owns(sym(name)), false, `newStandardTheory().owns(${JSON.stringify(name)}) must be false`);
  }
});

test("newStandardTheory() binds the four members in arith/text/term/list order (#574)", () => {
  const got = newStandardTheory().identity();
  const want = newCompoundTheory(newArithmeticTheory(), newTextTheory(), newTermTheory(), newListTheory()).identity();
  assert.deepEqual(got, want, "newStandardTheory() identity must equal the arith/text/term/list compound's");

  // The digest is order-sensitive (it commits to the ORDERED member identities), so a
  // re-ordered compound MUST differ — proving the order is load-bearing and pinned.
  const reordered = newCompoundTheory(newTextTheory(), newArithmeticTheory(), newTermTheory(), newListTheory()).identity();
  assert.notDeepEqual(got, reordered, "newStandardTheory() identity must be order-sensitive");
});
