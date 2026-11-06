/*
 * The pre-check capability query (#1371 stage 1) — the TS third of the tri-core surface.
 *
 * The two that matter are the NEGATIVE ones:
 *   - "an empty result does not promise acceptance" — the form-33 guard. Empty means no
 *     capability refusal will occur, NOT that `check` will accept.
 *   - "never calls decide" — proven by a theory whose `decide` throws.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  BuiltinNode,
  check,
  type CheckProfile,
  defaultLimits,
  Derivation,
  Evidence,
  GroundLiteral,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  PredicateSet,
  profileDecidesAllBuiltins,
  type Symbol,
  type Theory,
  TheoryOutcome,
  unownedBuiltinPredicates,
} from "../src/index.js";

// --------------------------------- theories ---------------------------------

/** Binds nothing — the theory-less host #1371 is about. */
// test-double: consumer(owns no predicate: the theory-less host)
const unboundTheory: Theory = {
  owns: () => false,
  decide: () => TheoryOutcome.NotMine,
};

/** Owns everything and decides it holds. */
// test-double: consumer(owns every predicate and holds it)
const owningTheory: Theory = {
  owns: () => true,
  decide: () => TheoryOutcome.Holds,
};

/** Owns exactly one named predicate. */
const ownsOnly = (name: string): Theory => ({
  owns: (pred: Symbol) => new TextDecoder().decode(pred.bytes()) === name,
  decide: () => TheoryOutcome.Holds,
});

/** Owns everything and THROWS if asked to decide — the query must never call it. */
// test-double: adversarial(throws if asked to decide)
const explodingTheory: Theory = {
  owns: () => true,
  decide: () => {
    throw new Error("the pre-check query must not call decide()");
  },
};

// ---------------------------------- leaves ----------------------------------

function leaves(extensional: PredicateSet): LeafVerifier<undefined> {
  return {
    extensional: () => extensional,
    verify: (): LeafOutcome => LeafOutcome.Reject("not_a_leaf_test"),
  };
}

function emptyLeaves(): LeafVerifier<undefined> {
  return leaves(new PredicateSet());
}

function leavesWith(pred: string): LeafVerifier<undefined> {
  const set = new PredicateSet();
  set.insert(pred);
  return leaves(set);
}

// ---------------------------------- harness ----------------------------------

const av = (s: string): Value => valueAtom(new TextEncoder().encode(s));

function deriv(...preds: string[]): Derivation {
  return new Derivation(
    preds.map((p) => new BuiltinNode(GroundLiteral.of(p, [av("a"), av("a")]))),
    0,
  );
}

function profile(
  theory: Theory,
  lv: LeafVerifier<undefined>,
): CheckProfile<undefined> {
  return {
    theory,
    leaves: lv,
    admit: new AlwaysAdmit<undefined>(),
    limits: defaultLimits(),
  };
}

const names = (syms: Symbol[]): string[] =>
  syms.map((s) => new TextDecoder().decode(s.bytes()));

// ----------------------------------- tests -----------------------------------

test("a theory-less host names the predicate it cannot decide", () => {
  const p = profile(unboundTheory, emptyLeaves());
  const d = deriv("=:=");
  assert.deepEqual(names(unownedBuiltinPredicates(d, p)), ["=:="]);
  assert.equal(profileDecidesAllBuiltins(d, p), false);
});

test("a bound theory reports nothing outstanding", () => {
  const p = profile(owningTheory, emptyLeaves());
  const d = deriv("=:=");
  assert.deepEqual(unownedBuiltinPredicates(d, p), []);
  assert.equal(profileDecidesAllBuiltins(d, p), true);
});

test("mixed ownership names only the unowned", () => {
  const p = profile(ownsOnly("=:="), emptyLeaves());
  const d = deriv("=:=", ">", "<");
  assert.deepEqual(names(unownedBuiltinPredicates(d, p)), [">", "<"]);
});

// Deduplicated on first appearance, in derivation node order — so the report is
// deterministic for a given derivation rather than merely a set.
test("deduplicated in node order", () => {
  const p = profile(unboundTheory, emptyLeaves());
  const d = deriv(">", "=:=", ">", "<", "=:=");
  assert.deepEqual(names(unownedBuiltinPredicates(d, p)), [">", "=:=", "<"]);
});

// THE FORM-33 GUARD. An empty result must NOT be read as "check will accept".
//
// The theory owns the predicate, so the query is EMPTY — the strongest possible "no
// capability problem" answer — and `check` still rejects, because the predicate is also
// extensional (a genuine §4.4 partition overlap). This is what stops the query being
// documented as a verifiability oracle.
test("an empty result does not promise acceptance", () => {
  const p = profile(owningTheory, leavesWith("=:="));
  const d = deriv("=:=");

  assert.deepEqual(
    unownedBuiltinPredicates(d, p),
    [],
    "precondition: the capability query must be clean here",
  );

  const claim = GroundLiteral.of("=:=", [av("a"), av("a")]);
  const outcome = check(new MapProgram(), claim, d, undefined, p);

  assert.equal(
    outcome.kind,
    "reject",
    "an empty capability report does not make an overlapping account valid",
  );
  assert.equal(
    outcome.kind === "reject" ? outcome.code : undefined,
    "predicate_partition_violation",
  );
});

// Total and side-effect-free: it consults owns() only. Proven rather than asserted —
// this theory throws if decide is ever reached.
test("never calls decide", () => {
  const p = profile(explodingTheory, emptyLeaves());
  const d = deriv("=:=", ">", "<");
  assert.deepEqual(unownedBuiltinPredicates(d, p), []);
  assert.equal(profileDecidesAllBuiltins(d, p), true);
});

test("a derivation with no builtins reports nothing", () => {
  const p = profile(unboundTheory, emptyLeaves());
  const d = new Derivation([], 0);
  assert.deepEqual(unownedBuiltinPredicates(d, p), []);
});
