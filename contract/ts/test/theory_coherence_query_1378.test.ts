/*
 * The arm-3 attribution query (#1378) — the TS third of the tri-core surface.
 *
 * `check` rejects an `owns()`-yes / `decide()`-NotMine theory with the structural code
 * `predicate_partition_violation`. That code is correct — the account cannot be verified by
 * this profile — but it points a consumer at the PRODUCER for a defect in the verifier's own
 * theory binding. Per the #1382 ruling on the sibling arm a new `RejectionCode` member is
 * v1-breaking in all three cores, so the attribution is a query rather than vocabulary.
 *
 * The two that matter are:
 *   - "arm 1 is not reported as incoherent" — arm 1 also answers NotMine and shares the
 *     rejection code, so a query keyed on the outcome alone would conflate them.
 *   - "an empty result does not certify the theory coherent" — the documented limit,
 *     executable (form 33).
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  BuiltinNode,
  type CheckProfile,
  defaultLimits,
  Derivation,
  GroundLiteral,
  incoherentBuiltinAtoms,
  LeafNode,
  LeafOutcome,
  type LeafVerifier,
  PredicateSet,
  type Theory,
  TheoryOutcome,
} from "../src/index.js";

// --------------------------------- theories ---------------------------------

/** Arm 3: `owns()` says yes, `decide()` disowns. The defect under test. */
// test-double: adversarial(owns a predicate yet decides NotMine: the defect under test)
const disowningTheory: Theory = {
  owns: () => true,
  decide: () => TheoryOutcome.NotMine,
};

/** A coherent theory: owns it and decides it. */
// test-double: consumer(owns every predicate and holds it)
const owningTheory: Theory = {
  owns: () => true,
  decide: () => TheoryOutcome.Holds,
};

/** Arm 1: a host binding no theory. `decide` also answers NotMine. */
// test-double: consumer(owns no predicate: the theory-less host)
const unboundTheory: Theory = {
  owns: () => false,
  decide: () => TheoryOutcome.NotMine,
};

// ---------------------------------- harness ----------------------------------

const av = (s: string): Value => valueAtom(new TextEncoder().encode(s));

const lit = (pred: string, arg: string): GroundLiteral =>
  GroundLiteral.of(pred, [av(arg)]);

function emptyLeaves(): LeafVerifier<undefined> {
  const set = new PredicateSet();
  return {
    extensional: () => set,
    verify: (): LeafOutcome => LeafOutcome.Reject("not_a_leaf_test"),
  };
}

function profile(theory: Theory): CheckProfile<undefined> {
  return {
    theory,
    leaves: emptyLeaves(),
    admit: new AlwaysAdmit<undefined>(),
    limits: defaultLimits(),
  };
}

/** `pairs` is a flat (pred, arg, pred, arg, ...) list, one BuiltinNode each. */
function deriv(...pairs: string[]): Derivation {
  const nodes: BuiltinNode[] = [];
  for (let i = 0; i + 1 < pairs.length; i += 2) {
    nodes.push(new BuiltinNode(lit(pairs[i] as string, pairs[i + 1] as string)));
  }
  return new Derivation(nodes, 0);
}

const render = (atoms: GroundLiteral[]): string[] =>
  atoms.map((a) => new TextDecoder().decode(a.pred.bytes()));

// ----------------------------------- tests -----------------------------------

test("names the atom an incoherent theory disowns", () => {
  const got = incoherentBuiltinAtoms(deriv("=:=", "a"), profile(disowningTheory));
  assert.equal(got.length, 1, `expected one atom, got ${render(got).join(" ")}`);
  assert.ok(
    got[0]?.equals(lit("=:=", "a")),
    "the query returns the ATOM, not the predicate — incoherence is only observable per atom",
  );
});

test("a coherent theory yields nothing", () => {
  const got = incoherentBuiltinAtoms(deriv("=:=", "a"), profile(owningTheory));
  assert.deepEqual(
    render(got),
    [],
    "without this the query could be returning every builtin atom it sees",
  );
});

// ⭐ THE DISCRIMINATING CONTROL. Arm 1 also answers NotMine and `check` gives it the SAME
// rejection code. A query keyed on the outcome alone would report arm 1 too — naming a defect
// in a theory the host never bound, which is the misattribution inverted rather than fixed.
test("arm 1 (unbound theory) is not reported as incoherent", () => {
  const got = incoherentBuiltinAtoms(deriv("=:=", "a"), profile(unboundTheory));
  assert.deepEqual(
    render(got),
    [],
    "arm 1 (no theory owns the predicate) is a HOST CAPABILITY refusal, not an incoherent " +
      "theory — the two share a rejection code and must not share this query",
  );
});

test("repeated and distinct atoms dedup in node order", () => {
  const got = incoherentBuiltinAtoms(
    deriv("=:=", "a", "<", "b", "=:=", "a"),
    profile(disowningTheory),
  );
  assert.deepEqual(render(got), ["=:=", "<"]);
});

// ⛔ THE DOCUMENTED LIMIT, MADE EXECUTABLE. The theory here is the same provably incoherent
// one as the first test, and the query returns empty — because this derivation cites no
// Builtin node for it to disagree on. An empty result is therefore not a coherence
// certificate: it is a PASS compatible with the thing still failing (form 33).
test("an empty result does not certify the theory coherent", () => {
  const d = new Derivation([new LeafNode(lit("edge", "a"))], 0);
  const got = incoherentBuiltinAtoms(d, profile(disowningTheory));
  assert.deepEqual(
    render(got),
    [],
    "the query can only witness incoherence on atoms the derivation cites, and this one " +
      "cites no Builtin node",
  );
});
