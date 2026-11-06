/*
 * Language-local id-pin tests for the §9 canonical clause encoding — the load-bearing
 * ORACLE for the ADR-0007 negation account encoding (NEG_TAG). These mirror Rust's
 * account.rs #[cfg(test)] pins; they are NOT cross-core vectors (that is the shared
 * vectors/account.json driven by the differential harness), but they assert the SAME
 * frozen ids, so a drift in the TS encoding fails here too.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { canonicalClauseId, Clause, Goal, Term } from "../src/index.js";

// The frozen canonical id of permit(S,A) :- grant(S,A), \+ denied(S,A). under the
// NEG_TAG reading — byte-pinned in vectors/account.json and Rust's account.rs.
const FROZEN_PERMIT_NEG_ID =
  "3670ee8eebbd14d90621ddf82d8244a555562194c64d11dcd9986bcfefed705d";

function goal(pred: string, ...args: Term[]): Goal {
  return Goal.of(pred, args);
}

test("neg clause id is pinned and distinct from the all-positive reading", () => {
  const permitNeg = Clause.withNeg(
    goal("permit", Term.var("S"), Term.var("A")),
    [goal("grant", Term.var("S"), Term.var("A"))],
    [goal("denied", Term.var("S"), Term.var("A"))],
  );
  // The SAME body literals, but BOTH read as positive.
  const permitAllPos = new Clause(goal("permit", Term.var("S"), Term.var("A")), [
    goal("grant", Term.var("S"), Term.var("A")),
    goal("denied", Term.var("S"), Term.var("A")),
  ]);

  const negID = canonicalClauseId(permitNeg).asStr();
  const posID = canonicalClauseId(permitAllPos).asStr();

  // Polarity is part of the id: the negated reading is distinct.
  assert.notEqual(negID, posID);
  // Pin the new Neg-bearing id (locks the NEG_TAG reading against drift).
  assert.equal(negID, FROZEN_PERMIT_NEG_ID);
});

test("positive clause ids are unchanged by the BodyLit amendment", () => {
  // Re-assert the 4 frozen positive clause ids from vectors/account.json: a positive
  // body literal reads as the bare goalAsTerm with no wrapper tag, so every
  // pre-amendment positive id is byte-for-byte unchanged.
  const atom = (s: string) => Term.atom(new TextEncoder().encode(s));
  const cases: ReadonlyArray<readonly [string, Clause, string]> = [
    // edge(a, b).
    [
      "edge_ab_fact",
      Clause.fact(goal("edge", atom("a"), atom("b"))),
      "0fa66252d400869a272c064a66c32d461b30f95f30e1d03a5fb961cb957bead3",
    ],
    // reach(X, Y) :- edge(X, Y).
    [
      "reach_base",
      new Clause(goal("reach", Term.var("X"), Term.var("Y")), [
        goal("edge", Term.var("X"), Term.var("Y")),
      ]),
      "c52ab14799945827045a4410caed08ca26f2704944da2a6fe48546c096702234",
    ],
    // reach(X, Z) :- edge(X, Y), reach(Y, Z).
    [
      "reach_rec",
      new Clause(goal("reach", Term.var("X"), Term.var("Z")), [
        goal("edge", Term.var("X"), Term.var("Y")),
        goal("reach", Term.var("Y"), Term.var("Z")),
      ]),
      "d5cb2f8c0811500282cacd5cdf0db22d3356d0eadbdc64e73a149d1c8122dd5d",
    ],
    // reach(X, Z) :- edge(X, Z).
    [
      "reach_base_renamed_Y_to_Z_differs",
      new Clause(goal("reach", Term.var("X"), Term.var("Z")), [
        goal("edge", Term.var("X"), Term.var("Z")),
      ]),
      "fff905c2dd63fb17d66bd109e0940df053606dd0270fdfa02b6a43168f5197b1",
    ],
  ];
  for (const [name, clause, want] of cases) {
    assert.equal(canonicalClauseId(clause).asStr(), want, `id mismatch for ${name}`);
  }
});
