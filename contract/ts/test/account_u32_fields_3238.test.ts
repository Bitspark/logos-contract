/**
 * #3238 (research 0021): a count premise's predicate arity, filter position and project attribute
 * are `u32` fields (logos-contract §3.0). rs reads them from the account term through
 * `u32::try_from`, go through `intTermToUint32`; ts bounded them by `Number.MAX_SAFE_INTEGER`, so a
 * clause whose count premise names arity `2^32` read back as a count premise in ts and as none in rs
 * and go. These pin ts to the domain at both sides of its upper bound.
 */
import test from "node:test";
import assert from "node:assert/strict";
import {
  BodyLit,
  Clause,
  clauseFromValue,
  clauseValue,
  CountLit,
  Goal,
  PredicateRef,
  ProjectSpec,
  Symbol,
  Term,
} from "../src/index.js";

const U32_MAX = 0xffff_ffff;

function countClause(arity: number, pos: number, attr: number): Clause {
  const count = new CountLit(
    new PredicateRef(Symbol.of("obs"), arity),
    [{ pos, term: Term.var("O") }],
    ProjectSpec.distinct(attr),
    Term.var("N"),
  );
  return new Clause(Goal.of("tally", [Term.var("O"), Term.var("N")]), [BodyLit.count(count)]);
}

/** Whether the clause's value reads back as a clause with a count premise of the same arity. */
function readsBack(c: Clause): boolean {
  const back = clauseFromValue(clauseValue(c));
  const lit = back?.body[0];
  return lit !== undefined && lit.countLit?.pred.arity === c.body[0]!.countLit!.pred.arity;
}

test("a count premise at the u32 domain's upper bound reads back", () => {
  assert.equal(readsBack(countClause(U32_MAX, U32_MAX, U32_MAX)), true);
});

test("a count premise one past the u32 domain does not read back as one", () => {
  // Each u32 field in turn, one past the bound: rs and go read none of these as a count premise.
  for (const [arity, pos, attr] of [
    [U32_MAX + 1, 0, 0],
    [1, U32_MAX + 1, 0],
    [1, 0, U32_MAX + 1],
  ] as const) {
    const back = clauseFromValue(clauseValue(countClause(arity, pos, attr)));
    const lit = back?.body[0];
    assert.ok(
      lit === undefined || lit.countLit === undefined,
      `arity ${arity}, pos ${pos}, attr ${attr}: read back as a count premise, which rs and go refuse`,
    );
  }
});
