import assert from "node:assert/strict";
import { test } from "node:test";
import {
  AlwaysAdmit, Clause, ClauseId, Derivation, Goal, MapProgram, Outcome, PredicateSet, RuleNode,
  check, defaultLimits, newStandardTheory, programBytes, programFromValue, programToValue,
} from "@bitspark/logos-contract";

const p = Goal.of("p", []);
const profile = {
  theory: newStandardTheory(),
  leaves: { extensional: () => PredicateSet.from([]), verify: () => assert.fail("unexpected leaf") },
  admit: new AlwaysAdmit(), limits: defaultLimits(),
};

test("program encoding preserves portable IDs including U+FFFD and supplementary characters", () => {
  for (const handle of ["", "A\uFFFD", "A\u{1F600}B", "\uFEFFid"]) {
    const id = ClauseId.of(handle);
    const program = new MapProgram().with(id, Clause.fact(p));
    const restored = programFromValue(programToValue(program));
    assert.ok(restored.clause(id));
    assert.deepEqual(programBytes(restored), programBytes(program));
  }
});

test("opaque native handles still check locally and refuse lossy portable encoding", () => {
  const replacement = ClauseId.of("A\uFFFD");
  for (const handle of ["A\uD800", "A\uDC00"]) {
    const id = ClauseId.of(handle);
    const program = new MapProgram().with(id, Clause.fact(p)).with(replacement, Clause.fact(Goal.of("other", [])));
    const claim = p.asGround();
    const proof = new Derivation([new RuleNode(claim, id, new Map(), [])], 0);
    assert.ok(Outcome.isAccept(check(program, claim, proof, undefined, profile)));
    assert.equal(Outcome.isAccept(check(program, Goal.of("other", []).asGround(), proof, undefined, profile)), false);
    for (const encode of [programToValue, programBytes]) {
      assert.throws(() => encode(program), (e) => e.name === "ClauseIdEncodingError" && e.clauseId === handle);
    }
  }
});
