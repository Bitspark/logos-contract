import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom, Tuple } from "@bitspark/ontos-core";
import * as contract from "@bitspark/logos-contract";

test("Ontos supplies ground values and Logos supplies terms with variables", () => {
  assert.equal("Atom" in contract, false);
  assert.equal("Tuple" in contract, false);
  const atom = new Atom(Uint8Array.of(97));
  const ground = new Tuple([atom]);
  const term = contract.Term.tuple([contract.Term.atom(Uint8Array.of(97))]);
  assert.ok(contract.Term.fromValue(ground).equals(term));
  assert.ok(contract.Term.fromValue(contract.Term.eraseGround(term)).equals(term));
  assert.equal(contract.Term.eraseGround(contract.Term.tuple([contract.Term.var("X")])), undefined);
});

test("typed checking retains the receiver's judgment and distinguishes four outcomes", () => {
  const t = contract.typed;
  const expected = t.pi(t.nat(), t.nat());
  const input = t.statement({ foundation: t.FOUNDATION, declarations: [], context: [], expected });
  const proof = t.lam(t.nat(), t.variable(0));
  const policy = t.policy({ foundation: t.FOUNDATION, checker: t.CHECKER, dependencies: [] });
  const limits = t.defaultLimits();
  assert.deepEqual([t.MAX_INPUT_DEPTH, t.MAX_DEPTH, t.MAX_NATURAL], [128, 512, 0xffff_ffff]);
  assert.deepEqual([limits.inputDepth, limits.depth], [t.MAX_INPUT_DEPTH, t.MAX_DEPTH]);
  const accepted = t.check(input, proof, policy);
  assert.equal(accepted.kind, "accepted");
  assert.equal(accepted.accepted.statement.expected.kind, "pi");
  assert.equal(accepted.accepted.candidate.kind, "lam");
  assert.deepEqual(accepted.accepted.dependencies, []);
  const invalid = t.check(input, t.falseValue(), policy, limits);
  assert.deepEqual([invalid.kind, invalid.code], ["invalid", "type-mismatch"]);
  const incomplete = t.check(input, proof, policy, t.limits({ ...limits, work: 0 }));
  assert.deepEqual([incomplete.kind, incomplete.code], ["incomplete", "work"]);
  const unsupported = t.check(input, proof, t.policy({ ...policy, checker: "unselected" }), limits);
  assert.deepEqual([unsupported.kind, unsupported.code], ["unsupported", "unadmitted-checker"]);
  const universe = t.statement({ foundation: t.FOUNDATION, declarations: [], context: [], expected: t.sort(t.MAX_NATURAL) });
  const cap = t.check(universe, t.sort(t.MAX_NATURAL - 1), policy);
  assert.deepEqual([cap.kind, cap.code], ["incomplete", "universe-capacity"]);
});
