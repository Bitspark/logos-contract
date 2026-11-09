import assert from "node:assert/strict";
import test from "node:test";
import { typed as t } from "../src/index.js";

function statement(expected: t.Expr, declarations: readonly t.Declaration[] = [],
  context: readonly t.Expr[] = []): t.Statement {
  return t.statement({ foundation: t.FOUNDATION, declarations, context, expected });
}
function policy(dependencies: readonly string[] = []): t.Policy {
  return t.policy({ foundation: t.FOUNDATION, checker: t.CHECKER, dependencies });
}
function requireAccepted(result: t.Outcome): t.Acceptance {
  assert.equal(result.kind, "accepted", JSON.stringify(result));
  if (result.kind !== "accepted") throw new Error("expected accepted proof");
  return result.accepted;
}
function requireFailure(result: t.Outcome, kind: "invalid" | "incomplete" | "unsupported",
  code: string): void {
  if (result.kind === "accepted") throw new Error("unexpected acceptance");
  assert.equal(result.kind, kind, JSON.stringify(result));
  assert.equal(result.code, code);
}

test("typed identity checks dependent binder types and fixes the exact expected statement", () => {
  const expected = t.pi(t.sort(0), t.pi(t.variable(0), t.variable(1)));
  const proof = t.lam(t.sort(0), t.lam(t.variable(0), t.variable(0)));
  requireAccepted(t.check(statement(expected), proof, policy()));
  requireFailure(t.check(statement(t.pi(t.sort(0), t.pi(t.variable(0), t.nat()))),
    proof, policy()), "invalid", "type-mismatch");
  requireFailure(t.check(statement(t.sort(0)), t.sort(0), policy()), "invalid", "type-mismatch");
});

test("substitution lifts the free variable below a new binder", () => {
  const functionType = t.pi(t.nat(), t.nat());
  const application = t.app(t.lam(t.nat(), t.lam(t.nat(), t.variable(1))), t.variable(0));
  const expectedFunction = t.lam(t.nat(), t.variable(1));
  const proof = t.refl(functionType, expectedFunction);
  requireAccepted(t.check(statement(t.id(functionType, application, expectedFunction), [], [t.nat()]),
    proof, policy()));
  requireFailure(t.check(statement(t.id(functionType, application, t.lam(t.nat(), t.variable(0))),
    [], [t.nat()]), proof, policy()), "invalid", "type-mismatch");
  requireFailure(t.check(statement(t.nat()), t.variable(0), policy()), "invalid", "escaped-variable");
});

test("dependent pairs project the instantiated second component", () => {
  const pairType = t.sigma(t.sort(0), t.variable(0));
  const pair = t.pair(pairType, t.nat(), t.zero());
  requireAccepted(t.check(statement(t.sort(0)), t.fst(pair), policy()));
  requireAccepted(t.check(statement(t.nat()), t.snd(pair), policy()));
  requireFailure(t.check(statement(pairType), t.pair(pairType, t.nat(), t.trueValue()), policy()),
    "invalid", "type-mismatch");
  requireFailure(t.check(statement(t.nat()), t.fst(t.zero()), policy()), "invalid", "expected-sigma");
});

test("natural and Boolean eliminators follow their typed computation rules", () => {
  const two = t.succ(t.succ(t.zero()));
  const recurrence = t.natElim(t.lam(t.nat(), t.nat()), t.zero(),
    t.lam(t.nat(), t.lam(t.nat(), t.succ(t.variable(0)))), two);
  requireAccepted(t.check(statement(t.id(t.nat(), recurrence, two)), t.refl(t.nat(), two), policy()));
  requireFailure(t.check(statement(t.id(t.nat(), recurrence, t.zero())),
    t.refl(t.nat(), t.zero()), policy()), "invalid", "type-mismatch");
  const selectType = (value: t.Expr): t.Expr =>
    t.boolElim(t.lam(t.bool(), t.sort(0)), t.nat(), t.bool(), value);
  requireAccepted(t.check(statement(selectType(t.falseValue())), t.zero(), policy()));
  requireAccepted(t.check(statement(selectType(t.trueValue())), t.trueValue(), policy()));
  requireFailure(t.check(statement(selectType(t.trueValue())), t.zero(), policy()), "invalid", "type-mismatch");
});

test("identity transport requires both endpoints and the exact dependent motive", () => {
  const transported = t.transport(t.nat(), t.zero(), t.zero(), t.refl(t.nat(), t.zero()),
    t.lam(t.nat(), t.nat()), t.zero());
  requireAccepted(t.check(statement(t.nat()), transported, policy()));
  requireFailure(t.check(statement(t.nat()), t.transport(t.nat(), t.zero(), t.succ(t.zero()),
    t.refl(t.nat(), t.zero()), t.lam(t.nat(), t.nat()), t.zero()), policy()), "invalid", "type-mismatch");
});

test("reachable declaration and context basis is computed, including erased arguments", () => {
  const declarations = [
    t.assume("A", t.sort(0), ["source.type"]),
    t.define("B", t.sort(0), t.constant("A")),
    t.assume("a", t.constant("A"), ["source.value"]),
    t.assume("irrelevant", t.sort(0), ["unused.assumption"]),
  ];
  const result = requireAccepted(t.check(statement(t.constant("B"), declarations), t.constant("a"),
    policy(["source.type", "source.value", "unused.allowance"])));
  assert.deepEqual(result.dependencies, ["source.type", "source.value"]);
  assert.deepEqual(result.usedConstants, ["A", "B", "a"]);
  requireFailure(t.check(statement(t.constant("B"), declarations), t.constant("a"),
    policy(["source.type"])), "unsupported", "unadmitted-dependency");
  const erased = t.app(t.lam(t.constant("A"), t.zero()), t.constant("a"));
  const erasedResult = requireAccepted(t.check(statement(t.nat(), declarations), erased,
    policy(["source.type", "source.value"])));
  assert.deepEqual(erasedResult.dependencies, ["source.type", "source.value"]);
  const contextResult = requireAccepted(t.check(statement(t.nat(), declarations, [t.constant("A")]),
    t.zero(), policy(["source.type"])));
  assert.deepEqual(contextResult.dependencies, ["source.type"]);
});

test("all declarations are checked, including unused ones and forward references", () => {
  requireFailure(t.check(statement(t.nat(), [t.define("cycle", t.nat(), t.constant("cycle"))]),
    t.zero(), policy()), "invalid", "unknown-constant");
  requireFailure(t.check(statement(t.nat(), [t.assume("x", t.nat(), ["x"]),
    t.assume("x", t.nat(), ["x"])]), t.zero(), policy()), "invalid", "duplicate-constant");
  requireFailure(t.check(statement(t.nat(), [t.assume("x", t.nat(), [])]),
    t.zero(), policy()), "invalid", "missing-assumptions");
  const invalid = t.check(statement(t.nat(), [t.define("bad", t.nat(), t.trueValue())]), t.zero(), policy());
  requireFailure(invalid, "invalid", "type-mismatch");
  if (invalid.kind !== "accepted") assert.deepEqual(invalid.location, { phase: "declaration", index: 0 });
});

test("accepted association is privately minted, immutable and separate from caller storage", () => {
  const source = statement(t.nat());
  const result = requireAccepted(t.check(source, t.zero(), policy()));
  assert.notEqual(result.statement, source);
  assert.notEqual(result.statement.expected, source.expected);
  assert.ok(Object.isFrozen(result));
  assert.ok(Object.isFrozen(result.statement));
  assert.ok(Object.isFrozen(result.statement.expected));
  assert.ok(Object.isFrozen(result.statement.declarations));
  assert.ok(Object.isFrozen(result.policy.dependencies));
  assert.throws(() => { (result.statement as unknown as { foundation: string }).foundation = "other"; });
  const constructor = result.constructor as new (...args: unknown[]) => unknown;
  assert.throws(() => new constructor(Symbol("forged"), source, t.zero(), policy(), [], [], 0));
});

test("a checked theorem is reused through a checked definition, never a verdict-shaped premise", () => {
  const expected = t.pi(t.nat(), t.nat());
  const first = requireAccepted(t.check(statement(expected), t.lam(t.nat(), t.variable(0)), policy()));
  const imported = t.define("identity", first.statement.expected, first.candidate);
  requireAccepted(t.check(statement(t.nat(), [imported]), t.app(t.constant("identity"), t.zero()), policy()));
  requireFailure(t.check(statement(t.nat()), first as unknown as t.Expr, policy()), "invalid", "malformed-input");
});
