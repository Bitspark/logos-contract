import assert from "node:assert/strict";
import test from "node:test";
import { typed as t } from "../src/index.js";
import { isExpr } from "../src/typed/expr.js";
import { isDeclaration, isLimits, isPolicy, isStatement } from "../src/typed/model.js";

const statement = (declarations: readonly t.Declaration[] = []): t.Statement =>
  t.statement({ foundation: t.FOUNDATION, declarations, context: [], expected: t.nat() });
const policy = (dependencies: readonly string[] = []): t.Policy =>
  t.policy({ foundation: t.FOUNDATION, checker: t.CHECKER, dependencies });
function refused(outcome: t.Outcome, kind: string, code: string): void {
  assert.equal(outcome.kind, kind);
  if (outcome.kind === "accepted") throw new Error("unexpected acceptance");
  assert.equal(outcome.code, code);
}

test("typed expression ownership follows immutable object identity across await", async () => {
  const first = t.zero();
  const forged = { ...first } as t.Expr;
  await Promise.resolve();
  t.succ(t.zero());
  assert.ok(isExpr(first));
  assert.equal(isExpr(forged), false);
  assert.equal(t.check(statement(), first, policy()).kind, "accepted");
  refused(t.check(statement(), forged, policy()), "invalid", "malformed-input");
  assert.throws(() => { (first as unknown as { kind: string }).kind = "true"; });
});

test("typed declaration ownership preserves its own copied assumptions across await", async () => {
  const dependencies = ["basis"];
  const first = t.assume("value", t.nat(), dependencies);
  const forged = { ...first } as t.Declaration;
  dependencies[0] = "other";
  await Promise.resolve();
  t.assume("value", t.bool(), ["other"]);
  assert.ok(isDeclaration(first));
  assert.equal(isDeclaration(forged), false);
  assert.equal(t.check(statement([first]), t.constant("value"), policy(["basis"])).kind, "accepted");
  refused(t.check(statement([forged]), t.zero(), policy()), "invalid", "malformed-input");
  assert.deepEqual(first.kind === "assume" ? first.dependencies : [], ["basis"]);
});

test("typed statement ownership preserves receiver storage across await", async () => {
  const declarations: t.Declaration[] = [];
  const context: t.Expr[] = [];
  const first = t.statement({ foundation: t.FOUNDATION, declarations, context, expected: t.nat() });
  const forged = { ...first } as t.Statement;
  declarations.push(t.define("invalid", t.nat(), t.trueValue()));
  context.push(t.zero());
  await Promise.resolve();
  statement(declarations);
  assert.ok(isStatement(first));
  assert.equal(isStatement(forged), false);
  assert.equal(t.check(first, t.zero(), policy()).kind, "accepted");
  refused(t.check(forged, t.zero(), policy()), "invalid", "malformed-input");
  assert.deepEqual(first.declarations, []);
  assert.deepEqual(first.context, []);
});

test("typed policy ownership preserves receiver permission across await", async () => {
  const dependencies = ["basis"];
  const first = policy(dependencies);
  const forged = { ...first } as t.Policy;
  dependencies[0] = "other";
  await Promise.resolve();
  const narrowed = policy();
  const s = statement([t.assume("value", t.nat(), ["basis"])]);
  assert.ok(isPolicy(first));
  assert.equal(isPolicy(forged), false);
  assert.equal(t.check(s, t.constant("value"), first).kind, "accepted");
  refused(t.check(s, t.constant("value"), narrowed), "unsupported", "unadmitted-dependency");
  refused(t.check(s, t.constant("value"), forged), "invalid", "malformed-input");
});

test("typed limit ownership preserves one invocation allowance across await", async () => {
  const input = { ...t.defaultLimits(), work: 0 };
  const first = t.limits(input);
  const forged = { ...first } as t.Limits;
  input.work = 1_000_000;
  await Promise.resolve();
  const other = t.defaultLimits();
  assert.ok(isLimits(first));
  assert.equal(isLimits(forged), false);
  refused(t.check(statement(), t.zero(), policy(), first), "incomplete", "work");
  refused(t.check(statement(), t.zero(), policy(), forged), "invalid", "malformed-input");
  assert.equal(t.check(statement(), t.zero(), policy(), other).kind, "accepted");
});
