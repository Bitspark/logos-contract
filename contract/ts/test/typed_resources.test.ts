import assert from "node:assert/strict";
import test from "node:test";
import { typed as t } from "../src/index.js";

const statement = (expected: t.Expr = t.nat(), context: readonly t.Expr[] = []): t.Statement =>
  t.statement({ foundation: t.FOUNDATION, declarations: [], context, expected });
const policy = (): t.Policy => t.policy({ foundation: t.FOUNDATION, checker: t.CHECKER, dependencies: [] });
const limits = (changes: Partial<t.LimitsInput>): t.Limits => t.limits({ ...t.defaultLimits(), ...changes });

function failure(result: t.Outcome, kind: "invalid" | "incomplete" | "unsupported", code: string): void {
  if (result.kind === "accepted") throw new Error("unexpected acceptance");
  assert.equal(result.kind, kind, JSON.stringify(result));
  assert.equal(result.code, code);
}

test("every input, work and structural bound is enforced without proving falsehood", () => {
  assert.equal(t.check(statement(), t.zero(), policy(), limits({ inputNodes: 2, inputDepth: 1 })).kind, "accepted");
  failure(t.check(statement(), t.zero(), policy(), limits({ inputNodes: 1 })), "incomplete", "input-nodes");
  failure(t.check(statement(), t.zero(), policy(), limits({ inputDepth: 0 })), "incomplete", "input-depth");
  failure(t.check(statement(), t.zero(), policy(), limits({ nameBytes: 0 })), "incomplete", "name-bytes");
  failure(t.check(statement(t.nat(), [t.nat()]), t.zero(), policy(), limits({ collectionEntries: 0 })),
    "incomplete", "collection-entries");
  failure(t.check(statement(), t.zero(), policy(), limits({ work: 0 })), "incomplete", "work");
  failure(t.check(statement(), t.zero(), policy(), limits({ depth: 0 })), "incomplete", "depth");
  let deep = t.zero();
  for (let i = 0; i < 128; i += 1) deep = t.succ(deep);
  failure(t.check(statement(), deep, policy(), limits({ inputDepth: 0xffff_ffff })), "incomplete", "input-depth");
});

test("finite universe capacity is noncompletion and does not wrap into a lower universe", () => {
  failure(t.check(statement(t.sort(0)), t.sort(0xffff_ffff), policy()), "incomplete", "universe-capacity");
  failure(t.check(statement(), t.sort(0x1_0000_0000), policy()), "incomplete", "universe-capacity");
  failure(t.check(statement(), t.variable(0x1_0000_0000), policy()), "incomplete", "index-capacity");
  failure(t.check(statement(), t.sort(Number.MAX_SAFE_INTEGER + 1), policy()), "invalid", "malformed-input");
  failure(t.check(statement(), t.variable(-1), policy()), "invalid", "malformed-input");
  failure(t.check(statement(), t.sort(Number.NaN), policy()), "invalid", "malformed-input");
  failure(t.check(statement(), t.zero(), policy(), limits({ work: Infinity })), "invalid", "malformed-input");
});

test("representation capacity never hides malformed later syntax", () => {
  const oversized = t.sort(0x1_0000_0000);
  for (const later of [t.sort(-1), t.variable(0.5), t.constant("\ud800"),
    null as unknown as t.Expr, { kind: "zero" } as t.Expr]) {
    failure(t.check(statement(), t.app(oversized, later), policy()), "invalid", "malformed-input");
  }
  failure(t.check(statement(), t.app(t.variable(0x1_0000_0000), t.sort(Number.NaN)), policy()),
    "invalid", "malformed-input");
  failure(t.check(statement(oversized), t.succ(null as unknown as t.Expr), policy()),
    "invalid", "malformed-input");
});

test("forged syntax, host getters and cyclic records cannot enter the checker", () => {
  const forged = { kind: "zero", extra: true };
  failure(t.check(statement(), forged as unknown as t.Expr, policy()), "invalid", "malformed-input");
  const cycle: { kind: string; value?: unknown } = { kind: "succ" };
  cycle.value = cycle;
  failure(t.check(statement(), cycle as unknown as t.Expr, policy()), "invalid", "malformed-input");
  failure(t.check(statement(), t.succ(null as unknown as t.Expr), policy()), "invalid", "malformed-input");
  let invoked = false;
  const object = Object.defineProperty({}, "kind", { get: () => { invoked = true; throw new Error("host"); } });
  failure(t.check(statement(), object as t.Expr, policy()), "invalid", "malformed-input");
  assert.equal(invoked, false);
  failure(t.check({ ...statement() } as t.Statement, t.zero(), policy()), "invalid", "malformed-input");
  failure(t.check(statement(), t.zero(), { ...policy() } as t.Policy), "invalid", "malformed-input");
});

test("name checking charges work, rejects malformed Unicode and uses UTF-8 byte length", () => {
  const declared = (name: string): t.Statement => t.statement({ foundation: t.FOUNDATION,
    declarations: [t.assume(name, t.nat(), ["basis"])], context: [], expected: t.nat() });
  failure(t.check(declared("\ud800"), t.zero(), policy()), "invalid", "malformed-input");
  failure(t.check(declared(""), t.zero(), policy()), "invalid", "empty-constant-name");
  failure(t.check(declared("é".repeat(129)), t.zero(), policy()), "incomplete", "name-bytes");
  failure(t.check(declared("x".repeat(10_000)), t.zero(), policy(), limits({ nameBytes: 20_000, work: 150 })),
    "incomplete", "work");
});

test("supported foundation and the receiver's actual checker basis are separately required", () => {
  const different = t.statement({ ...statement(), foundation: "unserved" });
  failure(t.check(different, t.zero(), policy()), "unsupported", "foundation");
  failure(t.check(statement(), t.zero(), t.policy({ ...policy(), foundation: "other" })),
    "unsupported", "unadmitted-foundation");
  failure(t.check(statement(), t.zero(), t.policy({ ...policy(), checker: "other" })),
    "unsupported", "unadmitted-checker");
});

test("shared input subtrees consume input nodes at each occurrence", () => {
  const shared = t.nat();
  const expected = t.pi(shared, shared);
  const candidate = t.lam(shared, t.variable(0));
  // Both roots and their operands total six nodes despite repeated host identities.
  failure(t.check(statement(expected), candidate, policy(), limits({ inputNodes: 5 })), "incomplete", "input-nodes");
  assert.equal(t.check(statement(expected), candidate, policy(), limits({ inputNodes: 6 })).kind, "accepted");
});

test("reported identities sort by UTF-8 order without Unicode normalization", () => {
  const declarations = [t.assume("value", t.nat(), ["\u{10000}", "\ue000", "e\u0301", "é"])];
  const s = t.statement({ foundation: t.FOUNDATION, declarations, context: [], expected: t.nat() });
  const p = t.policy({ foundation: t.FOUNDATION, checker: t.CHECKER,
    dependencies: ["\ue000", "é", "\u{10000}", "e\u0301"] });
  const result = t.check(s, t.constant("value"), p);
  assert.equal(result.kind, "accepted");
  if (result.kind === "accepted") {
    assert.deepEqual(result.accepted.dependencies, ["e\u0301", "é", "\ue000", "\u{10000}"]);
  }
});
