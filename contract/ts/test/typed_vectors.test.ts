import assert from "node:assert/strict";
import test from "node:test";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { typed as t } from "../src/index.js";

interface FixtureDeclaration {
  readonly kind: "assume" | "define";
  readonly symbol: string;
  readonly type: unknown;
  readonly dependencies?: readonly string[];
  readonly value?: unknown;
}
interface FixtureLimits {
  readonly input_nodes: number; readonly input_depth: number;
  readonly collection_entries: number; readonly name_bytes: number;
  readonly work: number; readonly depth: number;
}
interface FixtureCase {
  readonly id: string;
  readonly statement: { readonly declarations: string; readonly context: readonly unknown[];
    readonly expected: unknown; readonly foundation?: string };
  readonly candidate: unknown;
  readonly policy: { readonly dependencies: readonly string[];
    readonly foundation?: string; readonly checker?: string };
  readonly limits?: Partial<FixtureLimits>;
  readonly expect: { readonly status: string; readonly code?: string;
    readonly dependencies?: readonly string[] };
}
interface FixtureFile {
  readonly schema: string;
  readonly foundation: string;
  readonly declaration_sets: Readonly<Record<string, readonly FixtureDeclaration[]>>;
  readonly cases: readonly FixtureCase[];
}

function loadFixtures(): FixtureFile {
  let directory = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(directory, "vectors", "typed_check.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8")) as FixtureFile;
    const parent = path.dirname(directory);
    if (parent === directory) throw new Error("could not locate vectors/typed_check.json");
    directory = parent;
  }
}

// The shared JSON is test notation only. Every expression is built through the
// production syntax constructors; this loader supplies no checking or reduction.
function expression(raw: unknown): t.Expr {
  assert.ok(Array.isArray(raw));
  const tag = raw[0] as string;
  const arities: Readonly<Record<string, number>> = { sort: 1, var: 1, const: 1,
    pi: 2, lam: 2, app: 2, sigma: 2, pair: 3, fst: 1, snd: 1, nat: 0, zero: 0,
    succ: 1, "nat-elim": 4, bool: 0, false: 0, true: 0, "bool-elim": 4,
    id: 3, refl: 2, transport: 6 };
  assert.ok(Object.hasOwn(arities, tag), `unknown fixture constructor ${tag}`);
  assert.equal(raw.length, arities[tag]! + 1, `fixture constructor arity: ${tag}`);
  const at = (index: number): t.Expr => expression(raw[index]);
  switch (tag) {
    case "sort": return t.sort(raw[1] as number);
    case "var": return t.variable(raw[1] as number);
    case "const": return t.constant(raw[1] as string);
    case "pi": return t.pi(at(1), at(2));
    case "lam": return t.lam(at(1), at(2));
    case "app": return t.app(at(1), at(2));
    case "sigma": return t.sigma(at(1), at(2));
    case "pair": return t.pair(at(1), at(2), at(3));
    case "fst": return t.fst(at(1));
    case "snd": return t.snd(at(1));
    case "nat": return t.nat();
    case "zero": return t.zero();
    case "succ": return t.succ(at(1));
    case "nat-elim": return t.natElim(at(1), at(2), at(3), at(4));
    case "bool": return t.bool();
    case "false": return t.falseValue();
    case "true": return t.trueValue();
    case "bool-elim": return t.boolElim(at(1), at(2), at(3), at(4));
    case "id": return t.id(at(1), at(2), at(3));
    case "refl": return t.refl(at(1), at(2));
    case "transport": return t.transport(at(1), at(2), at(3), at(4), at(5), at(6));
    default: throw new Error(`unknown fixture constructor ${tag}`);
  }
}

function declaration(raw: FixtureDeclaration): t.Declaration {
  if (raw.kind === "assume") return t.assume(raw.symbol, expression(raw.type), raw.dependencies!);
  assert.equal(raw.kind, "define");
  return t.define(raw.symbol, expression(raw.type), expression(raw.value));
}

const fixtures = loadFixtures();
assert.equal(fixtures.schema, "logos/typed-check-fixtures/v1");
assert.equal(fixtures.foundation, t.FOUNDATION);
assert.ok(fixtures.cases.length > 0);

function statement(c: FixtureCase, declarations?: readonly t.Declaration[]): t.Statement {
  const raw = fixtures.declaration_sets[c.statement.declarations];
  assert.ok(raw !== undefined, `unknown declaration set: ${c.statement.declarations}`);
  return t.statement({ foundation: c.statement.foundation ?? fixtures.foundation,
    declarations: declarations ?? raw.map(declaration), context: c.statement.context.map(expression),
    expected: expression(c.statement.expected) });
}
function policy(c: FixtureCase): t.Policy {
  return t.policy({ foundation: c.policy.foundation ?? fixtures.foundation,
    checker: c.policy.checker ?? t.CHECKER, dependencies: c.policy.dependencies });
}
function limits(c: FixtureCase): t.Limits {
  const defaults = t.defaultLimits();
  const raw = c.limits ?? {};
  return t.limits({ inputNodes: raw.input_nodes ?? defaults.inputNodes,
    inputDepth: raw.input_depth ?? defaults.inputDepth,
    collectionEntries: raw.collection_entries ?? defaults.collectionEntries,
    nameBytes: raw.name_bytes ?? defaults.nameBytes,
    work: raw.work ?? defaults.work, depth: raw.depth ?? defaults.depth });
}
function eachBudgetRaised(base: t.Limits): readonly t.Limits[] {
  const fields: readonly (keyof t.LimitsInput)[] = ["inputNodes", "inputDepth",
    "collectionEntries", "nameBytes", "work", "depth"];
  return fields.map((field) => t.limits({ ...base,
    [field]: Math.min(t.MAX_NATURAL, base[field] + 1_000) }));
}
function expectOutcome(c: FixtureCase, actual: t.Outcome): void {
  assert.equal(actual.kind, c.expect.status, `${c.id}: ${JSON.stringify(actual)}`);
  if (actual.kind === "accepted") assert.deepEqual(actual.accepted.dependencies, c.expect.dependencies, c.id);
  else assert.equal(actual.code, c.expect.code, c.id);
}

for (const c of fixtures.cases) {
  test(`typed shared fixture: ${c.id}`, () => {
    const s = statement(c);
    const candidate = expression(c.candidate);
    const p = policy(c);
    const allowance = limits(c);
    const outcome = t.check(s, candidate, p, allowance);
    expectOutcome(c, outcome);
    if (outcome.kind !== "accepted") return;
    assert.deepEqual(outcome.accepted.statement, s);
    assert.deepEqual(outcome.accepted.candidate, candidate);
    assert.deepEqual(outcome.accepted.policy, p);
    // R3: increasing each allowance independently preserves successful meaning.
    for (const raised of eachBudgetRaised(allowance)) {
      const next = t.check(s, candidate, p, raised);
      expectOutcome(c, next);
      if (next.kind !== "accepted") throw new Error("raising a budget lost acceptance");
      assert.deepEqual(next.accepted.statement, outcome.accepted.statement);
      assert.deepEqual(next.accepted.candidate, outcome.accepted.candidate);
      assert.deepEqual(next.accepted.policy, outcome.accepted.policy);
      assert.deepEqual(next.accepted.dependencies, outcome.accepted.dependencies);
    }
  });
}

test("public Page theorem acceptance is reused as a checked definition for Person and nested Page", () => {
  const findCase = (id: string): FixtureCase => {
    const found = fixtures.cases.find((c) => c.id === id);
    assert.ok(found !== undefined, `missing Page fixture ${id}`);
    return found;
  };
  const symbolic = findCase("page-symbolic-theorem");
  const declarations = fixtures.declaration_sets["page"]!.map(declaration);
  const theorem = declarations.pop()!;
  assert.equal(theorem.name, "page.proof");
  if (theorem.kind !== "define") throw new Error("Page fixture must provide an actual definition");
  const checked = t.check(t.statement({ foundation: fixtures.foundation, declarations,
    context: [], expected: theorem.type }), theorem.value, policy(symbolic), limits(symbolic));
  expectOutcome(symbolic, checked);
  if (checked.kind !== "accepted") throw new Error("closed Page theorem was not accepted");
  const imported = [...declarations, t.define("page.proof", checked.accepted.statement.expected,
    checked.accepted.candidate)];
  for (const id of ["page-checked-theorem-reuse", "page-person-application",
    "page-nested-application-consumes-both-projections",
    "page-nesting-cannot-substitute-membership-for-representation"]) {
    const c = findCase(id);
    expectOutcome(c, t.check(statement(c, imported), expression(c.candidate), policy(c), limits(c)));
  }
});
