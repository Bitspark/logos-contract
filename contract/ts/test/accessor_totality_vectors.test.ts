/*
 * TS replay of vectors/accessor_totality.json — the BodyLit accessor family's behaviour around
 * the count variant.
 *
 * Every case carries ONE outcome, the same in every core: the file is an interface section
 * (vectors/CORPUS-CLASSES.md). It keyed outcomes per core until #2733, because the partial
 * inner() accessor failed differently on a count (the empty goal here, a trap in rs, #728). That
 * accessor was deleted tri-core (#2733, seat:caa's D1), and the total asInner() is the only one.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
  BodyLit,
  CountLit,
  Goal,
  PredicateRef,
  ProjectSpec,
  Symbol as LSymbol,
  Term,
} from "../src/index.js";

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "accessor_totality.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/accessor_totality.json");
    dir = parent;
  }
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function loadFile(): any {
  return JSON.parse(
    fs.readFileSync(path.join(repoRoot(), "vectors", "accessor_totality.json"), "utf8"),
  );
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function fixtureGoal(fixture: any): Goal {
  const atom: string = fixture.goal.args[0].atom_str;
  return new Goal(LSymbol.of(fixture.goal.pred), [
    Term.atom(new TextEncoder().encode(atom)),
  ]);
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function build(variant: string, fixture: any): BodyLit {
  switch (variant) {
    case "pos":
      return BodyLit.pos(fixtureGoal(fixture));
    case "neg":
      return BodyLit.neg(fixtureGoal(fixture));
    case "count": {
      const c = fixture.count;
      assert.equal(c.project, "rows", "fixture count project must be rows");
      return BodyLit.count(
        new CountLit(
          new PredicateRef(LSymbol.of(c.pred), c.arity),
          [],
          ProjectSpec.rows(),
          Term.var(c.count_var),
        ),
      );
    }
    default:
      throw new Error(`unknown variant ${variant}`);
  }
}

const decoder = new TextDecoder();

/** Classify a returned goal against the closed outcome vocabulary. */
function classify(g: Goal, expected: Goal): string {
  const pred = decoder.decode(g.pred.bytes());
  const expectedPred = decoder.decode(expected.pred.bytes());
  if (pred === expectedPred && g.args.length === expected.args.length) return "goal";
  return "other";
}

/** Observe one accessor and map its result onto the outcome vocabulary. */
function observe(bl: BodyLit, accessor: string, expected: Goal): string {
  if (accessor === "as_inner") {
    const g = bl.asInner();
    return g === null ? "none" : classify(g, expected);
  }
  return "unknown_accessor";
}

test("accessor_totality vectors replay (ts arm)", () => {
  const file = loadFile();
  assert.equal(file.cases.length, 3, "the pin file carries exactly 3 cases");
  const expected = fixtureGoal(file.fixture);
  for (const c of file.cases) {
    // An interface section: ONE outcome for every core, never an object keyed by core.
    assert.equal(typeof c.outcome, "string", `case ${c.name}: the outcome must be one value for every core`);
    const pinned: string = c.outcome;
    const bl = build(c.variant, file.fixture);
    assert.equal(observe(bl, c.accessor, expected), pinned, `case ${c.name}`);
  }
});
