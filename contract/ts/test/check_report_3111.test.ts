/*
 * #3111 (checker SPI v2, ADR 0036 D8 change 5): `check` returns `Outcome { verdict, report }`, and
 * the report counts the work the check did by the rules in the module doc of
 * `contract/rs/src/check/report.rs`. These tests pin those rules on tiny hand-built derivations: the
 * ts port of contract/rs/tests/check_report_3111.rs, with the same derivations and the same exact
 * expected numbers. Every expected count below is computed by hand from the rules, never read back
 * from a run.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  BuiltinNode,
  CHECK_REPORT_COUNTERS_VERSION,
  check,
  type CheckLimits,
  type CheckProfile,
  CheckReport,
  Clause,
  ClauseId,
  defaultLimits,
  Derivation,
  Evidence,
  Goal,
  GroundLiteral,
  LeafNode,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  NegPremise,
  type Node,
  NodeMeta,
  Outcome,
  PredicateSet,
  type Premise,
  type RejectionCode,
  ReportCount,
  RuleNode,
  Subst,
  Symbol,
  Term,
  type Theory,
  TheoryGround,
  VarId,
} from "../src/index.js";

function bytes(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

/** `a < b` bytewise. */
function bytesLess(a: Uint8Array, b: Uint8Array): boolean {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    if (a[i] !== b[i]) return a[i]! < b[i]!;
  }
  return a.length < b.length;
}

/** Owns `lt`: `lt(a, b)` holds iff both arguments are atoms and `a < b` bytewise. */
// test-double: consumer(a less-than theory over atoms)
class LtTheory implements Theory {
  owns(pred: Symbol): boolean {
    return pred.equals(Symbol.of("lt"));
  }
  decideGround(atom: GroundLiteral): TheoryGround {
    const args = atom.args;
    if (args.length !== 2) return TheoryGround.fails("lt_arity");
    const a = args[0]!;
    const b = args[1]!;
    if (a.kind === "atom" && b.kind === "atom" && bytesLess(a.bytes(), b.bytes())) {
      return TheoryGround.holds();
    }
    return TheoryGround.fails("not_less_than");
  }
}

/** `edge` is extensional, and every `edge` leaf is admitted. */
// test-double: consumer(admits every leaf of its extensional set)
class EdgeLeaves implements LeafVerifier<void> {
  readonly #extensional = PredicateSet.from(["edge"]);
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcome.Admit;
  }
}

function profile(limits: CheckLimits): CheckProfile<void> {
  return { theory: new LtTheory(), leaves: new EdgeLeaves(), admit: new AlwaysAdmit<void>(), limits };
}

/** `path(X, Y) :- edge(X, Y).` and `step(X, Y) :- edge(X, Y), lt(X, Y).` */
function program(): MapProgram {
  const args = (): Term[] => [Term.var("X"), Term.var("Y")];
  return new MapProgram()
    .with("path_edge", new Clause(Goal.of("path", args()), [Goal.of("edge", args())]))
    .with("step", new Clause(Goal.of("step", args()), [Goal.of("edge", args()), Goal.of("lt", args())]));
}

function atom(s: string): Value {
  return valueAtom(bytes(s));
}

function lit(pred: string, x: string, y: string): GroundLiteral {
  return GroundLiteral.of(pred, [atom(x), atom(y)]);
}

/** `X = x, Y = y`. */
function xy(x: string, y: string): Subst {
  return new Subst([
    [new VarId("X"), Term.fromValue(atom(x))],
    [new VarId("Y"), Term.fromValue(atom(y))],
  ]);
}

function leaf(x: string, y: string): Node {
  return new LeafNode(lit("edge", x, y), Evidence.none());
}

function rule(pred: string, clause: string, x: string, y: string, premises: Premise[]): Node {
  return new RuleNode(lit(pred, x, y), ClauseId.of(clause), xy(x, y), premises, NodeMeta.none());
}

function run(claim: GroundLiteral, deriv: Derivation, limits: CheckLimits): Outcome {
  return check(program(), claim, deriv, undefined, profile(limits));
}

const counted = ReportCount.counted;

/** The rejection's code, `undefined` on an accept. */
function code(outcome: Outcome): RejectionCode | undefined {
  return outcome.verdict.kind === "accept" ? undefined : outcome.verdict.code;
}

type Case = readonly [GroundLiteral, Derivation];

/** `path(a, b)` from one `edge(a, b)` leaf: two nodes. */
function small(): Case {
  const deriv = new Derivation([leaf("a", "b"), rule("path", "path_edge", "a", "b", [0])], 1);
  return [lit("path", "a", "b"), deriv];
}

/** `step(a, b)` from an `edge(a, b)` leaf and an `lt(a, b)` builtin: three nodes. */
function larger(): Case {
  const deriv = new Derivation(
    [leaf("a", "b"), new BuiltinNode(lit("lt", "a", "b")), rule("step", "step", "a", "b", [0, 1])],
    2,
  );
  return [lit("step", "a", "b"), deriv];
}

/**
 * `step(a, b)` whose second premise cites `lt(a, c)`, which holds but is not the grounded body
 * literal `lt(a, b)`: the rule node rejects at premise 1.
 */
function wrongSecondPremise(): Case {
  const deriv = new Derivation(
    [leaf("a", "b"), new BuiltinNode(lit("lt", "a", "c")), rule("step", "step", "a", "b", [0, 1])],
    2,
  );
  return [lit("step", "a", "b"), deriv];
}

/**
 * `step(b, a)` over an `lt(b, a)` builtin the theory decides false: the builtin node rejects before
 * the rule node is walked.
 */
function failingBuiltin(): Case {
  const deriv = new Derivation(
    [leaf("b", "a"), new BuiltinNode(lit("lt", "b", "a")), rule("step", "step", "b", "a", [0, 1])],
    2,
  );
  return [lit("step", "b", "a"), deriv];
}

/**
 * `path(a, b)` whose one premise is NEGATIVE against the clause's positive body literal: counted as
 * a negative premise, then refused on its polarity.
 */
function negativeAgainstPositive(): Case {
  const neg = new NegPremise(lit("edge", "a", "b"), 0, "direct_lookup");
  const deriv = new Derivation([rule("path", "path_edge", "a", "b", [neg])], 0);
  return [lit("path", "a", "b"), deriv];
}

test("#3111: an outcome's equality is its verdict's", () => {
  const [smallClaim, smallDeriv] = small();
  const [largerClaim, largerDeriv] = larger();
  const a = run(smallClaim, smallDeriv, defaultLimits());
  const b = run(largerClaim, largerDeriv, defaultLimits());
  assert.equal(a.verdict.kind, "accept");
  assert.equal(b.verdict.kind, "accept");
  // Two different-sized derivations, two different reports, one verdict: equal outcomes.
  assert.notDeepEqual(a.report, b.report, "two sizes, two reports");
  assert.ok(Outcome.equals(a, b), "an outcome's equality is its verdict's");
  // And the converse: equal work, different verdicts, unequal outcomes.
  const [wrongClaim, wrongDeriv] = wrongSecondPremise();
  const rejected = run(wrongClaim, wrongDeriv, defaultLimits());
  assert.equal(Outcome.equals(rejected, b), false);
});

test("#3111: the node kinds sum to nodes walked", () => {
  const cases: readonly (readonly [string, Case])[] = [
    ["small", small()],
    ["larger", larger()],
    ["wrong second premise", wrongSecondPremise()],
    ["failing builtin", failingBuiltin()],
    ["negative against positive", negativeAgainstPositive()],
  ];
  for (const [name, [claim, deriv]] of cases) {
    const outcome = run(claim, deriv, defaultLimits());
    assert.ok(
      CheckReport.nodeKindsSum(outcome.report),
      `${name}: the node kinds must sum to nodesWalked, got ${JSON.stringify(outcome.report)}`,
    );
  }
  // The control: a report whose kinds do not sum fails the check.
  const broken: CheckReport = { ...CheckReport.zero(), nodesWalked: counted(2), leafNodes: counted(1) };
  assert.equal(CheckReport.nodeKindsSum(broken), false);
});

test("#3111: a rejection reports the work up to the rejecting node", () => {
  // Node 0, the leaf: walked, depth 1, one leaf verification. Node 1, the builtin: walked, depth
  // 1, one theory decision (it holds). Node 2, the rule: walked, depth 2; step (f) counts premise
  // 0 (it matches), then premise 1, which rejects. No admissibility call is reached.
  {
    const [claim, deriv] = wrongSecondPremise();
    const outcome = run(claim, deriv, defaultLimits());
    assert.equal(code(outcome), "instantiation_mismatch");
    const r = outcome.report;
    assert.deepEqual(r.nodesWalked, counted(3));
    assert.deepEqual(r.ruleNodes, counted(1));
    assert.deepEqual(r.builtinNodes, counted(1));
    assert.deepEqual(r.leafNodes, counted(1));
    assert.deepEqual(r.premisesPos, counted(2));
    assert.deepEqual(r.premisesNeg, counted(0));
    assert.deepEqual(r.theoryDecisions, counted(1));
    assert.deepEqual(r.leafVerifications, counted(1));
    assert.deepEqual(r.admissibilityChecks, counted(0));
    assert.deepEqual(r.maxDepthReached, counted(2));
  }

  // The builtin decided false: nodes 0 and 1 are walked, node 2 never is.
  {
    const [claim, deriv] = failingBuiltin();
    const outcome = run(claim, deriv, defaultLimits());
    assert.equal(code(outcome), "builtin_failed");
    const expected: CheckReport = {
      ...CheckReport.zero(),
      nodesWalked: counted(2),
      builtinNodes: counted(1),
      leafNodes: counted(1),
      theoryDecisions: counted(1),
      leafVerifications: counted(1),
      maxDepthReached: counted(1),
      maxTermDepthReached: counted(1),
    };
    assert.deepEqual(outcome.report, expected);
  }

  // A negative premise is counted as negative before its polarity is checked.
  {
    const [claim, deriv] = negativeAgainstPositive();
    const outcome = run(claim, deriv, defaultLimits());
    assert.equal(code(outcome), "instantiation_mismatch");
    const expected: CheckReport = {
      ...CheckReport.zero(),
      nodesWalked: counted(1),
      ruleNodes: counted(1),
      premisesNeg: counted(1),
      maxDepthReached: counted(1),
      maxTermDepthReached: counted(1),
    };
    assert.deepEqual(outcome.report, expected);
  }
});

test("#3111: a limits refusal reports zeros", () => {
  const [claim, deriv] = small();
  // A budget past the safe-integer domain this host represents exactly (rs: a 64-bit `usize::MAX`
  // past the protocol index domain): the configuration is refused before any node is read.
  const limits: CheckLimits = { ...defaultLimits(), maxNodes: Number.MAX_SAFE_INTEGER + 1 };
  const outcome = run(claim, deriv, limits);
  assert.equal(code(outcome), "invalid_check_limits");
  assert.deepEqual(outcome.report, CheckReport.zero());
});

test("#3111: the other refusals before the walk report what they did", () => {
  // The node cap reads no node: zeros.
  const [smallClaim, deriv] = small();
  {
    const outcome = run(smallClaim, deriv, { ...defaultLimits(), maxNodes: 1 });
    assert.equal(code(outcome), "too_many_nodes");
    assert.deepEqual(outcome.report, CheckReport.zero());
  }

  // The term-depth cap measured the claim's first argument, `t(a)` (depth 2), against a cap of 1,
  // and stopped there: zeros, except the depth it measured.
  {
    const deep = valueTuple([atom("t"), atom("a")]);
    const claim = GroundLiteral.of("path", [deep, atom("b")]);
    const outcome = run(claim, deriv, { ...defaultLimits(), maxTermDepth: 1 });
    assert.equal(code(outcome), "term_too_deep");
    const expected: CheckReport = { ...CheckReport.zero(), maxTermDepthReached: counted(2) };
    assert.deepEqual(outcome.report, expected);
  }
});

test("#3111: an accepted check reports its exact work", () => {
  // Node 0, the leaf: depth 1, one leaf verification. Node 1, the builtin: depth 1, one theory
  // decision. Node 2, the rule: depth 2, two positive premises, one admissibility call. Every term
  // is an atom, so the deepest term is 1. No certificate is cited.
  {
    const [claim, deriv] = larger();
    const outcome = run(claim, deriv, defaultLimits());
    assert.equal(outcome.verdict.kind, "accept");
    const expected: CheckReport = {
      countersVersion: CHECK_REPORT_COUNTERS_VERSION,
      nodesWalked: counted(3),
      ruleNodes: counted(1),
      builtinNodes: counted(1),
      leafNodes: counted(1),
      premisesPos: counted(2),
      premisesNeg: counted(0),
      theoryDecisions: counted(1),
      leafVerifications: counted(1),
      admissibilityChecks: counted(1),
      certsVerified: counted(0),
      certsMemoHits: counted(0),
      certTablesRead: counted(0),
      certRowsRead: counted(0),
      joinStepsUsed: counted(0),
      groundingsEnumerated: counted(0),
      maxDepthReached: counted(2),
      maxTermDepthReached: counted(1),
    };
    assert.deepEqual(outcome.report, expected);
  }

  // The smaller derivation: one leaf and one rule over it.
  {
    const [claim, deriv] = small();
    const outcome = run(claim, deriv, defaultLimits());
    assert.equal(outcome.verdict.kind, "accept");
    const expected: CheckReport = {
      ...CheckReport.zero(),
      nodesWalked: counted(2),
      ruleNodes: counted(1),
      leafNodes: counted(1),
      premisesPos: counted(1),
      leafVerifications: counted(1),
      admissibilityChecks: counted(1),
      maxDepthReached: counted(2),
      maxTermDepthReached: counted(1),
    };
    assert.deepEqual(outcome.report, expected);
  }
});
