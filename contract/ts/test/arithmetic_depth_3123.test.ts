/*
 * #3123: an arithmetic expression's depth is never a decided false. Until #3123 each core's
 * evaluator recursed once per level and stopped at 256 levels, and the stop was read as fails, so
 * `not(1 =:= E)` with E 257 levels deep could be answered and certified. The walk is iterative
 * now, so a deep expression evaluates; the only depth limit left is the caller's
 * CheckLimits.maxTermDepth, a completed policy decision check makes before any theory.
 *
 * Every witness is placed against OLD_ARITH_DEPTH_CAP and carries a control inside it. The same
 * cases are pinned in contract/rs (tests/arithmetic_depth_3123.rs) and contract/go
 * (arithmetic_depth_3123_test.go).
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom, tuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";
import {
  AlwaysAdmit,
  ArithmeticTheory,
  BuiltinNode,
  CertContext,
  check,
  checkClosedModelChain,
  type CheckLimits,
  type CheckProfile,
  Clause,
  ClosedModelCert,
  defaultLimits,
  Derivation,
  edbTableHash,
  type Evidence,
  FiniteDomain,
  Goal,
  GroundLiteral,
  type Hash,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  type Outcome,
  PredicateSet,
  programDigestOf,
  RelationTable,
  StratumPrefix,
  Symbol,
  Term,
  type TheoryOutcome,
} from "../src/index.js";

/** The depth at which the recursive evaluator stopped until #3123. */
const OLD_ARITH_DEPTH_CAP = 256;

/** The depths every witness runs at: a control inside the old cap, and two past it. */
const DEPTHS: ReadonlyArray<readonly [string, number]> = [
  ["control, inside the old cap", OLD_ARITH_DEPTH_CAP - 56],
  ["one past the old cap", OLD_ARITH_DEPTH_CAP + 1],
  ["well past the old cap", OLD_ARITH_DEPTH_CAP + 50],
];

const utf8 = new TextEncoder();
const int = (n: number): Value => encodeInt(BigInt(n));

/** '+'('+'(… int(1) …, int(0)), int(0)): `levels` operators over int(1), value 1. */
function deepOne(levels: number): Value {
  let e = int(1);
  for (let i = 0; i < levels; i += 1) {
    e = tuple([atom(utf8.encode("+")), e, int(0)]);
  }
  return e;
}

function decide(pred: string, lhs: Value, rhs: Value): TheoryOutcome {
  return new ArithmeticTheory().decide(GroundLiteral.of(pred, [lhs, rhs]));
}

test("#3123: the theory decides a deep expression by its value, in both polarities", () => {
  const wrong: string[] = [];
  for (const [name, levels] of DEPTHS) {
    const cases: ReadonlyArray<readonly [string, TheoryOutcome, boolean]> = [
      ["1 =:= E holds", decide("=:=", int(1), deepOne(levels)), true],
      ["2 =\\= E holds", decide("=\\=", int(2), deepOne(levels)), true],
      ["1 =\\= E fails", decide("=\\=", int(1), deepOne(levels)), false],
      ["1 is E holds", decide("is", int(1), deepOne(levels)), true],
      ["0 < E holds", decide("<", int(0), deepOne(levels)), true],
    ];
    for (const [what, got, want] of cases) {
      if ((got.kind === "holds") !== want) {
        wrong.push(`${name}: ${what}, got ${JSON.stringify(got)}`);
      }
    }
  }
  assert.deepEqual(wrong, []);
});

test("#3123: a 100,000-level expression is decided without one JS frame per level", () => {
  // The JS stack holds a few thousand frames on any V8 tier, so a recursive walk throws a
  // RangeError here; the iterative one does not.
  const got = decide("=:=", int(1), deepOne(100_000));
  assert.equal(got.kind, "holds", `1 =:= E must hold, got ${JSON.stringify(got)}`);
});

// test-double: consumer(an empty extensional set; admits nothing because nothing is a leaf)
const noLeaves: LeafVerifier<void> = {
  extensional: (): PredicateSet => PredicateSet.from([]),
  verify: (_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome => LeafOutcome.Reject("no_leaves"),
};

function verdict(o: Outcome): string {
  return o.kind === "accept" ? "accept" : `${o.code} (${o.detail})`;
}

function code(o: Outcome): string {
  return o.kind === "accept" ? "accept" : o.code;
}

function wide(): CheckLimits {
  return { ...defaultLimits(), maxTermDepth: 1_024 };
}

/** Check one Builtin node concluding pred(lhs, E) under limits. */
function checkBuiltin(pred: string, lhs: number, levels: number, limits: CheckLimits): Outcome {
  const claim = GroundLiteral.of(pred, [int(lhs), deepOne(levels)]);
  const deriv = new Derivation([new BuiltinNode(claim)], 0);
  const profile: CheckProfile<void> = {
    theory: new ArithmeticTheory(),
    leaves: noLeaves,
    admit: new AlwaysAdmit<void>(),
    limits,
  };
  return check(new MapProgram(), claim, deriv, undefined, profile);
}

test("#3123: a deep Builtin node is decided by value, or refused term_too_deep by the caller's budget", () => {
  const wrong: string[] = [];
  for (const [name, levels] of DEPTHS) {
    // Term depth is the operator levels plus 2 (the int leaf is int(Atom)).
    const wantDefault = levels + 2 > defaultLimits().maxTermDepth ? "term_too_deep" : "accept";
    const cases: ReadonlyArray<readonly [string, Outcome, string]> = [
      ["=:=(1, E), default budget", checkBuiltin("=:=", 1, levels, defaultLimits()), wantDefault],
      ["=:=(1, E), a budget that covers it", checkBuiltin("=:=", 1, levels, wide()), "accept"],
      ["=\\=(2, E), a budget that covers it", checkBuiltin("=\\=", 2, levels, wide()), "accept"],
      // The relation is false, decided by a completed evaluation.
      ["=\\=(1, E), a budget that covers it", checkBuiltin("=\\=", 1, levels, wide()), "builtin_failed"],
    ];
    for (const [what, got, want] of cases) {
      if (code(got) !== want) {
        wrong.push(`${name}: ${what}: ${verdict(got)}, want ${want}`);
      }
    }
  }
  assert.deepEqual(wrong, []);
});

// The certified form: a closed-model certificate's closure reads the comparison through
// theoryTruth. Sealing r EMPTY claims r(a) is false; a closure that reads a capacity as false
// accepts that claim, and every negation citing the certificate inherits it.

const A = atom(utf8.encode("a"));
const dA = GroundLiteral.of("d", [A]);

// test-double: consumer(admits every leaf and attests d's one-row EDB snapshot)
const dLeaves: LeafVerifier<void> = {
  extensional: (): PredicateSet => PredicateSet.from(["d"]),
  verify: (_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome => LeafOutcome.Admit,
  edbSnapshot: (pred: Symbol, _ctx: void): Hash | undefined =>
    pred.equals(Symbol.of("d")) ? edbTableHash(pred, [dA]) : undefined,
};

/** One certificate sealing {d, r}, with d = {d(a)} and r EMPTY, under the arithmetic theory. */
function rSealedEmpty(program: MapProgram, limits: CheckLimits): Outcome {
  const d = Symbol.of("d");
  const pin: Hash = new Uint8Array(32).fill(7);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [d, Symbol.of("r")]),
    programHash: programDigestOf(program),
    profileHash: pin,
    ctxHash: pin,
    theoryConfigHash: pin,
    edbSnapshotHashes: [edbTableHash(d, [dA])],
    domains: [FiniteDomain.of(Symbol.of("v"), [A])],
    extensions: [RelationTable.of(d, 1, [dA]), RelationTable.of(Symbol.of("r"), 1, [])],
    supports: [],
    limitsDecl: {
      certFacts: 1,
      domainValues: 1,
      supportEdges: 0,
      ruleGroundings: 1_000,
      joinSteps: 10_000,
      certBytes: 4_096,
    },
  });
  const profile: CheckProfile<void> = {
    theory: new ArithmeticTheory(),
    leaves: dLeaves,
    admit: new AlwaysAdmit<void>(),
    limits,
  };
  return checkClosedModelChain(program, [cert], undefined, profile, CertContext.of(programDigestOf(program), pin, pin, pin));
}

const x = Term.var("X");
const cmp = (pred: string, lhs: number, levels: number): Goal =>
  Goal.of(pred, [Term.fromValue(int(lhs)), Term.fromValue(deepOne(levels))]);

/** `r(X) :- d(X), pred(lhs, E).` */
function rIf(pred: string, lhs: number, levels: number): MapProgram {
  return new MapProgram().with("r_if", new Clause(Goal.of("r", [x]), [Goal.of("d", [x]), cmp(pred, lhs, levels)]));
}

/** `r(X) :- d(X), \+ pred(lhs, E).` */
function rUnless(pred: string, lhs: number, levels: number): MapProgram {
  return new MapProgram().with(
    "r_unless",
    Clause.withNeg(Goal.of("r", [x]), [Goal.of("d", [x])], [cmp(pred, lhs, levels)]),
  );
}

// r sealed empty is accepted exactly when the comparison in the clause body, read by value, keeps
// r(a) out of the model; when r(a) is in the model the table is refused as not closed. Either
// verdict may instead be term_too_deep, the caller's budget: the chain path does not apply
// maxTermDepth to the program's clauses today (it measures only the certificate's own data), so at
// the default budget the closure reaches the theory and decides E by value. That gap is a
// budget-enforcement residue named on #3123's PR, not a soundness one, and this test does not pin
// it either way.
test("#3123: a certificate sealing r empty is judged by the comparison's value", () => {
  const wrong: string[] = [];
  for (const [name, levels] of DEPTHS) {
    for (const limits of [defaultLimits(), wide()]) {
      const cases: ReadonlyArray<readonly [string, MapProgram, boolean]> = [
        ["r(X) :- d(X), 1 =:= E", rIf("=:=", 1, levels), true],
        ["r(X) :- d(X), 2 =\\= E", rIf("=\\=", 2, levels), true],
        ["r(X) :- d(X), 1 =\\= E", rIf("=\\=", 1, levels), false],
        ["r(X) :- d(X), \\+ 1 =:= E", rUnless("=:=", 1, levels), false],
        ["r(X) :- d(X), \\+ 2 =:= E", rUnless("=:=", 2, levels), true],
      ];
      for (const [clause, program, rHolds] of cases) {
        const got = rSealedEmpty(program, limits);
        // r(a) in the model: sealing r empty must be refused. Otherwise it is accepted.
        const c = code(got);
        const ok = c === "term_too_deep" || (rHolds ? c === "cert_not_closed" : c === "accept");
        if (!ok) {
          wrong.push(`${name}, maxTermDepth ${limits.maxTermDepth}: ${clause}: ${verdict(got)}, r(a) holds=${rHolds}`);
        }
      }
    }
  }
  assert.deepEqual(wrong, []);
});
