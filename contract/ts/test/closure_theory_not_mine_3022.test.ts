/*
 * #3022 step 4 (research 0028 A8), the negative witness uabszqyzof asked for on #3037: a
 * closed-model certificate's closure reads a theory-owned body literal through theoryTruth, and a
 * theory that OWNS the predicate but decides not_mine is refused predicate_partition_violation,
 * never read as false. Both polarities are planted, each against its control, a theory that decides
 * fails, which is what not_mine used to be read as. The same four cases are pinned in contract/rs
 * (tests/closure_theory_not_mine_3022.rs) and contract/go (closure_theory_not_mine_3022_test.go).
 *
 * - positive: `r(X) :- d(X), q(X).` over d(a), r sealed EMPTY. Read as false, not_mine left the
 *   body false, so the empty table looked closed and the certificate was accepted.
 * - negated: `r(X) :- d(X).` and `r(X) :- d(X), \+ q(X).` over d(a), r sealed {r(a)}. Read as
 *   false, not_mine made `\+ q(a)` TRUE, and the certificate was accepted.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  CertContext,
  checkClosedModelChain,
  Clause,
  ClauseId,
  ClosedModelCert,
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
  SupportEdge,
  SupportRef,
  Symbol,
  Term,
  type Theory,
  type TheoryOutcome,
  type CheckProfile,
  defaultLimits,
} from "../src/index.js";

const A = valueAtom(new TextEncoder().encode("a"));
const lit = (pred: string): GroundLiteral => GroundLiteral.of(pred, [A]);

// test-double: consumer(owns q and decides it with one fixed outcome)
function qTheory(outcome: TheoryOutcome): Theory {
  return {
    owns: (pred: Symbol): boolean => pred.equals(Symbol.of("q")),
    decide: (_atom: GroundLiteral): TheoryOutcome => outcome,
  };
}

// test-double: consumer(admits every leaf and attests d's one-row EDB snapshot)
const dLeaves: LeafVerifier<void> = {
  extensional: (): PredicateSet => PredicateSet.from(["d"]),
  verify: (_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome => LeafOutcome.Admit,
  edbSnapshot: (pred: Symbol, _ctx: void): Hash | undefined =>
    pred.equals(Symbol.of("d")) ? edbTableHash(pred, [lit("d")]) : undefined,
};

/** One certificate sealing {d, r} (d = {d(a)}, r = rRows, with edges) over program, under a theory
 * that decides q with outcome. */
function chain(program: MapProgram, rRows: GroundLiteral[], edges: SupportEdge[], outcome: TheoryOutcome): Outcome {
  const d = Symbol.of("d");
  const pin: Hash = new Uint8Array(32).fill(7);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [d, Symbol.of("r")]),
    programHash: programDigestOf(program),
    profileHash: pin,
    ctxHash: pin,
    theoryConfigHash: pin,
    edbSnapshotHashes: [edbTableHash(d, [lit("d")])],
    domains: [FiniteDomain.of(Symbol.of("v"), [A])],
    extensions: [RelationTable.of(d, 1, [lit("d")]), RelationTable.of(Symbol.of("r"), 1, rRows)],
    supports: edges,
    limitsDecl: {
      certFacts: 1 + rRows.length,
      domainValues: 1,
      supportEdges: edges.length,
      ruleGroundings: 1_000,
      joinSteps: 10_000,
      certBytes: 4_096,
    },
  });
  const profile: CheckProfile<void> = {
    theory: qTheory(outcome),
    leaves: dLeaves,
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
  return checkClosedModelChain(program, [cert], undefined, profile, CertContext.of(programDigestOf(program), pin, pin, pin));
}

const x = Term.var("X");

/** The positive polarity: q(a) filters the only clause, and r is sealed empty. */
function positive(outcome: TheoryOutcome): Outcome {
  const program = new MapProgram().with("r_q", new Clause(Goal.of("r", [x]), [Goal.of("d", [x]), Goal.of("q", [x])]));
  return chain(program, [], [], outcome);
}

/** The negated polarity: `\+ q(a)` filters the second clause, and r(a) is sealed, supported by the
 * first. */
function negated(outcome: TheoryOutcome): Outcome {
  const program = new MapProgram()
    .with("r_d", new Clause(Goal.of("r", [x]), [Goal.of("d", [x])]))
    .with("r_not_q", Clause.withNeg(Goal.of("r", [x]), [Goal.of("d", [x])], [Goal.of("q", [x])]));
  const edge = new SupportEdge(
    lit("r"),
    ClauseId.of("r_d"),
    new Map([["X", Term.fromValue(A)]]),
    [SupportRef.lowerStratum(0, lit("d"))],
    1,
  );
  return chain(program, [lit("r")], [edge], outcome);
}

function verdict(o: Outcome): string {
  return o.kind === "accept" ? "accept" : o.code;
}

test("#3022 step 4: a closure literal whose owning theory decides not_mine is refused in either polarity", () => {
  const fails: TheoryOutcome = { kind: "fails", code: "q_does_not_hold" };
  const notMine: TheoryOutcome = { kind: "not_mine" };
  // All four verdicts at once, so a failure shows every case rather than the first.
  assert.deepEqual(
    {
      positiveControl: verdict(positive(fails)),
      positiveWitness: verdict(positive(notMine)),
      negatedControl: verdict(negated(fails)),
      negatedWitness: verdict(negated(notMine)),
    },
    {
      positiveControl: "accept",
      positiveWitness: "predicate_partition_violation",
      negatedControl: "accept",
      negatedWitness: "predicate_partition_violation",
    },
  );
});
