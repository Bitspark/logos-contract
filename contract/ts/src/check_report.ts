// `check`'s report of the work it actually performed (checker SPI v2, ADR 0036 D8 change 5;
// design 0006 P1, #1932, #3111). TS sibling of contract/rs/src/check/report.rs.
//
// The report rides beside the verdict in `Outcome` and never decides it: an outcome's equality is
// its verdict's (`Outcome.equals`), so a counter can never turn a verdict test red. It counts the
// work done up to and including a rejecting node.
//
// **Counters are defined per checker version.** `CHECK_REPORT_COUNTERS_VERSION` names the checker
// version whose counting rules these are, and a kernel test pins it equal to `CHECKER_VERSION`: a
// change to what a counter counts is a checker-version bump.
//
// THE COUNTING RULES are normative in the module doc of contract/rs/src/check/report.rs, and this
// core mirrors them site for site. One `Tally` is threaded through the check as a parameter, never
// held in module state, and each increment site in check.ts, cert_check.ts and cert_stack.ts carries
// a comment naming its counter. Every counter is `counted` in ts.

import { Tuple as ValueTupleClass, type Value } from "@bitspark/ontos-core";
import { isNegPremise, type Premise } from "./derivation.js";
import type { Term } from "./term.js";
import type { Outcome, Verdict } from "./check.js";

/**
 * The checker version whose counting rules `CheckReport`'s counters follow. A kernel test asserts
 * it equals `CHECKER_VERSION`.
 */
export const CHECK_REPORT_COUNTERS_VERSION = 24;

/**
 * One counter: a count the checker kept, or `unsupported` where this core does not count it.
 * `unsupported` is never a zero (omit, never fake). rs `ReportCount`.
 */
export type ReportCount = { readonly kind: "counted"; readonly count: number } | { readonly kind: "unsupported" };

export const ReportCount = Object.freeze({
  /** A count the checker kept. */
  counted(count: number): ReportCount {
    return Object.freeze({ kind: "counted", count });
  },
  /** A counter this core does not count. */
  Unsupported: Object.freeze({ kind: "unsupported" } as const satisfies ReportCount),
  /** The count, or `undefined` where it is not supported. */
  get(c: ReportCount): number | undefined {
    return c.kind === "counted" ? c.count : undefined;
  },
});

/**
 * The work one `check` performed. Each field's increment event is stated on it; the three node
 * kinds sum to `nodesWalked`, a checked invariant (`CheckReport.nodeKindsSum`). rs `CheckReport`.
 */
export type CheckReport = {
  /** The checker version whose counting rules these counters follow. */
  readonly countersVersion: number;
  /** Each derivation node visited, up to and including a rejecting node. */
  readonly nodesWalked: ReportCount;
  /** Each `rule` node visited. */
  readonly ruleNodes: ReportCount;
  /** Each `builtin` node visited. */
  readonly builtinNodes: ReportCount;
  /** Each `leaf` node visited. */
  readonly leafNodes: ReportCount;
  /** Each positive premise examined (a count premise is positive). */
  readonly premisesPos: ReportCount;
  /** Each negative premise examined. */
  readonly premisesNeg: ReportCount;
  /** Each call to a theory's `decideGround`. */
  readonly theoryDecisions: ReportCount;
  /** Each leaf-verifier call. */
  readonly leafVerifications: ReportCount;
  /** Each rule-admissibility test. */
  readonly admissibilityChecks: ReportCount;
  /** Each closed-model certificate verified (a memo hit is not a verification). */
  readonly certsVerified: ReportCount;
  /** Each certificate whose verification was answered by the world memo instead. */
  readonly certsMemoHits: ReportCount;
  /** Each certificate table read during verification. */
  readonly certTablesRead: ReportCount;
  /** Each certificate row read during verification. */
  readonly certRowsRead: ReportCount;
  /** The closure join steps actually spent (beside the declared `maxJoinSteps` budget). */
  readonly joinStepsUsed: ReportCount;
  /** The rule groundings actually enumerated (beside the declared `maxRuleGroundings`). */
  readonly groundingsEnumerated: ReportCount;
  /** The deepest derivation depth reached. */
  readonly maxDepthReached: ReportCount;
  /** The deepest term depth reached. */
  readonly maxTermDepthReached: ReportCount;
};

export const CheckReport = Object.freeze({
  /**
   * A report under the current counting rules with every counter at zero: what a check refused
   * before its walk reports.
   */
  zero(): CheckReport {
    return new Tally().report();
  },
  /** `ruleNodes + builtinNodes + leafNodes === nodesWalked`, where all four are counted. */
  nodeKindsSum(r: CheckReport): boolean {
    const counts = [r.nodesWalked, r.ruleNodes, r.builtinNodes, r.leafNodes].map(ReportCount.get);
    const [n, rule, builtin, leaf] = counts;
    if (n !== undefined && rule !== undefined && builtin !== undefined && leaf !== undefined) {
      return rule + builtin + leaf === n;
    }
    return counts.every((c) => c === undefined);
  },
});

/**
 * One check's running counts (#3111): plain counters the checker bumps at the points the rs module
 * doc names, turned into the `CheckReport` of the `Outcome` once the check ends. Internal to the
 * checker (not exported from the package), created per check and passed down as a parameter. rs
 * `Tally`.
 */
export class Tally {
  nodesWalked = 0;
  ruleNodes = 0;
  builtinNodes = 0;
  leafNodes = 0;
  premisesPos = 0;
  premisesNeg = 0;
  theoryDecisions = 0;
  leafVerifications = 0;
  admissibilityChecks = 0;
  certsVerified = 0;
  certsMemoHits = 0;
  certTablesRead = 0;
  certRowsRead = 0;
  joinStepsUsed = 0;
  groundingsEnumerated = 0;
  maxDepthReached = 0;
  maxTermDepthReached = 0;

  /** `premisesPos` / `premisesNeg`: one premise examined, by its own kind (a count is positive). */
  premise(premise: Premise): void {
    if (isNegPremise(premise)) {
      this.premisesNeg += 1;
    } else {
      this.premisesPos += 1;
    }
  }

  /** `maxDepthReached`: one derivation depth compared against `maxDepth`. */
  reachDepth(depth: number): void {
    this.maxDepthReached = Math.max(this.maxDepthReached, depth);
  }

  /** `maxTermDepthReached`: measure `term` against `max`; `true` when it is within. */
  termWithin(term: Term, max: number): boolean {
    return this.#reachTermDepth(termDepthCapped(term, max), max);
  }

  /** `maxTermDepthReached`: measure `value` against `max`; `true` when it is within. */
  valueWithin(value: Value, max: number): boolean {
    return this.#reachTermDepth(valueDepthCapped(value, max), max);
  }

  #reachTermDepth(depth: number, max: number): boolean {
    this.maxTermDepthReached = Math.max(this.maxTermDepthReached, depth);
    return depth <= max;
  }

  /** The check's result: `verdict`, with the report of the work counted so far. */
  outcome(verdict: Verdict): Outcome {
    return { verdict, report: this.report() };
  }

  /** The report: every counter `counted`, since ts counts all of them. */
  report(): CheckReport {
    const c = ReportCount.counted;
    return Object.freeze({
      countersVersion: CHECK_REPORT_COUNTERS_VERSION,
      nodesWalked: c(this.nodesWalked),
      ruleNodes: c(this.ruleNodes),
      builtinNodes: c(this.builtinNodes),
      leafNodes: c(this.leafNodes),
      premisesPos: c(this.premisesPos),
      premisesNeg: c(this.premisesNeg),
      theoryDecisions: c(this.theoryDecisions),
      leafVerifications: c(this.leafVerifications),
      admissibilityChecks: c(this.admissibilityChecks),
      certsVerified: c(this.certsVerified),
      certsMemoHits: c(this.certsMemoHits),
      certTablesRead: c(this.certTablesRead),
      certRowsRead: c(this.certRowsRead),
      joinStepsUsed: c(this.joinStepsUsed),
      groundingsEnumerated: c(this.groundingsEnumerated),
      maxDepthReached: c(this.maxDepthReached),
      maxTermDepthReached: c(this.maxTermDepthReached),
    });
  }
}

/**
 * The depth `Term.depthLe` measures, by the same walk and the same cutoff: the term's depth when it
 * is at most `max`, else `max + 1`, the first level past `max`, where the walk stops. rs
 * `Term::depth_capped`.
 */
function termDepthCapped(t: Term, max: number): number {
  let deepest = 0;
  const work: Array<{ term: Term; level: number }> = [{ term: t, level: 1 }];
  while (work.length > 0) {
    const { term, level } = work.pop()!;
    if (level > max) return level;
    deepest = Math.max(deepest, level);
    if (term.kind === "tuple") {
      for (const child of term.children()) {
        work.push({ term: child, level: level + 1 });
      }
    }
  }
  return deepest;
}

/**
 * The depth `valueDepthLe` measures, by the same walk and the same cutoff: the value's depth when it
 * is at most `max`, else `max + 1`. rs `value_depth_capped`.
 */
function valueDepthCapped(value: Value, max: number): number {
  let deepest = 0;
  const work: Array<{ value: Value; level: number }> = [{ value, level: 1 }];
  while (work.length > 0) {
    const { value: v, level } = work.pop()!;
    if (level > max) return level;
    deepest = Math.max(deepest, level);
    if (v instanceof ValueTupleClass) {
      for (const child of v.items()) {
        work.push({ value: child, level: level + 1 });
      }
    }
  }
  return deepest;
}
