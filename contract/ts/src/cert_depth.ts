// The cert-deep term-depth gate (issue #253, ADR 0007), split out of cert_check.ts when #3111's
// report counting brought that file within 50 lines of the 2,000-line ceiling. A pure move: the
// functions are cert_check.ts's, unchanged but for the `tally` each measurement now goes into
// (`maxTermDepthReached`). Mirrors Rust's `check_term_depths` block (c) and `cert_depths_within`.

import { type ClosedModelCert, type SupportRef } from "./cert.js";
import { type Derivation, isCountPremise, isNegPremise } from "./derivation.js";
import { type GroundLiteral } from "./literal.js";
import { Verdict } from "./check.js";
import { type Tally } from "./check_report.js";

// ============================ cert-deep term-depth gate ============================

/**
 * Cert-deep term-depth check (issue #253, ADR 0007). For an all-positive derivation
 * `closedWorld` is empty, so this is a no-op and the positive path is byte-identical.
 * Covers every term/value reachable through a cert: extension rows, domain values,
 * support-edge facts / subst images / body-ref atoms, and `Neg`-premise atoms.
 */
export function checkCertTermDepths(deriv: Derivation, max: number, tally: Tally): Verdict {
  const tooDeep = (what: string): Verdict =>
    Verdict.reject("term_too_deep", `${what} nests deeper than max_term_depth ${max}`);
  for (const cert of deriv.closedWorld) {
    const what = certDepthsWithin(cert, max, tally);
    if (what !== undefined) return tooDeep(what);
  }
  for (const node of deriv.nodes) {
    if (node.kind === "rule") {
      for (const premise of node.premises) {
        if (isNegPremise(premise) && !groundWithin(premise.atom, max, tally)) {
          return tooDeep("negated premise atom argument");
        }
        if (isCountPremise(premise)) {
          for (const e of premise.filter) {
            if (!tally.valueWithin(e.value, max)) return tooDeep("count premise filter value");
          }
          if (!tally.valueWithin(premise.k, max)) return tooDeep("count premise k value");
        }
      }
    }
  }
  return Verdict.Accept;
}

/** Every argument of a GroundLiteral nests within `max`, each measured into `tally` (`maxTermDepthReached`). */
function groundWithin(lit: GroundLiteral, max: number, tally: Tally): boolean {
  return lit.args.every((v) => tally.valueWithin(v, max));
}

/**
 * The per-certificate half of `checkCertTermDepths`: every deep datum of one closed-model
 * certificate the cert path traverses recursively is within `max`. A result names the first datum
 * over the bound, in the same words the derivation path reports. Shared with
 * `checkClosedModelChain` (#2313), whose certificates no derivation cites. Each depth it measures
 * goes into `tally` (`maxTermDepthReached`). Mirrors Rust's `cert_depths_within`.
 */
export function certDepthsWithin(cert: ClosedModelCert, max: number, tally: Tally): string | undefined {
  for (const table of cert.extensions) {
    for (const fact of table.rows) {
      if (!groundWithin(fact, max, tally)) return "certificate extension row argument";
    }
  }
  for (const domain of cert.domains) {
    for (const v of domain.values) {
      if (!tally.valueWithin(v, max)) return "certificate domain value";
    }
  }
  for (const edge of cert.supports) {
    if (!groundWithin(edge.fact, max, tally)) return "certificate support-edge fact argument";
    for (const term of edge.subst.values()) {
      if (!tally.termWithin(term, max)) return "certificate support-edge subst image";
    }
    for (const ref of edge.bodyRefs) {
      const atom = refAtom(ref); // a count_lower ref carries none; its values are the subst's
      if (atom !== undefined && !groundWithin(atom, max, tally)) return "certificate support-ref atom argument";
    }
  }
  return undefined;
}

/** The atom a support ref cites, or `undefined` for a `count_lower` ref, which carries none. */
export function refAtom(ref: SupportRef): GroundLiteral | undefined {
  if (ref.kind === "count_lower") return undefined;
  return ref.kind === "same_stratum" ? ref.fact : ref.atom;
}
