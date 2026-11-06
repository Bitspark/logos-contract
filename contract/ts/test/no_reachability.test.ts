/**
 * §4 core obligation 6 — **no reachability requirement** (frozen; downstream-load-bearing).
 *
 * TS twin of contract/rs/tests/no_reachability.rs (issue #710): check verifies
 * obligations 1–5 — each node locally valid, the root concluding the claim — and
 * nothing about node connectivity beyond the per-Rule premise edges. A locally-valid
 * node the root does not transitively cite is neither rejected nor required. This
 * *absence* is consumed as law by a downstream verifier (thesmos CD-015,
 * "reach-as-non-op / enforcement-by-absence"), so it is pinned here as a CI guard:
 * **adding** a reachability check to check fails this suite, not the consumer's
 * shipped law. Named frozen in docs/spec/logos-contract.md §4 (PR #705, the
 * load-bearing register / consumer change gate).
 *
 * Two halves, both load-bearing:
 *  1. ACCEPT — an extra, locally-valid, root-UNREACHABLE node does not reject.
 *  2. REJECT — an extra root-unreachable node is still LOCALLY verified (obligations
 *     1–5 range over *every* node, cited or not): an invalid uncited node rejects.
 *     "No reachability requirement" means unreachable ≠ exempt, not unreachable ≠ seen.
 */
import test from "node:test";
import assert from "node:assert/strict";

import { atom } from "@bitspark/ontos-core";

import {
  AlwaysAdmit,
  check,
  defaultLimits,
  type CheckProfile,
  type Outcome,
  ClauseId,
  Clause,
  Goal,
  Term,
  type Subst,
  GroundLiteral,
  type Symbol,
  Derivation,
  RuleNode,
  LeafNode,
  type Node,
  NodeMeta,
  Evidence,
  PredicateSet,
  MapProgram,
  type Theory,
  type LeafVerifier,
  TheoryOutcome,
  LeafOutcome,
} from "../src/index.js";

// A theory that owns nothing (this suite needs no builtins).
// test-double: consumer(owns no predicate)
class NoReachTheory implements Theory {
  owns(_pred: Symbol): boolean {
    return false;
  }
  decide(_atom: GroundLiteral): TheoryOutcome {
    return TheoryOutcome.NotMine;
  }
}

// A leaf verifier that declares `grant`/`audit` extensional and admits any leaf.
// test-double: consumer(admits grant and audit leaves)
class NoReachLeaves implements LeafVerifier<undefined> {
  readonly #ext = PredicateSet.from(["grant", "audit"]);

  extensional(): PredicateSet {
    return this.#ext;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: undefined): LeafOutcome {
    return LeafOutcome.Admit;
  }
}

function noReachProfile(): CheckProfile<undefined> {
  return {
    theory: new NoReachTheory(),
    leaves: new NoReachLeaves(),
    admit: new AlwaysAdmit<undefined>(),
    limits: defaultLimits(),
  };
}

const CLAUSE_PERMIT = "permit_rule";

// `permit(S) :- grant(S).` — `grant`/`audit` are extensional (leaves).
function noReachProgram(): MapProgram {
  return new MapProgram().with(
    ClauseId.of(CLAUSE_PERMIT),
    new Clause(Goal.of("permit", [Term.var("S")]), [Goal.of("grant", [Term.var("S")])]),
  );
}

function v(s: string) {
  return atom(new TextEncoder().encode(s));
}

/**
 * Nodes [0] leaf grant(s1) ← cited, [1] rule permit(s1) = root. `extra` (if any) is
 * appended as node [2]: present in the DAG, **cited by nothing, unreachable from root**.
 */
function noReachDerivation(extra?: Node): Derivation {
  const subst: Subst = new Map([["S", Term.atom(new TextEncoder().encode("s1"))]]);
  const nodes: Node[] = [
    new LeafNode(GroundLiteral.of("grant", [v("s1")]), Evidence.none()),
    new RuleNode(
      GroundLiteral.of("permit", [v("s1")]),
      ClauseId.of(CLAUSE_PERMIT),
      subst,
      [0],
      NodeMeta.none(),
    ),
  ];
  if (extra !== undefined) {
    nodes.push(extra);
  }
  return new Derivation(nodes, 1);
}

function reject(out: Outcome): { code: string; detail: string } {
  assert.equal(out.kind, "reject", `expected Reject, got ${JSON.stringify(out)}`);
  return out as { kind: "reject"; code: string; detail: string };
}

// Baseline: the two-node derivation (no extra node) accepts.
test("no-reachability: baseline without extra node accepts", () => {
  const out = check<undefined>(
    noReachProgram(),
    GroundLiteral.of("permit", [v("s1")]),
    noReachDerivation(),
    undefined,
    noReachProfile(),
  );
  assert.equal(out.kind, "accept", `baseline must accept, got ${JSON.stringify(out)}`);
});

// THE FROZEN ABSENCE (obligation 6): a locally-valid extensional leaf the root never
// cites — node [2] audit(x9), reachable from nothing — must NOT cause rejection. A
// future reachability requirement in check turns this test red before it turns thesmos
// CD-015 wrong.
test("no-reachability: locally-valid root-unreachable node accepts (§4 obligation 6, frozen)", () => {
  const extra = new LeafNode(GroundLiteral.of("audit", [v("x9")]), Evidence.none());
  const out = check<undefined>(
    noReachProgram(),
    GroundLiteral.of("permit", [v("s1")]),
    noReachDerivation(extra),
    undefined,
    noReachProfile(),
  );
  assert.equal(
    out.kind,
    "accept",
    `a locally-valid, root-unreachable node must be neither rejected nor required ` +
      `(§4 obligation 6, frozen; thesmos CD-015 rests on this) — got ${JSON.stringify(out)}`,
  );
});

// The other half: unreachable does NOT mean exempt. Obligations 1–5 range over every
// node — an *invalid* uncited node (a Leaf concluding the intensional `permit`, the
// §4.2 sealing violation) still rejects, even though the root never cites it.
test("no-reachability: locally-invalid root-unreachable node still rejects (sealed_violation)", () => {
  const extra = new LeafNode(GroundLiteral.of("permit", [v("x9")]), Evidence.none());
  const out = reject(
    check<undefined>(
      noReachProgram(),
      GroundLiteral.of("permit", [v("s1")]),
      noReachDerivation(extra),
      undefined,
      noReachProfile(),
    ),
  );
  assert.equal(out.code, "sealed_violation");
});
