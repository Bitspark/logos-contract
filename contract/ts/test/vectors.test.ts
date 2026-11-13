/*
 * Language-local tests for the TS binding's host-extension band and the two rule-head
 * sealing/partition branches — the parts NOT pinned by the shared, cross-language oracle.
 *
 * The shared check.json/account.json vectors are no longer replayed here: that is the
 * differential CLI harness (conformance/, ADR 0006), which drives the per-language
 * check CLIs as black boxes over the one oracle. This file keeps only the host band
 * (builtin_failed / leaf_rejected / rule_inadmissible) + the rule-head branch tests.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  canonicalClauseId,
  check,
  Clause,
  ClauseId,
  Derivation,
  Evidence,
  Goal,
  GroundLiteral,
  isStructural,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  type Node,
  NodeMeta,
  Outcome,
  PredicateSet,
  type RuleAdmissibility,
  RuleOutcome,
  Subst,
  Symbol,
  Term,
  type Theory,
  TheoryGround,
  type CheckLimits,
  type CheckProfile,
  defaultLimits,
  BuiltinNode,
  LeafNode,
  RuleNode,
  VarId,
} from "../src/index.js";

// =================== the `demo_v1` profile (shared by name) ===================
// Implemented identically in each language binding; the JSON pins program +
// derivation + claim + outcome. Context is unit.

/** Bytewise lexicographic compare mirroring Rust's `Vec<u8>` Ord (shorter-is-less on a prefix). */
function bytesLess(a: Uint8Array, b: Uint8Array): boolean {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const x = a[i]!;
    const y = b[i]!;
    if (x !== y) return x < y;
  }
  return a.length < b.length;
}

/**
 * Theory owning `lt`: `lt(a, b)` Holds iff both args are atoms and `a < b`
 * bytewise else Fails{"not_less_than"}; non-binary arity Fails{"lt_arity"}.
 * Pure, total, config-free.
 */
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

/** LeafVerifier with `edge` extensional; admits any `edge` leaf (trusted facts). */
// test-double: consumer(admits any edge leaf)
class EdgeLeaves implements LeafVerifier<void> {
  readonly #extensional = PredicateSet.from(["edge"]);
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return LeafOutcome.Admit;
  }
}

function demoProfile(limits: CheckLimits): CheckProfile<void> {
  return {
    theory: new LtTheory(),
    leaves: new EdgeLeaves(),
    admit: new AlwaysAdmit<void>(),
    limits,
  };
}

// ===== language-local host-extension band tests (NOT in the shared vectors) =====
// The host band's sub-codes are an open set pinned only in a consumer's own suite;
// here we verify the three wrapper codes + that the seam's sub-code reaches detail.

function ontosValue(s: string): Value {
  return valueAtom(new TextEncoder().encode(s));
}
function lt(a: string, b: string): GroundLiteral {
  return GroundLiteral.of("lt", [ontosValue(a), ontosValue(b)]);
}

test("host band: builtin_failed", () => {
  // lt(b, a): b > a, so the theory Fails -> builtin_failed, sub-code in detail.
  const deriv = new Derivation([new BuiltinNode(lt("b", "a"))], 0);
  const profile = demoProfile(defaultLimits());
  const got = check(new MapProgram(), lt("b", "a"), deriv, undefined, profile).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") {
    assert.equal(got.code, "builtin_failed");
    assert.equal(got.detail, "not_less_than");
    assert.equal(isStructural(got.code), false);
  }
});

test("host band: leaf_rejected", () => {
  // A LeafVerifier that always rejects with a custom sub-code.
  // test-double: adversarial(rejects every leaf with a custom sub-code)
  class RejectingLeaves implements LeafVerifier<void> {
    readonly #ext = PredicateSet.from(["edge"]);
    extensional(): PredicateSet {
      return this.#ext;
    }
    verify(_atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
      return LeafOutcome.Reject("no_attestation");
    }
  }
  const edge = GroundLiteral.of("edge", [ontosValue("a"), ontosValue("b")]);
  const deriv = new Derivation([new LeafNode(edge, Evidence.none())], 0);
  const profile: CheckProfile<void> = {
    theory: new LtTheory(),
    leaves: new RejectingLeaves(),
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
  const got = check(new MapProgram(), edge, deriv, undefined, profile).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") {
    assert.equal(got.code, "leaf_rejected");
    assert.equal(got.detail, "no_attestation");
  }
});

test("host band: rule_inadmissible", () => {
  // A RuleAdmissibility that always rejects; the rule is otherwise valid.
  // test-double: adversarial(rejects every otherwise-valid rule)
  class DenyAdmit implements RuleAdmissibility<void> {
    admissible(_clause: Clause, _meta: NodeMeta, _ctx: void): RuleOutcome {
      return RuleOutcome.Reject("placement_mismatch");
    }
  }
  // program: greet(X) :- edge(X, X). (intensional head greet, extensional body edge)
  const program = new MapProgram().with(
    "greet_rule",
    new Clause(Goal.of("greet", [Term.var("X")]), [
      Goal.of("edge", [Term.var("X"), Term.var("X")]),
    ]),
  );
  const edgeAa = GroundLiteral.of("edge", [ontosValue("a"), ontosValue("a")]);
  const greetA = GroundLiteral.of("greet", [ontosValue("a")]);
  const subst: Subst = new Subst([[VarId.of("X"), Term.atom(new TextEncoder().encode("a"))]]);
  const deriv = new Derivation(
    [
      new LeafNode(edgeAa, Evidence.none()),
      new RuleNode(greetA, ClauseId.of("greet_rule"), subst, [0], NodeMeta.none()),
    ],
    1,
  );
  const profile: CheckProfile<void> = {
    theory: new LtTheory(),
    leaves: new EdgeLeaves(),
    admit: new DenyAdmit(),
    limits: defaultLimits(),
  };
  const got = check(program, greetA, deriv, undefined, profile).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") {
    assert.equal(got.code, "rule_inadmissible");
    assert.equal(got.detail, "placement_mismatch");
  }
});

// ===== sealing/partition branches on a Rule head (ts-local; shared program is clean) =====

test("rule head collides with extensional is sealed", () => {
  // edge_sym: edge(X,Y) :- edge(Y,X). `edge` is extensional, so a rule concluding
  // it is the §4.2 "rule head collides with an extensional predicate" error.
  const program = new MapProgram().with(
    "edge_sym",
    new Clause(Goal.of("edge", [Term.var("X"), Term.var("Y")]), [
      Goal.of("edge", [Term.var("Y"), Term.var("X")]),
    ]),
  );
  const edgeBa = GroundLiteral.of("edge", [ontosValue("b"), ontosValue("a")]);
  const edgeAb = GroundLiteral.of("edge", [ontosValue("a"), ontosValue("b")]);
  const subst: Subst = new Subst([
    [VarId.of("X"), Term.atom(new TextEncoder().encode("a"))],
    [VarId.of("Y"), Term.atom(new TextEncoder().encode("b"))],
  ]);
  const deriv = new Derivation(
    [
      new LeafNode(edgeBa, Evidence.none()),
      new RuleNode(edgeAb, ClauseId.of("edge_sym"), subst, [0], NodeMeta.none()),
    ],
    1,
  );
  const profile = demoProfile(defaultLimits());
  const got = check(program, edgeAb, deriv, undefined, profile).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") {
    assert.equal(got.code, "sealed_violation");
  }
});

test("rule head owned by theory is partition violation", () => {
  // lt_rule: lt(X,Y) :- edge(X,Y). `lt` is theory-owned, so a rule concluding it
  // is a §4.4 predicate-partition violation.
  const program = new MapProgram().with(
    "lt_rule",
    new Clause(Goal.of("lt", [Term.var("X"), Term.var("Y")]), [
      Goal.of("edge", [Term.var("X"), Term.var("Y")]),
    ]),
  );
  const edgeAb = GroundLiteral.of("edge", [ontosValue("a"), ontosValue("b")]);
  const ltAb = GroundLiteral.of("lt", [ontosValue("a"), ontosValue("b")]);
  const subst: Subst = new Subst([
    [VarId.of("X"), Term.atom(new TextEncoder().encode("a"))],
    [VarId.of("Y"), Term.atom(new TextEncoder().encode("b"))],
  ]);
  const deriv = new Derivation(
    [
      new LeafNode(edgeAb, Evidence.none()),
      new RuleNode(ltAb, ClauseId.of("lt_rule"), subst, [0], NodeMeta.none()),
    ],
    1,
  );
  const profile = demoProfile(defaultLimits());
  const got = check(program, ltAb, deriv, undefined, profile).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") {
    assert.equal(got.code, "predicate_partition_violation");
  }
});

