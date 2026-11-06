/*
 * #2226's rows, after #3022. #2226 added the exact term identity beside the default reify_lists,
 * whose label-tolerant sites ACCEPTED the issue's join, head, hidden and nested diag rows and a root
 * respelled against its claim. #3022 (seat:caa's ruling) makes every certified literal claim exact:
 * every comparison site is structural under EVERY identity, so all five are refused under both, and
 * ctl-same (every spelling alike) is accepted under both. The same inputs are pinned in contract/rs,
 * contract/go and contract/ts.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  check,
  type CheckLimits,
  type CheckProfile,
  Clause,
  ClauseId,
  CompoundTheory,
  defaultLimits,
  Derivation,
  edbTableHash,
  Evidence,
  Goal,
  GroundLiteral,
  type Hash,
  LeafNode,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  type Node,
  NodeMeta,
  type Outcome,
  PredicateSet,
  RuleNode,
  type Subst,
  Symbol,
  Term,
  type TermIdentity,
} from "../src/index.js";

function av(s: string): Value {
  return valueAtom(new TextEncoder().encode(s));
}
const consA = valueTuple([av("."), av("a"), av("[]")]); // .(a, []): the list [a], cons form
const listA = valueTuple([av("list"), av("a")]); // list(a): the same list, reified

/** Admits exactly its rows (exact identity) and attests their EDB snapshot. */
// test-double: consumer(a fixed EDB: admits exactly its rows and attests them)
class Leaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #rows: readonly GroundLiteral[];
  constructor(extensional: readonly string[], rows: readonly GroundLiteral[]) {
    this.#extensional = PredicateSet.from([...extensional]);
    this.#rows = rows;
  }
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return this.#rows.some((row) => row.equals(atom)) ? LeafOutcome.Admit : LeafOutcome.Reject("not_admitted");
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    const rows = this.#rows.filter((row) => row.pred.equals(pred));
    return rows.length === 0 ? undefined : edbTableHash(pred, rows);
  }
}

/** One row: the program, the claim, the derivation (root last), the extensional predicates, the leaf rows. */
interface Fixture {
  readonly program: MapProgram;
  readonly claim: GroundLiteral;
  readonly nodes: Node[];
  readonly ext: readonly string[];
  readonly rows: GroundLiteral[];
}

function run(f: Fixture, termIdentity: TermIdentity): Outcome {
  const profile: CheckProfile<void> = {
    theory: new CompoundTheory([]),
    leaves: new Leaves(f.ext, f.rows),
    admit: new AlwaysAdmit<void>(),
    limits: { ...defaultLimits(), termIdentity },
  };
  return check(f.program, f.claim, new Derivation(f.nodes, f.nodes.length - 1), undefined, profile);
}

function verdict(o: Outcome): string {
  return o.kind === "accept" ? "ACCEPT" : o.code;
}
const x = (v: Value): Subst => new Map([["X", Term.fromValue(v)]]);
const leaf = (g: GroundLiteral): Node => new LeafNode(g, Evidence.none());
const rule = (conc: GroundLiteral, id: string, s: Subst, premises: number[]): Node =>
  new RuleNode(conc, ClauseId.of(id), s, premises, NodeMeta.none());

/** `twin(X) :- left(X), right(X).` over `left(.(a,[]))` and `right(rightArg)`. */
function twin(rightArg: Value): Fixture {
  const X = Term.var("X");
  const rows = [GroundLiteral.of("left", [consA]), GroundLiteral.of("right", [rightArg])];
  const claim = GroundLiteral.of("twin", [consA]);
  return {
    program: new MapProgram().with("twin", new Clause(Goal.of("twin", [X]), [Goal.of("left", [X]), Goal.of("right", [X])])),
    claim,
    nodes: [leaf(rows[0]!), leaf(rows[1]!), rule(claim, "twin", x(consA), [0, 1])],
    ext: ["left", "right"],
    rows,
  };
}

/** `copy(X) :- seen(X).` over `seen(.(a,[]))`, X = `.(a,[])`, the node concluding `nodeArg`, the claim `claimArg`. */
function copy(nodeArg: Value, claimArg: Value): Fixture {
  const X = Term.var("X");
  const rows = [GroundLiteral.of("seen", [consA])];
  return {
    program: new MapProgram().with("copy", new Clause(Goal.of("copy", [X]), [Goal.of("seen", [X])])),
    claim: GroundLiteral.of("copy", [claimArg]),
    nodes: [leaf(rows[0]!), rule(GroundLiteral.of("copy", [nodeArg]), "copy", x(consA), [0])],
    ext: ["seen"],
    rows,
  };
}

/** `allowed :- seen(list(a)).` over `seen(.(a,[]))`: the conclusion shows neither spelling. */
function hidden(): Fixture {
  const rows = [GroundLiteral.of("seen", [consA])];
  return {
    program: new MapProgram().with("allowed", new Clause(Goal.of("allowed", []), [Goal.of("seen", [Term.fromValue(listA)])])),
    claim: GroundLiteral.of("allowed", []),
    nodes: [leaf(rows[0]!), rule(GroundLiteral.of("allowed", []), "allowed", new Map(), [0])],
    ext: ["seen"],
    rows,
  };
}

/** `diag(X) :- pair(p(X, X)).` over the single fact `pair(p(.(a,[]), list(a)))`. */
function diag(): Fixture {
  const X = Term.var("X");
  const rows = [GroundLiteral.of("pair", [valueTuple([av("p"), consA, listA])])];
  const claim = GroundLiteral.of("diag", [consA]);
  return {
    program: new MapProgram().with(
      "diag",
      new Clause(Goal.of("diag", [X]), [Goal.of("pair", [Term.tuple([Term.atom(new TextEncoder().encode("p")), X, X])])]),
    ),
    claim,
    nodes: [leaf(rows[0]!), rule(claim, "diag", x(consA), [0])],
    ext: ["pair"],
    rows,
  };
}

test("#3022: every identity refuses every respelling", () => {
  const cases: [string, Fixture, string][] = [
    ["ctl-same", twin(consA), "ACCEPT"],
    ["join", twin(listA), "instantiation_mismatch"],
    ["head", copy(listA, listA), "instantiation_mismatch"],
    ["hidden", hidden(), "instantiation_mismatch"],
    ["diag", diag(), "instantiation_mismatch"],
    ["root", copy(consA, listA), "root_conclusion_mismatch"],
  ];
  for (const [id, f, exact] of cases) {
    assert.equal(verdict(run(f, "reify_lists")), exact, `${id} under reify_lists`);
    assert.equal(verdict(run(f, "exact")), exact, `${id} under exact`);
  }
});

test("#2226: the default term identity is reify_lists, and an absent field means it", () => {
  assert.equal(defaultLimits().termIdentity, "reify_lists");
  // A limits literal written before the field existed carries no termIdentity: it keeps the default.
  const d = defaultLimits();
  const legacy: CheckLimits = {
    maxNodes: d.maxNodes,
    maxDepth: d.maxDepth,
    maxTermDepth: d.maxTermDepth,
    maxCertBytes: d.maxCertBytes,
    maxCertFacts: d.maxCertFacts,
    maxDomainValues: d.maxDomainValues,
    maxSupportEdges: d.maxSupportEdges,
    maxRuleGroundings: d.maxRuleGroundings,
    maxJoinSteps: d.maxJoinSteps,
  };
  // Since #3022 an absent identity checks as every identity does: exactly.
  for (const [f, want] of [
    [twin(consA), "ACCEPT"],
    [twin(listA), "instantiation_mismatch"],
  ] as const) {
    const profile: CheckProfile<void> = {
      theory: new CompoundTheory([]),
      leaves: new Leaves(f.ext, f.rows),
      admit: new AlwaysAdmit<void>(),
      limits: legacy,
    };
    assert.equal(verdict(check(f.program, f.claim, new Derivation(f.nodes, f.nodes.length - 1), undefined, profile)), want);
  }
});
