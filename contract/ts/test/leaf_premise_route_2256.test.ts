/*
 * #2256: the exact cone (ruled by seat:caa, issuecomment-5813063113). After #2242 a Leaf- or
 * Rule-cited positive premise still matches by account equality, so the substitution can carry the
 * other list spelling into a spelling-sensitive judgment of the same rule instance, or of a higher
 * one through a derived fact. A rule instance whose clause is spelling-sensitive (a Neg literal, a
 * count literal, or any builtin literal) must be exact-grounded: every positive premise equals its
 * cited node's underlying exact fact (a Rule node's instantiated head, not its conclusion label),
 * and every cited node is exact-grounded. #3022 (seat:caa's ruling) then made every certified
 * literal claim exact: every comparison site is structural for every clause, so the exact cone holds
 * by construction, and the positive-only rows #2256 left on #277's account equality are refused too.
 * The same inputs are pinned in contract/rs and contract/go.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";
import {
  AlwaysAdmit,
  BodyLit,
  BuiltinNode,
  CertContext,
  check,
  checkWithCertContext,
  Clause,
  ClauseId,
  ClosedModelCert,
  CountLit,
  CountPremise,
  Derivation,
  edbTableHash,
  Evidence,
  FiniteDomain,
  Goal,
  GroundLiteral,
  type Hash,
  LeafNode,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  NegPremise,
  newStandardTheory,
  NodeMeta,
  type Node,
  type Outcome,
  PredicateRef,
  PredicateSet,
  programDigestOf,
  ProjectSpec,
  RelationTable,
  RuleNode,
  StratumPrefix,
  Subst,
  Symbol,
  Term,
  type CheckProfile,
  defaultLimits,
  VarId,
} from "../src/index.js";

function av(s: string): Value {
  return valueAtom(new TextEncoder().encode(s));
}
const listA = valueTuple([av("list"), av("a")]); // list(a)
const consA = valueTuple([av("."), av("a"), av("[]")]); // .(a, []), the same list
const listX = valueTuple([av("list"), av("x")]); // list(x)
const consX = valueTuple([av("."), av("x"), av("[]")]); // .(x, []), the same list
const pin: Hash = new Uint8Array(32).fill(1);

/** Admits exactly its rows (exact identity) and attests their EDB snapshot. */
// test-double: consumer(a fixed EDB: admits exactly its rows and attests them)
class Leaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #rows: readonly GroundLiteral[];
  constructor(extensional: string[], rows: readonly GroundLiteral[]) {
    this.#extensional = PredicateSet.from(extensional);
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

function verdict(o: Outcome): string {
  return o.verdict.kind === "accept" ? "ACCEPT" : o.verdict.code;
}
function subst(pairs: [string, Value][]): Subst {
  return new Subst(pairs.map(([v, value]) => [new VarId(v), Term.fromValue(value)] as const));
}
const leaf = (g: GroundLiteral): Node => new LeafNode(g, Evidence.none());

/**
 * Checks `claim` under leaves that admit exactly `rows`. With a domain, the derivation carries one
 * certificate sealing `member` exactly as `rows` hold it, with that finite domain.
 */
function run(
  program: MapProgram,
  claim: GroundLiteral,
  nodes: Node[],
  root: number,
  ext: string[],
  rows: GroundLiteral[],
  domain?: Value[],
): Outcome {
  const profile: CheckProfile<void> = {
    theory: newStandardTheory(),
    leaves: new Leaves(ext, rows),
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
  if (domain === undefined) return check(program, claim, new Derivation(nodes, root), undefined, profile);
  const member = Symbol.of("member");
  const sealed = rows.filter((row) => row.pred.equals(member));
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [member]),
    programHash: programDigestOf(program),
    profileHash: pin,
    ctxHash: pin,
    theoryConfigHash: pin,
    edbSnapshotHashes: [edbTableHash(member, sealed)],
    domains: [FiniteDomain.of(Symbol.of("v"), domain)],
    extensions: [RelationTable.of(member, 1, sealed)],
    supports: [],
    limitsDecl: {
      certFacts: sealed.length,
      domainValues: domain.length,
      supportEdges: 0,
      ruleGroundings: 1_000,
      joinSteps: 10_000,
      certBytes: 4_096,
    },
  });
  return checkWithCertContext(
    program,
    claim,
    new Derivation(nodes, root, [cert]),
    undefined,
    profile,
    CertContext.of(programDigestOf(program), pin, pin, pin),
  );
}

/** `unlisted :- name(X), \+ member(X).` over name(nameRow), member(list(a)), X = x, the Neg atom member(negArg). */
function n(nameRow: Value, x: Value, negArg: Value, ...domain: Value[]): Outcome {
  const X = Term.var("X");
  const program = new MapProgram().with("unlisted", Clause.withNeg(Goal.of("unlisted", []), [Goal.of("name", [X])], [Goal.of("member", [X])]));
  const rows = [GroundLiteral.of("name", [nameRow]), GroundLiteral.of("member", [listA])];
  const nodes: Node[] = [
    leaf(rows[0]!),
    new RuleNode(GroundLiteral.of("unlisted", []), ClauseId.of("unlisted"), subst([["X", x]]), [
      0,
      new NegPremise(GroundLiteral.of("member", [negArg]), 0),
    ]),
  ];
  return run(program, GroundLiteral.of("unlisted", []), nodes, 1, ["name", "member"], rows, domain);
}

/** `conflict :- dep(R1), rev(R2), R1 \== R2.` over dep(list(x)), rev(revRow), R1 = list(x), R2 = r2, the node \==(list(x), neArg). */
function r(revRow: Value, r2: Value, neArg: Value): Outcome {
  const [R1, R2] = [Term.var("R1"), Term.var("R2")];
  const program = new MapProgram().with(
    "conflict",
    new Clause(Goal.of("conflict", []), [Goal.of("dep", [R1]), Goal.of("rev", [R2]), Goal.of("\\==", [R1, R2])]),
  );
  const rows = [GroundLiteral.of("dep", [listX]), GroundLiteral.of("rev", [revRow])];
  const nodes: Node[] = [
    leaf(rows[0]!),
    leaf(rows[1]!),
    new BuiltinNode(GroundLiteral.of("\\==", [listX, neArg])),
    new RuleNode(GroundLiteral.of("conflict", []), ClauseId.of("conflict"), subst([["R1", listX], ["R2", r2]]), [0, 1, 2]),
  ];
  return run(program, GroundLiteral.of("conflict", []), nodes, 3, ["dep", "rev"], rows);
}

/**
 * `name2(X) :- name(X).` then `unlisted :- name2(X), \+ member(X).` over name(list(a)),
 * member(list(a)), X = x in both. With whole = false only the positive-only intermediate is
 * checked, as the root, with no certificate.
 */
function launder(x: Value, whole: boolean): Outcome {
  const X = Term.var("X");
  const program = new MapProgram()
    .with("name2", new Clause(Goal.of("name2", [X]), [Goal.of("name", [X])]))
    .with("unlisted", Clause.withNeg(Goal.of("unlisted", []), [Goal.of("name2", [X])], [Goal.of("member", [X])]));
  const rows = [GroundLiteral.of("name", [listA]), GroundLiteral.of("member", [listA])];
  const name2 = GroundLiteral.of("name2", [x]);
  const nodes: Node[] = [leaf(rows[0]!), new RuleNode(name2, ClauseId.of("name2"), subst([["X", x]]), [0])];
  if (!whole) return run(program, name2, nodes, 1, ["name", "member"], rows);
  nodes.push(
    new RuleNode(GroundLiteral.of("unlisted", []), ClauseId.of("unlisted"), subst([["X", x]]), [
      1,
      new NegPremise(GroundLiteral.of("member", [x]), 0),
    ]),
  );
  return run(program, GroundLiteral.of("unlisted", []), nodes, 2, ["name", "member"], rows, [listA, consA]);
}

/** `n(N) :- name(X), count(member where arg0 = X) = N.` over name(list(a)), member(list(a)), X = x, k rows claimed. */
function count(x: Value, k: number): Outcome {
  const [X, N] = [Term.var("X"), Term.var("N")];
  const member = new PredicateRef(Symbol.of("member"), 1);
  const program = new MapProgram().with(
    "n",
    new Clause(Goal.of("n", [N]), [
      BodyLit.pos(Goal.of("name", [X])),
      BodyLit.count(new CountLit(member, [{ pos: 0, term: X }], ProjectSpec.rows(), N)),
    ]),
  );
  const rows = [GroundLiteral.of("name", [listA]), GroundLiteral.of("member", [listA])];
  const kv = encodeInt(BigInt(k));
  const claim = GroundLiteral.of("n", [kv]);
  const nodes: Node[] = [
    leaf(rows[0]!),
    new RuleNode(claim, ClauseId.of("n"), subst([["X", x], ["N", kv]]), [
      0,
      new CountPremise(member, [{ pos: 0, value: x }], ProjectSpec.rows(), kv, 0),
    ]),
  ];
  return run(program, claim, nodes, 1, ["name", "member"], rows, [listA, consA]);
}

/** #2226's positive-only rows, refused since #3022. */
function join(): Outcome {
  const X = Term.var("X");
  const program = new MapProgram().with("twin", new Clause(Goal.of("twin", [X]), [Goal.of("left", [X]), Goal.of("right", [X])]));
  const rows = [GroundLiteral.of("left", [consA]), GroundLiteral.of("right", [listA])];
  const claim = GroundLiteral.of("twin", [consA]);
  const nodes: Node[] = [leaf(rows[0]!), leaf(rows[1]!), new RuleNode(claim, ClauseId.of("twin"), subst([["X", consA]]), [0, 1])];
  return run(program, claim, nodes, 2, ["left", "right"], rows);
}

function hidden(): Outcome {
  const program = new MapProgram().with("allowed", new Clause(Goal.of("allowed", []), [Goal.of("seen", [Term.fromValue(listA)])]));
  const rows = [GroundLiteral.of("seen", [consA])];
  const nodes: Node[] = [leaf(rows[0]!), new RuleNode(GroundLiteral.of("allowed", []), ClauseId.of("allowed"), new Subst(), [0])];
  return run(program, GroundLiteral.of("allowed", []), nodes, 1, ["seen"], rows);
}

test("#2256: a spelling-sensitive rule instance must be exact-grounded (the exact cone)", () => {
  const [a, c] = [listA, consA];
  const cases: [string, Outcome, string][] = [
    // Rejected: a respelled binding reaches a spelling-sensitive judgment.
    ["N1 X = .(a,[]) via leaf name(list(a)), Neg member(.(a,[]))", n(a, c, c, a, c), "instantiation_mismatch"],
    ["R1 R2 = .(x,[]) via leaf rev(list(x)), \\==(list(x), .(x,[]))", r(listX, consX, consX), "instantiation_mismatch"],
    ["L laundered through the positive-only name2", launder(c, true), "instantiation_mismatch"],
    ["C count over a respelled X", count(c, 0), "instantiation_mismatch"],
    // Rejected since #3022: a positive-only rule's respelled premise is no longer account-equal.
    ["L's positive-only intermediate alone", launder(c, false), "instantiation_mismatch"],
    ["#2226 join", join(), "instantiation_mismatch"],
    ["#2226 hidden", hidden(), "instantiation_mismatch"],
    // Unchanged.
    ["N0 exact spelling, present", n(a, a, a, a), "neg_atom_present"],
    ["N3 #2227's form, Neg atom respelled", n(a, a, c, a, c), "instantiation_mismatch"],
    ["R0 exact spelling, \\== fails", r(listX, listX, listX), "builtin_failed"],
    ["R2 #2232's form, builtin node respelled", r(listX, listX, consX), "instantiation_mismatch"],
    // Stay accepted: the rule does not reach them.
    ["N4 mixed EDB, honest exact binding", n(c, c, c, a, c), "ACCEPT"],
    ["R3 mixed EDB, honest exact binding", r(consX, consX, consX), "ACCEPT"],
    ["L's positive-only intermediate, honest exact binding", launder(a, false), "ACCEPT"],
    ["C honest count", count(a, 1), "ACCEPT"],
  ];
  const wrong = cases.filter(([, got, want]) => verdict(got) !== want).map(([name, got, want]) => `${name}: ${verdict(got)}, want ${want}`);
  assert.deepEqual(wrong, []);
});
