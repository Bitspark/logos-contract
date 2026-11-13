/*
 * #2232 / #2227: the premise-match discipline at the two SPELLING-SENSITIVE premise sites (ruled
 * by seat:caa, issuecomment-5811831064). A positive premise that cites a Builtin node, and a Neg
 * premise's atom, must EXACTLY equal the grounded body literal. Rule and Leaf premises keep #277's
 * account equality. The same inputs are pinned in contract/rs and contract/go.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  BuiltinNode,
  CertContext,
  check,
  checkWithCertContext,
  Clause,
  ClauseId,
  ClosedModelCert,
  CompoundTheory,
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
  type Outcome,
  PredicateSet,
  programDigestOf,
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
/** `.(a, [])`: the list `[a]`, cons form. */
const consA = valueTuple([av("."), av("a"), av("[]")]);
/** `list(a)`: the list `[a]`, reified form. */
const listA = valueTuple([av("list"), av("a")]);

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

function profile(extensional: string[], rows: readonly GroundLiteral[]): CheckProfile<void> {
  return { theory: newStandardTheory(), leaves: new Leaves(extensional, rows), admit: new AlwaysAdmit<void>(), limits: defaultLimits() };
}

function verdict(o: Outcome): string {
  return o.verdict.kind === "accept" ? "ACCEPT" : o.verdict.code;
}

function subst(pairs: [string, Value][]): Subst {
  return new Subst(pairs.map(([v, value]) => [new VarId(v), Term.fromValue(value)] as const));
}

/** `self_neq(.(a,[]))` from `self_neq(X) :- cand(X), X \== X.`, citing `\==(.(a,[]), second)`. */
function selfNeq(second: Value): Outcome {
  const cand = GroundLiteral.of("cand", [consA]);
  const x = Term.var("X");
  const program = new MapProgram().with(
    "self_neq",
    new Clause(Goal.of("self_neq", [x]), [Goal.of("cand", [x]), Goal.of("\\==", [x, x])]),
  );
  const claim = GroundLiteral.of("self_neq", [consA]);
  const deriv = new Derivation(
    [
      new LeafNode(cand, Evidence.none()),
      new BuiltinNode(GroundLiteral.of("\\==", [consA, second])),
      new RuleNode(claim, ClauseId.of("self_neq"), subst([["X", consA]]), [0, 1], NodeMeta.none()),
    ],
    2,
  );
  return check(program, claim, deriv, undefined, profile(["cand"], [cand]));
}

test("#2232: a Builtin-cited premise matches the body literal EXACTLY", () => {
  // A, the control: the honest node is decided false by the theory.
  assert.equal(verdict(selfNeq(consA)), "builtin_failed");
  // B: the node is respelled `list(a)`, true in the theory, cited for `.(a,[]) \== .(a,[])`.
  assert.equal(verdict(selfNeq(listA)), "instantiation_mismatch");

  // `lst(X) :- seen(X), is_list(X).` over seen(list(a)), citing is_list(.(a,[])).
  const x = Term.var("X");
  const seen = GroundLiteral.of("seen", [listA]);
  const lstProgram = new MapProgram().with(
    "lst",
    new Clause(Goal.of("lst", [x]), [Goal.of("seen", [x]), Goal.of("is_list", [x])]),
  );
  const lstClaim = GroundLiteral.of("lst", [listA]);
  const lst = new Derivation(
    [
      new LeafNode(seen, Evidence.none()),
      new BuiltinNode(GroundLiteral.of("is_list", [consA])),
      new RuleNode(lstClaim, ClauseId.of("lst"), subst([["X", listA]]), [0, 1], NodeMeta.none()),
    ],
    2,
  );
  assert.equal(verdict(check(lstProgram, lstClaim, lst, undefined, profile(["seen"], [seen]))), "instantiation_mismatch");

  // `same(X,Y) :- l(X), r(Y), X == Y.` over l(.(a,[])), r(list(a)), citing ==(.(a,[]), .(a,[])).
  const y = Term.var("Y");
  const l = GroundLiteral.of("l", [consA]);
  const r = GroundLiteral.of("r", [listA]);
  const sameProgram = new MapProgram().with(
    "same",
    new Clause(Goal.of("same", [x, y]), [Goal.of("l", [x]), Goal.of("r", [y]), Goal.of("==", [x, y])]),
  );
  const sameClaim = GroundLiteral.of("same", [consA, listA]);
  const same = new Derivation(
    [
      new LeafNode(l, Evidence.none()),
      new LeafNode(r, Evidence.none()),
      new BuiltinNode(GroundLiteral.of("==", [consA, consA])),
      new RuleNode(sameClaim, ClauseId.of("same"), subst([["X", consA], ["Y", listA]]), [0, 1, 2], NodeMeta.none()),
    ],
    3,
  );
  assert.equal(
    verdict(check(sameProgram, sameClaim, same, undefined, profile(["l", "r"], [l, r]))),
    "instantiation_mismatch",
  );
});

/**
 * `r :- \+ seen(body).` with a Neg premise atom `seen(premise)`, against a certificate that seals
 * `seen` with exactly `sealed` and the finite domain `domain`.
 */
function negation(body: Value, sealed: Value[], premise: Value, domain: Value[]): Outcome {
  const seenSym = Symbol.of("seen");
  const rows = sealed.map((value) => GroundLiteral.of("seen", [value]));
  const program = new MapProgram().with(
    "r",
    Clause.withNeg(Goal.of("r", []), [], [Goal.of("seen", [Term.fromValue(body)])]),
  );
  const claim = GroundLiteral.of("r", []);
  const pin: Hash = new Uint8Array(32).fill(1);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, [seenSym]),
    programHash: programDigestOf(program),
    profileHash: pin,
    ctxHash: pin,
    theoryConfigHash: pin,
    edbSnapshotHashes: [edbTableHash(seenSym, rows)],
    domains: [FiniteDomain.of(Symbol.of("v"), domain)],
    extensions: [RelationTable.of(seenSym, 1, rows)],
    supports: [],
    limitsDecl: {
      certFacts: rows.length,
      domainValues: domain.length,
      supportEdges: 0,
      ruleGroundings: 1_000,
      joinSteps: 10_000,
      certBytes: 4_096,
    },
  });
  const deriv = new Derivation(
    [new RuleNode(claim, ClauseId.of("r"), new Subst(), [new NegPremise(GroundLiteral.of("seen", [premise]), 0)], NodeMeta.none())],
    0,
    [cert],
  );
  const negationProfile: CheckProfile<void> = {
    theory: new CompoundTheory([]),
    leaves: new Leaves(["seen"], rows),
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
  return checkWithCertContext(program, claim, deriv, undefined, negationProfile, CertContext.of(programDigestOf(program), pin, pin, pin));
}

test("#2227: a Neg premise atom matches the body literal EXACTLY", () => {
  const b = av("b");
  const cases: [string, Outcome, string][] = [
    ["A honest negation (control)", negation(consA, [b], consA, [consA, b]), "ACCEPT"],
    ["B present, exact spelling (control)", negation(consA, [consA], consA, [consA]), "neg_atom_present"],
    ["C present, premise respelled list(a)", negation(consA, [consA], listA, [consA, listA]), "instantiation_mismatch"],
    ["D reverse spelling", negation(listA, [listA], consA, [listA, consA]), "instantiation_mismatch"],
  ];
  for (const [name, got, want] of cases) {
    assert.equal(verdict(got), want, name);
  }
});
