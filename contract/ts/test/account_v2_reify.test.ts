/*
 * account-v2 list reification (#277), after #3022 — the TS mirror of contract/rs's
 * account_v2_reify tests. Every certified literal claim is EXACT (#3022): a derivation whose
 * nodes conclude the REIFIED `list(…)` spelling of a cons-form instance is REFUSED by `check`,
 * under every term identity, because the reified conclusion is not the instantiated head. The
 * cons↔`list` canonicalization stays a bijection (no conflation) and is the PRESENTATION
 * equivalence a producer shows a list in, beside the exact fact; the cons-form derivation an
 * engine emits is accepted as before.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, equals as valueEquals, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  canonicalizeLists,
  check,
  Clause,
  ClauseId,
  Derivation,
  Evidence,
  Goal,
  GroundLiteral,
  LeafNode,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  NodeMeta,
  PredicateSet,
  RuleNode,
  Subst,
  type Symbol,
  Term,
  type Theory,
  TheoryGround,
  type CheckProfile,
  defaultLimits,
  VarId,
} from "../src/index.js";

// ----------------------------- profile + helpers -----------------------------

/** A theory that owns nothing (no builtins needed here). */
// test-double: consumer(owns no predicate)
class NoTheory implements Theory {
  owns(_pred: Symbol): boolean {
    return false;
  }
  decideGround(_atom: GroundLiteral): TheoryGround {
    return TheoryGround.disowned();
  }
}

/**
 * A `LeafVerifier` whose extensional set is `src`. It admits any `src` leaf whose
 * argument, AFTER cons↔`list` canonicalization, is in its cons-form EDB-of-record —
 * exercising the "a reified leaf matches the cons-form EDB" obligation of #277 via the
 * public `canonicalizeLists` primitive (the SAME bijection `check` uses).
 */
// test-double: consumer(a cons-form src EDB matched after list canonicalization)
class SrcLeaves implements LeafVerifier<void> {
  readonly #ext = PredicateSet.from(["src"]);
  readonly #edbCons: readonly GroundLiteral[];
  constructor(edbCons: readonly GroundLiteral[]) {
    this.#edbCons = edbCons;
  }
  extensional(): PredicateSet {
    return this.#ext;
  }
  verify(atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    const canon = (g: GroundLiteral): GroundLiteral =>
      new GroundLiteral(g.pred, g.args.map(canonicalizeLists));
    const want = canon(atom);
    for (const row of this.#edbCons) {
      if (canon(row).equals(want)) return LeafOutcome.Admit;
    }
    return LeafOutcome.Reject("not_in_edb");
  }
}

function srcProfile(leaves: SrcLeaves): CheckProfile<void> {
  return {
    theory: new NoTheory(),
    leaves,
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
}

function av(s: string): Value {
  return valueAtom(new TextEncoder().encode(s));
}
function nilv(): Value {
  return av("[]");
}
function consv(head: Value, tail: Value): Value {
  return valueTuple([av("."), head, tail]);
}
/** A proper cons list `[e0, e1, …]`, right-folded onto `[]` — the FROZEN surface form. */
function consList(elems: readonly Value[]): Value {
  let acc = nilv();
  for (let i = elems.length - 1; i >= 0; i -= 1) {
    acc = consv(elems[i]!, acc);
  }
  return acc;
}
/** The ontos/data flat `list` embedding `list(e0, …)` — the REIFIED form. */
function listEmbed(elems: readonly Value[]): Value {
  return valueTuple([av("list"), ...elems]);
}
function gl(pred: string, arg: Value): GroundLiteral {
  return GroundLiteral.of(pred, [arg]);
}
/** The program `wrap(X) :- src(X).` — src extensional, wrap intensional. */
function wrapProgram(): MapProgram {
  return new MapProgram().with(
    "wrap_rule",
    new Clause(Goal.of("wrap", [Term.var("X")]), [Goal.of("src", [Term.var("X")])]),
  );
}
/** `subst {X = <cons-form list term>}`. */
function substXConsList(elems: readonly Value[]): Subst {
  return new Subst([[VarId.of("X"), Term.fromValue(consList(elems))]]);
}

// ======================= 1. THE REIFIED SPELLING IS REFUSED (#3022) ========================

test("a reified list derivation is REFUSED: its conclusion is not the instantiated head (#3022)", () => {
  const elems = [av("a"), av("b")];
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList(elems))]);
  const wrapList = gl("wrap", listEmbed(elems));
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", listEmbed(elems)), Evidence.none()),
      new RuleNode(wrapList, ClauseId.of("wrap_rule"), substXConsList(elems), [0], NodeMeta.none()),
    ],
    1,
  );
  const got = check(program, wrapList, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind === "reject" ? got.code : got.kind, "instantiation_mismatch", JSON.stringify(got));
});

test("a reified node is refused at its own head before a cons-form claim is read (#3022)", () => {
  const elems = [av("a"), av("b")];
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList(elems))]);
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", listEmbed(elems)), Evidence.none()),
      new RuleNode(
        gl("wrap", listEmbed(elems)),
        ClauseId.of("wrap_rule"),
        substXConsList(elems),
        [0],
        NodeMeta.none(),
      ),
    ],
    1,
  );
  const consClaim = gl("wrap", consList(elems));
  const got = check(program, consClaim, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind === "reject" ? got.code : got.kind, "instantiation_mismatch", JSON.stringify(got));
});

test("the frozen cons-form derivation still accepts (additive)", () => {
  const elems = [av("a"), av("b")];
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList(elems))]);
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", consList(elems)), Evidence.none()),
      new RuleNode(
        gl("wrap", consList(elems)),
        ClauseId.of("wrap_rule"),
        substXConsList(elems),
        [0],
        NodeMeta.none(),
      ),
    ],
    1,
  );
  const consClaim = gl("wrap", consList(elems));
  const got = check(program, consClaim, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind, "accept", JSON.stringify(got));
});

// ================================ 2. REJECT ===============================

test("a wrong-order reified list is REJECTED (no conflation)", () => {
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList([av("a"), av("b")]))]);
  const wrong = gl("wrap", listEmbed([av("b"), av("a")]));
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", listEmbed([av("a"), av("b")])), Evidence.none()),
      new RuleNode(
        wrong,
        ClauseId.of("wrap_rule"),
        substXConsList([av("a"), av("b")]),
        [0],
        NodeMeta.none(),
      ),
    ],
    1,
  );
  const got = check(program, wrong, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") assert.equal(got.code, "instantiation_mismatch");
});

test("an improper cons claimed as a proper list is REJECTED (no conflation)", () => {
  const program = wrapProgram();
  const improper = consv(av("a"), av("b"));
  const subst: Subst = new Subst([[VarId.of("X"), Term.fromValue(improper)]]);
  const leaves = new SrcLeaves([gl("src", improper)]);
  const dishonest = gl("wrap", listEmbed([av("a"), av("b")]));
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", improper), Evidence.none()),
      new RuleNode(dishonest, ClauseId.of("wrap_rule"), subst, [0], NodeMeta.none()),
    ],
    1,
  );
  const got = check(program, dishonest, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") assert.equal(got.code, "instantiation_mismatch");
});

test("a distinct cons root still rejects a cons claim (additive)", () => {
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList([av("a")]))]);
  const deriv = new Derivation(
    [
      new LeafNode(gl("src", consList([av("a")])), Evidence.none()),
      new RuleNode(
        gl("wrap", consList([av("a")])),
        ClauseId.of("wrap_rule"),
        substXConsList([av("a")]),
        [0],
        NodeMeta.none(),
      ),
    ],
    1,
  );
  const otherClaim = gl("wrap", consList([av("z")]));
  const got = check(program, otherClaim, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind, "reject");
  if (got.kind === "reject") assert.equal(got.code, "root_conclusion_mismatch");
});

// ============================ 3. BIJECTION ============================

test("[] and list() stay distinct (no empty conflation)", () => {
  assert.ok(valueEquals(canonicalizeLists(nilv()), nilv()), "[] is left as the bare atom");
  assert.ok(
    valueEquals(canonicalizeLists(listEmbed([])), listEmbed([])),
    "list() is left as the empty embedding",
  );
  assert.ok(
    !valueEquals(canonicalizeLists(nilv()), canonicalizeLists(listEmbed([]))),
    "[] and list() must NOT canonicalize to the same value",
  );
});

test("cons↔list is bijective (no conflation of distinct sequences)", () => {
  const ab = [av("a"), av("b")];
  const ba = [av("b"), av("a")];
  assert.ok(valueEquals(canonicalizeLists(consList(ab)), canonicalizeLists(listEmbed(ab))));
  assert.ok(valueEquals(canonicalizeLists(consList(ab)), listEmbed(ab)));
  assert.ok(!valueEquals(canonicalizeLists(consList(ab)), canonicalizeLists(consList(ba))));
  assert.ok(!valueEquals(canonicalizeLists(consList([av("a")])), canonicalizeLists(consList(ab))));
});

test("canonicalize is idempotent", () => {
  const once = canonicalizeLists(consList([av("a"), av("b")]));
  assert.ok(valueEquals(once, canonicalizeLists(once)));
  const already = listEmbed([av("a")]);
  assert.ok(valueEquals(canonicalizeLists(already), already));
});

test("improper cons is not reified", () => {
  const improper = consv(av("a"), av("b"));
  assert.ok(valueEquals(canonicalizeLists(improper), improper));
  assert.ok(!valueEquals(canonicalizeLists(improper), listEmbed([av("a"), av("b")])));
});

test("a non-list compound is untouched but the list functor IS a sequence", () => {
  const f = valueTuple([av("f"), av("a"), av("b")]);
  assert.ok(valueEquals(canonicalizeLists(f), f));
  const fWithList = valueTuple([av("f"), consList([av("a")])]);
  const expected = valueTuple([av("f"), listEmbed([av("a")])]);
  assert.ok(valueEquals(canonicalizeLists(fWithList), expected));
});

test("deep nested lists canonicalize recursively", () => {
  const outerCons = consList([consList([av("a")]), consList([av("b"), av("c")])]);
  const expected = listEmbed([listEmbed([av("a")]), listEmbed([av("b"), av("c")])]);
  assert.ok(valueEquals(canonicalizeLists(outerCons), expected));
  const outerList = listEmbed([consList([av("a")]), listEmbed([av("b"), av("c")])]);
  assert.ok(valueEquals(canonicalizeLists(outerList), expected));
});

test("a reified leaf matches the cons-form EDB-of-record", () => {
  const program = wrapProgram();
  const leaves = new SrcLeaves([gl("src", consList([av("a"), av("b")]))]);
  const leafList = gl("src", listEmbed([av("a"), av("b")]));
  const deriv = new Derivation([new LeafNode(leafList, Evidence.none())], 0);
  const got = check(program, leafList, deriv, undefined, srcProfile(leaves)).verdict;
  assert.equal(got.kind, "accept", JSON.stringify(got));

  const leaves2 = new SrcLeaves([gl("src", consList([av("a"), av("b")]))]);
  const absent = gl("src", listEmbed([av("z")]));
  const deriv2 = new Derivation([new LeafNode(absent, Evidence.none())], 0);
  const got2 = check(program, absent, deriv2, undefined, srcProfile(leaves2)).verdict;
  assert.equal(got2.kind, "reject");
  if (got2.kind === "reject") assert.equal(got2.code, "leaf_rejected");
});
