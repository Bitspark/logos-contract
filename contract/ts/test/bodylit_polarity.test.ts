// BodyLit polarity predicates — isPos / isNeg / isCount must PARTITION the polarity.
//
// WHY THIS EXISTS. Before isPos, the contract exported only the complements (isNeg,
// isCount). A consumer gating on positive-only bodies — e.g. arche PROTOCOL 3.10a, which
// says a rule-fact body is positive Horn — could therefore only express its rule as
// "not neg and not count": a BLACKLIST. That admits every polarity added later BY DEFAULT,
// silently, in every consumer not updated in lockstep. It is how a `count` body literal
// came to be admitted by one consumer core and rejected by two others (thesmos#409) — an
// authorization split on attacker-supplied bytes, since rule-fact clauses are untrusted.
//
// The partition assertion below is the load-bearing one: it fails if a new polarity is
// added without a matching predicate, which is exactly the moment a downstream whitelist
// would otherwise start silently under-matching.

import { strict as assert } from "node:assert";
import { test } from "node:test";

import {
  BodyLit,
  CountLit,
  Goal,
  type Polarity,
  PredicateRef,
  ProjectSpec,
  Symbol,
  Term,
} from "../src/index.js";

// EXHAUSTIVENESS FORCER (#996) — the ts half of what #991 gave rust.
//
// The type annotation is the whole mechanism. `Record<Polarity, …>` requires a key for EVERY
// member of the `Polarity` union, so adding one to `type Polarity = "pos" | "neg" | "count"`
// makes this object fail to COMPILE ("Property 'foo' is missing in type ..."). tsc stops the
// author right here, at the corpus, which is the same class of forcing as rust's arm-less
// `match` — and it is available because ts models the polarity as a string-literal union.
//
// ⚠ Do NOT loosen this to `Record<string, BodyLit>` or `Partial<Record<…>>`. Either one
// restores exactly the silent vacuity the forcer exists to remove: every guard below iterates
// this corpus, so a polarity missing from it passes them ALL without being tested.
//
// HONEST BOUND: this forces a compile stop at the corpus. It does not prove the sample added is
// a CORRECT one — the partition guard covers that, and can only cover what is listed here.
//
// (Go can have neither this nor rust's: `Polarity` is `int` + `iota` there, with no switch
// exhaustiveness and no const reflection. Its equivalent parses its own source at test time —
// see contract/go/polarity_tripwire_test.go.)
const POLARITY_CORPUS: Record<Polarity, BodyLit> = (() => {
  const g = Goal.of("p", [Term.var("X")]);
  return {
    pos: BodyLit.pos(g),
    neg: BodyLit.neg(g),
    count: BodyLit.count(
      new CountLit(new PredicateRef(Symbol.of("q"), 1), [], ProjectSpec.rows(), Term.var("N")),
    ),
  };
})();

// Derived from the forced corpus, so the cases and the forcer cannot drift apart.
//
// ⚠ This function's doc used to say "the partition test fails until you do, and that failure is
// the point". THAT WAS FALSE (#996): every guard iterates these cases, so a polarity added
// without listing it here left them all passing VACUOUSLY — including "isPos is not the negated
// complement", whose own message warns about "a polarity it was never told about". A guard that
// cannot see the thing it warns about is the defect it warns about. The compile stop above is
// what actually forces the update now.
function polarityCases(): Array<[string, BodyLit]> {
  return Object.entries(POLARITY_CORPUS);
}

test("isPos holds only for a positive body literal", () => {
  for (const [name, bl] of polarityCases()) {
    assert.equal(bl.isPos(), name === "pos", `isPos() wrong for ${name}`);
  }
});

// EXACTLY ONE of isPos/isNeg/isCount must hold for every polarity.
//
// "At least one" fails when a polarity is added with no predicate — the case where a
// downstream whitelist (isPos) silently stops matching a body it should classify.
// "At most one" fails if two ever overlap, which would make a whitelist and a blacklist
// disagree about the same literal.
test("polarity predicates partition the polarity", () => {
  for (const [name, bl] of polarityCases()) {
    const n = [bl.isPos(), bl.isNeg(), bl.isCount()].filter(Boolean).length;
    assert.equal(
      n,
      1,
      `polarity ${name}: ${n} of {isPos, isNeg, isCount} hold, want exactly 1 — a polarity ` +
        `with no predicate is admitted by default in any consumer that gates by ruling out ` +
        `the others`,
    );
  }
});

// Pins why isPos is not a convenience alias for the negated complement: the two agree
// TODAY, and a polarity added without a predicate makes them diverge. Consumers gating on
// positive-Horn bodies must use the whitelist.
test("isPos is not the negated complement", () => {
  for (const [name, bl] of polarityCases()) {
    const whitelist = bl.isPos();
    const blacklist = !bl.isNeg() && !bl.isCount();
    assert.equal(
      whitelist,
      blacklist,
      `polarity ${name}: isPos()=${whitelist} but !isNeg()&&!isCount()=${blacklist} — the ` +
        `blacklist formulation admits a polarity it was never told about`,
    );
  }
});

// UNKNOWN-POLARITY FAIL-CLOSED GUARD (#996) — pins caa's ruling on the three structural surfaces.
//
// THE DEFECT THIS REPLACES. `default:` used to be an ALIAS for the pos case — commented
// `// pos` — on bindingTerms, requiredTerms and dependency. That aliasing turned "a polarity we
// have never seen" into "the most permissive polarity we have", at three surfaces feeding range
// restriction and stratification. MEASURED in the go sibling before the fix, for a fourth
// polarity: bindingTerms = its args (claims it BINDS them), requiredTerms = [] (claims it
// requires NOTHING bound), dependency.nonMonotone = FALSE (tells the stratifier there is NO
// barrier).
//
// An unknown polarity must instead bind nothing, require everything, and force a barrier — deny
// in every direction.
//
// The cast is deliberate and is the only honest way to write this test: the forcer above makes
// an unhandled polarity a COMPILE error, so the runtime case can only be reached by stepping
// around the type system — which is exactly what a core built against an older contract does.
//
// REACHABILITY (measured for #996): an unknown polarity cannot arrive from outside the process —
// bodyLitFromTerm constructs only via BodyLit.pos/neg/count, so there is no byte path to an
// arbitrary polarity. This guards a maintainer adding a variant, not an attacker sending one.
test("an unknown polarity fails closed on binding, safety, and dependency", () => {
  const lit = Goal.of("p", [Term.var("X"), Term.var("Y")]);
  const unknown = new BodyLit("probe-unknown" as Polarity, lit);

  assert.equal(unknown.isPos(), false, "isPos() must deny an unknown polarity");
  assert.equal(unknown.asInner(), null, "asInner() must deny an unknown polarity");

  assert.deepEqual(
    unknown.bindingTerms(),
    [],
    "bindingTerms() must assume an unknown literal binds NOTHING — it returned lit.args while " +
      "`default` aliased the pos case",
  );
  assert.equal(
    unknown.requiredTerms().length,
    lit.args.length,
    "requiredTerms() must assume an unknown literal evaluates NOTHING on its own, so range " +
      "restriction demands every argument already bound",
  );
  assert.equal(
    unknown.dependency().nonMonotone,
    true,
    "dependency().nonMonotone must be true for an unknown polarity so the stratifier keeps its " +
      "barrier — false here is what let an unseen polarity through with no stratum at all",
  );
});

// CLOSES THE LAST UNFORCED STEP (#996), for ts.
//
// The `Record<Polarity, BodyLit>` forcer above proves a sample EXISTS for every polarity. It does
// not prove the sample is the RIGHT one: `foo: BodyLit.pos(g)` satisfies the compiler perfectly
// while leaving the new polarity untested and quietly testing "pos" twice. caa named this residue
// on #991 as the last unforced step in the chain and could not see a way to close it from the
// contract tier.
//
// For ts it closes, because the corpus KEY is the polarity itself. The compiler forces
// key-set == union; this forces sample.polarity == key. Together they force: every polarity has a
// sample, and that sample IS that polarity. There is no remaining way to satisfy the forcer without
// testing the new variant.
//
// (The same closure is available in go — see contract/go/polarity_tripwire_test.go, where the AST's
// declaration ORDER supplies the iota value the sample must carry. Rust's corpus already derives its
// label from the value via variant_name(), so its residue is narrower, but the enumeration half
// still cannot come from the type system.)
test("every corpus sample actually has the polarity it is filed under", () => {
  const entries = Object.entries(POLARITY_CORPUS);
  for (const [key, bl] of entries) {
    assert.equal(
      bl.polarity,
      key,
      `corpus entry ${JSON.stringify(key)} holds a literal whose polarity is ` +
        `${JSON.stringify(bl.polarity)} — the Record forcer is satisfied by ANY BodyLit under a ` +
        `key, so a mis-filed sample leaves ${key} untested while testing ${bl.polarity} twice`,
    );
  }
  assert.equal(entries.length, 3, `corpus size ${entries.length}`); // denominator, printed on failure
});
