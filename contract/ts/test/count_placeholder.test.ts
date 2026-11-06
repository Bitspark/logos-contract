// The Count placeholder must be EMPTY, matching go and rust (logos#723).
//
// WHY THIS IS PINNED. `BodyLit.count` used to fill `lit` with the COUNTED PREDICATE's name
// while go's `CountLitBody` left the field unset and rust's `Count` variant carries no such
// field at all. The field was read through `inner()`, the documented-partial accessor since
// deleted in #2733 — so a consumer reading it without branching on polarity got a DIFFERENT ANSWER
// PER CORE, and three separate consumers were measured doing exactly that:
//
//   thesmos#409     a count-bearing rule-fact ADMITTED here, REJECTED by go — an
//                   authorization split on attacker-supplied bytes.
//   stele#579       the read-gate's matchLiteral gates on the pred, so the same rule over
//                   the same store produced DIFFERENT DERIVED ROWS across cores.
//   logos-db#153    a rule-fact whose body is a count over `p`, plus a readable zero-arity
//                   fact `p`, DERIVED ITS HEAD here while go refused identical bytes.
//
// Empty is the fail-closed choice: a consumer gating on the pred degrades to "matches
// nothing" rather than silently matching real facts under a name the rule author never wrote.
//
// This test exists because the divergence was INVISIBLE TO THE CONFORMANCE ORACLE — the
// account codec routes a Count to countLitAsTerm before inner() is ever called, so no
// byte-vector could catch it. Nothing compared the placeholder, so nothing noticed.

import { strict as assert } from "node:assert";
import { test } from "node:test";

// This suite reads the public `lit` field directly. The partial inner() accessor was deleted
// (#2733), but the field stays public, so a consumer reading it must still see an EMPTY
// placeholder on a count: that is the invariant pinned here.
import { BodyLit, CountLit, PredicateRef, ProjectSpec, Symbol, Term } from "../src/index.js";

function countLit(): CountLit {
  return new CountLit(new PredicateRef(Symbol.of("counted"), 1), [], ProjectSpec.rows(), Term.var("N"));
}

test("a Count's placeholder goal is EMPTY, not the counted predicate", () => {
  const bl = BodyLit.count(countLit());

  // The regression itself: this returned Symbol.of("counted") before logos#723.
  assert.equal(
    bl.lit.pred.bytes().length,
    0,
    "a Count's placeholder must expose an EMPTY predicate — a real name here is what made " +
      "consumer gates that read the pred admit/derive where go refused (thesmos#409, " +
      "stele#579, logos-db#153)",
  );
  assert.equal(bl.lit.args.length, 0, "a Count's placeholder carries no args");
});

test("the counted predicate is still reachable where it belongs", () => {
  const bl = BodyLit.count(countLit());

  // Emptying the placeholder must not lose the information — it moves it to the accessors
  // that branch on polarity, which is the whole point.
  assert.equal(new TextDecoder().decode(bl.countLit!.pred.pred.bytes()), "counted");
  assert.equal(new TextDecoder().decode(bl.pred().bytes()), "counted");
  assert.equal(new TextDecoder().decode(bl.dependency().pred.bytes()), "counted");
});

// A consumer must not be able to tell a Count from a positive literal by reading the `lit` field
// alone — that indistinguishability is deliberate, and is why isPos() exists (#722).
test("the placeholder field cannot be used to classify a Count", () => {
  const count = BodyLit.count(countLit());
  const pos = BodyLit.pos(new (Object.getPrototypeOf(count.lit).constructor)(Symbol.of(""), []));

  assert.equal(
    count.lit.pred.bytes().length,
    pos.lit.pred.bytes().length,
    "a Count and an empty-pred positive literal must look identical through the field — " +
      "classification is isPos()/isCount()'s job, never a field read",
  );
  assert.equal(count.isPos(), false, "and isPos() is how you actually tell them apart");
});
