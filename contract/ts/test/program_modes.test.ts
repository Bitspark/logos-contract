// Pins the first-class binding & dependency mode descriptors on BodyLit (research-doc 0009):
// bindingTerms / requiredTerms / dependency, each total over pos/neg/count. The analyzer's safety
// + dependency passes rely on these uniformly; mirrors the rs program::tests::bodylit_first_class_modes
// and the go TestBodyLitFirstClassModes.

import { test } from "node:test";
import assert from "node:assert/strict";

import { BodyLit, CountLit, Goal, PredicateRef, ProjectSpec, Symbol as ContractSymbol, Term } from "../src/index.js";

const dec = (b: Uint8Array): string => new TextDecoder().decode(b);

test("BodyLit first-class binding & dependency modes", () => {
  const [x, y, z, g, n] = [Term.var("X"), Term.var("Y"), Term.var("Z"), Term.var("G"), Term.var("N")];
  const pos = BodyLit.pos(Goal.of("p", [x, y]));
  const neg = BodyLit.neg(Goal.of("q", [z]));
  const count = BodyLit.count(
    new CountLit(new PredicateRef(ContractSymbol.of("obs"), 3), [{ pos: 0, term: g }], ProjectSpec.rows(), n),
  );

  // bindingTerms: a positive atom binds all its args; a negation binds nothing; a count binds only
  // its result.
  assert.deepEqual(pos.bindingTerms(), [x, y]);
  assert.equal(neg.bindingTerms().length, 0);
  assert.deepEqual(count.bindingTerms(), [n]);

  // requiredTerms: a positive atom requires nothing; a negation requires all its args; a count
  // requires its filter/group vars (the result is exempt).
  assert.equal(pos.requiredTerms().length, 0);
  assert.deepEqual(neg.requiredTerms(), [z]);
  assert.deepEqual(count.requiredTerms(), [g]);

  // dependency: (read predicate, non-monotone?). A positive atom is monotone; a negation and an
  // aggregate are non-monotone (both read a sealed, strictly-lower stratum).
  for (const [name, b, wantPred, wantNonMo] of [
    ["pos", pos, "p", false],
    ["neg", neg, "q", true],
    ["count", count, "obs", true],
  ] as const) {
    const dep = b.dependency();
    assert.equal(dec(dep.pred.bytes()), wantPred, `${name} pred`);
    assert.equal(dep.nonMonotone, wantNonMo, `${name} nonMonotone`);
  }
});
