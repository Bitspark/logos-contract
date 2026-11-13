import assert from "node:assert/strict";
import { test } from "node:test";
import {
  AlwaysAdmit, BuiltinNode, Clause, ClauseId, DecisionCompletion, Derivation, Goal,
  GroundLiteral, LeafNode, LeafOutcome, MapProgram, PredicateSet, RuleNode,
  RuleOutcome, Symbol, TheoryGround, check, completion, completionOf, defaultLimits,
  newStandardTheory, Verdict,
  Subst,
} from "@bitspark/logos-contract";

const fact = Goal.of("fact", []);
const claim = fact.asGround();
const id = ClauseId.of("id");
const program = new MapProgram().with(id, Clause.fact(fact));
const proof = new Derivation([new RuleNode(claim, id, new Subst(), [])], 0);
const profile = {
  theory: newStandardTheory(),
  leaves: { extensional: () => PredicateSet.from(["leaf"]), verify: () => LeafOutcome.Reject("unattested") },
  admit: new AlwaysAdmit(),
  limits: defaultLimits(),
};
const verify = (goal, candidate, bound = profile) => check(program, goal, candidate, undefined, bound);

// On the affected package the write succeeds. Restore it even when an assertion fails so
// every case exercises its own authority boundary. A fixed package can decline the write.
function tryEdit(object, key, value, observe) {
  const original = object[key];
  const changed = Reflect.set(object, key, value);
  try {
    observe();
  } finally {
    if (changed) Reflect.set(object, key, original);
  }
}

function rejectionSurvives(run, code, object, key, replacement) {
  const expected = run();
  assert.equal(expected.verdict.kind, "reject");
  assert.equal(expected.verdict.code, code);
  tryEdit(object, key, replacement, () => assert.deepEqual(run().verdict, expected.verdict));
}

test("a public importer cannot make an empty derivation check", () => {
  const empty = new Derivation([], 0);
  const checkEmpty = () => verify(claim, empty);
  assert.equal(verify(claim, proof).verdict.kind, "accept");
  rejectionSurvives(checkEmpty, "empty_derivation", Verdict, "reject", () => Verdict.Accept);
});

test("editing a returned acceptance cannot change a subsequent successful check", () => {
  const accepted = verify(claim, proof);
  assert.equal(accepted.verdict.kind, "accept");
  tryEdit(accepted.verdict, "kind", "reject", () => assert.equal(verify(claim, proof).verdict.kind, "accept"));
});

test("a standard theory still rejects a builtin with the wrong arity", () => {
  const length = GroundLiteral.of("length", []);
  const candidate = new Derivation([new BuiltinNode(length)], 0);
  const run = () => verify(length, candidate);
  rejectionSurvives(run, "builtin_failed", TheoryGround, "fails", () => TheoryGround.holds());
});

test("the configured verifier owns its leaf rejection", () => {
  const leaf = GroundLiteral.of("leaf", []);
  const candidate = new Derivation([new LeafNode(leaf)], 0);
  const run = () => verify(leaf, candidate);
  rejectionSurvives(run, "leaf_rejected", LeafOutcome, "Reject", () => LeafOutcome.Admit);
  const admits = { ...profile, leaves: { ...profile.leaves, verify: () => LeafOutcome.Admit } };
  assert.equal(verify(leaf, candidate, admits).verdict.kind, "accept");
});

test("the configured rule-admissibility component owns its denial", () => {
  const denies = { ...profile, admit: { admissible: () => RuleOutcome.Reject("denied") } };
  const run = () => verify(claim, proof, denies);
  rejectionSurvives(run, "rule_inadmissible", RuleOutcome, "Reject", () => RuleOutcome.Admit);
  assert.equal(verify(claim, proof).verdict.kind, "accept");
});

test("a theory without a completion declaration stays undeclared", () => {
  const pred = Symbol.of("p");
  const theory = { owns: () => true, decideGround: () => TheoryGround.holds() };
  const read = () => completionOf(theory, pred).kind;
  assert.equal(read(), "undeclared");
  tryEdit(DecisionCompletion, "undeclared", () => DecisionCompletion.StopsAreTyped, () => assert.equal(read(), "undeclared"));
  assert.equal(completionOf({ ...theory, completion: () => DecisionCompletion.StopsAreTyped }, pred).kind, "stops_are_typed");
});

test("reading the completed positive decision cannot turn other positive decisions into failures", () => {
  const read = () => TheoryGround.holds().value.kind;
  assert.equal(read(), "holds");
  tryEdit(completion.theoryHolds, "kind", "fails", () => assert.equal(read(), "holds"));
  tryEdit(TheoryGround, "holds", () => TheoryGround.fails("edited"), () => assert.equal(read(), "holds"));
});

test("an inspected logic result cannot rewrite subsequent negation or malformed-input handling", () => {
  const negated = () => completion.not(completion.completed(completion.fails("unsatisfied"))).value.kind;
  assert.equal(negated(), "holds");
  tryEdit(completion.holds, "kind", "fails", () => assert.equal(negated(), "holds"));
  const normalize = () => completion.normalize(null).cause;
  assert.equal(normalize().kind, "malformed_outcome");
  tryEdit(normalize(), "kind", "inconsistent_theory", () => assert.equal(normalize().kind, "malformed_outcome"));
});

test("an importer cannot change a component's shared positive response", () => {
  const leaf = GroundLiteral.of("leaf", []);
  const leafProof = new Derivation([new LeafNode(leaf)], 0);
  const admits = { ...profile, leaves: { ...profile.leaves, verify: () => LeafOutcome.Admit } };
  const acceptedLeaf = () => verify(leaf, leafProof, admits).verdict.kind;
  assert.equal(acceptedLeaf(), "accept");
  tryEdit(LeafOutcome.Admit, "kind", "reject", () => assert.equal(acceptedLeaf(), "accept"));
  tryEdit(RuleOutcome.Admit, "kind", "reject", () => assert.equal(verify(claim, proof).verdict.kind, "accept"));
  const declaration = () => completionOf(profile.theory, Symbol.of("length")).kind;
  assert.equal(declaration(), "stops_are_typed");
  tryEdit(DecisionCompletion.StopsAreTyped, "kind", "undeclared", () => assert.equal(declaration(), "stops_are_typed"));
});
