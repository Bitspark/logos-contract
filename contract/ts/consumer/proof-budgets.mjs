import assert from "node:assert/strict";
import { test } from "node:test";
import {
  AlwaysAdmit, CertContext, Derivation, GroundLiteral, LeafNode, LeafOutcome, MapProgram,
  PredicateSet, Term, WorldMemo, captureCheckLimits, captureCheckProfile, captureDerivation, captureSubst, check, checkClosedModelChain, checkWithCertContext,
  checkWithWorldMemo, defaultLimits, newStandardTheory,
  Subst,
  VarId,
} from "@bitspark/logos-contract";

const claim = GroundLiteral.of("fact", []);
const proof = new Derivation([new LeafNode(claim)], 0);
const program = new MapProgram();
const context = CertContext.zero();

function exercise(limits, throughMemo = false) {
  let calls = 0;
  const profile = {
    theory: newStandardTheory(),
    leaves: {
      extensional: () => PredicateSet.from(["fact"]),
      verify: () => { calls++; return LeafOutcome.Admit; },
    },
    admit: new AlwaysAdmit(), limits,
  };
  const outcome = throughMemo
    ? checkWithWorldMemo(new WorldMemo(program, profile, undefined, context), claim, proof)
    : check(program, claim, proof, undefined, profile);
  return { outcome, calls };
}

for (const throughMemo of [false, true]) {
  const path = throughMemo ? "memo" : "direct";
  for (const [field, value] of [
    ["maxNodes", NaN], ["maxNodes", Infinity], ["maxDepth", 0.5], ["maxDepth", 2 ** 53],
    ["maxTermDepth", -1], ["maxCertBytes", -1], ["maxCertFacts", -1], ["maxDomainValues", -1],
    ["maxSupportEdges", -1], ["maxRuleGroundings", -1], ["maxJoinSteps", -1],
  ]) {
    test(`${path} checker refuses ${field}=${String(value)} before consulting the verifier`, () => {
      const { outcome, calls } = exercise({ ...defaultLimits(), [field]: value }, throughMemo);
      assert.deepEqual([outcome.verdict.kind, outcome.verdict.code, calls], ["reject", "invalid_check_limits", 0]);
    });
  }
  test(`${path} checker distinguishes zero capacity from invalid configuration`, () => {
    const limits = defaultLimits();
    assert.equal(exercise(limits, throughMemo).calls, 1);
    const zero = exercise({ ...limits, maxNodes: 0 }, throughMemo);
    assert.deepEqual([zero.outcome.verdict.code, zero.calls], ["too_many_nodes", 0]);
    for (const n of [1, Number.MAX_SAFE_INTEGER]) {
      const accepted = exercise({ ...limits, maxNodes: n, maxDepth: n }, throughMemo);
      assert.deepEqual([accepted.outcome.verdict.kind, accepted.calls], ["accept", 1]);
    }
  });
}

test("a closed-world check distinguishes malformed budgets from an empty chain", () => {
  const profile = {
    theory: newStandardTheory(),
    leaves: { extensional: () => PredicateSet.from([]), verify: () => assert.fail("unexpected leaf") },
    admit: new AlwaysAdmit(), limits: defaultLimits(),
  };
  const run = limits => checkClosedModelChain(program, [], undefined, { ...profile, limits }, context);
  assert.equal(run(profile.limits).verdict.code, "cert_out_of_range");
  assert.equal(run({ ...profile.limits, maxCertBytes: NaN }).verdict.code, "invalid_check_limits");
});

const checkerPaths = {
  direct: profile => check(program, claim, proof, undefined, profile),
  context: profile => checkWithCertContext(program, claim, proof, undefined, profile, context),
  memo: profile => checkWithWorldMemo(new WorldMemo(program, profile, undefined, context), claim, proof),
  chain: profile => checkClosedModelChain(program, [], undefined, profile, context),
};

for (const [path, run] of Object.entries(checkerPaths)) {
  test(`${path} checks a profile supplied through declared getters`, () => {
    const limits = Object.create(defaultLimits());
    const counts = new Map();
    for (const [key, value] of Object.entries(defaultLimits())) {
      Object.defineProperty(limits, key, { get() {
        counts.set(key, (counts.get(key) ?? 0) + 1);
        return value;
      } });
    }
    const ordinary = {
      theory: newStandardTheory(), admit: new AlwaysAdmit(), limits: defaultLimits(),
      leaves: { extensional: () => PredicateSet.from(["fact"]), verify: () => LeafOutcome.Admit },
    };
    const structural = Object.create({ ...ordinary, limits });
    Object.defineProperty(structural, "unrelated", { enumerable: true, get() {
      assert.fail("checker consulted an application field outside CheckProfile");
    } });
    const control = run(ordinary);
    assert.equal(path === "chain" ? control.verdict.code : control.verdict.kind, path === "chain" ? "cert_out_of_range" : "accept");
    assert.deepEqual(run(structural).verdict, control.verdict);
    for (const key of Object.keys(ordinary.limits)) assert.equal(counts.get(key), 1, key);
  });
}

test("a missing inherited budget reports its own field before reading a proof", () => {
  const limits = Object.create(defaultLimits(), { maxJoinSteps: { value: undefined } });
  const unreachable = { get nodes() { assert.fail("read proof with malformed configuration"); } };
  const result = captureDerivation(unreachable, limits);
  assert.equal(result.code, "invalid_check_limits");
  assert.match(result.detail, /max_join_steps/);
});

test("standalone proof capture uses the node cap it validated", () => {
  let reads = 0;
  const limits = Object.create(defaultLimits(), { maxNodes: { get() { return ++reads === 1 ? 0 : 1; } } });
  assert.equal(captureDerivation(proof, limits).code, "too_many_nodes");
  assert.equal(reads, 1);
});

test("standalone substitution capture reads the native term-depth budget once", () => {
  let reads = 0;
  const limits = Object.create(defaultLimits(), { maxTermDepth: { get() { reads++; return 64; } } });
  assert.equal(captureSubst(new Subst([[VarId.of("X"), Term.var("Y")]]), limits).kind, "captured");
  assert.equal(reads, 1);
});

test("native policy capture returns owned values and preserves independently supplied verifier handles", () => {
  const base = defaultLimits();
  const theory = newStandardTheory(), admit = new AlwaysAdmit();
  const leaves = { extensional: () => PredicateSet.from(["fact"]), verify: () => LeafOutcome.Admit };
  const source = Object.create({ theory, leaves, admit, limits: Object.create(base) });
  const captured = captureCheckProfile(source);
  assert.equal(captured.ok, true);
  for (const key of ["theory", "leaves", "admit"]) assert.equal(captured.value[key], source[key]);
  const updated = captureCheckLimits(source.limits, Object.create({ maxDepth: 0 }));
  assert.equal(updated.ok, true);
  const original = base.maxDepth;
  base.maxDepth = 41;
  assert.equal(captured.value.limits.maxDepth, original);
  assert.equal(updated.value.maxDepth, 0);
  assert.equal(Reflect.set(updated.value, "maxDepth", 2), false);
  assert.equal(Reflect.set(captured.value, "leaves", {}), false);
});

test("invalid budgets precede later policy getters and report the observed number", () => {
  const limits = Object.create(defaultLimits(), {
    maxDepth: { value: -1 },
    maxTermDepth: { get() { assert.fail("sampled a later budget"); } },
  });
  const input = { limits, get theory() { assert.fail("sampled an invalid policy's theory"); } };
  const result = captureCheckProfile(input);
  assert.equal(result.ok, false);
  assert.equal(result.error.field, "max_depth");
  assert.equal(result.error.value, -1);
  const direct = check(program, claim, proof, undefined, input);
  assert.equal(direct.verdict.code, "invalid_check_limits");
  assert.match(direct.verdict.detail, /max_depth/);
});
