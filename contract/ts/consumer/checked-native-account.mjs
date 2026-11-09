import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom, Tuple } from "@bitspark/ontos-core";
import {
  AlwaysAdmit, CertContext, ClosedModelCert, Derivation, Evidence, FiniteDomain,
  GroundLiteral, LeafNode, LeafOutcome, MapProgram, PredicateSet, StratumPrefix, Symbol, WorldMemo, check, checkClosedModelChain, checkWithCertContext, checkWithWorldMemo,
  defaultLimits, newStandardTheory, programDigest,
} from "@bitspark/logos-contract";

const a = new Atom(Uint8Array.of(97));
const attested = GroundLiteral.of("allowed", [a]);
const wrong = GroundLiteral.of("other", [a]);
const program = new MapProgram();
const profile = {
  theory: newStandardTheory(),
  leaves: {
    extensional: () => PredicateSet.from(["allowed"]),
    verify: literal => attested.equals(literal) ? LeafOutcome.Admit : LeafOutcome.Reject("no_attestation"),
  },
  admit: new AlwaysAdmit(),
  limits: defaultLimits(),
};
const ctx = CertContext.zero();
const proofOf = literal => new Derivation([new LeafNode(literal, Evidence.none())], 0);
const checks = [
  ["check", (claim, proof) => check(program, claim, proof, undefined, profile)],
  ["checkWithCertContext", (claim, proof) => checkWithCertContext(program, claim, proof, undefined, profile, ctx)],
  ["checkWithWorldMemo", (claim, proof) => checkWithWorldMemo(new WorldMemo(program, profile, undefined, ctx), claim, proof)],
];

for (const [name, verify] of checks) {
  test(`${name} owns the final comparison with the caller's claim`, () => {
    assert.equal(verify(attested, proofOf(attested)).kind, "accept");
    assert.equal(verify(wrong, proofOf(attested)).code, "root_conclusion_mismatch");
    let calls = 0;
    const proposed = { pred: attested.pred, args: attested.args, equals() { calls++; return true; } };
    assert.equal(verify(wrong, proofOf(proposed)).kind, "reject");
    assert.equal(calls, 0);
  });

  test(`${name} refuses a counterfeit ground value nested inside a native tuple`, () => {
    const fake = Object.create(Atom.prototype);
    Object.defineProperty(fake, "equals", { value: () => assert.fail("called a producer equality method") });
    const forged = GroundLiteral.of("allowed", [new Tuple([fake])]);
    assert.equal(verify(attested, proofOf(forged)).code, "unknown_node_kind");
  });

  test(`${name} reads the selected node array once and checks its indexed contents`, () => {
    const nodes = [new LeafNode(attested, Evidence.none())];
    Object.defineProperty(nodes, globalThis.Symbol.iterator, {
      value: () => assert.fail("invoked a producer-supplied node iterator"),
    });
    let reads = 0;
    const proposal = {
      get nodes() { reads++; return nodes; },
      root: 0,
      closedWorld: [],
    };
    assert.equal(verify(attested, proposal).kind, "accept");
    assert.equal(reads, 1);
  });
}

test("whole-chain verification interprets the domain's actual values", () => {
  const pin = new Uint8Array(32).fill(1);
  const bound = CertContext.of(programDigest([]), pin, pin, pin);
  const domainTag = Symbol.of("domain");
  const chain = domain => [new ClosedModelCert({
    ...bound, scope: StratumPrefix.of(0, []), edbSnapshotHashes: [],
    domains: [domain], extensions: [], supports: [],
    limitsDecl: { certFacts: 0, domainValues: 2, supportEdges: 0, ruleGroundings: 10, joinSteps: 10, certBytes: 4096 },
  })];
  const verify = domain => checkClosedModelChain(program, chain(domain), undefined, profile, bound);
  assert.equal(verify(FiniteDomain.of(domainTag, [a])).kind, "accept");
  const duplicated = new FiniteDomain(domainTag, [a, a]);
  const expected = verify(duplicated);
  assert.equal(expected.kind, "reject");
  let calls = 0;
  class ClaimedCanonical extends FiniteDomain {
    isCanonical() { calls++; return true; }
  }
  assert.deepEqual(verify(new ClaimedCanonical(domainTag, [a, a])), expected);
  assert.equal(calls, 0);
});
