import assert from "node:assert/strict";
import { test } from "node:test";
import * as contract from "@bitspark/logos-contract";

test("the standalone package exposes whole checks and hides checker stages", () => {
  for (const name of ["check", "checkWithCertContext", "checkWithWorldMemo", "checkClosedModelChain", "programDigestOf"]) {
    assert.equal(typeof contract[name], "function", name);
  }
  for (const name of ["verifyCert", "verifyNegPremise", "verifyCountPremise", "checkScopeDownwardClosed",
    "STANDALONE_CERT", "checkCertTermDepths", "equalGroundFilter", "projectEquals", "programDigestOverScope",
    "eachBudgetRaised"]) {
    assert.equal(name in contract, false, name);
  }
});

test("package consumers cannot import private certificate stages", async () => {
  await assert.rejects(import("@bitspark/logos-contract/dist/src/cert_check.js"),
    { code: "ERR_PACKAGE_PATH_NOT_EXPORTED" });
});

test("the identity advisory reports the slots and allowances selected for this call", () => {
  const id = contract.ComponentIdentity.of(new Uint8Array([1]), new Uint8Array([2]), new Uint8Array(32));
  const allow = ["admit"];
  const leaves = { extensional: () => contract.PredicateSet.from([]), verify: () => contract.LeafOutcome.Reject("empty") };
  const profile = {
    theory: {
      owns: () => false,
      decideGround: () => contract.TheoryGround.disowned(),
      identity() {
        profile.leaves = { ...leaves, identity: () => id };
        allow[0] = "leaves";
        return id;
      },
    },
    leaves,
    admit: { admissible: () => contract.RuleOutcome.Admit },
    get limits() { assert.fail("an identity report asked for proof budgets"); },
  };
  assert.deepEqual(contract.unidentifiedProfileSlotsAllowing(profile, allow), ["leaves"]);
  assert.deepEqual(contract.unidentifiedProfileSlotsAllowing(profile, allow), ["admit"]);
});

