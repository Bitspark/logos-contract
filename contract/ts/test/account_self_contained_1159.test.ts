// `Derivation.isSelfContained()` — §8.2's first portability arm (#1159, P4).
//
// The account-side mirror of the kernel seam's `CheckContext.isTrivial`. BOTH directions are
// pinned, because a predicate that is constant passes a one-armed test: an all-positive
// account is self-contained, one carrying a ClosedModelCert is not, and the two must DIFFER.

import { strict as assert } from "node:assert";
import { test } from "node:test";
import {
  BuiltinNode,
  CertSizeDecl,
  ClosedModelCert,
  Derivation,
  GroundLiteral,
  type Hash,
  type Node,
  StratumPrefix,
  Symbol,
} from "../src/index.js";

/**
 * A structurally minimal cert. Never verified here — `isSelfContained` reads only
 * `closedWorld`'s length, so the cert's CONTENTS are deliberately irrelevant, and a valid
 * one would be testing something this predicate does not do.
 */
function anyCert(): ClosedModelCert {
  const zero: Hash = new Uint8Array(32);
  const limitsDecl: CertSizeDecl = {
    certFacts: 0,
    domainValues: 0,
    supportEdges: 0,
    ruleGroundings: 0,
    joinSteps: 0,
    certBytes: 0,
  };
  return new ClosedModelCert({
    scope: StratumPrefix.of(0, [Symbol.of("p")]),
    programHash: zero,
    profileHash: zero,
    ctxHash: zero,
    theoryConfigHash: zero,
    edbSnapshotHashes: [],
    domains: [],
    extensions: [],
    supports: [],
    limitsDecl,
  });
}

function oneNode(): Node {
  return new BuiltinNode(GroundLiteral.of("p", []));
}

test("an all-positive account is self-contained (§8.2's first arm)", () => {
  const deriv = new Derivation([oneNode()], 0);
  assert.equal(
    deriv.isSelfContained(),
    true,
    "an all-positive account cites no closure, so it needs no context",
  );
});

test("an account carrying a ClosedModelCert is NOT self-contained", () => {
  const deriv = new Derivation([oneNode()], 0, [anyCert()]);
  assert.equal(
    deriv.isSelfContained(),
    false,
    "a certifying check needs a bound cert context",
  );
});

// The vacuity guard. Each test above passes on a predicate hard-coded to its own answer;
// only the DIFFERENCE shows the predicate reads anything at all.
test("the predicate is not constant — the two arms differ", () => {
  const positive = new Derivation([oneNode()], 0);
  const certifying = new Derivation([oneNode()], 0, [anyCert()]);
  assert.notEqual(
    positive.isSelfContained(),
    certifying.isSelfContained(),
    "a constant predicate satisfies both one-armed tests",
  );
});

// The one thing the doc promises beyond the body: it tracks `closedWorld` and nothing else,
// so node count and shape must not move it.
test("self-containment tracks closedWorld only, not node count", () => {
  const one = new Derivation([oneNode()], 0);
  const many = new Derivation([oneNode(), oneNode(), oneNode()], 0);
  assert.equal(one.isSelfContained(), true);
  assert.equal(many.isSelfContained(), true);

  const certifyingMany = new Derivation([oneNode(), oneNode(), oneNode()], 0, [anyCert()]);
  assert.equal(certifyingMany.isSelfContained(), false);
});
