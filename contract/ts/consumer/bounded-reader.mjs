import assert from "node:assert/strict";
import { test } from "node:test";
import {
  BoundedWireError, CHECK_BUDGETS, CheckLimitError, ClosedModelCert, Derivation,
  derivationWireV1CertPath, GroundLiteral, LeafNode, StratumPrefix,
  certBytesSlack, certSpanOverBudget, certWireSpans, decodeDerivationWireV1Bounded, defaultLimits, encodeDerivationWireV1,
} from "@bitspark/logos-contract";

const certificate = new ClosedModelCert({
  scope: StratumPrefix.of(0, []),
  programHash: new Uint8Array(32), profileHash: new Uint8Array(32),
  ctxHash: new Uint8Array(32), theoryConfigHash: new Uint8Array(32),
  edbSnapshotHashes: [], domains: [], extensions: [], supports: [],
  limitsDecl: { certFacts: 0, domainValues: 0, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 0 },
});
const leaf = new LeafNode(GroundLiteral.of("fact", []));
const frame = count => encodeDerivationWireV1(new Derivation([leaf], 0, Array(count).fill(certificate)));
const limits = maxCertBytes => ({ ...defaultLimits(), maxCertBytes });

function overBudget(cap) {
  return error => error instanceof BoundedWireError && error.kind === "cert_wire_over_budget"
    && error.maxCertBytes === cap;
}

test("the bounded reader owns the v1 path even when an inspector chooses an absent slot", () => {
  const wire = frame(2);
  const path = derivationWireV1CertPath();
  const spans = certWireSpans(wire, path);
  assert.equal(spans.length, 2);
  const cap = Math.max(...spans) - certBytesSlack();
  assert.equal(decodeDerivationWireV1Bounded(wire, limits(cap)).closedWorld.length, 2);
  assert.throws(() => decodeDerivationWireV1Bounded(wire, limits(cap - 1)), overBudget(cap - 1));
  const original = path[1];
  try {
    path[1] = 99;
    assert.deepEqual(certWireSpans(wire, path), []);
    assert.throws(() => decodeDerivationWireV1Bounded(wire, limits(cap - 1)), overBudget(cap - 1));
    assert.throws(() => decodeDerivationWireV1Bounded(wire, limits(0)), overBudget(0));
  } finally {
    path[1] = original;
  }
});

test("positive proofs need no certificate allowance", () => {
  assert.equal(decodeDerivationWireV1Bounded(frame(0), limits(0)).closedWorld.length, 0);
});

test("certificate preflight and decode consume the actual native view and its offset", () => {
  const encoded = frame(1);
  const storage = new Uint8Array(encoded.length + 4);
  storage.set(encoded, 2);
  const view = storage.subarray(2, 2 + encoded.length);
  for (const field of ["length", "buffer", "byteOffset", "byteLength", "subarray"]) {
    Object.defineProperty(view, field, { get() { throw Error(`unexpected input getter: ${field}`); } });
  }
  assert.equal(decodeDerivationWireV1Bounded(view, defaultLimits()).closedWorld.length, 1);
  assert.throws(() => decodeDerivationWireV1Bounded(view, limits(0)), overBudget(0));

  const shared = new Uint8Array(new SharedArrayBuffer(encoded.length));
  shared.set(encoded);
  assert.equal(decodeDerivationWireV1Bounded(shared, defaultLimits()).closedWorld.length, 1);
  assert.throws(() => decodeDerivationWireV1Bounded(shared, limits(0)), overBudget(0));
});

test("an invalid native view is distinct from an empty proof frame", () => {
  const encoded = frame(0);
  const buffer = new ArrayBuffer(encoded.length + 2, { maxByteLength: encoded.length + 2 });
  const input = new Uint8Array(buffer, 1, encoded.length);
  input.set(encoded);
  assert.equal(decodeDerivationWireV1Bounded(input, defaultLimits()).closedWorld.length, 0);
  buffer.resize(0);
  assert.throws(() => decodeDerivationWireV1Bounded(input, defaultLimits()), TypeError);
  assert.throws(() => decodeDerivationWireV1Bounded(new Uint8Array(), defaultLimits()), error =>
    error instanceof BoundedWireError && error.kind === "cert_wire_unreadable");
});

for (const [field, key] of CHECK_BUDGETS) {
  test(`the bounded reader reports invalid ${field} before inspecting a proof frame`, () => {
    for (const count of [-1, NaN, Infinity, 0.5, 2 ** 53]) {
      const input = { ...defaultLimits(), [key]: count };
      for (const wire of [new Uint8Array(), frame(1)]) {
        assert.throws(() => decodeDerivationWireV1Bounded(wire, input), error =>
          error instanceof BoundedWireError && error.kind === "invalid_check_limits"
          && error.detail instanceof CheckLimitError && error.detail.field === field);
      }
    }
  });
}

test("one budget controls both certificates and the reported refusal", () => {
  const wire = frame(2);
  const admitted = Math.max(...certWireSpans(wire, [1, 2])) - certBytesSlack();
  for (const first of [0, admitted]) {
    let reads = 0;
    const policy = Object.create(defaultLimits(), {
      maxCertBytes: { get() { return ++reads === 1 ? first : first === 0 ? admitted : 0; } },
    });
    if (first === 0) {
      assert.throws(() => decodeDerivationWireV1Bounded(wire, policy), overBudget(0));
    } else {
      assert.equal(decodeDerivationWireV1Bounded(wire, policy).closedWorld.length, 2);
    }
    assert.equal(reads, 1);
  }
});

test("the wire budget is numeric and does not read native term-display policy", () => {
  const policy = Object.create(defaultLimits(), {
    termIdentity: { get() { throw Error("term display was inspected"); } },
  });
  assert.equal(decodeDerivationWireV1Bounded(frame(1), policy).closedWorld.length, 1);
});

test("portable certificate byte caps retain the exact span boundary", () => {
  for (const cap of [2 ** 32 - 1, 2 ** 32, Number.MAX_SAFE_INTEGER]) {
    assert.equal(decodeDerivationWireV1Bounded(frame(1), limits(cap)).closedWorld.length, 1);
  }
  const slack = certBytesSlack();
  const last = Number.MAX_SAFE_INTEGER;
  assert.equal(certSpanOverBudget(last, last - slack), false);
  assert.equal(certSpanOverBudget(last, last - slack - 1), true);
  for (const invalid of [-1, NaN, Infinity, 1.5, 2 ** 53]) {
    assert.throws(() => certSpanOverBudget(10, invalid), CheckLimitError);
    assert.throws(() => certSpanOverBudget(invalid, 10), RangeError);
  }
});
