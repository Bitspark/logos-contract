// #2605 (seat:caa's condition 3 for ts): the length reading equals the encoding it measures. A
// helper module, not a test file, so the replays of vectors/{cert_encoded_bytes,negation,
// aggregation}.json and wire_sink_2605.test.ts can share it without re-registering each other's tests.

import assert from "node:assert/strict";

import { encode } from "@bitspark/ontos-codec";

import { ClosedModelCert, certEncodedBytes, closedModelCertAsValue } from "../../src/index.js";

export function assertLengthReading2605(where: string, cert: ClosedModelCert): void {
  const zeroed = new ClosedModelCert({ ...cert, limitsDecl: { ...cert.limitsDecl, certBytes: 0 } });
  assert.equal(
    certEncodedBytes(cert),
    encode(closedModelCertAsValue(zeroed)).length,
    `${where}: the length reading disagrees with the encoding it measures`,
  );
}
