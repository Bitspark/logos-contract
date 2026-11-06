// #2561 (seat:caa's ruling): decodeDerivationWireV1Bounded holds a derivation wire's certificates to
// the caller's CheckLimits BEFORE decoding. The wires are the real producer derivations of
// vectors/cert_encoded_bytes.json (#2524), which rs and go decode in their twins.

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { DecodeError } from "@bitspark/ontos-codec";

import {
  BOUNDED_WIRE_DECODE,
  BOUNDED_WIRE_OVER_BUDGET,
  BOUNDED_WIRE_STOPPED,
  BOUNDED_WIRE_UNREADABLE,
  BoundedWireError,
  certBytesSlack,
  certWireSpans,
  decodeDerivationWireV1Bounded,
  defaultLimits,
  DERIVATION_WIRE_V1_CERT_PATH,
} from "../src/index.js";

function wire(name: string): Uint8Array {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "cert_encoded_bytes.json");
    if (fs.existsSync(candidate)) {
      const v = JSON.parse(fs.readFileSync(candidate, "utf8")) as { cases: { name: string; derivation_wire: string }[] };
      const c = v.cases.find((x) => x.name === name);
      if (c === undefined) throw new Error(`no case ${name}`);
      const out = new Uint8Array(c.derivation_wire.length / 2);
      for (let i = 0; i < out.length; i++) out[i] = parseInt(c.derivation_wire.slice(2 * i, 2 * i + 2), 16);
      return out;
    }
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/cert_encoded_bytes.json");
    dir = parent;
  }
}

const limitsAt = (maxCertBytes: number) => ({ ...defaultLimits(), maxCertBytes });

const kindOf = (f: () => unknown): string | undefined => {
  try {
    f();
    return undefined;
  } catch (e) {
    if (e instanceof BoundedWireError) return e.kind;
    throw e;
  }
};

test("#2561: a certificate over the caller's budget is refused before decoding", () => {
  for (const name of ["permit_one_certificate", "stacked_two_certificates"]) {
    const bytes = wire(name);
    const spans = certWireSpans(bytes, DERIVATION_WIRE_V1_CERT_PATH);
    assert.ok(spans.length > 0, `${name}: the wire carries certificates`);
    const largest = Math.max(...spans);
    const at = largest - certBytesSlack();
    assert.equal(decodeDerivationWireV1Bounded(bytes, limitsAt(at)).closedWorld.length, spans.length, `${name}: CONTROL: read at max + slack`);
    assert.throws(
      () => decodeDerivationWireV1Bounded(bytes, limitsAt(at - 1)),
      (e: unknown) => e instanceof BoundedWireError && e.kind === BOUNDED_WIRE_OVER_BUDGET && e.span === largest,
      `${name}: one byte past max + slack is refused undecoded`,
    );
  }
});

test("#2561: bytes the walk cannot read are refused, and a readable non-wire is the decoder's refusal", () => {
  const bytes = wire("permit_one_certificate");
  assert.equal(kindOf(() => decodeDerivationWireV1Bounded(bytes.subarray(0, bytes.length / 2), defaultLimits())), BOUNDED_WIRE_UNREADABLE);
  const trailing = new Uint8Array(bytes.length + 1);
  trailing.set(bytes);
  assert.equal(kindOf(() => decodeDerivationWireV1Bounded(trailing, defaultLimits())), BOUNDED_WIRE_UNREADABLE);
  const notAWire = Uint8Array.from([0x01, 0x02, 0x00, 0x01, 0x78, 0x01, 0x00]);
  assert.equal(kindOf(() => decodeDerivationWireV1Bounded(notAWire, defaultLimits())), BOUNDED_WIRE_DECODE);
  // A codec capacity stop is the codec's own error, never the shape refusal (#2734 3c).
  const nested = new Uint8Array(4002);
  for (let i = 0; i < 2000; i++) nested.set([0x01, 0x01], 2 * i);
  let stopped: unknown;
  try {
    decodeDerivationWireV1Bounded(nested, defaultLimits());
  } catch (e) {
    stopped = e;
  }
  assert.ok(stopped instanceof BoundedWireError && stopped.kind === BOUNDED_WIRE_STOPPED, `a value past the codec's decode depth stops the codec, got ${String(stopped)}`);
  assert.ok(stopped.detail instanceof DecodeError && stopped.detail.code === "limit_exceeded", "the codec's own DecodeError rides unfolded");
  assert.throws(() => decodeDerivationWireV1Bounded(bytes, limitsAt(0)), /^BoundedWireError: cert_wire_over_budget|cert_wire_over_budget/);
});
