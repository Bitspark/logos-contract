/*
 * Language-local tests for the ComponentIdentity / optional identity?() seam
 * (ADR 0004 D4 · tri-core parity with the Rust binding's ComponentIdentity +
 * defaulted identity()). Identity is exposed for attestation only; the binding
 * computes NO digest. Mirrors contract/go/spi_test.go.
 */

import test from "node:test";
import assert from "node:assert/strict";

import {
  AlwaysAdmit,
  ComponentIdentity,
  GroundLiteral,
  Symbol,
  type Theory,
  TheoryGround,
} from "../src/index.js";

function utf8(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

test("ComponentIdentity.unidentified() is stable", () => {
  const a = ComponentIdentity.unidentified();
  const b = ComponentIdentity.unidentified();
  assert.deepEqual(a.id, utf8("unidentified"));
  assert.equal(a.version.length, 0);
  assert.deepEqual(a.configDigest, new Uint8Array(32));
  // Two calls produce the same identity.
  assert.deepEqual(a.id, b.id);
  assert.deepEqual(a.version, b.version);
  assert.deepEqual(a.configDigest, b.configDigest);
});

test("ComponentIdentity.of round-trips its parts", () => {
  const digest = new Uint8Array(32);
  digest[0] = 0xab;
  digest[31] = 0xcd;
  const id = ComponentIdentity.of(utf8("some/component"), utf8("2.1.0"), digest);
  assert.deepEqual(id.id, utf8("some/component"));
  assert.deepEqual(id.version, utf8("2.1.0"));
  assert.deepEqual(id.configDigest, digest);
});

test("ComponentIdentity.of rejects a non-32-byte digest", () => {
  assert.throws(() => ComponentIdentity.of(utf8("x"), utf8("1"), new Uint8Array(8)), RangeError);
});

test("AlwaysAdmit implements identity() with the canonical id", () => {
  const admit = new AlwaysAdmit<void>();
  assert.equal(typeof admit.identity, "function");
  const id = admit.identity();
  assert.deepEqual(id.id, utf8("core/always-admit"));
  assert.deepEqual(id.version, utf8("1.0.0"));
  assert.deepEqual(id.configDigest, new Uint8Array(32));
  // And via the resolve helper (component opts in).
  assert.deepEqual(ComponentIdentity.resolve(admit).id, utf8("core/always-admit"));
});

test("a component without identity() resolves to unidentified", () => {
  // A Theory that does NOT implement the optional identity() — the common case
  // (an impl predating, or simply not opting into, the identity seam). It still
  // satisfies the Theory interface (optional member = non-breaking).
  // test-double: adversarial(relies on the default identity: the unidentified fallback under test)
  class UnidentifiedTheory implements Theory {
    owns(_pred: Symbol): boolean {
      return false;
    }
    decideGround(_atom: GroundLiteral): TheoryGround {
      return TheoryGround.disowned();
    }
  }
  const theory: Theory = new UnidentifiedTheory();
  assert.equal(theory.identity, undefined);
  const id = ComponentIdentity.resolve(theory);
  assert.deepEqual(id.id, utf8("unidentified"));
});
