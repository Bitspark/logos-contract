import assert from "node:assert/strict";
import { test } from "node:test";
import { runInNewContext } from "node:vm";
import { parseHashHex } from "@bitspark/logos-contract";

const canonical = "01ab".repeat(16);
const expected = Uint8Array.from({ length: 32 }, (_, index) => index % 2 === 0 ? 1 : 0xab);

test("the standalone hash parser reads text and ASCII bytes in the same grammar", () => {
  assert.deepEqual(parseHashHex("00".repeat(32)), new Uint8Array(32));
  assert.deepEqual(parseHashHex(canonical), expected);
  const encoded = new TextEncoder().encode(canonical);
  const hash = parseHashHex(encoded);
  assert.deepEqual(hash, expected);
  encoded.fill(0);
  assert.deepEqual(hash, expected);
  for (const text of ["fg" + canonical.slice(2), "00".repeat(31), canonical + "0f", canonical.toUpperCase(), "０".repeat(64)]) {
    assert.equal(parseHashHex(text), undefined);
    assert.equal(parseHashHex(new TextEncoder().encode(text)), undefined);
  }
});

test("binary hash input uses the extent and bytes of the genuine view", () => {
  const foreign = runInNewContext("Uint8Array.from(input)", { input: new TextEncoder().encode(canonical) });
  Object.defineProperty(foreign, "length", { get() { assert.fail("read application length"); } });
  Object.defineProperty(foreign, Symbol.iterator, { get() { assert.fail("read application iterator"); } });
  assert.deepEqual(parseHashHex(foreign), expected);
  const long = new Uint8Array(65).fill(0x30);
  Object.defineProperty(long, "length", { value: 64 });
  assert.equal(parseHashHex(long), undefined);
  assert.equal(parseHashHex(new Uint16Array(64).fill(0x30)), undefined);
});
