import assert from "node:assert/strict";
import { test } from "node:test";
import { type OctetSource, type Hash, hashFromBytes, copyOctets } from "@bitspark/logos-contract";

test("public raw hash and byte declarations accept a readonly octet sequence", () => {
  const octets: OctetSource = [0, 255] as const;
  const hash: Hash = hashFromBytes(new Uint8Array(32));
  assert.deepEqual(copyOctets(octets), Uint8Array.of(0, 255));
  assert.equal(hash.length, 32);
});

await import(new URL("../../consumer/octet-input.mjs", import.meta.url).href);
