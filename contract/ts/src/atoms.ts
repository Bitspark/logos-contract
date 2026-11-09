// The two scalar readings the certificate's wire shape needs, in a LEAF module (#2625 (b),
// `seat:caa`'s note on #2629). `wire_sink.ts` imported them from `derivation_wire.ts`, which imports
// its builders from `wire_sink.ts`. That cycle was safe only while both sides held hoisted function
// declarations: a module-scope `const` on either side would meet the temporal dead zone.
// `derivation_wire.ts` re-exports both, so their public names do not move.

import { atom as valueAtom, toHex as coreToHex, type Value } from "@bitspark/ontos-core";
import { hashFromBytes, type OctetSource } from "./octets.js";
import { encodeInt } from "@bitspark/ontos-data";

const enc = new TextEncoder();

/**
 * A non-negative integer as the FROZEN ontos-data `int` embedding (§0.3.5):
 * `Tuple[Atom("int"), Atom(sign ‖ minimal-BE-magnitude)]`. Going through
 * encodeInt is what makes the rs/go/ts integer wire form identical by construction.
 * (All seam integers are non-negative counts/caps. BigInt keeps all 64 bits exact.)
 */
export function intAtom(n: number): Value {
  if (!Number.isFinite(n) || n < 0 || !Number.isInteger(n)) {
    throw new Error(`intAtom expects a non-negative integer, got ${n}`);
  }
  return encodeInt(BigInt(n));
}

/**
 * A 32-byte digest as its lowercase-hex `Atom` (§0.3.7, §1.3) — the on-the-wire form
 * of every 32-byte digest in the seam. A digest is an opaque identifier, so it is a
 * bare hex `Atom`, not a scalar embedding.
 */
export function digestAtom(d: OctetSource): Value {
  return valueAtom(enc.encode(coreToHex(hashFromBytes(d))));
}
