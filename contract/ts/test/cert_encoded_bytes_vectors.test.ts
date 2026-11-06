// TS replay of vectors/cert_encoded_bytes.json (#2524): a certificate's size in bytes is its
// canonical encoding with `limitsDecl.certBytes` zeroed. Every case decodes one derivation wire and
// measures its closedWorld certificates, which must equal the numbers the rs generator measured.

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { certEncodedBytes, decodeDerivationWireV1, encodeDerivationWireV1 } from "../src/index.js";
import { assertLengthReading2605 } from "./support/cert_len_2605.js";

interface CertEncodedBytesCase {
  readonly name: string;
  readonly produced: boolean;
  readonly cert_bytes: readonly number[];
  readonly derivation_wire: string;
}

function load(): { readonly cases: readonly CertEncodedBytesCase[] } {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "cert_encoded_bytes.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8"));
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/cert_encoded_bytes.json");
    dir = parent;
  }
}

function fromHex(hex: string): Uint8Array {
  assert.equal(hex.length % 2, 0, "an even-length hex wire");
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.slice(2 * i, 2 * i + 2), 16);
  return out;
}

test("#2524: every core measures the vector's certificates the same", () => {
  const { cases } = load();
  assert.equal(cases.length, 7, "the vector's seven cases");
  for (const c of cases) {
    const deriv = decodeDerivationWireV1(fromHex(c.derivation_wire));
    // #2605: the value reading is byte-identical to the one the generator wrote.
    assert.equal(Buffer.from(encodeDerivationWireV1(deriv)).toString("hex"), c.derivation_wire, `${c.name}: the wire re-encodes byte-identically`);
    assert.ok(deriv.closedWorld.length > 0, `${c.name}: a case carries a certificate`);
    assert.equal(deriv.closedWorld.length, c.cert_bytes.length, `${c.name}: one pinned measure per certificate`);
    deriv.closedWorld.forEach((cert, i) => {
      const got = certEncodedBytes(cert);
      assertLengthReading2605(`${c.name} certificate ${i}`, cert);
      assert.equal(got, c.cert_bytes[i], `${c.name}: certificate ${i}`);
      if (c.produced) assert.equal(cert.limitsDecl.certBytes, got, `${c.name}: certificate ${i} declares its measure`);
    });
  }
});
