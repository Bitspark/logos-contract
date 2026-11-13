// Checker SPI v2, ADR 0036 D8 change 4 (#3111; #2734 ruling C): the trusted decoder's codec stop is
// its own FAULT class, carrying the codec's error, and a decoded value of the wrong shape is still
// the shape refusal. Twin of rs's trusted_codec_fault_3111 module and go's
// TestACodecStopOnTrustedBytesIsACodecFaultNotAShape3111.
import test from "node:test";
import assert from "node:assert/strict";

import { atom } from "@bitspark/ontos-core";
import { DecodeError as CodecDecodeError, encode } from "@bitspark/ontos-codec";

import { DecodeCodecFault, DecodeError, decodeDerivationWireV1 } from "../src/index.js";

test("a codec stop on trusted bytes is a codec fault, not a shape (#3111)", () => {
  assert.throws(
    () => decodeDerivationWireV1(new Uint8Array()),
    (e: unknown) => {
      assert.ok(e instanceof DecodeCodecFault, `expected the codec fault class, got ${String(e)}`);
      assert.ok(e instanceof DecodeError, "the fault is still a DecodeError, as rs's arm and go's kind are");
      assert.equal(e.ctx, "derivation wire v1 bytes");
      const codecError = e.codecError;
      assert.ok(codecError instanceof CodecDecodeError, "the codec's own error is carried");
      assert.equal(codecError.code, "unexpected_eof");
      assert.equal(e.message, "decode derivation wire v1 bytes: codec fault: unexpected_eof");
      return true;
    },
  );
});

test("CONTROL: a decoded value of the wrong shape is still a shape refusal (#3111)", () => {
  assert.throws(
    () => decodeDerivationWireV1(encode(atom(new TextEncoder().encode("not-a-wire")))),
    (e: unknown) => e instanceof DecodeError && !(e instanceof DecodeCodecFault),
  );
});
