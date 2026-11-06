import test from "node:test";
import assert from "node:assert/strict";

import { atom, tuple } from "@bitspark/ontos-core";
import type { Value } from "@bitspark/ontos-core";

import {
  DecodeError,
  GroundLiteral,
  Symbol,
  Term,
  groundLiteralAsValue,
  groundLiteralFromValueV1,
  quote,
} from "../src/index.js";

// #1914 — the public strict inverse of the ground-literal account representation, exercised
// ONLY through the exported surface: no derivation is fabricated, no private decoder copied.

const bytes = (s: string): Uint8Array => new TextEncoder().encode(s);
const lit = (pred: string, args: readonly Value[]): GroundLiteral =>
  new GroundLiteral(new Symbol(bytes(pred)), args);

function roundTrip(l: GroundLiteral): void {
  const v = groundLiteralAsValue(l);
  const back = groundLiteralFromValueV1(v);
  assert.deepEqual(groundLiteralAsValue(back), v, "re-encoding is byte-stable");
  assert.deepEqual(back.pred.bytes(), l.pred.bytes());
  assert.equal(back.args.length, l.args.length);
}

test("ground literal decode: positive cases round-trip", () => {
  roundTrip(lit("p", []));
  roundTrip(new GroundLiteral(new Symbol(new Uint8Array([112, 0, 255])), [atom(bytes("a"))]));
  roundTrip(lit("q", [atom(new Uint8Array()), atom(new Uint8Array([0, 255, 7]))]));
  roundTrip(lit("nested", [tuple([atom(bytes("a")), tuple([atom(bytes("b")), tuple([])])])]));
});

test("ground literal decode: data that looks like a variable is preserved", () => {
  roundTrip(lit("looks", [atom(bytes("X")), atom(bytes("_"))]));
});

test("ground literal decode: refusals name the class", () => {
  // #2630: the one decoder's refusal text, byte-identical to rs's (its path, then its class).
  const refuse = (name: string, v: Value, want: string) => {
    assert.throws(
      () => groundLiteralFromValueV1(v),
      (e: unknown) => e instanceof DecodeError && e.message === want,
      name,
    );
  };
  refuse("missing predicate", tuple([]), "decode ground literal: expected arity 1, got 0");
  refuse("non-atom predicate", tuple([tuple([])]), "decode ground literal: expected a different value shape");
  // the RAW Ontos compound reading: an unquoted argument is outside the image of quote
  refuse(
    "unquoted argument",
    tuple([atom(bytes("p")), atom(bytes("a"))]),
    "decode ground literal: value is not a quoted ground term",
  );
  refuse(
    "quoted variable",
    tuple([atom(bytes("p")), quote(Term.var("X"))]),
    "decode ground literal: value is not a quoted ground term",
  );
  refuse(
    "nested variable",
    tuple([atom(bytes("p")), quote(Term.tuple([Term.atom(bytes("a")), Term.var("Y")]))]),
    "decode ground literal: value is not a quoted ground term",
  );
  refuse("not a tuple", atom(bytes("p")), "decode ground literal: expected a different value shape");
});
