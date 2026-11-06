/*
 * #2247: a positive literal whose predicate is an account tag byte (0x00 negation, 0x01 count)
 * reads exactly like the tagged literal, so it shares that literal's clause bytes, id and program
 * digest. Every ingress refuses it by name (seat:caa, issuecomment-5812420549). The same
 * witnesses are pinned in contract/rs and contract/go; K6 is pinned in each kernel.
 */

import test from "node:test";
import assert from "node:assert/strict";

import {
  Clause,
  ClauseId,
  Goal,
  loadPrelude,
  MapProgram,
  PreludeError,
  programBytes,
  programToValue,
  ProgramSerdeEncodeError,
  RESERVED_PREDICATE_SYMBOLS,
  reservedPredicateOf,
  Symbol,
  Term,
} from "../src/index.js";

const enc = new TextEncoder();

/** A goal whose predicate is the raw byte `tag`. */
function tagged(tag: number, args: Term[]): Goal {
  return Goal.of(Symbol.of(new Uint8Array([tag])), args);
}

/** K1's B: `p(Y) :- r(Y), <0x00>(q(Y)).`, a positive literal that reads as a negated `q(Y)`. */
function k1B(): Clause {
  const y = Term.var("Y");
  return new Clause(Goal.of("p", [y]), [Goal.of("r", [y]), tagged(0x00, [Term.tuple([Term.atom(enc.encode("q")), y])])]);
}

/** K2's D: `n(N) :- <0x01>(N).`, a positive literal led by the count tag. */
function k2D(): Clause {
  const n = Term.var("N");
  return new Clause(Goal.of("n", [n]), [tagged(0x01, [n])]);
}

test("#2247: both tag bytes are reserved, and the shared check finds them", () => {
  assert.deepEqual(
    RESERVED_PREDICATE_SYMBOLS.map((s) => [...s]),
    [[0x00], [0x01]],
  );
  assert.deepEqual([...(reservedPredicateOf(k1B()) ?? [])], [0x00]);
  assert.deepEqual([...(reservedPredicateOf(k2D()) ?? [])], [0x01]);
  assert.deepEqual([...(reservedPredicateOf(Clause.fact(tagged(0x01, [Term.atom(enc.encode("a"))]))) ?? [])], [0x01]);
  assert.equal(reservedPredicateOf(Clause.fact(Goal.of("p", [Term.atom(enc.encode("a"))]))), undefined);
});

test("#2247: program serde refuses K1 and K2 by name", () => {
  for (const [name, clause] of [
    ["K1", k1B()],
    ["K2", k2D()],
  ] as const) {
    const program = new MapProgram().with("c", clause);
    assert.throws(() => programToValue(program), ProgramSerdeEncodeError, `${name}: programToValue`);
    assert.throws(() => programBytes(program), ProgramSerdeEncodeError, `${name}: programBytes`);
  }
  void ClauseId;
});

test("#2247 K5: the prelude loader refuses a reserved predicate BEFORE the digest check", () => {
  for (const tag of [0x00, 0x01]) {
    const doc = JSON.stringify({
      name: "t",
      version: "0.0.0",
      program_digest: "00".repeat(32),
      clauses: [
        {
          clause: {
            head: { pred: "p", args: [{ var: "Y" }] },
            body: [
              { pred: "r", args: [{ var: "Y" }] },
              { pred: String.fromCharCode(tag), args: [{ var: "Y" }] },
            ],
          },
        },
      ],
    });
    assert.throws(
      () => loadPrelude(doc),
      (e: unknown) => e instanceof PreludeError && e.kind === "bad_clause" && e.index === 0 && e.message.includes("reserved predicate"),
      `tag ${tag}`,
    );
  }
});
