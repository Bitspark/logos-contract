// §10 Program (de)serialization — a clause `MapProgram` ⇄ a ground ontos `Value`, with
// CANONICAL, byte-deterministic `ontos-codec-v1` output (issue #310). TS sibling of
// contract/rs/src/program_serde.rs and contract/go/program_serde.go.
//
// A consumer's whole policy is a `MapProgram` — a `ClauseId → Clause` map. To store,
// transmit, or content-address a WHOLE program (not just a single clause) it must
// become ordinary ground data and back. This is the program-level analogue of the §2a
// quote/reify term reification and the §9 per-clause account codec; it REUSES both, so
// it introduces no new frozen bytes:
//
//   programToValue(p) = Tuple[ Atom(version), entry0, entry1, …, entry_{n-1} ]
//   entry_i           = Tuple[ Atom(<clause-id utf8 bytes>), clauseValue(clause_i) ]
//
// where `clauseValue` is the FROZEN account encoding of a clause's `head :- body`. The
// entries are emitted in CANONICAL ORDER — sorted by the clause-id bytes — so the value
// (and hence its `ontos-codec-v1` bytes) is INDEPENDENT of `MapProgram` insertion order.
// The leading `Atom(version)` domain-separates the shape.
//
// Canonical bytes := `encode(programToValue(p))` — the cross-language byte-pin all three
// bindings reproduce (vectors/program_serde.json). Byte-identical to Rust's
// `program_bytes` and Go's `ProgramBytes`.
//
// THE RESERVED PREDICATE SYMBOL (why serialization is FALLIBLE). The frozen account
// body-literal encoding is NOT injective over arbitrary predicate symbols: a POSITIVE
// literal reads as the bare `goalAsTerm(g) = Tuple[Atom(pred), args…]` and a NEGATED one
// as `Tuple[Atom([NEG_TAG=0x00]), goalAsTerm(g)]`. A positive literal whose predicate
// symbol is exactly the single byte `0x00` AND which has exactly one argument therefore
// encodes to `Tuple[Atom([0x00]), arg]` — byte-identical to a negated reading, so a
// decoder cannot recover the polarity. (`Symbol`/`Goal` accept arbitrary bytes with no
// validation, so such a clause is reachable via the public API.) Because the account
// encoding is FROZEN (its bytes feed `clauseBytes` / `programDigest`, cross-core
// vectored), the sound fix is to RESERVE the byte `0x00` as the body-literal negation
// tag: it is not a valid predicate name in a serializable program. `programToValue` /
// `programBytes` therefore THROW (`ProgramSerdeEncodeError`) on any clause whose head or
// body-literal predicate equals `0x00`. Over the ACCEPTED programs the round-trip law is
// then total.

import { UTF8_STRICT } from "./utf8.js";
import { encode } from "@bitspark/ontos-codec";
import { Atom, Tuple, atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";

import { clauseFromValue, clauseValue } from "./account.js";
import { Clause, ClauseId, MapProgram } from "./program.js";

/**
 * The version/shape tag atom that heads a serialized program (domain separation —
 * distinct from the §2a quote tags and the §9 clause prefix). Frozen v1;
 * byte-identical across {rs,go,ts}.
 */
export const PROGRAM_SERDE_VERSION: Uint8Array = new TextEncoder().encode("logos/program/v1");

/**
 * The single byte the frozen account encoding reserves as the body-literal NEGATION tag
 * (ADR-0007 NEG_TAG). A goal whose predicate symbol equals this byte cannot be serialized
 * unambiguously, so it is NOT a valid predicate name in a serializable program (see the
 * module note). Mirrors Rust's `RESERVED_PREDICATE_SYMBOL` and Go's
 * `ReservedPredicateSymbol`.
 */
export const RESERVED_PREDICATE_SYMBOL: Uint8Array = new Uint8Array([0x00]);

/**
 * Every predicate symbol the account encoding reserves (#2247): the negation tag and the count
 * tag. A positive literal whose predicate is one of these reads exactly like the tagged literal,
 * so it shares that literal's clause bytes, canonical id and program digest, and decodes as it.
 * With both excluded from the predicate domain the reading is injective, so every ingress that
 * makes a caller's clause identity-bearing or executable refuses them through
 * `reservedPredicateOf`. Mirrors Rust's `RESERVED_PREDICATE_SYMBOLS`.
 */
export const RESERVED_PREDICATE_SYMBOLS: readonly Uint8Array[] = [new Uint8Array([0x00]), new Uint8Array([0x01])];

/**
 * The first reserved predicate symbol (see `RESERVED_PREDICATE_SYMBOLS`) the clause carries, on
 * its head or any body literal, the counted predicate of a count literal included; `undefined`
 * when it carries none. The one check every ingress shares (#2247). Mirrors Rust's
 * `reserved_predicate`.
 */
export function reservedPredicateOf(clause: Clause): Uint8Array | undefined {
  const preds = [clause.head.pred.bytes(), ...clause.body.map((lit) => lit.pred().bytes())];
  return preds.find((pred) => RESERVED_PREDICATE_SYMBOLS.some((reserved) => bytesEqual(pred, reserved)));
}

/** Why a `Value` is not a well-formed serialized program (the decode inverse is partial). */
export type ProgramSerdeError =
  | { kind: "not_a_tuple" }
  | { kind: "bad_version" }
  | { kind: "bad_entry" }
  | { kind: "bad_clause" }
  | { kind: "duplicate_clause_id"; id: string };

/** Thrown by `programFromValue` when a value is not a well-formed serialized program. */
export class ProgramSerdeDecodeError extends Error {
  readonly detail: ProgramSerdeError;
  constructor(detail: ProgramSerdeError) {
    super(describe(detail));
    this.detail = detail;
    this.name = "ProgramSerdeDecodeError";
  }
}

/**
 * Thrown by `programToValue` / `programBytes` (the ENCODE direction) when a clause carries
 * a goal (head or body literal) whose predicate symbol equals `RESERVED_PREDICATE_SYMBOL`
 * (the NEG_TAG byte `0x00`), which the frozen account encoding cannot serialize
 * unambiguously. Names the offending clause id + predicate (lowercase hex).
 */
export class ProgramSerdeEncodeError extends Error {
  readonly clauseId: string;
  readonly predicateHex: string;
  constructor(clauseId: string, predicateHex: string) {
    super(
      `clause ${clauseId} carries a reserved predicate symbol 0x${predicateHex} ` +
        `(an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)`,
    );
    this.clauseId = clauseId;
    this.predicateHex = predicateHex;
    this.name = "ProgramSerdeEncodeError";
  }
}

function describe(e: ProgramSerdeError): string {
  switch (e.kind) {
    case "not_a_tuple":
      return "program value is not a Tuple";
    case "bad_version":
      return "program value has a bad/missing version tag";
    case "bad_entry":
      return "program entry is not a Tuple[Atom(id), clause]";
    case "bad_clause":
      return "program entry's clause value is malformed";
    case "duplicate_clause_id":
      return `duplicate clause id in serialized program: ${e.id}`;
  }
}

function bytesEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) if (a[i] !== b[i]) return false;
  return true;
}

/** Lexicographic byte ordering (the total order Rust's slice `Ord` / Go's bytes.Compare uses). */
function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const ai = a[i]!;
    const bi = b[i]!;
    if (ai !== bi) return ai < bi ? -1 : 1;
  }
  return a.length - b.length;
}

function toHex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}

/**
 * Reject a clause that carries the reserved predicate symbol on its head or any body
 * literal — the encode-time guard that keeps the round-trip total (see the module note).
 * Throws `ProgramSerdeEncodeError`; returns normally otherwise.
 */
function checkNoReservedPredicate(id: string, clause: Clause): void {
  const pred = reservedPredicateOf(clause);
  if (pred !== undefined) {
    throw new ProgramSerdeEncodeError(id, toHex(pred));
  }
}

/**
 * Serialize a `MapProgram` to its canonical ground `Value` (§10).
 *
 * FALLIBLE — throws `ProgramSerdeEncodeError` if any clause carries a goal (head or body
 * literal) whose predicate symbol equals `RESERVED_PREDICATE_SYMBOL` (the NEG_TAG byte
 * `0x00`); such a clause cannot be serialized unambiguously under the frozen account
 * encoding (see the module note). For every ACCEPTED program there is exactly one
 * canonical value. The clause entries are emitted SORTED by clause-id bytes (independent
 * of how the program was built). The canonical BYTES are `encode` of this.
 */
export function programToValue(program: MapProgram): Value {
  const enc = new TextEncoder();
  const entries = program.entries().map(([id, clause]) => {
    checkNoReservedPredicate(id, clause);
    return { id: enc.encode(id), value: clauseValue(clause) };
  });
  entries.sort((a, b) => compareBytes(a.id, b.id));
  const children: Value[] = [valueAtom(PROGRAM_SERDE_VERSION)];
  for (const e of entries) {
    children.push(valueTuple([valueAtom(e.id), e.value]));
  }
  return valueTuple(children);
}

/**
 * The canonical bytes of a program: `ontos-codec-v1(programToValue(p))`. FALLIBLE for the
 * same reserved-predicate reason as `programToValue`.
 */
export function programBytes(program: MapProgram): Uint8Array {
  return encode(programToValue(program));
}

/**
 * The partial inverse of `programToValue`: rebuild the `MapProgram` a value denotes, or
 * throw a `ProgramSerdeDecodeError` if `value` is not in the image of `programToValue`
 * (§10). The round-trip law is TOTAL OVER ACCEPTED programs: for any `p` that
 * `programToValue` accepts (i.e. carries no reserved predicate symbol),
 * `programFromValue(programToValue(p))` equals `p`. A program with a reserved predicate
 * symbol is rejected at encode time, so it never produces a value to invert.
 */
export function programFromValue(value: Value): MapProgram {
  if (!(value instanceof Tuple)) throw new ProgramSerdeDecodeError({ kind: "not_a_tuple" });
  const items = value.items();
  if (items.length === 0) throw new ProgramSerdeDecodeError({ kind: "bad_version" });
  const version = items[0]!;
  if (!(version instanceof Atom) || !bytesEqual(version.bytes(), PROGRAM_SERDE_VERSION)) {
    throw new ProgramSerdeDecodeError({ kind: "bad_version" });
  }
  const decoder = UTF8_STRICT;
  const program = new MapProgram();
  for (let i = 1; i < items.length; i += 1) {
    const entry = items[i]!;
    if (!(entry instanceof Tuple)) throw new ProgramSerdeDecodeError({ kind: "bad_entry" });
    const pair = entry.items();
    if (pair.length !== 2) throw new ProgramSerdeDecodeError({ kind: "bad_entry" });
    const idValue = pair[0]!;
    if (!(idValue instanceof Atom)) throw new ProgramSerdeDecodeError({ kind: "bad_entry" });
    // The id was serialized from a `ClauseId`'s UTF-8 handle bytes; reject a non-UTF-8 id.
    let id: string;
    try {
      id = decoder.decode(idValue.bytes());
    } catch {
      throw new ProgramSerdeDecodeError({ kind: "bad_entry" });
    }
    const clause = clauseFromValue(pair[1]!);
    if (clause === undefined) throw new ProgramSerdeDecodeError({ kind: "bad_clause" });
    if (program.clause(ClauseId.of(id)) !== undefined) {
      throw new ProgramSerdeDecodeError({ kind: "duplicate_clause_id", id });
    }
    program.insert(ClauseId.of(id), clause);
  }
  return program;
}
