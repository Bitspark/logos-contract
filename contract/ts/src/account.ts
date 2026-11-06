// §2a/§9 Account codec — the canonical, FROZEN encoding of account artifacts
// (quote byte form · ClauseId canonical hash). TS sibling of
// contract/rs/src/account.rs and contract/go/account.go.
//
// This freezes the quote byte form (§2a) and defines the canonical ClauseId as the
// lowercase-hex SHA-256 of the domain-separated, ontos-codec bytes of a clause
// quote'd into a ground ontos value.
//
// SYNTACTIC (§9 decision, 2026-06-01): variable names are part of the encoding —
// there is no alpha-normalization. p(X):-q(X) and p(Y):-q(Y) are distinct clauses
// with distinct ids. Cross-language: any {rs,ts,go} binding that follows this
// encoding computes the same id for the same clause — pinned for all three by the
// shared vectors/account.json.
//
// SHA-256 is the sync, browser-safe @noble/hashes implementation (the same library
// arche-core's browser checker already bundles), so canonicalClauseId is sync and
// runs in the browser — matching the rs/go bindings (and keeping check() sync).

import { UTF8_LOSSY } from "./utf8.js";
import { encode } from "@bitspark/ontos-codec";
import { type Value } from "@bitspark/ontos-core";
import { encodeInt, readInt } from "@bitspark/ontos-data";
import { sha256 } from "@noble/hashes/sha2.js";

import { Term } from "./term.js";
import { Goal, Symbol } from "./literal.js";
import {
  BodyLit,
  Clause,
  ClauseId,
  type CountFilterEntry,
  CountLit,
  PredicateRef,
  type ProjectSpec,
} from "./program.js";
import { quote, reify } from "./reify.js";

/**
 * Domain separator for a canonical clause hash (so a clause id can never collide
 * with another hash over the same bytes).
 */
export const CLAUSE_PREFIX: Uint8Array = new TextEncoder().encode("logos/account/clause/v1\n");

/**
 * Domain separator for the canonical whole-program digest (ADR 0007 §3.1). Distinct
 * from `CLAUSE_PREFIX` so a program digest can never collide with a single-clause hash
 * over the same bytes. Mirrors Rust's `PROGRAM_PREFIX`.
 */
export const PROGRAM_PREFIX: Uint8Array = new TextEncoder().encode("logos/account/program/v1\n");

/**
 * Tag byte sealing the negated body-literal reading (ADR 0007). A `Neg(g)` reads as
 * `Tuple[Atom(NEG_TAG), goalAsTerm(g)]` — a 2-tuple whose first child is this
 * single-byte atom. A positive `goalAsTerm(g)` is `Tuple[Atom(pred), args…]` whose
 * first child is the PREDICATE atom. The two readings are distinct only because `0x00` is
 * not a valid predicate name: a `Symbol` itself accepts any bytes, so a positive literal with
 * predicate `0x00` WOULD read as a `Neg`. This reading is therefore injective only over
 * clauses without a reserved predicate, and every ingress refuses one (`reservedPredicateOf`:
 * `programToValue`, `loadPrelude`, the kernel's `analyze`; #2247). Mirrors Rust's `NEG_TAG`.
 */
const NEG_TAG = 0x00;

/**
 * Tag byte sealing the count body-literal reading (ADR 0023). A count literal reads as
 * `Tuple[Atom(COUNT_TAG), pred_ref, filter, project, count]` — a 5-tuple whose first child
 * is this single-byte atom, distinct from both a positive reading (first child = the
 * predicate atom, which is never `0x01` because every ingress refuses that predicate, #2247)
 * and the negated reading (first child = `Atom(NEG_TAG=0x00)`).
 * So a body with no count literal encodes byte-identically to the pre-amendment account.
 * Mirrors Rust's `COUNT_TAG`.
 */
const COUNT_TAG = 0x01;

/** The canonical ontos-data int embedding of a small non-negative count as a Term. */
function intTerm(n: number): Term {
  return Term.fromValue(encodeInt(BigInt(n)));
}

/**
 * Inverse of `intTerm`: a canonical int term in the `u32` domain → a number, or `undefined`. Every
 * field it reads (a project attribute, a predicate arity, a filter position) is a `u32` field
 * (logos-contract §3.0), as rs's `u32::try_from` and go's `intTermToUint32` read it. It was bounded by
 * `Number.MAX_SAFE_INTEGER`, so ts read an arity in `(2^32, 2^53)` as a count premise that rs and go
 * do not read as one (#3238).
 */
function intTermToU32(t: Term): number | undefined {
  // An int embedding is Tuple[Atom("int"), Atom(payload)], depth 2, so a deeper term is not
  // one. Reject it before erasing (#2366): erasing a deep term only to reject it walks the
  // whole term, the quadratic trap the rs readers fell into.
  if (!Term.depthLe(t, 2)) return undefined;
  const v = Term.eraseGround(t);
  if (v === undefined) return undefined;
  let n: bigint;
  try {
    n = readInt(v);
  } catch {
    return undefined;
  }
  if (n < 0n || n > 0xffff_ffffn) return undefined;
  return Number(n);
}

/**
 * Account-codec reading of a `ProjectSpec` (ADR 0023 + #587): `rows` ⇒ `Atom("rows")`,
 * `distinct{attr}` ⇒ `Tuple[Atom("distinct"), int(attr)]`, and the `min`/`max`/`sum` folds ⇒
 * `Tuple[Atom("sum"|"min"|"max"), int(attr)]`. The `rows`/`distinct` readings are
 * BYTE-IDENTICAL to the pre-#587 codec (the new tags are additive), so every existing count
 * clause id is unchanged. Mirrors Rust's `project_as_term`.
 */
function projectAsTerm(p: ProjectSpec): Term {
  const attrTag = (tag: string, attr: number): Term =>
    Term.tuple([Term.atom(new TextEncoder().encode(tag)), intTerm(attr)]);
  switch (p.kind) {
    case "rows":
      return Term.atom(new TextEncoder().encode("rows"));
    case "distinct":
      return attrTag("distinct", p.attr);
    case "sum":
      return attrTag("sum", p.attr);
    case "min":
      return attrTag("min", p.attr);
    case "max":
      return attrTag("max", p.attr);
  }
}

/** Inverse of `projectAsTerm`. */
function projectFromTerm(t: Term): ProjectSpec | undefined {
  if (t.kind === "atom") {
    return decoder.decode(t.bytes()) === "rows" ? { kind: "rows" } : undefined;
  }
  if (t.kind !== "tuple") return undefined;
  const children = t.children();
  if (children.length !== 2) return undefined;
  const tag = children[0]!;
  if (tag.kind !== "atom") return undefined;
  const attr = intTermToU32(children[1]!);
  if (attr === undefined) return undefined;
  switch (decoder.decode(tag.bytes())) {
    case "distinct":
      return { kind: "distinct", attr };
    case "sum":
      return { kind: "sum", attr };
    case "min":
      return { kind: "min", attr };
    case "max":
      return { kind: "max", attr };
    default:
      return undefined;
  }
}

/**
 * Account-codec reading of an arity-sensitive `PredicateRef` (ADR 0023, #581): the 2-tuple
 * `Tuple[Atom(pred), int(arity)]`. Pinning the arity makes `obs/3` and `obs/2` distinct
 * counted relations. Mirrors Rust's `predicate_ref_as_term`.
 */
function predicateRefAsTerm(p: PredicateRef): Term {
  return Term.tuple([Term.atom(p.pred.bytes()), intTerm(p.arity)]);
}

/** Inverse of `predicateRefAsTerm`. */
function predicateRefFromTerm(t: Term): PredicateRef | undefined {
  if (t.kind !== "tuple") return undefined;
  const children = t.children();
  if (children.length !== 2) return undefined;
  const predChild = children[0]!;
  if (predChild.kind !== "atom") return undefined;
  const arity = intTermToU32(children[1]!);
  if (arity === undefined) return undefined;
  return new PredicateRef(new Symbol(predChild.bytes()), arity);
}

/**
 * Account-codec reading of a `CountLit` (ADR 0023): the sealed 5-tuple
 * `Tuple[Atom(COUNT_TAG), pred_ref, filter, project, count]`, where `pred_ref` is the
 * arity-sensitive `Tuple[Atom(pred), int(arity)]` (#581), `filter` is
 * `Tuple[ Tuple[int(pos), term], … ]` (caller order preserved). Mirrors Rust's
 * `count_lit_as_term`.
 */
function countLitAsTerm(c: CountLit): Term {
  const filter = Term.tuple(c.filter.map((e) => Term.tuple([intTerm(e.pos), e.term])));
  return Term.tuple([
    Term.atom(new Uint8Array([COUNT_TAG])),
    predicateRefAsTerm(c.pred),
    filter,
    projectAsTerm(c.project),
    c.count,
  ]);
}

/** Inverse of `countLitAsTerm`. `children` is the full 5-tuple's children (incl. the tag). */
function countLitFromTerm(children: readonly Term[]): CountLit | undefined {
  if (children.length !== 5) return undefined;
  const pred = predicateRefFromTerm(children[1]!);
  if (pred === undefined) return undefined;
  const filterTerm = children[2]!;
  if (filterTerm.kind !== "tuple") return undefined;
  const filter: CountFilterEntry[] = [];
  for (const entry of filterTerm.children()) {
    if (entry.kind !== "tuple") return undefined;
    const pair = entry.children();
    if (pair.length !== 2) return undefined;
    const pos = intTermToU32(pair[0]!);
    if (pos === undefined) return undefined;
    filter.push({ pos, term: pair[1]! });
  }
  const project = projectFromTerm(children[3]!);
  if (project === undefined) return undefined;
  return new CountLit(pred, filter, project, children[4]!);
}

/** A shared decoder for the small ASCII tags in the count reading. */
const decoder = UTF8_LOSSY;

/**
 * The labeled-compound reading of a goal `p(a…)` as a `Term`: `Tuple[Atom(p), a…]`
 * (§1.1). A nullary goal `p()` is `Tuple[Atom(p)]` (arity 1) — distinct from the
 * bare atom `p`.
 */
function goalAsTerm(goal: Goal): Term {
  return Term.tuple([Term.atom(goal.pred.bytes()), ...goal.args]);
}

/**
 * The reading of one polarity-tagged body literal (ADR 0007).
 *
 * Byte-compat invariant: a positive literal reads byte-identically to the bare
 * `goalAsTerm(g)` — no wrapper, no tag — so every pre-amendment positive clause id is
 * unchanged. A negated literal reads as the sealed 2-tuple
 * `Tuple[Atom(NEG_TAG), goalAsTerm(g)]`, which is distinct from every positive reading over
 * clauses without a reserved predicate, which every ingress refuses (see `NEG_TAG`, #2247).
 * Mirrors Rust's `body_lit_as_term`.
 */
function bodyLitAsTerm(lit: BodyLit): Term {
  if (lit.isCount()) {
    return countLitAsTerm(lit.countLit!);
  }
  // Non-null: the count arm above covers the only inner-less form.
  const goal = lit.asInner()!;
  if (lit.isNeg()) {
    return Term.tuple([Term.atom(new Uint8Array([NEG_TAG])), goalAsTerm(goal)]);
  }
  return goalAsTerm(goal);
}

/**
 * A clause `head :- b₀,…,bₙ` as a `Term`: `Tuple[ head, Tuple[b₀,…,bₙ] ]` (a 2-tuple
 * of the head reading and the ordered body readings; empty body = `Tuple[head, Tuple[]]`).
 * Each body literal reads via `bodyLitAsTerm`, so an all-positive body is
 * byte-identical to the pre-ADR-0007 encoding.
 */
function clauseAsTerm(clause: Clause): Term {
  return Term.tuple([goalAsTerm(clause.head), Term.tuple(clause.body.map(bodyLitAsTerm))]);
}

/**
 * The canonical ground ontos value of a clause: `quote(clauseAsTerm(clause))`. Total
 * (every clause has one) and injective on distinct clauses.
 */
export function clauseValue(clause: Clause): Value {
  return quote(clauseAsTerm(clause));
}

/**
 * The partial inverse of `clauseValue`: recover the `Clause` whose canonical ground
 * value is `value`, or `undefined` if `value` is not in the image of `clauseValue`.
 * Used by the program (de)serialization (`program_serde.ts`) to read a clause back out
 * of an ontos `Value` without re-deriving its `ClauseId`. Mirrors Rust's
 * `account::clause_from_value` and Go's `ClauseFromValue`.
 *
 * The decode mirrors `clauseAsTerm` exactly: `value` must `reify` to
 * `Tuple[ headTerm, Tuple[ bodyTerm… ] ]`, where `headTerm` is the labeled compound
 * `Tuple[Atom(pred), arg…]` (arity ≥ 1) and each `bodyTerm` is either the bare
 * `goalAsTerm` (positive) or the sealed 2-tuple `Tuple[Atom([NEG_TAG]), goalAsTerm]`
 * (negated). The polarity rule is the producer's: a body term is NEGATED iff it is a
 * 2-tuple whose first child is exactly the single-byte atom `Atom([NEG_TAG])`.
 */
export function clauseFromValue(value: Value): Clause | undefined {
  const term = reify(value);
  if (term === undefined || term.kind !== "tuple") return undefined;
  const parts = term.children();
  if (parts.length !== 2) return undefined;
  const headTerm = parts[0]!;
  const bodyTerm = parts[1]!;
  const head = goalFromTerm(headTerm);
  if (head === undefined) return undefined;
  if (bodyTerm.kind !== "tuple") return undefined;
  const body: BodyLit[] = [];
  for (const lit of bodyTerm.children()) {
    const b = bodyLitFromTerm(lit);
    if (b === undefined) return undefined;
    body.push(b);
  }
  return new Clause(head, body);
}

/**
 * Inverse of `goalAsTerm`: read `Tuple[Atom(pred), arg…]` back into a `Goal`. The first
 * child is the predicate atom; the rest are the argument terms (which may contain
 * `Var`s — this is a clause head/body literal, not a ground one). `undefined` if the
 * term is not a tuple headed by an atom (arity ≥ 1).
 */
function goalFromTerm(term: Term): Goal | undefined {
  if (term.kind !== "tuple") return undefined;
  const children = term.children();
  if (children.length < 1) return undefined;
  const headChild = children[0]!;
  if (headChild.kind !== "atom") return undefined;
  return new Goal(new Symbol(headChild.bytes()), children.slice(1));
}

/**
 * Inverse of `bodyLitAsTerm`: a 2-tuple whose first child is exactly `Atom([NEG_TAG])`
 * is a negated literal over the second child's goal; anything else is read as a
 * positive literal over the whole term's goal.
 */
function bodyLitFromTerm(term: Term): BodyLit | undefined {
  if (term.kind === "tuple") {
    const children = term.children();
    // A negated reading is the 2-tuple [Atom(NEG_TAG), goal].
    if (children.length === 2) {
      const tag = children[0]!;
      if (tag.kind === "atom") {
        const tb = tag.bytes();
        if (tb.length === 1 && tb[0] === NEG_TAG) {
          const g = goalFromTerm(children[1]!);
          return g === undefined ? undefined : BodyLit.neg(g);
        }
      }
    }
    // A count reading (ADR 0023) is the 5-tuple led by Atom(COUNT_TAG).
    if (children.length >= 1) {
      const tag = children[0]!;
      if (tag.kind === "atom") {
        const tb = tag.bytes();
        if (tb.length === 1 && tb[0] === COUNT_TAG) {
          const c = countLitFromTerm(children);
          return c === undefined ? undefined : BodyLit.count(c);
        }
      }
    }
  }
  const g = goalFromTerm(term);
  return g === undefined ? undefined : BodyLit.pos(g);
}

/** The canonical, frozen bytes of a clause: `ontos-codec(quote(clause))`. */
export function clauseBytes(clause: Clause): Uint8Array {
  return encode(clauseValue(clause));
}

/**
 * The canonical `ClauseId` of a clause — lowercase-hex
 * `SHA-256(CLAUSE_PREFIX ‖ ontos-codec(quote(clause)))` (§9, syntactic).
 *
 * Stable and cross-language: any binding that follows this encoding computes the
 * same id for the same clause. The id satisfies the v1 `ClauseId` contract (stable +
 * lookup-able) and is additionally a canonical hash. Sync + browser-safe; mirrors
 * Rust's `ClauseId::canonical` and Go's `CanonicalClauseId`.
 */
export function canonicalClauseId(clause: Clause): ClauseId {
  const body = clauseBytes(clause);
  const input = new Uint8Array(CLAUSE_PREFIX.length + body.length);
  input.set(CLAUSE_PREFIX, 0);
  input.set(body, CLAUSE_PREFIX.length);
  return ClauseId.of(toHex(sha256(input)));
}

/**
 * The canonical whole-program digest (ADR 0007 §3.1): the 32-byte
 * `SHA-256(PROGRAM_PREFIX ‖ ⨁ len-prefixed SORTED clauseBytes)` over the program's
 * COMPLETE clause set. The per-clause frozen account bytes are SORTED (lexicographic
 * byte order — the same total order Rust's `Vec<Vec<u8>>::sort` uses), so the digest is
 * independent of clause enumeration order and commits to the WHOLE clause set: a dropped
 * or added clause changes the digest. Each clause's bytes are length-prefixed with its
 * length as an 8-byte big-endian u64, so the concatenation is unambiguous.
 *
 * Byte-identical to Rust's `program_digest` (contract/rs/src/check.rs) and Go's
 * `ProgramDigest` — the frozen ontos-codec + syntactic `VarId` pin the same 32 bytes
 * across {rs,go,ts} for the same clause set (the prelude trust anchor). A prelude loader
 * recomputes and verifies the manifest's pinned `program_digest` against this.
 */
export function programDigest(clauses: readonly Clause[]): Uint8Array {
  const byteVecs = clauses.map(clauseBytes);
  byteVecs.sort(compareBytes);
  let total = PROGRAM_PREFIX.length;
  for (const b of byteVecs) total += 8 + b.length;
  const input = new Uint8Array(total);
  let off = 0;
  input.set(PROGRAM_PREFIX, off);
  off += PROGRAM_PREFIX.length;
  const view = new DataView(input.buffer);
  for (const b of byteVecs) {
    // Length-prefix each clause's bytes with an 8-byte big-endian u64.
    view.setBigUint64(off, BigInt(b.length), false);
    off += 8;
    input.set(b, off);
    off += b.length;
  }
  return sha256(input);
}

/** The canonical `program_digest` (lowercase hex) of a clause set — the value a manifest pins. */
export function bundleDigest(clauses: readonly Clause[]): string {
  return toHex(programDigest(clauses));
}

/**
 * Lexicographic byte ordering on two `Uint8Array`s (the total order Rust's slice `Ord`
 * uses), so the program digest is independent of clause enumeration order.
 */
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
  for (const b of bytes) {
    out += b.toString(16).padStart(2, "0");
  }
  return out;
}
