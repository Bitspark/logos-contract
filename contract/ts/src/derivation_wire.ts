// §5.2 Canonical wire encoding — asValue + the digest helpers. [UNFROZEN v1]
// TS sibling of kernel/rs/src/seam/wire.rs.
//
// Every serializable negotiation type reads as a total, injective ontos `Value`
// (Atom | Tuple), exactly as the account codec reads a clause (clauseValue). The
// codec then produces the frozen ontos-codec bytes, and a domain-separated SHA-256
// yields the digest — mirroring ClauseId.canonical.
//
// ONTOS-NATIVE scalars. This seam NEVER hand-rolls a scalar byte form. Integers and
// booleans go through the FROZEN ontos-data embeddings (encodeInt / encodeBool), so
// the rs/go/ts wire forms are identical BY CONSTRUCTION — there is no per-language
// scalar drift to keep in sync. (This is the fix vs. the salvaged contract/ts
// negotiate/wire.ts, which hand-rolled an 8-byte-BE int atom and Atom("true")/
// Atom("false") bools — those bytes do NOT match the Rust kernel.) FIRM sub-values
// (Subst / Derivation / Term / Literal) reuse the account's canonical quote/account
// readings; identifiers (Symbol / ComponentId / EngineId / version strings) stay
// bare Atom(bytes) — they are *names*, not human text, and bare-Atom is exactly the
// account's Symbol encoding (§0.3.6).
//
// The determinism rules (§0.3) realized here:
//   1. Fixed field order — a struct reads as Tuple[field0, …] in declaration order.
//   2. Enums as tagged tuples — a variant reads Tuple[Atom(tag), payload…] (tagged);
//      a fieldless string-enum reads as the bare Atom(tag) (tagAtom).
//   3. Maps/sets sort before encoding — sortedMap/sortedSet sort by the codec bytes
//      of the key/member, reproducing BTreeMap/BTreeSet order.
//   4. Options — None → Tuple[Atom("none")]; Some(x) → Tuple[Atom("some"), asValue(x)].
//   5. Integers — the FROZEN ontos-data `int` embedding (encodeInt); never a bare
//      hand-rolled big-endian atom, never decimal.
//   6. Booleans — the FROZEN ontos-data `bool` embedding (encodeBool).
//   7. Identifiers/digests — bare Atom(bytes) (bytesAtom / digestAtom).
//   8. Reused FIRM sub-values read via the frozen account/quote readings.

import { decodeUtf8Lossy, decodeUtf8 } from "./utf8.js";
import { portableClauseIdBytes } from "./clause_id_encoding.js";
import { Atom, Tuple, atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { encode, decode, DecodeError as CodecDecodeError } from "@bitspark/ontos-codec";
import { encodeBool, readInt } from "@bitspark/ontos-data";
import { sha256 } from "@noble/hashes/sha2.js";
import { ClauseId, PredicateRef, ProjectSpec, type Clause } from "./program.js";
import {
  type CertSizeDecl,
  ClosedModelCert,
  parseHashHex,
  FiniteDomain,
  RelationTable,
  StratumPrefix,
  SupportEdge,
  SupportRef,
} from "./cert.js";
import { GroundLiteral, Symbol } from "./literal.js";
import {
  BuiltinNode,
  CountPremise,
  Derivation,
  Evidence,
  LeafNode,
  NegPremise,
  type Node,
  NodeMeta,
  type Premise,
  RuleNode,
  isCountPremise,
  isNegPremise,
  type GroundFilterEntry,
} from "./derivation.js";
import {
  Term,
  Subst,
  VarId,
} from "./term.js";
import { quote, reify } from "./reify.js";
import { buildValue, measureLen, writeClosedModelCert, writeGroundLiteral, writeSubst } from "./wire_sink.js";
import { digestAtom, intAtom } from "./atoms.js";
import { clauseValue } from "./account.js";

const enc = new TextEncoder();

/** A negotiation type that has a total, injective ontos-value reading (§0.3). */
export interface AsValue {
  asValue(): Value;
}

// ----------------------------- scalar readings ------------------------------

/**
 * A byte string as a bare `Atom` (§0.3.7) — the reading for an *identifier*: a
 * Symbol, ComponentId, EngineId, or version string. Identifiers are names, not
 * human text, so they are NOT the ontos-data `utf8-text` embedding; bare Atom(bytes)
 * is exactly the account's Symbol encoding.
 */
export function bytesAtom(bytes: Uint8Array): Value {
  return valueAtom(bytes);
}

/** A UTF-8 string as a bare byte `Atom` (a diagnostic note / reason string). */
export function strAtom(s: string): Value {
  return valueAtom(enc.encode(s));
}

// `intAtom` and `digestAtom` live in the leaf `atoms.ts` (#2625 (b)) so `wire_sink.ts` can use them
// without importing this module, which imports its builders from `wire_sink.ts`. Re-exported here, so
// their public names do not move.
export { digestAtom, intAtom };

/**
 * A `bool` as the FROZEN ontos-data `bool` embedding (§0.3.6):
 * `Tuple[Atom("bool"), Atom(0x00 | 0x01)]`. Distinct from the `int` embedding by its
 * label, so it never collides with an integer reading.
 */
export function boolAtom(b: boolean): Value {
  return encodeBool(b);
}

// --------------------------- tagged-enum readings ---------------------------

/** A fieldless string-enum variant: the bare `Atom(tag)` (§0.3.2). */
export function tagAtom(tag: string): Value {
  return valueAtom(enc.encode(tag));
}

/** A tagged variant `Tuple[Atom(tag), payload…]` (§0.3.2). */
export function tagged(tag: string, ...payload: Value[]): Value {
  return valueTuple([tagAtom(tag), ...payload]);
}

// ------------------------------- composites ---------------------------------

/**
 * A fixed-order product: `Tuple[fields…]` (§0.3.1). The caller passes fields in the
 * spec's declaration order.
 */
export function record(fields: readonly Value[]): Value {
  return valueTuple(Array.from(fields));
}

/**
 * An ordered list (order is identity-bearing — NOT sorted), e.g. the theories list
 * or a fallback chain (§5.2).
 */
export function list<T extends AsValue>(items: readonly T[]): Value {
  return valueTuple(items.map((x) => x.asValue()));
}

/**
 * An `Option<T>` (§0.3.4): undefined → Tuple[Atom("none")]; x → Tuple[Atom("some"),
 * as(x)].
 */
export function opt<T>(o: T | undefined, as: (x: T) => Value): Value {
  return o === undefined ? tagged("none") : tagged("some", as(o));
}

/** An `Option<number>` — `opt` specialized to the integer reading. */
export function optInt(o: number | undefined): Value {
  return o === undefined ? tagged("none") : tagged("some", intAtom(o));
}

/** An `Option<string>` — `opt` specialized to the byte-atom reading. */
export function optStr(o: string | undefined): Value {
  return o === undefined ? tagged("none") : tagged("some", strAtom(o));
}

/** Lexicographic byte ordering `a < b` (mirrors Rust slice Ord). */
function bytesLess(a: Uint8Array, b: Uint8Array): boolean {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const x = a[i]!;
    const y = b[i]!;
    if (x !== y) return x < y;
  }
  return a.length < b.length;
}

/** Compare two `Value`s by their codec bytes (§0.3.3 sort key). */
function codecCmp(a: Value, b: Value): number {
  const ea = encode(a);
  const eb = encode(b);
  if (bytesLess(ea, eb)) return -1;
  if (bytesLess(eb, ea)) return 1;
  return 0;
}

/**
 * A set of values sorted by codec bytes (§0.3.3). Go/TS reproduce the order a Rust
 * BTreeSet already iterates in.
 */
export function sortedSet(members: readonly Value[]): Value {
  const items = Array.from(members);
  items.sort(codecCmp);
  return valueTuple(items);
}

/**
 * A map sorted by the codec bytes of its key (§0.3.3): `Tuple[ Tuple[k0,v0], … ]`.
 */
export function sortedMap(entries: readonly (readonly [Value, Value])[]): Value {
  const pairs = entries.map(([k, v]) => ({ k, v }));
  pairs.sort((p, q) => codecCmp(p.k, q.k));
  return valueTuple(pairs.map((p) => valueTuple([p.k, p.v])));
}

// ----------------------- reused FIRM sub-value readings ---------------------

/** A predicate `Symbol` as a bare `Atom(bytes)` (the account reading). */
export function symbolAsValue(sym: Symbol): Value {
  return bytesAtom(sym.bytes());
}

/**
 * A `Subst` (keyed by `VarId`) as `Tuple` of `Tuple[Atom(var_id), quote(term)]`
 * sorted by var-id bytes — matching the rs `BTreeMap` order (§5.2). Terms reuse the
 * FROZEN quote reading; no second encoding.
 */
export function substAsValue(subst: Subst): Value {
  // #2605: the shape is written once, in wire_sink.ts, and read here as a value. Its sort is
  // sortedMap's: codec(key) order.
  return buildValue((s) => writeSubst(s, subst));
}

/**
 * A ground literal `p(a…)` as `Tuple[Atom(p), quote(a)…]` — the labeled-compound
 * reading the account codec uses (goalAsTerm), threaded through the FROZEN quote.
 * Reused by derivationAsValue; never a second encoding.
 */
export function groundLiteralAsValue(lit: GroundLiteral): Value {
  // #2605: the shape is written once, in wire_sink.ts, and read here as a value.
  return buildValue((s) => writeGroundLiteral(s, lit));
}

function nodeMetaAsValue(meta: NodeMeta): Value {
  const v = meta.value();
  return v === undefined ? tagged("none") : tagged("some", v);
}

function evidenceAsValue(evidence: Evidence): Value {
  const v = evidence.value();
  return v === undefined ? tagged("none") : tagged("some", v);
}

/**
 * A `Premise` as a value (ADR 0007). A positive premise reads as the BARE `intAtom`
 * node index — byte-identical to the pre-ADR-0007 wire (so a positive derivation's
 * bytes are unchanged). A negated premise reads as a tagged tuple `Tuple[Atom("neg"),
 * atom, Atom(cert)]`. Mirrors the Rust kernel seam's `premise_as_value`.
 */
function premiseAsValue(premise: Premise): Value {
  if (isNegPremise(premise)) {
    return tagged("neg", groundLiteralAsValue(premise.atom), intAtom(premise.cert));
  }
  if (isCountPremise(premise)) {
    // ADR 0023: a certifiable count premise reads as a tagged tuple carrying the
    // arity-sensitive counted predicate (Tuple[Atom(pred), int(arity)], #581), the
    // (pos,value) filter, the projection, the claimed count `k`, and the cert index.
    // Engines do not emit `Count` yet (Phase 3); this keeps the wire total over the
    // additive `Premise` sum. Mirrors the Rust kernel seam's `premise_as_value`.
    return tagged(
      "count",
      valueTuple([symbolAsValue(premise.pred.pred), intAtom(premise.pred.arity)]),
      valueTuple(premise.filter.map((e) => valueTuple([intAtom(e.pos), e.value]))),
      projectSpecAsValue(premise.project),
      premise.k,
      intAtom(premise.cert),
    );
  }
  return intAtom(premise);
}

/**
 * A [`ProjectSpec`] as a value (ADR 0023 + #587): `rows` ⇒ `Atom("rows")`,
 * `distinct{attr}` ⇒ `Tuple[Atom("distinct"), int(attr)]`, and the `min`/`max`/`sum`
 * folds ⇒ `Tuple[Atom("sum"|"min"|"max"), int(attr)]`. Mirrors the Rust kernel seam's
 * `project_spec_as_value` (the same tags the account codec uses, so the candidate digest
 * commits to the fold kind).
 */
function projectSpecAsValue(project: ProjectSpec): Value {
  if (project.kind === "rows") return bytesAtom(enc.encode("rows"));
  // distinct / sum / min / max all carry an attr — tag by the fold kind.
  return tagged(project.kind, intAtom(project.attr));
}

function nodeAsValue(node: Node): Value {
  switch (node.kind) {
    case "rule":
      return tagged(
        "rule",
        groundLiteralAsValue(node.conclusion),
        bytesAtom(portableClauseIdBytes(node.clause.asStr())),
        substAsValue(node.subst),
        valueTuple(node.premises.map(premiseAsValue)),
        nodeMetaAsValue(node.meta),
      );
    case "builtin":
      return tagged("builtin", groundLiteralAsValue(node.conclusion));
    case "leaf":
      return tagged("leaf", groundLiteralAsValue(node.conclusion), evidenceAsValue(node.evidence));
  }
}

/**
 * A `Derivation` as `Tuple[ Tuple[node0, …], Atom(root) ]` — the nodes read via the
 * FIRM account/quote readings of conclusions/substs (§5.2). The node ordering is the
 * derivation's own (a DAG order is identity-bearing); it is NOT sorted.
 */
export function derivationAsValue(deriv: Derivation): Value {
  // closedWorld is a TRAILING-OPTIONAL 3rd element (ADR 0007 / ADR 0023): appended ONLY when
  // non-empty, so an all-positive derivation encodes the EXACT same Tuple[nodes, root] bytes as
  // before — byte-compat for every existing positive derivation is preserved.
  const fields: Value[] = [valueTuple(deriv.nodes.map(nodeAsValue)), intAtom(deriv.root)];
  if (deriv.closedWorld.length > 0) {
    fields.push(valueTuple(deriv.closedWorld.map(closedModelCertAsValue)));
  }
  return valueTuple(fields);
}

/**
 * A `ClosedModelCert` (ADR 0007 / ADR 0023) as a value — the sealed finite-model certificate
 * a Neg/Count premise discharges against, carried in derivationAsValue's trailing closedWorld
 * slot so a certified candidate round-trips across the seam. Mirrors the rs/go kernel seam's
 * closed_model_cert_as_value. (The closure witness is an empty v1 marker carrying no bytes.)
 */
export function closedModelCertAsValue(cert: ClosedModelCert): Value {
  // #2605: the shape is written once, in wire_sink.ts, and read here as a value.
  return buildValue((s) => writeClosedModelCert(s, cert, cert.limitsDecl));
}

/**
 * The byte charge a producer declares and the checker measures, with certBytes zeroed.
 * For a portable certificate this equals the exact canonical encoded length. A native-only
 * handle charges three bytes per unpaired surrogate. The length reading emits no proof.
 */
export function certEncodedBytes(cert: ClosedModelCert): number {
  // #2605: measured through the length reading of the one wire shape, so no value tree and no
  // encoded buffer is built (the rs twin was 41% of a certified-set run's peak heap, #2602).
  return measureLen((s) => writeClosedModelCert(s, cert, { ...cert.limitsDecl, certBytes: 0 }));
}

/** A structural decode failure — the analogue of Go's `error` return / rs `DecodeError`. */
export class DecodeError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DecodeError";
  }
}

/**
 * `decodeDerivationWireV1`'s codec stopped on the caller's own bytes: the codec's error, unfolded in
 * `codecError` (checker SPI v2, ADR 0036 D8 change 4; #2734 3c, seat:caa's ruling C), rs's
 * `DecodeError::CodecFault` and go's `DecodeCodecFault`. It is a FAULT, never a shape refusal: that
 * decoder reads bytes its caller produced and trusts, so a codec that cannot read them is the
 * caller's defect. Bytes from anyone else go through `decodeDerivationWireV1Bounded`, whose
 * `decode_stopped` kind carries the same error as an ordinary refusal. The message names the
 * codec's portable `code`; its own message stays in `codecError`, because the cores' codecs word it
 * differently. Test for it with `instanceof DecodeCodecFault` before reading a `DecodeError` as a
 * refusal.
 */
export class DecodeCodecFault extends DecodeError {
  readonly ctx: string;
  readonly codecError: unknown;
  constructor(ctx: string, codecError: unknown) {
    const code = codecError instanceof CodecDecodeError ? String(codecError.code) : "not_a_codec_error";
    super(`decode ${ctx}: codec fault: ${code}`);
    this.name = "DecodeCodecFault";
    this.ctx = ctx;
    this.codecError = codecError;
  }
}

// ------------------------- the one rendering per class ----------------------
//
// #2630 (`seat:caa`'s ruling): this is the ONE derivation/certificate decoder, a line-for-line
// port of rs's (contract/rs/src/derivation_wire.rs): the same readers, the same check order, the
// same path at every refusal, and each refusal class rendered byte-identical to rs's
// `DecodeError` Display, `decode <path>: <defect>`. `vectors/derivation_wire.json`'s `refusal`
// rows pin it in all three cores.

/**
 * The ONE rendering of an arity refusal, rs's `arity_refusal`: a reading that takes one arity keeps
 * `decode <ctx>: expected arity N, got M`; a reading with trailing-optional slots names every
 * arity it takes, `decode <ctx>: M elements, expected 10, 11 or 12`.
 */
export function arityRefusal(ctx: string, accepted: readonly number[], got: number): string {
  if (accepted.length === 0) return `decode ${ctx}: ${got} elements, and no arity is accepted`;
  if (accepted.length === 1) return `decode ${ctx}: expected arity ${accepted[0]}, got ${got}`;
  const last = accepted[accepted.length - 1];
  return `decode ${ctx}: ${got} elements, expected ${accepted.slice(0, -1).join(", ")} or ${last}`;
}

/**
 * The ONE rendering of an unknown tag in a refusal text (#2682, seat:caa's ruling B): a
 * double-quoted string in which each ASCII byte renders exactly as rs's `{:?}` renders that
 * character (\" \\ \t \r \n \0, another control as \u{hex}, a printable byte as itself), and each
 * byte >= 0x80 renders as \x{hh}. Nothing is UTF-8-decoded, so it is identical in rs, go and ts
 * by construction.
 */
export function renderTag(bytes: Uint8Array): string {
  let out = '"';
  for (const b of bytes) {
    if (b === 0x22) out += '\\"';
    else if (b === 0x5c) out += "\\\\";
    else if (b === 0x09) out += "\\t";
    else if (b === 0x0d) out += "\\r";
    else if (b === 0x0a) out += "\\n";
    else if (b === 0) out += "\\0";
    else if (b >= 0x20 && b <= 0x7e) out += String.fromCharCode(b);
    else if (b < 0x80) out += `\\u{${b.toString(16)}}`;
    else out += `\\x{${b.toString(16).padStart(2, "0")}}`;
  }
  return out + '"';
}

const refuse = {
  shape: (ctx: string) => new DecodeError(`decode ${ctx}: expected a different value shape`),
  arity: (ctx: string, accepted: readonly number[], got: number) => new DecodeError(arityRefusal(ctx, accepted, got)),
  unknownTag: (ctx: string, tag: Uint8Array) => new DecodeError(`decode ${ctx}: unknown tag ${renderTag(tag)}`),
  notQuoted: (ctx: string) => new DecodeError(`decode ${ctx}: value is not a quoted ground term`),
  badInt: (ctx: string) => new DecodeError(`decode ${ctx}: not a canonical int embedding`),
  badUtf8: (ctx: string) => new DecodeError(`decode ${ctx}: not valid UTF-8`),
  notCanonical: (ctx: string) => new DecodeError(`decode ${ctx}: not in canonical sorted+deduped order`),
};

// There is no depth class here, in any core (#2731, `seat:caa`'s ruling). The decoder imposes no
// depth POLICY: check's max_term_depth (default 256, identical tri-core) is the one depth refusal,
// so a derivation within it decodes everywhere (derivation_wire.json's ground_arg_256/257 rows).
// rs refused a quoted term past 256 VALUE levels here until #2731; its readers no longer recurse.
// A core's CAPACITY is separate and declared: ts builds far deeper safely
// (TS_VALUE_STACK_DEPTH_LIMIT), and its host refuses past its own measured bound as
// reply_decode_limit (#2366, #2456).

// ------------------------------- small helpers ------------------------------

function items(v: Value, ctx: string): readonly Value[] {
  if (!(v instanceof Tuple)) throw refuse.shape(ctx);
  return v.items();
}

function itemsN(v: Value, ctx: string, accepted: readonly number[]): readonly Value[] {
  const its = items(v, ctx);
  if (!accepted.includes(its.length)) throw refuse.arity(ctx, accepted, its.length);
  return its;
}

function atomBytes(v: Value, ctx: string): Uint8Array {
  if (!(v instanceof Atom)) throw refuse.shape(ctx);
  return v.bytes();
}

function splitTag(v: Value, ctx: string): [Uint8Array, readonly Value[]] {
  const its = items(v, ctx);
  if (its.length === 0) throw refuse.arity(ctx, [1], 0);
  return [atomBytes(its[0]!, ctx), its.slice(1)];
}

function tagText(tag: Uint8Array): string {
  return decodeUtf8Lossy(tag);
}

/**
 * The contract's bound on every index and count field: a root, a premise or certificate index, a
 * limits_decl field (#2682, seat:caa's ruling A). 2^53 - 1, so every core holds every in-domain
 * value exactly, and above it every core refuses BadInt the same way. A ts number holds all of it,
 * so ts has no platform arm (rs and go refuse past their build's width by name).
 */
export const INDEX_MAX = 2n ** 53n - 1n;

/** Read an index or count field into 0..=INDEX_MAX, else BadInt. */
function readUsize(v: Value, ctx: string): number {
  let n: bigint;
  try {
    n = readInt(v);
  } catch {
    throw refuse.badInt(ctx);
  }
  if (n < 0n || n > INDEX_MAX) throw refuse.badInt(ctx);
  return Number(n);
}

/**
 * Read an int field the account types as u32 (an arity, a position, an attribute, a stratum level,
 * a rank). A value past 2^32 - 1 is refused as BadInt, as rs and go refuse it; rs/go formerly
 * TRUNCATED it while ts kept the full number, so one input decoded to two values (#2682).
 */
function readU32(v: Value, ctx: string): number {
  let n: bigint;
  try {
    n = readInt(v);
  } catch {
    throw refuse.badInt(ctx);
  }
  if (n < 0n || n > 0xffffffffn) throw refuse.badInt(ctx);
  return Number(n);
}

function readOpt(v: Value, ctx: string): Value | undefined {
  const [tag, payload] = splitTag(v, ctx);
  switch (tagText(tag)) {
    case "none":
      if (payload.length !== 0) throw refuse.arity(ctx, [1], payload.length + 1);
      return undefined;
    case "some":
      if (payload.length !== 1) throw refuse.arity(ctx, [2], payload.length + 1);
      return payload[0]!;
    default:
      throw refuse.unknownTag(ctx, tag);
  }
}

function strictText(bytes: Uint8Array, ctx: string): string {
  try {
    return decodeUtf8(bytes);
  } catch {
    throw refuse.badUtf8(ctx);
  }
}

function groundArgFromQuoted(v: Value, ctx: string): Value {
  const term = reify(v);
  if (term === undefined) throw refuse.notQuoted(ctx);
  const ground = Term.eraseGround(term);
  if (ground === undefined) throw refuse.notQuoted(ctx);
  return ground;
}

/** Assert a tagged payload's arity; `accepted` counts the tag, as a reader sees on the wire. */
function expectN(payload: readonly Value[], accepted: readonly number[], ctx: string): readonly Value[] {
  if (!accepted.includes(payload.length + 1)) throw refuse.arity(ctx, accepted, payload.length + 1);
  return payload;
}

function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) if (a[i] !== b[i]) return a[i]! - b[i]!;
  return a.length - b.length;
}

// ------------------------------ term / literal ------------------------------

/**
 * The public strict inverse of groundLiteralAsValue (#1914): decode ONE standalone ground literal
 * from its account representation Tuple[Atom(pred), quote(arg)…]. It refuses a missing or non-atom
 * predicate, an argument outside the image of quote, and a quoted variable or any non-ground
 * argument. An unquoted compound is refused, by design. There is no decode depth bound here, unlike
 * rs's (#2658's retracted ruling 3): ts builds deep terms safely.
 */
export function groundLiteralFromValueV1(v: Value): GroundLiteral {
  return groundLiteralFromValue(v, "ground literal");
}

function groundLiteralFromValue(v: Value, ctx: string): GroundLiteral {
  const its = items(v, ctx);
  if (its.length === 0) throw refuse.arity(ctx, [1], 0);
  const pred = new Symbol(atomBytes(its[0]!, ctx));
  const args = its.slice(1).map((arg) => groundArgFromQuoted(arg, ctx));
  return new GroundLiteral(pred, args);
}

// ---------------------------------- subst -----------------------------------

/**
 * The inverse of substAsValue: Tuple[ Tuple[Atom(var_id), quote(term)], … ] back to a Subst. The
 * entries must arrive strictly increasing in the codec bytes of their key, as the encoder writes
 * them (#2630): a repeated or misordered var-id is refused by name. Terms go through reify, the
 * frozen inverse of quote, and may contain holes. Each key is built by the `VarId` constructor
 * (#3288), from text `strictText` has already decoded as UTF-8, so the constructor's test cannot fail.
 */
export function substFromValue(v: Value): Subst {
  const entries = items(v, "subst");
  const out = new Subst();
  let previousKey: Uint8Array | undefined;
  for (const entry of entries) {
    const pair = itemsN(entry, "subst.entry", [2]);
    const name = strictText(atomBytes(pair[0]!, "subst.var"), "subst.var");
    const key = encode(pair[0]!);
    if (previousKey !== undefined && compareBytes(previousKey, key) >= 0) throw refuse.notCanonical("subst");
    previousKey = key;
    const term = reify(pair[1]!);
    if (term === undefined) throw refuse.notQuoted("subst.term");
    out.set(new VarId(name), term);
  }
  return out;
}

// -------------------------------- derivation --------------------------------

function nodeMetaFromValue(v: Value): NodeMeta {
  const inner = readOpt(v, "node.meta");
  return inner === undefined ? NodeMeta.none() : NodeMeta.of(inner);
}

function evidenceFromValue(v: Value): Evidence {
  const inner = readOpt(v, "node.evidence");
  return inner === undefined ? Evidence.none() : Evidence.of(inner);
}

function nodeFromValue(v: Value): Node {
  const [tag, payload] = splitTag(v, "node");
  switch (tagText(tag)) {
    case "rule": {
      if (payload.length !== 5) throw refuse.arity("node.rule", [6], payload.length + 1);
      const conclusion = groundLiteralFromValue(payload[0]!, "node.rule.conclusion");
      const clause = ClauseId.of(strictText(atomBytes(payload[1]!, "node.rule.clause"), "node.rule.clause"));
      const subst = substFromValue(payload[2]!);
      const premises = items(payload[3]!, "node.rule.premises").map((p) => premiseFromValue(p));
      const meta = nodeMetaFromValue(payload[4]!);
      return new RuleNode(conclusion, clause, subst, premises, meta);
    }
    case "builtin": {
      if (payload.length !== 1) throw refuse.arity("node.builtin", [2], payload.length + 1);
      return new BuiltinNode(groundLiteralFromValue(payload[0]!, "node.builtin.conclusion"));
    }
    case "leaf": {
      if (payload.length !== 2) throw refuse.arity("node.leaf", [3], payload.length + 1);
      const conclusion = groundLiteralFromValue(payload[0]!, "node.leaf.conclusion");
      return new LeafNode(conclusion, evidenceFromValue(payload[1]!));
    }
    default:
      throw refuse.unknownTag("node", tag);
  }
}

/**
 * A bare int is a positive premise (node index), read FIRST as rs does; a
 * Tuple[Atom("neg"|"count"), …] is a Neg (ADR 0007) or Count (ADR 0023) premise.
 */
function premiseFromValue(p: Value): Premise {
  try {
    return readUsize(p, "node.rule.premise");
  } catch {
    // not an index: the tagged forms below
  }
  const [tag, payload] = splitTag(p, "node.rule.premise");
  switch (tagText(tag)) {
    case "neg": {
      if (payload.length !== 2) throw refuse.arity("node.rule.premise.neg", [3], payload.length + 1);
      const atom = groundLiteralFromValue(payload[0]!, "node.rule.premise.neg.atom");
      const cert = readUsize(payload[1]!, "node.rule.premise.neg.cert");
      return new NegPremise(atom, cert);
    }
    case "count": {
      if (payload.length !== 5) throw refuse.arity("node.rule.premise.count", [6], payload.length + 1);
      const predItems = itemsN(payload[0]!, "node.rule.premise.count.pred", [2]);
      const name = atomBytes(predItems[0]!, "node.rule.premise.count.pred.name");
      const arity = readU32(predItems[1]!, "node.rule.premise.count.pred.arity");
      const pred = new PredicateRef(new Symbol(name), arity);
      const filter: GroundFilterEntry[] = items(payload[1]!, "node.rule.premise.count.filter").map((entry) => {
        const pair = itemsN(entry, "node.rule.premise.count.filter.entry", [2]);
        const pos = readU32(pair[0]!, "node.rule.premise.count.filter.pos");
        return { pos, value: pair[1]! };
      });
      const project = projectSpecFromValue(payload[2]!);
      const k = payload[3]!;
      const cert = readUsize(payload[4]!, "node.rule.premise.count.cert");
      return new CountPremise(pred, filter, project, k, cert);
    }
    default:
      throw refuse.unknownTag("node.rule.premise", tag);
  }
}

/** Atom("rows") is Rows; Tuple[Atom("distinct"|"sum"|"min"|"max"), int(attr)] is the fold. */
function projectSpecFromValue(v: Value): ProjectSpec {
  const ctx = "node.rule.premise.count.project";
  if (v instanceof Atom) {
    if (tagText(v.bytes()) === "rows" && v.bytes().length === 4) return ProjectSpec.rows();
    throw refuse.unknownTag(ctx, v.bytes());
  }
  const [tag, payload] = splitTag(v, ctx);
  if (payload.length !== 1) throw refuse.arity(ctx, [2], payload.length + 1);
  const attr = readU32(payload[0]!, "node.rule.premise.count.project.attr");
  switch (tagText(tag)) {
    case "distinct":
      return ProjectSpec.distinct(attr);
    case "sum":
      return ProjectSpec.sum(attr);
    case "min":
      return ProjectSpec.min(attr);
    case "max":
      return ProjectSpec.max(attr);
    default:
      throw refuse.unknownTag(ctx, tag);
  }
}

/**
 * The inverse of derivationAsValue: Tuple[ Tuple[node…], int(root) (, Tuple[cert…]) ]. Node order
 * is identity-bearing and preserved. The root is NOT checked against the node count here (#2630,
 * `seat:caa`'s ruling): a Derivation can hold it out of range, and check refuses it by its FIRM
 * root_out_of_range, so the decoder passes it through.
 */
export function derivationFromValue(v: Value): Derivation {
  const its = items(v, "derivation");
  if (its.length !== 2 && its.length !== 3) throw refuse.arity("derivation", [2, 3], its.length);
  const nodes = items(its[0]!, "derivation.nodes").map((nv) => nodeFromValue(nv));
  const root = readUsize(its[1]!, "derivation.root");
  const closedWorld =
    its.length === 3 ? items(its[2]!, "derivation.closed_world").map((cv) => closedModelCertFromValue(cv)) : [];
  return new Derivation(nodes, root, closedWorld);
}

/** A digest atom (64 lowercase-hex chars) into its 32 bytes, the inverse of digestAtom. */
function readHash(v: Value, ctx: string): Uint8Array {
  const bytes = parseHashHex(atomBytes(v, ctx));
  if (bytes === undefined) throw refuse.shape(ctx);
  return bytes;
}

function symbolFromValue(v: Value, ctx: string): Symbol {
  return new Symbol(atomBytes(v, ctx));
}

/**
 * Reconstruct a `ClosedModelCert`: the ONE certificate decoder (#2630). TEN, ELEVEN or TWELVE
 * elements: the 11th is ADR 0029 D10's slice-seal pin, the 12th ADR 0030's partial sub-scope;
 * anything else is refused by arity under the closed posture. The slots are read in rs's order, so
 * a certificate with two defects is refused for the same one in every core.
 */
export function closedModelCertFromValue(v: Value): ClosedModelCert {
  const its = items(v, "closed_world.cert");
  if (its.length < 10 || its.length > 12) throw refuse.arity("closed_world.cert", [10, 11, 12], its.length);
  const decompositionWitness =
    its.length >= 11 && !(its.length === 12 && isOptNone(its[10]!))
      ? readHash(its[10]!, "closed_world.cert.decomposition_witness")
      : undefined;
  const partialScope = its.length === 12 ? stratumPrefixFromValue(its[11]!) : undefined;
  const edbSnapshotHashes = items(its[5]!, "closed_world.cert.edb_snapshot_hashes").map((h) =>
    readHash(h, "closed_world.cert.edb_snapshot_hash"),
  );
  const domains = items(its[6]!, "closed_world.cert.domains").map((d) => finiteDomainFromValue(d));
  const extensions = items(its[7]!, "closed_world.cert.extensions").map((t) => relationTableFromValue(t));
  const supports = items(its[8]!, "closed_world.cert.supports").map((e) => supportEdgeFromValue(e));
  const scope = stratumPrefixFromValue(its[0]!);
  const programHash = readHash(its[1]!, "closed_world.cert.program_hash");
  const profileHash = readHash(its[2]!, "closed_world.cert.profile_hash");
  const ctxHash = readHash(its[3]!, "closed_world.cert.ctx_hash");
  const theoryConfigHash = readHash(its[4]!, "closed_world.cert.theory_config_hash");
  const limitsDecl = certSizeDeclFromValue(its[9]!);
  return new ClosedModelCert({
    scope,
    programHash,
    profileHash,
    ctxHash,
    theoryConfigHash,
    edbSnapshotHashes,
    domains,
    extensions,
    supports,
    limitsDecl,
    decompositionWitness,
    partialScope,
  });
}

/**
 * Is `v` the opt none marker Tuple[Atom("none")] (ADR 0030 D4's stand-in for an absent slice-seal
 * pin at the 11th slot when the 12th is present)? A malformed tuple is simply NOT the marker; the
 * next read reports it.
 */
function isOptNone(v: Value): boolean {
  try {
    const [tag, payload] = splitTag(v, "closed_world.cert.decomposition_witness");
    return tagText(tag) === "none" && tag.length === 4 && payload.length === 0;
  } catch {
    return false;
  }
}

/** Canonical order is CHECKED against what the constructor would build, never repaired (#839). */
function requireCanonicalOrder<T>(built: readonly T[], raw: readonly T[], path: string): void {
  if (built.length !== raw.length || built.some((x, i) => x !== raw[i])) throw refuse.notCanonical(path);
}

function stratumPrefixFromValue(v: Value): StratumPrefix {
  const its = itemsN(v, "closed_world.cert.scope", [2]);
  const level = readU32(its[0]!, "closed_world.cert.scope.level");
  const preds = items(its[1]!, "closed_world.cert.scope.predicates").map((p) =>
    symbolFromValue(p, "closed_world.cert.scope.predicate"),
  );
  const scope = StratumPrefix.of(level, preds);
  requireCanonicalOrder(scope.predicates, preds, "closed_world.cert.scope.predicates");
  return scope;
}

function finiteDomainFromValue(v: Value): FiniteDomain {
  const its = itemsN(v, "closed_world.cert.domain", [2]);
  const typeTag = symbolFromValue(its[0]!, "closed_world.cert.domain.type_tag");
  const values = Array.from(items(its[1]!, "closed_world.cert.domain.values"));
  const domain = FiniteDomain.of(typeTag, values);
  requireCanonicalOrder(domain.values, values, "closed_world.cert.domain.values");
  return domain;
}

function relationTableFromValue(v: Value): RelationTable {
  const its = itemsN(v, "closed_world.cert.extension", [3]);
  const pred = symbolFromValue(its[0]!, "closed_world.cert.extension.pred");
  const arity = readU32(its[1]!, "closed_world.cert.extension.arity");
  const rows = items(its[2]!, "closed_world.cert.extension.rows").map((r) =>
    groundLiteralFromValue(r, "closed_world.cert.extension.row"),
  );
  const table = RelationTable.of(pred, arity, rows);
  requireCanonicalOrder(table.rows, rows, "closed_world.cert.extension.rows");
  return table;
}

function supportEdgeFromValue(v: Value): SupportEdge {
  const its = itemsN(v, "closed_world.cert.support", [5]);
  const fact = groundLiteralFromValue(its[0]!, "closed_world.cert.support.fact");
  const clause = ClauseId.of(
    strictText(atomBytes(its[1]!, "closed_world.cert.support.clause"), "closed_world.cert.support.clause"),
  );
  const subst = substFromValue(its[2]!);
  const bodyRefs = items(its[3]!, "closed_world.cert.support.body_refs").map((r) => supportRefFromValue(r));
  const rank = readU32(its[4]!, "closed_world.cert.support.rank");
  return new SupportEdge(fact, clause, subst, bodyRefs, rank);
}

function supportRefFromValue(v: Value): SupportRef {
  const [tag, payload] = splitTag(v, "closed_world.cert.support.ref");
  switch (tagText(tag)) {
    case "same_stratum": {
      const p = expectN(payload, [3], "closed_world.cert.support.ref.same_stratum");
      const fact = groundLiteralFromValue(p[0]!, "closed_world.cert.support.ref.fact");
      return SupportRef.sameStratum(fact, readU32(p[1]!, "closed_world.cert.support.ref.rank"));
    }
    case "lower_stratum": {
      const p = expectN(payload, [3], "closed_world.cert.support.ref.lower_stratum");
      const cert = readUsize(p[0]!, "closed_world.cert.support.ref.cert");
      return SupportRef.lowerStratum(cert, groundLiteralFromValue(p[1]!, "closed_world.cert.support.ref.atom"));
    }
    case "builtin": {
      const p = expectN(payload, [2], "closed_world.cert.support.ref.builtin");
      return SupportRef.builtin(groundLiteralFromValue(p[0]!, "closed_world.cert.support.ref.atom"));
    }
    case "neg_lower": {
      const p = expectN(payload, [3], "closed_world.cert.support.ref.neg_lower");
      const cert = readUsize(p[0]!, "closed_world.cert.support.ref.cert");
      return SupportRef.negLower(cert, groundLiteralFromValue(p[1]!, "closed_world.cert.support.ref.atom"));
    }
    case "count_lower": {
      const p = expectN(payload, [2], "closed_world.cert.support.ref.count_lower");
      return SupportRef.countLower(readUsize(p[0]!, "closed_world.cert.support.ref.cert"));
    }
    default:
      throw refuse.unknownTag("closed_world.cert.support.ref", tag);
  }
}

function certSizeDeclFromValue(v: Value): CertSizeDecl {
  const its = itemsN(v, "closed_world.cert.limits_decl", [6]);
  return {
    certFacts: readUsize(its[0]!, "closed_world.cert.limits_decl.cert_facts"),
    domainValues: readUsize(its[1]!, "closed_world.cert.limits_decl.domain_values"),
    supportEdges: readUsize(its[2]!, "closed_world.cert.limits_decl.support_edges"),
    ruleGroundings: readUsize(its[3]!, "closed_world.cert.limits_decl.rule_groundings"),
    joinSteps: readUsize(its[4]!, "closed_world.cert.limits_decl.join_steps"),
    certBytes: readUsize(its[5]!, "closed_world.cert.limits_decl.cert_bytes"),
  };
}

export const DERIVATION_WIRE_V1_TAG = "proof-interchange/derivation/v1";

/** Reads a derivation as the public v1 payload. */
export function derivationWirePayloadV1ToValue(deriv: Derivation): Value {
  return derivationAsValue(deriv);
}

/** Decodes the public v1 derivation payload. */
export function derivationWirePayloadV1FromValue(value: Value): Derivation {
  return derivationFromValue(value);
}

/** Wraps a derivation payload with the proof-interchange v1 tag. */
export function derivationWireV1ToValue(deriv: Derivation): Value {
  return valueTuple([strAtom(DERIVATION_WIRE_V1_TAG), derivationAsValue(deriv)]);
}

/** Unwraps a proof-interchange v1 tagged derivation payload. */
export function derivationWireV1FromValue(value: Value): Derivation {
  const its = itemsN(value, "derivation wire v1", [2]);
  const tag = atomBytes(its[0]!, "derivation wire v1 tag");
  if (tagText(tag) !== DERIVATION_WIRE_V1_TAG || tag.length !== DERIVATION_WIRE_V1_TAG.length) {
    throw refuse.unknownTag("derivation wire v1", tag);
  }
  return derivationFromValue(its[1]!);
}

/** Encodes the public proof-interchange v1 wrapper as ontos-codec bytes. */
export function encodeDerivationWireV1(deriv: Derivation): Uint8Array {
  return encode(derivationWireV1ToValue(deriv));
}

/**
 * Decodes ontos-codec bytes as a public proof-interchange v1 derivation. For bytes the caller trusts:
 * bytes it did not produce go through `decodeDerivationWireV1Bounded`, which holds every certificate
 * to the caller's CheckLimits before decoding (#2561).
 */
export function decodeDerivationWireV1(bytes: Uint8Array): Derivation {
  let value: Value;
  try {
    value = decode(bytes);
  } catch (e) {
    throw new DecodeCodecFault("derivation wire v1 bytes", e);
  }
  return derivationWireV1FromValue(value);
}

