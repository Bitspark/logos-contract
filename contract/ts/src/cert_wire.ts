/**
 * #2528 (seat:caa's ruling (a)): the byte spans of the certificates inside an encoded frame, read
 * WITHOUT decoding it, so a host can refuse a certificate wire longer than its budget before it
 * materialises a single value. The checker's measure (#2524) bounds what a DECODED certificate may
 * declare and be; only this bounds what an adversary makes a host READ.
 *
 * The ontos codec stores no per-element length: a tuple is `0x01 || uvarint(arity) || items` and an
 * atom `0x00 || uvarint(len) || bytes`, so a span is found by walking tags and uvarints. Skipping is
 * iterative (a count of values still to skip, so a frame's nesting sets no recursion depth); the walk
 * recurses only along the host's own path steps. It allocates only its output, and rejects a
 * non-canonical or overflowing uvarint exactly as the codec's decoder does. Mirrors rs `cert_wire` and
 * go `CertWireSpans` / `CertWireSpansAt`, pinned by the generated `vectors/cert_wire_spans.json`.
 *
 * Soundness of refusing on a span holds for a CANONICALLY encoded certificate: its literal span is
 * its measure (`certEncodedBytes`, the encoding with `certBytes` zeroed) plus the declaration's own
 * width above that of `0`, which is at most `certBytesSlack()`. So a span over `maxCertBytes + slack`
 * means a measure over `maxCertBytes`, which the checker refuses whatever the certificate declares. A
 * non-canonical (padded) certificate may be refused although a normalising decoder would shrink it;
 * that is still right, since the bound is on the bytes a host reads.
 */

import { decode, encode } from "@bitspark/ontos-codec";
import { type Value } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";
import { captureProofBudgets, proofBudgetError, type CheckLimits } from "./check.js";
import { type Derivation } from "./derivation.js";
import { derivationWireV1FromValue } from "./derivation_wire.js";
import { nativeOctetView } from "./octets.js";

/** Why a requested walk could not proceed: invalid configuration or unreadable frame, never a certificate verdict. */
export class CertWireError extends Error {
  /** The stable name every core reports, pinned by the shared vector. */
  readonly wireName: string;
  constructor(wireName: string) {
    super(`cert wire: ${wireName}`);
    this.wireName = wireName;
  }
}

const TAG_ATOM = 0x00;
const TAG_TUPLE = 0x01;

class Cursor {
  pos = 0;
  readonly bytes: Uint8Array;
  constructor(bytes: Uint8Array) {
    const frame = nativeOctetView(bytes);
    if (frame === undefined) throw new TypeError("a wire frame must be a valid Uint8Array");
    this.bytes = frame;
  }

  remaining(): bigint {
    return BigInt(this.bytes.length - this.pos);
  }

  byte(): number {
    if (this.pos >= this.bytes.length) throw new CertWireError("truncated");
    return this.bytes[this.pos++]!;
  }

  /** One shortest-form LEB128 uvarint over the u64 domain: overflow while reading, canonicality after. */
  uvarint(): bigint {
    const start = this.pos;
    let value = 0n;
    let shift = 0n;
    for (;;) {
      const b = this.byte();
      if (shift >= 64n || (shift === 63n && (b & 0x7f) > 1)) throw new CertWireError("uvarint_overflow");
      value |= BigInt(b & 0x7f) << shift;
      if ((b & 0x80) === 0) break;
      shift += 7n;
    }
    // Shortest form: the final byte carries payload, unless the value is a single 0x00.
    if (this.pos - start > 1 && this.bytes[this.pos - 1] === 0) throw new CertWireError("non_canonical_uvarint");
    return value;
  }

  /** A value's tag and uvarint, bounded by the bytes left (a value takes at least two bytes). */
  header(): [number, bigint] {
    const tag = this.byte();
    if (tag !== TAG_ATOM && tag !== TAG_TUPLE) throw new CertWireError("unknown_tag");
    const n = this.uvarint();
    const bound = tag === TAG_ATOM ? this.remaining() : this.remaining() / 2n;
    if (n > bound) throw new CertWireError("truncated");
    return [tag, n];
  }

  /** Skip one whole value without materialising it. */
  skip(): void {
    this.skipValues(1n);
  }

  /** Skip `count` whole values without materialising them. */
  skipValues(count: bigint): void {
    let pending = count;
    while (pending > 0n) {
      pending -= 1n;
      const [tag, n] = this.header();
      if (tag === TAG_ATOM) this.pos += Number(n);
      else pending += n;
    }
  }
}

/**
 * The byte span of every element of the tuple reached by following `path` from the frame's root
 * value, each step an index into the tuple at that point. A step at or past a tuple's arity means the
 * slot is ABSENT (an optional trailing element, an option's `none`): no certificates, an empty result.
 * Throws `CertWireError` for an invalid selector or unreadable frame.
 * Each index must be a nonnegative safe integer. The entire selector is captured before reading bytes.
 *
 * The WHOLE frame is walked, not only the path (seat:caa's fail-closed condition): every sibling
 * after the target and the rest of an absent slot's tuple are skipped too, and bytes after the one
 * value are refused. So a frame this accepts is one the codec could read in full, and a host that
 * refuses every throw never hands the decoder a frame its bound has not covered.
 *
 * The index-only case of {@link certWireSpansAt}, which it runs.
 */
export function certWireSpans(frame: Uint8Array, path: readonly number[]): number[] {
  const length = selectorLength(path);
  const steps: PathStep[] = [];
  for (let i = 0; i < length; i++) steps.push({ kind: "index", index: selectorIndex(path[i]) });
  return selectedSpans(frame, steps).map((c) => c.span);
}

/**
 * One step of a certificate path (#2561, seat:caa's ruling): an index into the tuple at that point,
 * or every element of it. `each` may appear any number of times, at any depth, so a frame that carries
 * certificates inside a list (the event door's output batch) needs no new walker. Its kinds are open
 * to growth.
 */
export type PathStep = { readonly kind: "index"; readonly index: number } | { readonly kind: "each" };

/**
 * The step to the element at `index`. One at or past the tuple's arity is an ABSENT slot (an optional
 * trailing element, an option's `none`), with no certificates.
 */
export function pathIndex(index: number): PathStep {
  return { kind: "index", index };
}

/** The step to every element, each followed by the rest of the path. */
export const PATH_EACH: PathStep = Object.freeze({ kind: "each" });

/**
 * One certificate {@link certWireSpansAt} found: its byte span, where it starts, and the concrete path
 * to it, every `each` resolved to the element's index and the certificate's own index last, so a
 * refusal names which element carried it. `start` (#2584) lets a host read the certificate's own
 * bytes, `frame.subarray(start, start + span)`, to share a stack whose bytes an earlier frame carried.
 */
export interface CertSpan {
  /** The concrete path from the frame's root to the certificate. */
  readonly path: readonly number[];
  /** The certificate's byte span on the wire. */
  readonly span: number;
  /** The offset in the frame at which the certificate's encoding starts. */
  readonly start: number;
}

/**
 * The byte span of every certificate the `steps` reach, with its concrete path: each path the steps
 * expand to (every `each` over every element) leads to a tuple, and each element of that tuple is a
 * certificate. A path through an absent slot reaches none. Throws `CertWireError` when the frame
 * cannot be walked. Malformed configuration reports `invalid_path` before any frame traversal.
 *
 * Fail closed exactly as {@link certWireSpans}: the WHOLE frame is walked and bytes after the one
 * value are refused. The walk recurses only along the steps, so its depth is the path's length, which
 * the host chooses, never the frame's nesting; skipping stays iterative.
 */
export function certWireSpansAt(frame: Uint8Array, steps: readonly PathStep[]): CertSpan[] {
  const length = selectorLength(steps);
  const owned: PathStep[] = [];
  for (let i = 0; i < length; i++) {
    const step = steps[i];
    if (step === null || (typeof step !== "object" && typeof step !== "function")) {
      throw new CertWireError("invalid_path");
    }
    const kind = step.kind;
    if (kind === "each") owned.push({ kind });
    else if (kind === "index") owned.push({ kind, index: selectorIndex(step.index) });
    else throw new CertWireError("invalid_path");
  }
  return selectedSpans(frame, owned);
}

/** Capture the declared indexed sequence without invoking collection methods. */
function selectorLength(steps: readonly unknown[]): number {
  if (!Array.isArray(steps)) throw new CertWireError("invalid_path");
  const length = steps.length;
  if (!Number.isInteger(length) || length < 0 || length > 0xffff_ffff) throw new CertWireError("invalid_path");
  return length;
}

function selectorIndex(index: unknown): number {
  if (typeof index !== "number" || !Number.isSafeInteger(index) || index < 0) throw new CertWireError("invalid_path");
  return index === 0 ? 0 : index;
}

/** Only captured, validated selector instructions reach the frame. */
function selectedSpans(frame: Uint8Array, steps: readonly PathStep[]): CertSpan[] {
  const c = new Cursor(frame);
  const out: CertSpan[] = [];
  spansAt(c, steps, 0, [], out);
  if (c.pos !== c.bytes.length) throw new CertWireError("trailing_bytes");
  return out;
}

/**
 * The fail-closed walk alone (#2561): the whole frame read without decoding it, refused by the same
 * names as {@link certWireSpans}. For a frame that carries no certificates, so a host never hands the
 * decoder bytes no walk has covered. Throws `CertWireError`.
 */
export function certWireWalk(frame: Uint8Array): void {
  const c = new Cursor(frame);
  c.skip();
  if (c.pos !== c.bytes.length) throw new CertWireError("trailing_bytes");
}

/** Walk one whole value, following `steps` from `at`; `path` is the concrete path to it. */
function spansAt(c: Cursor, steps: readonly PathStep[], at: number, path: number[], out: CertSpan[]): void {
  const [tag, arity] = c.header();
  if (tag !== TAG_TUPLE) throw new CertWireError("not_a_tuple");
  const step = steps[at];
  if (step === undefined) {
    // The certificates' tuple: each element is one.
    for (let i = 0n; i < arity; i++) {
      const start = c.pos;
      c.skip();
      out.push({ path: [...path, Number(i)], span: c.pos - start, start });
    }
    return;
  }
  if (step.kind === "each") {
    for (let i = 0n; i < arity; i++) {
      path.push(Number(i));
      spansAt(c, steps, at + 1, path, out);
      path.pop();
    }
    return;
  }
  const index = BigInt(step.index);
  if (index >= arity) {
    c.skipValues(arity);
    return;
  }
  c.skipValues(index);
  path.push(step.index);
  spansAt(c, steps, at + 1, path, out);
  path.pop();
  c.skipValues(arity - index - 1n);
}

/**
 * The bytes of the atom that tags a frame, `Tuple[Atom(tag), ..]`, read without decoding; `undefined`
 * when the root is not a tuple led by an atom. A host checks it before choosing a path, so an
 * `incomplete` trailer is never walked as a completeness one.
 */
export function certWireTag(frame: Uint8Array): Uint8Array | undefined {
  const c = new Cursor(frame);
  const [tag, arity] = c.header();
  if (tag !== TAG_TUPLE || arity === 0n) return undefined;
  const [inner, n] = c.header();
  if (inner !== TAG_ATOM) return undefined;
  return c.bytes.subarray(c.pos, c.pos + Number(n));
}

/**
 * The most a certificate's literal span can exceed its measure: the widest encoding of the declared
 * `certBytes` (an `int` atom) minus the encoding of the `0` the measure writes there.
 */
export function certBytesSlack(): number {
  const width = (n: bigint): number => encode(encodeInt(n)).length;
  return width((1n << 64n) - 1n) - width(0n);
}

/** Whether a certificate whose wire span is `span` measures over `maxCertBytes` for certain. */
export function certSpanOverBudget(span: number, maxCertBytes: number): boolean {
  if (!Number.isSafeInteger(span) || span < 0) throw new RangeError("a wire span must be a nonnegative safe integer");
  const invalid = proofBudgetError("max_cert_bytes", maxCertBytes);
  if (invalid !== undefined) throw invalid;
  return span - maxCertBytes > certBytesSlack();
}

/** The refusal a host reports for a certificate wire whose span exceeds its budget. */
export function certWireOverBudget(index: number, span: number, maxCertBytes: number): Error {
  return new Error(
    `cert_wire_over_budget: certificate ${index} spans ${span} bytes, over max_cert_bytes ${maxCertBytes} + slack ${certBytesSlack()}`,
  );
}

/** The path to a v1 derivation wire's certificates: the tagged payload, then the derivation's trailing closed_world slot. */
export function derivationWireV1CertPath(): readonly number[] {
  return [1, 2];
}

/**
 * The kinds of `BoundedWireError`. The set is OPEN (seat:caa, #2561): a future decode-time bound adds a
 * kind, so a consumer must treat an unknown kind as a refusal, never as success.
 */
export const BOUNDED_WIRE_UNREADABLE = "cert_wire_unreadable";
export const BOUNDED_WIRE_OVER_BUDGET = "cert_wire_over_budget";
export const BOUNDED_WIRE_INVALID_LIMITS = "invalid_check_limits";
/**
 * The bytes walked within budget, and the codec STOPPED before they were a value (#2734 3c, seat:caa's
 * ruling C). `detail` is the codec's own `DecodeError`, unfolded: a capacity stop (its decode depth, an
 * atom length or an arity) is not evidence the bytes are invalid, so a consumer classifies it apart from
 * malformed bytes (the kernel's `classifyDecodeStop` reads it).
 */
export const BOUNDED_WIRE_STOPPED = "decode_stopped";
/** The bytes decoded to a value, and the value is not a derivation wire. */
export const BOUNDED_WIRE_DECODE = "decode";

/**
 * Why `decodeDerivationWireV1Bounded` refused its bytes. `kind` is one of the BOUNDED_WIRE_* kinds, an
 * open set. `cert`, `span` and `maxCertBytes` are set for an over-budget refusal; `detail` carries the
 * caller's `CheckLimitError`, the walk's `CertWireError`, the codec's `DecodeError`, or the shape decoder's error.
 */
export class BoundedWireError extends Error {
  readonly kind: string;
  readonly cert: number | undefined;
  readonly span: number | undefined;
  readonly maxCertBytes: number | undefined;
  readonly detail: unknown;
  constructor(kind: string, message: string, detail: unknown, over?: { cert: number; span: number; maxCertBytes: number }) {
    super(message);
    this.name = "BoundedWireError";
    this.kind = kind;
    this.detail = detail;
    this.cert = over?.cert;
    this.span = over?.span;
    this.maxCertBytes = over?.maxCertBytes;
  }
}

/**
 * `decodeDerivationWireV1` held to the caller's `CheckLimits` BEFORE decoding (#2561, seat:caa's ruling),
 * for a consumer decoding a derivation from bytes it did not produce. The bytes are walked whole
 * (`certWireSpans`, fail closed) and every closed_world certificate's span is held to `maxCertBytes`
 * plus the slack, the rule the hosts apply to the guest's frames (#2528). It takes the whole
 * `CheckLimits` so a future decode bound joins by construction. Throws `BoundedWireError`.
 */
export function decodeDerivationWireV1Bounded(bytes: Uint8Array, limits: CheckLimits): Derivation {
  const counts = captureProofBudgets(limits);
  if (!counts.ok) {
    throw new BoundedWireError(BOUNDED_WIRE_INVALID_LIMITS, `${BOUNDED_WIRE_INVALID_LIMITS}: ${counts.error.message}`, counts.error);
  }
  const maxCertBytes = counts.value.maxCertBytes;
  let frame = nativeOctetView(bytes);
  if (frame === undefined) throw new TypeError("a proof frame must be a valid Uint8Array");
  checkCertificateSpans(frame, maxCertBytes);
  if (isSharedBuffer(frame.buffer)) {
    // Refuse an oversized frame before copying it. A concurrent writer may
    // have changed the shared bytes; check the private image that is decoded.
    frame = new Uint8Array(frame);
    checkCertificateSpans(frame, maxCertBytes);
  }
  // The codec's own stop, never folded into the value's shape (#2734 3c): the trusted
  // decodeDerivationWireV1 still folds it, which ADR 0036's v2 list records as a fault.
  let value: Value;
  try {
    value = decode(frame);
  } catch (e) {
    throw new BoundedWireError(BOUNDED_WIRE_STOPPED, `${BOUNDED_WIRE_STOPPED}: ${(e as Error).message}`, e);
  }
  try {
    return derivationWireV1FromValue(value);
  } catch (e) {
    throw new BoundedWireError(BOUNDED_WIRE_DECODE, `${BOUNDED_WIRE_DECODE}: ${(e as Error).message}`, e);
  }
}

function isSharedBuffer(buffer: ArrayBufferLike): boolean {
  try {
    Reflect.get(ArrayBuffer.prototype, "byteLength", buffer);
    return false;
  } catch {
    // Only ordinary and shared buffers can back a genuine native view.
    return true;
  }
}

function checkCertificateSpans(frame: Uint8Array, maxCertBytes: number): void {
  let spans: number[];
  try {
    spans = certWireSpans(frame, derivationWireV1CertPath());
  } catch (e) {
    if (e instanceof CertWireError) throw new BoundedWireError(BOUNDED_WIRE_UNREADABLE, `${BOUNDED_WIRE_UNREADABLE}: ${e.wireName}`, e);
    throw e;
  }
  spans.forEach((span, cert) => {
    if (certSpanOverBudget(span, maxCertBytes)) {
      throw new BoundedWireError(
        BOUNDED_WIRE_OVER_BUDGET,
        `${BOUNDED_WIRE_OVER_BUDGET}: certificate ${cert} spans ${span} bytes, over max_cert_bytes ${maxCertBytes} + slack ${certBytesSlack()}`,
        undefined,
        { cert, span, maxCertBytes },
      );
    }
  });
}
