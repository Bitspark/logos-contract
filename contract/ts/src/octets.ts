/** The native binary representations admitted by Logos. An authored array has
 * an explicit integer from 0 through 255 at each position. */
export type OctetSource = Uint8Array | readonly number[];

/** Inspect the native extent without dispatching to a caller-supplied getter. */
export function nativeOctetLength(source: unknown): number | undefined {
  const proto = Uint8Array.prototype;
  if (Reflect.get(proto, Symbol.toStringTag, source) !== "Uint8Array") return undefined;
  const length = Reflect.get(proto, "byteLength", source) as number;
  if (length === 0) {
    // Detached and out-of-bounds views also report zero. The native iterator
    // constructor checks that state without reading an element or advancing.
    try { proto.values.call(source as Uint8Array); } catch { return undefined; }
  }
  return length;
}

/** Borrow the native extent without calling a subclass's species constructor. */
export function nativeOctetView(source: unknown): Uint8Array | undefined {
  const length = nativeOctetLength(source);
  if (length === undefined) return undefined;
  const proto = Uint8Array.prototype;
  const buffer = Reflect.get(proto, "buffer", source) as ArrayBufferLike;
  const offset = Reflect.get(proto, "byteOffset", source) as number;
  return new Uint8Array(buffer, offset, length);
}

/** A byte sequence with the wrong length for an identity of fixed width. */
export class OctetWidthError extends RangeError {
  constructor(width: number, length: number) {
    super("a hash must be exactly " + width + " bytes, got " + length);
  }
}

/** Capture octets once. A fixed width is checked before any numeric element
 * is read. Sparse arrays fail at their first missing position. */
function readOctets(source: OctetSource, width?: number): Uint8Array {
  const bytes: number[] | Uint8Array | undefined = Array.isArray(source) ? source : nativeOctetView(source);
  if (bytes === undefined) throw new TypeError("expected a Uint8Array or an octet array");
  const length = bytes.length;
  if (width !== undefined && length !== width) throw new OctetWidthError(width, length);
  if (!Array.isArray(bytes)) return new Uint8Array(bytes);
  if (!Number.isInteger(length) || length < 0 || length > 0xffff_ffff) throw new TypeError("invalid octet array length");
  const octets: number[] = [];
  for (let i = 0; i < length; i++) {
    if (!Object.hasOwn(bytes, i)) throw new TypeError(`missing octet at index ${i}`);
    const value = bytes[i];
    if (typeof value !== "number" || !Number.isInteger(value) || value < 0 || value > 255) {
      throw new TypeError(`invalid octet at index ${i}`);
    }
    octets.push(value);
  }
  return new Uint8Array(octets);
}

/** Own an exact byte string of any length. */
export function copyOctets(source: OctetSource): Uint8Array {
  return readOctets(source);
}

/**
 * A 32-byte pin (e.g. a SHA-256 digest). The contract carries the raw bytes; how a
 * hash is computed is a consumer/kernel concern (the contract never learns the
 * scheme — it only compares pins for equality). Mirrors Rust's `Hash = [u8; 32]`.
 */
export type Hash = Uint8Array;

/** Own the 32 supplied octets of an already computed hash. */
export function hashFromBytes(source: OctetSource): Hash {
  return readOctets(source, 32);
}
