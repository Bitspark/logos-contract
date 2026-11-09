/** One-shot UTF-8 decoding for Logos text fields. Both readings preserve a leading BOM. */
const strict = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
const lossy = new TextDecoder("utf-8", { fatal: false, ignoreBOM: true });

const encoder = new TextEncoder();

/** Encode one complete Unicode scalar sequence, preserving a leading BOM. */
export function encodeUtf8(text: string): Uint8Array {
  if (typeof text !== "string" || !wellFormedUtf16(text)) throw new TypeError("text must be well-formed UTF-16");
  return encoder.encode(text);
}

/** Decode a complete field, throwing TypeError on ill-formed UTF-8. */
export function decodeUtf8(bytes: Uint8Array): string {
  return strict.decode(bytes);
}

/** Decode a complete field, replacing each ill-formed sequence with U+FFFD. */
export function decodeUtf8Lossy(bytes: Uint8Array): string {
  return lossy.decode(bytes);
}

/**
 * Whether `s` is well-formed UTF-16: every surrogate is half of a high+low pair. A well-formed string
 * is exactly one UTF-8 can encode, so it is the text rs's `String` holds. A lone surrogate is not:
 * `TextEncoder` writes it as U+FFFD, so two distinct strings would encode to one byte string.
 *
 * The ONE ts test of that domain. #2233 wrote it for the prelude loader; #3115 moved it here so the
 * `VarId` constructor (§2a: a variable's name is UTF-8 text) calls the same function rather than a
 * copy. Every `VarId`, and so every `Subst` key, passes through it.
 */
export function wellFormedUtf16(s: string): boolean {
  for (let i = 0; i < s.length; i += 1) {
    const unit = s.charCodeAt(i);
    if (unit >= 0xdc00 && unit <= 0xdfff) return false;
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = s.charCodeAt(i + 1);
      if (!(next >= 0xdc00 && next <= 0xdfff)) return false;
      i += 1;
    }
  }
  return true;
}
