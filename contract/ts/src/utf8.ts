/**
 * The ONE place ts turns bytes into text (#2682).
 *
 * A `TextDecoder` does work the contract never named: by default it STRIPS a leading UTF-8 BOM
 * (`EF BB BF`). So ts read `BOM rule` as the tag `rule`, keyed two subst variables `X` and `BOM X`
 * as one, and gave a BOM-prefixed atom a different text from rs and go, which read exact bytes.
 * Both decoders here keep the BOM (`ignoreBOM: true`), so a text is exactly its bytes, as in rs
 * (`std::str::from_utf8` / `String::from_utf8_lossy`) and go (`string(b)`).
 *
 * Every ts source file decodes through these two. A structural guard
 * (`contract/ts/test/utf8_one_decoder.test.ts`) fails on a decoder constructed anywhere else, so a
 * platform default cannot come back unobserved.
 *
 * Neither decoder is used in streaming mode, so one shared instance each is stateless.
 */

/** Exact bytes to text; throws a `TypeError` on ill-formed UTF-8 (a fatal decoder). */
export const UTF8_STRICT: TextDecoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });

/** Exact bytes to text; an ill-formed sequence becomes U+FFFD, per the WHATWG decoder. */
export const UTF8_LOSSY: TextDecoder = new TextDecoder("utf-8", { fatal: false, ignoreBOM: true });

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
