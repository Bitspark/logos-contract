import { nativeOctetView } from "./octets.js";

type HexLetterCase = "lowercase" | "mixed";

/** Read pairs of ASCII hex digits. The enclosing representation owns its
 * permitted letter case, byte length and error reporting. */
export function decodeHexPairs(input: string | Uint8Array, letterCase: HexLetterCase, byteCount?: number): Uint8Array | undefined {
  const text = typeof input === "string" ? input : nativeOctetView(input);
  if (text === undefined) return undefined;
  const length = text.length;
  if (length % 2 !== 0 || (byteCount !== undefined && length !== 2 * byteCount)) return undefined;
  const codeAt = typeof text === "string" ? (i: number) => text.charCodeAt(i) : (i: number) => text[i]!;
  const bytes = new Uint8Array(length / 2);
  for (let i = 0; i < bytes.length; i++) {
    const high = hexDigit(codeAt(2 * i), letterCase);
    const low = hexDigit(codeAt(2 * i + 1), letterCase);
    if (high === undefined || low === undefined) return undefined;
    bytes[i] = (high << 4) | low;
  }
  return bytes;
}

function hexDigit(code: number, letterCase: HexLetterCase): number | undefined {
  if (code >= 0x30 && code <= 0x39) return code - 0x30;
  if (code >= 0x61 && code <= 0x66) return code - 0x61 + 10;
  if (letterCase === "mixed" && code >= 0x41 && code <= 0x46) return code - 0x41 + 10;
  return undefined;
}
