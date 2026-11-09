import { wellFormedUtf16 } from "./utf8.js";

const encoder = new TextEncoder();

/** The native lookup handle has no exact UTF-8 spelling in a portable proof or program. */
export class ClauseIdEncodingError extends Error {
  constructor(readonly clauseId: string) {
    super(`clause ID ${JSON.stringify(clauseId)} cannot be encoded as UTF-8`);
    this.name = "ClauseIdEncodingError";
  }
}

/** A portable handle has exactly one lossless UTF-8 reading. */
export function portableClauseIdBytes(handle: string): Uint8Array {
  if (!wellFormedUtf16(handle)) throw new ClauseIdEncodingError(handle);
  return encoder.encode(handle);
}
