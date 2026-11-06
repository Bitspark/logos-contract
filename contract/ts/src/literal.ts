// §1.1 Literal — a predicate application `p(args…)`. [FIRM]
// TS sibling of contract/rs/src/literal.rs.
//
// The logic-level "atom" of Horn logic — a different type from an ontos
// Atom(bytes). Ground-ness is a type: Goal (args are Term) vs GroundLiteral
// (args are ontos Value, always ground).

import { bytesEqual, copyBytes, equals as valueEquals, type Value } from "@bitspark/ontos-core";
import { Term, type Subst } from "./term.js";
import { UTF8_STRICT } from "./utf8.js";

/** A predicate symbol — an ontos `Atom(bytes)`, by convention a name. */
export class Symbol {
  readonly #bytes: Uint8Array;

  constructor(bytes: Uint8Array | readonly number[]) {
    this.#bytes = copyBytes(bytes);
    Object.freeze(this);
  }

  static of(bytes: Uint8Array | readonly number[] | string): Symbol {
    if (typeof bytes === "string") {
      return new Symbol(new TextEncoder().encode(bytes));
    }
    return new Symbol(bytes);
  }

  bytes(): Uint8Array {
    return this.#bytes;
  }

  equals(other: Symbol): boolean {
    return bytesEqual(this.#bytes, other.#bytes);
  }
}

/**
 * THE injective rendering of a name's bytes as text (#1961's ruling; shared by #2763, and moved
 * beside `Symbol` by #3057, since a type's canonical rendering lives with the type: seat:caa's
 * ruling on #2984): valid UTF-8 verbatim except `%`, which becomes `%25`, and every byte outside
 * valid UTF-8 as `%XX` (uppercase hex). Injective because `%` only ever starts an escape. A lossy
 * render maps every ill-formed byte to U+FFFD, so two identities that differ only there read as
 * one. rs (`logos_contract::escaped_name`) and go (`EscapedName`) render the same bytes to the same
 * text, pinned by `vectors/identity_bytes.json`'s `escaped_name` section.
 *
 * Well-formedness is Unicode's Table 3-7. A continuation byte never starts a valid sequence, so
 * escaping one byte at a time escapes exactly the bytes rs's maximal-subpart split escapes.
 */
export function escapedName(bytes: Uint8Array): string {
  let out = "";
  let i = 0;
  const cont = (at: number, lo = 0x80, hi = 0xbf): boolean =>
    at < bytes.length && bytes[at]! >= lo && bytes[at]! <= hi;
  while (i < bytes.length) {
    const b = bytes[i]!;
    let len = 0;
    if (b <= 0x7f) len = 1;
    else if (b >= 0xc2 && b <= 0xdf) len = cont(i + 1) ? 2 : 0;
    else if (b === 0xe0) len = cont(i + 1, 0xa0) && cont(i + 2) ? 3 : 0;
    else if ((b >= 0xe1 && b <= 0xec) || b === 0xee || b === 0xef) len = cont(i + 1) && cont(i + 2) ? 3 : 0;
    else if (b === 0xed) len = cont(i + 1, 0x80, 0x9f) && cont(i + 2) ? 3 : 0;
    else if (b === 0xf0) len = cont(i + 1, 0x90) && cont(i + 2) && cont(i + 3) ? 4 : 0;
    else if (b >= 0xf1 && b <= 0xf3) len = cont(i + 1) && cont(i + 2) && cont(i + 3) ? 4 : 0;
    else if (b === 0xf4) len = cont(i + 1, 0x80, 0x8f) && cont(i + 2) && cont(i + 3) ? 4 : 0;
    if (len === 0) {
      out += `%${b.toString(16).toUpperCase().padStart(2, "0")}`;
      i += 1;
    } else {
      const text = UTF8_STRICT.decode(bytes.subarray(i, i + len));
      out += text === "%" ? "%25" : text;
      i += len;
    }
  }
  return out;
}

/** A clause head / body literal / claim-with-holes (§1.1). May contain `Var`s. */
export class Goal {
  readonly pred: Symbol;
  readonly args: readonly Term[];

  constructor(pred: Symbol, args: readonly Term[]) {
    this.pred = pred;
    this.args = Object.freeze(Array.from(args));
    Object.freeze(this);
  }

  static of(pred: Symbol | string, args: Iterable<Term>): Goal {
    return new Goal(typeof pred === "string" ? Symbol.of(pred) : pred, Array.from(args));
  }

  /** Apply a grounding substitution to every argument (§3, Rule obligation). */
  substitute(subst: Subst): Goal {
    return new Goal(this.pred, this.args.map((t) => Term.substitute(t, subst)));
  }

  /**
   * Erase a fully-ground goal to a `GroundLiteral`; `undefined` if any argument
   * still contains a `Var`.
   */
  asGround(): GroundLiteral | undefined {
    const args: Value[] = [];
    for (const arg of this.args) {
      const v = Term.eraseGround(arg);
      if (v === undefined) return undefined;
      args.push(v);
    }
    return new GroundLiteral(this.pred, args);
  }
}

/** A ground literal — the conclusion of every `Derivation` node (§3). */
export class GroundLiteral {
  readonly pred: Symbol;
  readonly args: readonly Value[];

  constructor(pred: Symbol, args: readonly Value[]) {
    this.pred = pred;
    this.args = Object.freeze(Array.from(args));
    Object.freeze(this);
  }

  static of(pred: Symbol | string, args: Iterable<Value>): GroundLiteral {
    return new GroundLiteral(typeof pred === "string" ? Symbol.of(pred) : pred, Array.from(args));
  }

  /** Lift a `GroundLiteral` back into a `Goal` (ground, no holes). */
  toGoal(): Goal {
    return new Goal(this.pred, this.args.map(Term.fromValue));
  }

  equals(other: GroundLiteral): boolean {
    if (!this.pred.equals(other.pred)) return false;
    if (this.args.length !== other.args.length) return false;
    for (let i = 0; i < this.args.length; i += 1) {
      const left = this.args[i];
      const right = other.args[i];
      if (left === undefined || right === undefined || !valueEquals(left, right)) {
        return false;
      }
    }
    return true;
  }
}
