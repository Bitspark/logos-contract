// The product semiring (v2 §14.2; ADR 0031; P9 I7, ruled on #1821, Q23-Q28). [PROPOSED]
// The TS binding of contract/rs/src/semiring_product.rs; contract/go/semiring_product.go is the third.
//
// A product is binary: member 0, then member 1. Its element is a bare Tuple[a, b], with a an element
// of member 0 and b an element of member 1. Zero and one are componentwise, and so are add and mul:
//   - an operand that is not a product element answers `not_an_element` before any member runs;
//   - member 0's operation runs first. Its `not_an_element` or its stop is the product's answer, and
//     member 1 is not consulted;
//   - then member 1's operation, read the same way; otherwise the answer is Tuple[r0, r1].
// Its laws are the AND of its members' declared laws: the product declares nothing on its own.
//
// Its declared identity is logos-core/product-semiring@1.0.0, with a config digest that commits to
// the ORDERED members' COMPUTED identities (semiringIdentity, laws folded in): SHA-256 of
// "logos-core/product-semiring/v1\n" followed, per member, by u64be(len id) ‖ id ‖ u64be(len version)
// ‖ version ‖ the member's identity digest, the per-member layout of compoundIdentityOf. So the
// swapped order is another identity, and the identity a verdict names folds the product's own laws in
// as for every semiring (semiringIdentity).

import { sha256 } from "@noble/hashes/sha2.js";
import { Tuple, tuple, type Value } from "@bitspark/ontos-core";

import { type LawDeclaration, type Semiring, SemiringAnswer, semiringIdentity } from "./semiring.js";
import { ComponentIdentity } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** The domain separator of a product semiring's declared config digest ({@link newProductSemiring}). */
export function productSemiringPrefix(): Uint8Array {
  return utf8Encoder.encode("logos-core/product-semiring/v1\n");
}

/**
 * The product of two semirings, `first` (member 0) then `second` (member 1) (v2 §14.2; ADR 0031;
 * ruled on #1821). Its element is a bare Tuple[a, b], a an element of `first` and b of `second`;
 * zero, one, add and mul are componentwise, and an operation reads member 0's answer before member
 * 1 is consulted (see the file comment). Its laws are the AND of the members' laws. Identity
 * logos-core/product-semiring@1.0.0, its config digest committing to the ordered members' computed
 * identities.
 */
export function newProductSemiring(first: Semiring, second: Semiring): Semiring {
  return new ProductSemiring(first, second);
}

/** One member operation: `add` or `mul` of `member` on its two operands. */
type MemberOp = (member: Semiring, x: Value, y: Value) => SemiringAnswer;

class ProductSemiring implements Semiring {
  readonly #first: Semiring;
  readonly #second: Semiring;

  constructor(first: Semiring, second: Semiring) {
    this.#first = first;
    this.#second = second;
    Object.freeze(this);
  }

  declaredIdentity(): ComponentIdentity {
    const parts: Uint8Array[] = [productSemiringPrefix()];
    for (const member of [this.#first, this.#second]) {
      const named = semiringIdentity(member);
      const id = named.id;
      const version = named.version;
      parts.push(u64be(id.length), id, u64be(version.length), version, named.configDigest);
    }
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/product-semiring"),
      utf8Encoder.encode("1.0.0"),
      sha256(concatBytes(parts)),
    );
  }

  /** The AND of the members' declared laws, each declaration read once. */
  laws(): LawDeclaration {
    const a = this.#first.laws();
    const b = this.#second.laws();
    return Object.freeze({
      idempotent: a.idempotent === true && b.idempotent === true,
      bounded: a.bounded === true && b.bounded === true,
      monotone: a.monotone === true && b.monotone === true,
      commutative: a.commutative === true && b.commutative === true,
      supportsRetraction: a.supportsRetraction === true && b.supportsRetraction === true,
    });
  }

  zero(): Value {
    return tuple([this.#first.zero(), this.#second.zero()]);
  }

  one(): Value {
    return tuple([this.#first.one(), this.#second.one()]);
  }

  isElement(value: Value): boolean {
    return this.#pair(value) !== undefined;
  }

  add(a: Value, b: Value): SemiringAnswer {
    return this.#combine(a, b, (member, x, y) => member.add(x, y));
  }

  mul(a: Value, b: Value): SemiringAnswer {
    return this.#combine(a, b, (member, x, y) => member.mul(x, y));
  }

  /** The two items of `value` when it is a product element, member 0's then member 1's, or `undefined`. */
  #pair(value: Value): readonly [Value, Value] | undefined {
    if (!(value instanceof Tuple)) return undefined;
    const items = value.items();
    if (items.length !== 2) return undefined;
    const x = items[0]!;
    const y = items[1]!;
    return this.#first.isElement(x) && this.#second.isElement(y) ? [x, y] : undefined;
  }

  /**
   * `op` componentwise: `not_an_element` when an operand is not a product element, before any member
   * runs; then member 0's answer, whose `not_an_element` or stop is the product's; then member 1's.
   */
  #combine(a: Value, b: Value, op: MemberOp): SemiringAnswer {
    const x = this.#pair(a);
    const y = this.#pair(b);
    if (x === undefined || y === undefined) return SemiringAnswer.notAnElement();
    const left = memberAnswer(op(this.#first, x[0], y[0]));
    if (left.kind !== "element") return left;
    const right = memberAnswer(op(this.#second, x[1], y[1]));
    if (right.kind !== "element") return right;
    return SemiringAnswer.element(tuple([left.value, right.value]));
  }
}
Object.freeze(ProductSemiring.prototype);

/**
 * A member's answer, read once, as the contract's own answer: its element, its stop with the member's
 * non-completion, or `not_an_element` (also for a kind the SPI does not define).
 */
function memberAnswer(answer: SemiringAnswer): SemiringAnswer {
  switch (answer.kind) {
    case "element":
      return SemiringAnswer.element(answer.value);
    case "stopped":
      return Object.freeze({ kind: "stopped", cause: answer.cause } as const);
    case "not_an_element":
      return SemiringAnswer.notAnElement();
  }
  return SemiringAnswer.notAnElement();
}

/** The 8-byte big-endian encoding of `n` (the u64 length prefix). */
function u64be(n: number): Uint8Array {
  const buf = new Uint8Array(8);
  new DataView(buf.buffer).setBigUint64(0, BigInt(n), false);
  return buf;
}

/** Concatenate byte slices into one buffer. */
function concatBytes(parts: readonly Uint8Array[]): Uint8Array {
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let offset = 0;
  for (const p of parts) {
    out.set(p, offset);
    offset += p.length;
  }
  return out;
}
