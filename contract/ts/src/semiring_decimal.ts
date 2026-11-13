// The two decimal core semirings of v2 §8.3 (ADR 0031 D2), Tropical and Probability, over the
// contract's exact decimal (the frozen ontos-data decimal embedding). [PROPOSED] The TS binding
// of contract/rs/src/semiring_decimal.rs.
//
// Their carriers were ruled on #1821 (2026-11-11): exact only, no float (#331).
//   - An element is a CANONICAL non-negative decimal: decimal(int m, int e) with a non-zero m not
//     divisible by 10, zero only as decimal(0, 0), and e inside the decimal value band
//     (|e| <= 65536, #2679). An integer value is the decimal with e >= 0; an int embedding is NOT
//     an element, since two spellings of one value would break the axioms under value equality.
//   - Tropical adds +∞, the atom inf, as its zero.
//   - Both carriers declare the decimal's capacity bounds (ADR 0031 D1 as clarified on #1821): a
//     sum whose operands need an alignment shift past the decimal's cap (#3126), or a result whose
//     exponent leaves the band, is a capacity stop, never an element and never a rejection.

import { atom, equals, type Value } from "@bitspark/ontos-core";

import { BigDecimal, type DecimalResult } from "./decval.js";
import { type LawDeclaration, type Semiring, SemiringAnswer } from "./semiring.js";
import { ComponentIdentity } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** The bytes of the atom Tropical's +∞ is spelled with. */
export function tropicalInfinity(): Uint8Array {
  return utf8Encoder.encode("inf");
}

/** The canonical non-negative decimal `value` embeds, or `undefined`. */
function nonNegative(value: Value): BigDecimal | undefined {
  const decimal = BigDecimal.fromTerm(value);
  return decimal === undefined || decimal.isNegative() ? undefined : decimal;
}

/**
 * A decimal operation's result as a semiring answer: the element, or a capacity stop for every
 * error (`+` and `×` never divide, so the division errors cannot arise).
 */
function decimalAnswer(result: DecimalResult<BigDecimal>): SemiringAnswer {
  return result.ok ? SemiringAnswer.element(result.value.toTerm()) : SemiringAnswer.capacity();
}

function infinity(): Value {
  return atom(tropicalInfinity());
}

/** A Tropical element: a finite decimal, or `"infinite"`. */
function cost(value: Value): BigDecimal | "infinite" | undefined {
  if (equals(value, infinity())) return "infinite";
  return nonNegative(value);
}

const NOT_AN_ELEMENT = SemiringAnswer.notAnElement();

const TROPICAL_LAWS: LawDeclaration = Object.freeze({
  idempotent: true,
  bounded: true,
  monotone: true,
  commutative: true,
  supportsRetraction: false,
});

class TropicalSemiring implements Semiring {
  constructor() {
    Object.freeze(this);
  }

  declaredIdentity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/tropical-semiring"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  laws(): LawDeclaration {
    return TROPICAL_LAWS;
  }

  zero(): Value {
    return infinity();
  }

  one(): Value {
    return BigDecimal.zero().toTerm();
  }

  isElement(value: Value): boolean {
    return cost(value) !== undefined;
  }

  /** `min(a, b)`; `+∞` is its identity. */
  add(a: Value, b: Value): SemiringAnswer {
    const x = cost(a);
    const y = cost(b);
    if (x === undefined || y === undefined) return NOT_AN_ELEMENT;
    if (x === "infinite") return SemiringAnswer.element(b);
    if (y === "infinite") return SemiringAnswer.element(a);
    return SemiringAnswer.element(y.cmp(x) < 0 ? b : a);
  }

  /** `a + b`; `+∞` absorbs. */
  mul(a: Value, b: Value): SemiringAnswer {
    const x = cost(a);
    const y = cost(b);
    if (x === undefined || y === undefined) return NOT_AN_ELEMENT;
    if (x === "infinite" || y === "infinite") return SemiringAnswer.element(infinity());
    return decimalAnswer(x.add(y));
  }
}
Object.freeze(TropicalSemiring.prototype);

/**
 * The tropical semiring (ℚ≥0 ∪ {+∞}, min, +, +∞, 0) over exact decimals (v2 §8.3 `Tropical`;
 * ADR 0031 D2), a core semiring: shortest-path cost. It declares idempotent, bounded
 * (min(0, a) = 0, so recursion through it converges), monotone and commutative; it does not
 * support retraction. Identity logos-core/tropical-semiring@1.0.0.
 */
export function newTropicalSemiring(): Semiring {
  return new TropicalSemiring();
}

const PROBABILITY_LAWS: LawDeclaration = Object.freeze({
  idempotent: false,
  bounded: false,
  monotone: true,
  commutative: true,
  supportsRetraction: true,
});

class ProbabilitySemiring implements Semiring {
  constructor() {
    Object.freeze(this);
  }

  declaredIdentity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/probability-semiring"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  laws(): LawDeclaration {
    return PROBABILITY_LAWS;
  }

  zero(): Value {
    return BigDecimal.zero().toTerm();
  }

  one(): Value {
    return BigDecimal.fromBigInt(1n).toTerm();
  }

  isElement(value: Value): boolean {
    return nonNegative(value) !== undefined;
  }

  add(a: Value, b: Value): SemiringAnswer {
    const x = nonNegative(a);
    const y = nonNegative(b);
    return x === undefined || y === undefined ? NOT_AN_ELEMENT : decimalAnswer(x.add(y));
  }

  mul(a: Value, b: Value): SemiringAnswer {
    const x = nonNegative(a);
    const y = nonNegative(b);
    return x === undefined || y === undefined ? NOT_AN_ELEMENT : decimalAnswer(x.mul(y));
  }
}
Object.freeze(ProbabilitySemiring.prototype);

/**
 * The probability semiring (ℚ≥0, +, ×, 0, 1) over exact decimals (v2 §8.3
 * `Probability(Independence::Assumed)`, §14.4; ADR 0031 D2), a core semiring: sum-product, as
 * ruled on #1821. Derivations that share base facts are counted twice and a value can exceed 1:
 * the declared interpretation, not an error. It declares monotone, commutative and
 * supportsRetraction; it is neither idempotent nor bounded. Identity
 * logos-core/probability-semiring@1.0.0.
 */
export function newProbabilitySemiring(): Semiring {
  return new ProbabilitySemiring();
}
