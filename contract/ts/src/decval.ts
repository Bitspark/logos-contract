// BigDecimal — the TS binding of logos's exact-decimal numeric domain (#331), a
// judgment-for-judgment mirror of the Rust BigDecimal (contract/rs/src/decval.rs) and the
// Go bigDecimal (contract/go/decval.go).
//
// A decimal is mantissa × 10^exponent, exact (no float — the §1.3 prize is structural
// value equality, which float breaks). Its ground form IS the FROZEN ontos-data §5.9
// `decimal` embedding Tuple(Atom("decimal"), int(mantissa), int(exponent)), canonical (a
// non-zero mantissa is not divisible by 10; zero is decimal(int 0, int 0)). All arithmetic
// reuses the native `bigint` — there is no second bignum.
//
// # The scale bound (#331 — total, DoS-resistant checker; byte-identical to Rust/Go)
//
// The mantissa is UNBOUNDED (bigint); the exponent is bounded to i128 — a decimal term
// whose exponent exceeds i128 is NOT a well-formed number (fromTerm returns undefined),
// matching Rust. Comparison decides by magnitude ORDER (digit-count + exponent) and only
// aligns within a shared decade. +/− align scales; the shift is capped at
// MAX_DECIMAL_SCALE_SHIFT. × and ÷ never align (they add/subtract exponents).

import { type Value } from "@bitspark/ontos-core";
import { encodeDecimal, readDecimal } from "@bitspark/ontos-data";

/**
 * The +/− scale-alignment shift cap, mirroring Rust's MAX_DECIMAL_SCALE_SHIFT. A DIFFERENT
 * quantity from MAX_DECIMAL_EXPONENT (the VALUE bound): they share a number and are two names on
 * purpose, so changing one never silently moves the other (research-docs/0016).
 */
const MAX_DECIMAL_SCALE_SHIFT = 65536n;

/**
 * Why a decimal operation returned no value (#3161, #3126), Rust's `DecimalError`. Two kinds, and the
 * difference is the point: the first three are the LANGUAGE's answer (the expression has no value in
 * ADR 0022's domain, so the goal is false), and `alignment_cap` is the IMPLEMENTATION stopping before
 * it knew (not decided). Nothing converts one into the other.
 *   - `division_by_zero`: a zero divisor for /, // or mod;
 *   - `non_terminating`: a / whose exact quotient does not terminate in base 10 (1.0 / 3);
 *   - `outside_domain`: the result lies outside the value domain |exponent| <= 65536;
 *   - `alignment_cap`: the exact alignment of two in-domain operands needs a shift past
 *     MAX_DECIMAL_SCALE_SHIFT, a WORK CAP. The result exists; it was not computed.
 */
export type DecimalError = "division_by_zero" | "non_terminating" | "outside_domain" | "alignment_cap";

/** A decimal operation's result: its value, or why it has none. */
export type DecimalResult<T> = { readonly ok: true; readonly value: T } | { readonly ok: false; readonly error: DecimalError };

function ok<T>(value: T): DecimalResult<T> {
  return { ok: true, value };
}

function err<T>(error: DecimalError): DecimalResult<T> {
  return { ok: false, error };
}

/** `fromParts`' refusal as the decimal error it is: a result outside the value domain. */
function inDomain(d: BigDecimal | undefined): DecimalResult<BigDecimal> {
  return d === undefined ? err("outside_domain") : ok(d);
}

/**
 * The decimal value domain (#2679), mirroring Rust's MAX_DECIMAL_EXPONENT: every decimal logos
 * produces or decodes has |exponent| <= it. Checked in ONE place, {@link BigDecimal.fromParts},
 * which every decimal-producing path returns through, and at the wire decode (fromTerm, #1385).
 * INCLUSIVE: 1e65536 is a value, 1e65537 is not.
 */
export const MAX_DECIMAL_EXPONENT = 65536n;

/** Whether `exponent` lies in the decimal value domain. */
function inDecimalDomain(exponent: bigint): boolean {
  return absBig(exponent) <= MAX_DECIMAL_EXPONENT;
}

/** 2^127 − 1, the exponent scale bound (mirroring Rust's i128-bounded exponent). */
const I128_MAX = (1n << 127n) - 1n;

/** |n| for a bigint. */
function absBig(n: bigint): bigint {
  return n < 0n ? -n : n;
}

/** The number of base-10 digits of |n| (zero → 0). */
function digitCount(n: bigint): number {
  return n === 0n ? 0 : absBig(n).toString().length;
}

/** How many times `base` divides |n| (bounded by digitCount(n)). */
function factorCount(n: bigint, base: bigint): number {
  if (n === 0n) return 0;
  let cur = absBig(n);
  let count = 0;
  while (cur % base === 0n) {
    cur /= base;
    count += 1;
  }
  return count;
}

/** 10^exp (exp ≥ 0n, bounded by the caller — a scale / digit count). */
function pow10(exp: bigint): bigint {
  return 10n ** exp;
}

/**
 * An exact decimal mantissa × 10^exponent — the decimal sibling of the `bigint` integer
 * domain. Canonical: a non-zero mantissa is not divisible by 10; zero is (0, 0). The
 * mantissa is unbounded; the exponent is i128-bounded on decode (#331).
 */
export class BigDecimal {
  private constructor(
    readonly mantissa: bigint,
    readonly exponent: bigint,
  ) {}

  /** The decimal zero, decimal(int 0, int 0). */
  static zero(): BigDecimal {
    return new BigDecimal(0n, 0n);
  }

  /**
   * Build a canonical BigDecimal from a (mantissa, exponent) pair: zero collapses to
   * (0,0); otherwise trailing base-10 zeros of the mantissa are carried into the exponent
   * (the ontos canonical form, one spelling per value). Mirrors Rust's from_parts.
   *
   * THE ONE LIMIT-CHECKED CONSTRUCTOR (#2679): `undefined` when the CANONICAL exponent lies
   * outside the value domain |exponent| <= MAX_DECIMAL_EXPONENT. Every decimal-producing path
   * returns through here. The check runs AFTER canonicalization, because stripping trailing
   * zeros raises the exponent and what must be in the domain is the value that results.
   *
   * Also `undefined` when carrying a trailing zero would push the exponent past the
   * i128 scale bound (#475): the canonicalization increment is CHECKED, not unbounded, so
   * a value that cannot be represented as a well-formed i128-scaled decimal is rejected
   * here (the goal fails) rather than producing a decimal(…, >i128) term that re-decodes as
   * not-a-number — the live tri-core divergence at the exponent boundary (rs used to
   * saturate; go/ts carried the increment on an unbounded big.Int/bigint). All three now
   * reject identically.
   */
  static fromParts(mantissa: bigint, exponent: bigint): BigDecimal | undefined {
    const d = BigDecimal.canonical(mantissa, exponent);
    return d !== undefined && inDecimalDomain(d.exponent) ? d : undefined;
  }

  /**
   * The canonical form of mantissa × 10^exponent WITHOUT the domain check: undefined only on
   * the i128 canonicalization overflow (#475). Private, so every value a caller can build still
   * passes {@link BigDecimal.fromParts}. Mirrors Rust's canonical.
   */
  private static canonical(mantissa: bigint, exponent: bigint): BigDecimal | undefined {
    if (mantissa === 0n) return BigDecimal.zero();
    let m = mantissa;
    let e = exponent;
    while (m % 10n === 0n) {
      m /= 10n;
      e += 1n;
      if (absBig(e) > I128_MAX) return undefined; // canonical exponent left the i128 band
    }
    return new BigDecimal(m, e);
  }

  /**
   * Promote an exact integer to a decimal (n × 10^0). The int → decimal promotion.
   *
   * Infallible: the exponent starts at 0n and canonicalization carries at most
   * digitCount(n) trailing zeros, so the result exponent is bounded by the operand's own
   * digit count (input-proportional) — it cannot reach i128::MAX for any term that fits in
   * memory. It canonicalizes WITHOUT the domain check (#2679): a promoted integer is an
   * OPERAND, never a result, and an integer past 10^65536 must still compare and promote. Every
   * decimal an operation RETURNS goes through fromParts, including add's zero short-circuits.
   */
  static fromBigInt(n: bigint): BigDecimal {
    return BigDecimal.canonical(n, 0n) as BigDecimal;
  }

  /**
   * Parse a decimal literal spelling [-+]?<digits>.<digits> (a `.` with ≥1 digit on each
   * side), or undefined for any other shape. Mirrors Rust's from_decimal_str. undefined, too,
   * for a spelling whose value lies outside the domain (#2679, seat:caa's ruling (a)): it
   * returns through fromParts like every arithmetic result.
   */
  static fromString(s: string): BigDecimal | undefined {
    let negative = false;
    let rest = s;
    if (s.startsWith("-")) {
      negative = true;
      rest = s.slice(1);
    } else if (s.startsWith("+")) {
      rest = s.slice(1);
    }
    const dot = rest.indexOf(".");
    if (dot < 0) return undefined;
    const intPart = rest.slice(0, dot);
    const fracPart = rest.slice(dot + 1);
    if (intPart === "" || fracPart === "") return undefined;
    if (!/^[0-9]+$/.test(intPart) || !/^[0-9]+$/.test(fracPart)) return undefined;
    let magnitude = BigInt(intPart + fracPart);
    if (negative) magnitude = -magnitude;
    // The exponent is −fracLen <= 0, and canonicalization only carries it up, so the i128
    // bound cannot overflow here. The DOMAIN can: a fraction longer than MAX_DECIMAL_EXPONENT
    // digits (after its trailing zeros are stripped) is refused by fromParts (#2679).
    return BigDecimal.fromParts(magnitude, -BigInt(fracPart.length));
  }

  isZero(): boolean {
    return this.mantissa === 0n;
  }

  isNegative(): boolean {
    return this.mantissa < 0n;
  }

  negate(): BigDecimal {
    return new BigDecimal(-this.mantissa, this.exponent);
  }

  abs(): BigDecimal {
    return new BigDecimal(absBig(this.mantissa), this.exponent);
  }

  /**
   * Total value order (consistent with equality): sign first, then by magnitude ORDER
   * (alignment-free unless two same-sign values share a decade). Mirrors Rust's cmp.
   * Returns -1/0/+1.
   */
  cmp(o: BigDecimal): number {
    const dn = this.isNegative();
    const on = o.isNegative();
    if (!dn && on) return 1;
    if (dn && !on) return -1;
    if (!dn && !on) return cmpDecMagnitude(this, o);
    return cmpDecMagnitude(o, this); // both negative: reverse the magnitude order
  }

  /**
   * self + other (exact), `alignment_cap` if the scale alignment exceeds MAX_DECIMAL_SCALE_SHIFT
   * (not decided, #3126), or `outside_domain`. Mirrors Rust's add.
   */
  add(o: BigDecimal): DecimalResult<BigDecimal> {
    // A zero operand returns the other one, and that one may be a promoted integer outside the
    // domain (see fromBigInt), so it is re-checked like every result (#2679).
    if (this.isZero()) return inDomain(BigDecimal.fromParts(o.mantissa, o.exponent));
    if (o.isZero()) return inDomain(BigDecimal.fromParts(this.mantissa, this.exponent));
    const eMin = this.exponent < o.exponent ? this.exponent : o.exponent;
    const shiftThis = this.exponent - eMin;
    const shiftO = o.exponent - eMin;
    if ((shiftThis > shiftO ? shiftThis : shiftO) > MAX_DECIMAL_SCALE_SHIFT) return err("alignment_cap");
    const m1 = this.mantissa * pow10(shiftThis);
    const m2 = o.mantissa * pow10(shiftO);
    return inDomain(BigDecimal.fromParts(m1 + m2, eMin));
  }

  /** self − other (exact); see add for the scale bound. */
  sub(o: BigDecimal): DecimalResult<BigDecimal> {
    return this.add(o.negate());
  }

  /**
   * self * other (exact): multiply mantissas, add exponents (no alignment). undefined on
   * the astronomical i128 exponent overflow OR (#475) when canonicalizing the product
   * mantissa carries a trailing zero past i128::MAX (e.g. decimal(2, i128::MAX) *
   * decimal(5, 0) → mantissa 10, exponent i128::MAX + 1) — fromParts rejects that boundary,
   * in parity with Rust/Go.
   */
  mul(o: BigDecimal): DecimalResult<BigDecimal> {
    // #1022's cap, which ts never got, is fromParts' now for all three cores (#2679): the
    // product is refused outside the value domain, checked on its canonical exponent. The i128
    // overflow is `outside_domain` by the argument Rust's mul records (research 0031 row 5).
    if (this.isZero() || o.isZero()) return ok(BigDecimal.zero());
    const exponent = this.exponent + o.exponent;
    if (absBig(exponent) > I128_MAX) return err("outside_domain");
    return inDomain(BigDecimal.fromParts(this.mantissa * o.mantissa, exponent));
  }

  /**
   * self / other iff the quotient TERMINATES in base 10 (the reduced denominator's only
   * prime factors are 2 and 5); otherwise undefined (the goal fails — no rounding, no
   * float). undefined on a zero divisor. Mirrors Rust's div_terminating.
   */
  divTerminating(o: BigDecimal): DecimalResult<BigDecimal> {
    if (o.isZero()) return err("division_by_zero");
    if (this.isZero()) return ok(BigDecimal.zero());
    const k = Math.max(factorCount(o.mantissa, 2n), factorCount(o.mantissa, 5n));
    const scaledNum = this.mantissa * pow10(BigInt(k));
    if (scaledNum % o.mantissa !== 0n) return err("non_terminating");
    const quotient = scaledNum / o.mantissa;
    const exponent = this.exponent - o.exponent - BigInt(k);
    if (absBig(exponent) > I128_MAX) return err("outside_domain");
    // #2679: / had no domain check, so 1e40000 / 1e-40000 minted decimal(1, 80000), which no
    // core decodes. It returns through the one constructor now.
    return inDomain(BigDecimal.fromParts(quotient, exponent));
  }

  /**
   * Align this and `other` to their common (smaller) exponent and return the two INTEGER
   * mantissas at that scale plus the shared exponent, or `alignment_cap` if the alignment shift
   * exceeds MAX_DECIMAL_SCALE_SHIFT (not decided, #3126 — the same DoS bound add/sub enforce).
   * At the common scale eMin the values are Xs × 10^eMin and Ys × 10^eMin, so this/other =
   * Xs/Ys EXACTLY — the cancelling scale factor lets // and mod reduce to integer division
   * on (Xs, Ys) with no decimal division (no termination concern). Mirrors Rust's
   * aligned_mantissas; used by divTruncInt and moduloFloored.
   */
  private alignedMantissas(o: BigDecimal): DecimalResult<{ xs: bigint; ys: bigint; eMin: bigint }> {
    const eMin = this.exponent < o.exponent ? this.exponent : o.exponent;
    const shiftThis = this.exponent - eMin;
    const shiftO = o.exponent - eMin;
    if ((shiftThis > shiftO ? shiftThis : shiftO) > MAX_DECIMAL_SCALE_SHIFT) return err("alignment_cap");
    const xs = this.mantissa * pow10(shiftThis);
    const ys = o.mantissa * pow10(shiftO);
    return ok({ xs, ys, eMin });
  }

  /**
   * this // other — TRUNCATING integer division (toward zero), the decimal lift of the
   * integer // . The result is an exact INTEGER (bigint), not a decimal: // answers "how
   * many whole other's fit in this", e.g. 7.5 // 2 = 3n, -7.5 // 2 = -3n (toward zero, NOT
   * floor -4). undefined on a zero divisor (mirroring the integer //) or an adversarial
   * scale gap. Mirrors Rust's div_trunc_int. `bigint` division truncates toward zero.
   */
  divTruncInt(o: BigDecimal): DecimalResult<bigint> {
    const aligned = this.alignedMantissas(o);
    if (!aligned.ok) return err(aligned.error);
    const a = aligned.value;
    if (a.ys === 0n) return err("division_by_zero");
    return ok(a.xs / a.ys);
  }

  /**
   * this mod other — ISO FLOORED modulo (the result takes the sign of the divisor), the
   * decimal lift of the integer mod. The result is an exact DECIMAL: this − floor(this/other)·other,
   * always exact here (no division — pure mantissa arithmetic), e.g. 7.5 mod 0.25 = 0.0,
   * -7.5 mod 2 = 0.5 (sign follows the positive divisor). undefined on a zero divisor or an
   * adversarial scale gap. At the common scale eMin the floored remainder of the integer
   * mantissas scaled back is the floored decimal remainder: (Xs mod Ys) × 10^eMin = this mod
   * other. Mirrors Rust's modulo_floored.
   */
  moduloFloored(o: BigDecimal): DecimalResult<BigDecimal> {
    const aligned = this.alignedMantissas(o);
    if (!aligned.ok) return err(aligned.error);
    const a = aligned.value;
    if (a.ys === 0n) return err("division_by_zero");
    // ISO floored remainder of the integer mantissas: %s is the truncated remainder
    // (sign of the dividend); correct it onto the divisor's side when the signs differ.
    let r = a.xs % a.ys;
    if (r !== 0n && r < 0n !== a.ys < 0n) {
      r += a.ys;
    }
    return inDomain(BigDecimal.fromParts(r, a.eMin));
  }

  /**
   * Lower to the ground `decimal` embedding via ontos-data encodeDecimal — byte-identical
   * to Rust/Go (the value is already canonical).
   */
  toTerm(): Value {
    return encodeDecimal(this.mantissa, this.exponent);
  }

  /**
   * Recognize and decode the ontos/data `decimal` embedding, or undefined for any term
   * that is not a canonical decimal — including (the #331 scale bound) an exponent beyond
   * i128. ontos-data's readDecimal is the canonical gate (it validates the structure and
   * rejects a non-canonical mantissa); we then narrow the exponent to the i128 scale.
   */
  static fromTerm(v: Value): BigDecimal | undefined {
    let parts: { mantissa: bigint; exponent: bigint };
    try {
      parts = readDecimal(v);
    } catch {
      return undefined;
    }
    // #1385: the value domain is WIRE VOCABULARY at this seam. An exponent past
    // +/-MAX_DECIMAL_EXPONENT is refused on decode rather than admitted as a
    // print-only value - every value narrowed away is one arithmetic already refuses
    // to combine, and admitting it was a live tri-core divergence (rs accepted
    // i128::MIN; go/ts rejected it, for the wrong reason). Decode-side only:
    // fromParts is untouched.
    if (!inDecimalDomain(parts.exponent)) return undefined;
    return new BigDecimal(parts.mantissa, parts.exponent);
  }
}

/**
 * Compare two same-sign decimals by magnitude. Decides by order (digit-count + exponent);
 * only aligns within a shared decade (shift bounded by the digit counts). Mirrors Rust's
 * cmp_magnitude.
 */
function cmpDecMagnitude(a: BigDecimal, b: BigDecimal): number {
  if (a.isZero() && b.isZero()) return 0;
  if (a.isZero()) return -1;
  if (b.isZero()) return 1;
  const orderA = BigInt(digitCount(a.mantissa)) + a.exponent;
  const orderB = BigInt(digitCount(b.mantissa)) + b.exponent;
  if (orderA !== orderB) return orderA < orderB ? -1 : 1;
  // Same decade ⇒ the exponent gap equals the digit-count difference (small): align to
  // the smaller exponent and compare magnitudes.
  const eMin = a.exponent < b.exponent ? a.exponent : b.exponent;
  const magA = absBig(a.mantissa) * pow10(a.exponent - eMin);
  const magB = absBig(b.mantissa) * pow10(b.exponent - eMin);
  return magA < magB ? -1 : magA > magB ? 1 : 0;
}
