//! Exact **decimals** over the **frozen `ontos/data` `decimal` embedding** (#331) —
//! the sibling of [`crate::intval`]'s [`BigInt`] for the decimal numeric domain.
//!
//! A decimal is `mantissa × 10^exponent`, exact (no float — the §1.3 prize is
//! *structural* value equality, and IEEE float breaks it exactly as it would for
//! integers; ontos froze an **exact** decimal, not a float). It mirrors [`BigInt`]
//! step for step: a hand-rolled value type whose ground form *is* the frozen
//! `ontos/data` `decimal` datum, so two arithmetically-equal decimals are the **same**
//! term, byte-for-byte. All arithmetic **reuses** [`BigInt`] — there is no second bignum.
//!
//! ## The embedding ([`ontos-data §5.9`], byte form FROZEN v1)
//!
//! `decimal = Tuple(Atom("decimal"), int(mantissa), int(exponent))`, the two children
//! the frozen `int` embedding. **Canonical** (one spelling per value, the §1.3 prize):
//! a non-zero `mantissa` is **not divisible by 10** (trailing base-10 zeros are carried
//! into the exponent), and zero is `decimal(int 0, int 0)`. [`BigDecimal::from_parts`]
//! re-establishes that invariant, so every `BigDecimal` this module *produces* is
//! canonical and lowers ([`to_decimal_term`](BigDecimal::to_decimal_term)) to the same
//! bytes `ontos_data::encode_decimal` would emit.
//!
//! ## The scale bound (#331 — keeping the trusted checker total)
//!
//! The **mantissa is unbounded** (like [`BigInt`]; a decimal arg term carrying a huge
//! mantissa is itself huge, so the work is input-proportional). The **exponent is
//! bounded to `i128`**: a `decimal` term whose exponent child exceeds `i128` is **not a
//! well-formed number** ([`from_decimal_term`](BigDecimal::from_decimal_term) → `None`),
//! matching `ontos_data::read_decimal`'s `i128` exponent surface. This bounds the one
//! amplification a decimal has that an integer does not: a small term denoting a vast
//! scale. Comparison ([`cmp`](BigDecimal::cmp)) is exact **and** alignment-free in the
//! common case (it decides by magnitude *order* — digit-count + exponent — and only
//! aligns when two values share a decade, where the shift is bounded by their digit
//! counts). Addition/subtraction must align scales; the shift is capped at
//! [`MAX_DECIMAL_SCALE_SHIFT`] (a `decimal(1,0) + decimal(1, −10⁹)` adversarial term is **not
//! decided**, [`DecimalError::AlignmentCap`], rather than materializing a billion-digit number;
//! #3126). Multiplication and
//! division never align (they add/subtract exponents), so they are unbounded only in
//! the input-proportional sense [`BigInt`] already is.
//!
//! ## The value domain (#2679: one constructor, not one guard per producer)
//!
//! Every decimal has `|exponent| ≤ `[`MAX_DECIMAL_EXPONENT`]. Since #1385 that band IS the
//! value domain on the wire (every core refuses a past-band exponent at decode), so a
//! producer that minted a past-band value handed back something no core can read as a
//! number. It was enforced per producer (#470 the scientific literal, #451 add/sub,
//! #1022 `*`, #1385 the decode), and `/`, `mod` and [`BigDecimal::from_decimal_str`]
//! were still open. Now [`BigDecimal::from_parts`] is the ONE limit-checked constructor:
//! every decimal-producing path returns through it, so no second place can skip the check
//! (research-docs/0016; `seat:caa`'s ruling on #2679).
//!
//! [`ontos-data §5.9`]: pinned in `ontos/docs/spec/ontos-data.md`, exercised by
//! `ontos/vectors/data.json`; frozen 2026-06-06.

use std::cmp::Ordering;

use crate::intval::BigInt;
use crate::Term;

/// The functor label of the ontos/data `decimal` embedding:
/// `decimal(int(mantissa), int(exponent))`.
const DECIMAL_LABEL: &[u8] = b"decimal";

/// The maximum scale-alignment shift [`BigDecimal::add`]/[`BigDecimal::sub`] (and `//`/`mod`)
/// will materialize before stopping with [`DecimalError::AlignmentCap`], never a panic or an
/// unbounded allocation. `+`/`−` of two decimals must bring them to a common exponent by scaling
/// the larger-exponent mantissa up by `10^Δ` where `Δ` is the exponent difference; an
/// adversarial ground term with a vast exponent gap would otherwise force the trusted
/// checker to build an enormous integer. `65536` is far above any realistic decimal (a
/// literal's scale is bounded by its digit count) while bounding the work.
///
/// **A work cap, not a failure (#3126, research 0031 rows 3 and 5).** Both operands are in the
/// value domain and the true result exists, so the stop is not knowledge: the evaluator reports
/// it as not decided (`NotCompleted(work_cap)`), which `check` refuses by name and a negation
/// never reads as false. Until #3126 it read as the goal failing, a decided false.
///
/// ⚠ A DIFFERENT quantity from [`MAX_DECIMAL_EXPONENT`], which bounds the VALUE; they share a
/// number and are two names on purpose, so changing one never silently moves the other
/// (research-docs/0016's "one constant, several policies" trap).
pub const MAX_DECIMAL_SCALE_SHIFT: i128 = 65536;

/// **The decimal value domain** (#2679): every decimal logos produces or decodes has
/// `|exponent| ≤ MAX_DECIMAL_EXPONENT`. Checked in ONE place per core,
/// [`BigDecimal::from_parts`], which every decimal-producing path returns through (the
/// arithmetic results, [`BigDecimal::from_decimal_str`], the parser's literal lowering), and
/// at the wire decode ([`BigDecimal::from_decimal_term`], #1385). The bound is INCLUSIVE:
/// `1e65536` is a value, `1e65537` is not.
pub const MAX_DECIMAL_EXPONENT: i128 = 65536;

/// Whether `exponent` lies in the decimal value domain. A range test, never `abs()`:
/// `i128::MIN.abs()` panics.
fn in_domain(exponent: i128) -> bool {
    (-MAX_DECIMAL_EXPONENT..=MAX_DECIMAL_EXPONENT).contains(&exponent)
}

/// Why a decimal operation returned no value (#3161, #3126). Two kinds, and the difference is
/// the whole point: the first three are the LANGUAGE's answer (the expression has no value in
/// ADR 0022's domain, so the goal is false), and the last is the IMPLEMENTATION stopping before
/// it knew (not decided). Nothing converts one kind into the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DecimalError {
    /// A zero divisor for `/`, `//` or `mod`.
    DivisionByZero,
    /// A `/` whose exact quotient does not terminate in base 10 (`1.0 / 3`).
    NonTerminating,
    /// The result lies outside the value domain `|exponent| <= MAX_DECIMAL_EXPONENT`.
    OutsideDomain,
    /// The exact alignment of two in-domain operands needs a shift past
    /// [`MAX_DECIMAL_SCALE_SHIFT`]: a work cap. The result exists; it was not computed.
    AlignmentCap,
}

impl std::fmt::Display for DecimalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecimalError::DivisionByZero => write!(f, "decimal division by zero"),
            DecimalError::NonTerminating => write!(f, "non-terminating decimal division (/)"),
            DecimalError::OutsideDomain => write!(
                f,
                "decimal exponent outside the domain |exponent| <= {MAX_DECIMAL_EXPONENT}"
            ),
            DecimalError::AlignmentCap => write!(
                f,
                "decimal scale alignment exceeds the maximum of {MAX_DECIMAL_SCALE_SHIFT}"
            ),
        }
    }
}

/// The refusal of a result outside the value domain.
fn outside_domain() -> DecimalError {
    DecimalError::OutsideDomain
}

/// An exact decimal `mantissa × 10^exponent`, the decimal sibling of [`BigInt`].
///
/// Invariant (canonical, enforced by [`from_parts`](Self::from_parts) and every
/// operation): a non-zero `mantissa` is **not divisible by 10** and zero is
/// `mantissa = 0, exponent = 0`. Given the invariant the derived `PartialEq`/`Eq` is
/// exact value equality (two equal decimals have identical fields), the lowered [`Term`]
/// is unique per value, and the hand-written value order [`cmp`](Self::cmp) is consistent
/// with it. The mantissa is an unbounded [`BigInt`]; the exponent is a host `i128` (the
/// #331 scale bound).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigDecimal {
    /// The significand. Canonical: non-zero ⇒ not divisible by 10. Carries the sign.
    mantissa: BigInt,
    /// The base-10 exponent. `0` whenever the mantissa is zero.
    exponent: i128,
}

impl BigDecimal {
    /// The decimal zero (`decimal(int 0, int 0)`).
    pub fn zero() -> Self {
        BigDecimal {
            mantissa: BigInt::zero(),
            exponent: 0,
        }
    }

    /// Build from a (mantissa, exponent) pair, **canonicalizing**: zero collapses to
    /// `(0, 0)`; otherwise trailing base-10 zeros of the mantissa are carried into the
    /// exponent so the stored mantissa is not divisible by 10 (the ontos canonical form,
    /// the one-spelling-per-value §1.3 prize).
    ///
    /// **The ONE limit-checked constructor (#2679).** Returns `None` when the CANONICAL
    /// exponent lies outside the value domain `|exponent| ≤ `[`MAX_DECIMAL_EXPONENT`]. Every
    /// decimal-producing path returns through here, so none can mint a past-band value. The
    /// check runs AFTER canonicalization: stripping trailing zeros raises the exponent, and
    /// what must be in the domain is the value that actually results.
    ///
    /// Also `None` when carrying a trailing zero would push the exponent past the
    /// `i128` scale bound (#475): the canonicalization increment is **checked**, not
    /// saturating, so a value that cannot be represented as a well-formed `i128`-scaled
    /// decimal is rejected here (the goal fails) rather than silently capping at
    /// `i128::MAX` — which would lower to a decimal term go/ts (unbounded big-int exponent)
    /// reject on re-decode, a live tri-core divergence at the exponent boundary. The
    /// caller treats `None` the same as the astronomical-overflow path `*`/`/` already do.
    pub fn from_parts(mantissa: BigInt, exponent: i128) -> Option<Self> {
        Self::canonical(mantissa, exponent).filter(|d| in_domain(d.exponent))
    }

    /// The canonical form of `mantissa × 10^exponent`, WITHOUT the domain check: `None` only on
    /// the `i128` canonicalization overflow (#475). Private to this module, so every value a
    /// caller can build still passes [`from_parts`](Self::from_parts).
    fn canonical(mantissa: BigInt, exponent: i128) -> Option<Self> {
        if mantissa.is_zero() {
            return Some(BigDecimal::zero());
        }
        let ten = BigInt::from_i128(10);
        let mut m = mantissa;
        let mut e = exponent;
        // Strip trailing base-10 zeros (each is one factor of 10 → exponent + 1). The
        // increment is checked: an overflow means the canonical exponent leaves the i128
        // band, so the value is not a well-formed decimal (#475).
        while let Some((q, r)) = m.div_rem_trunc(&ten) {
            if r.is_zero() {
                m = q;
                e = e.checked_add(1)?;
            } else {
                break;
            }
        }
        Some(BigDecimal {
            mantissa: m,
            exponent: e,
        })
    }

    /// Promote an exact integer to a decimal (`n × 10^0`), canonicalized. This is the
    /// `int → decimal` promotion the mixed-domain operators use.
    ///
    /// Infallible: the exponent starts at `0` and the canonicalization carries at most
    /// `digit_count(n)` trailing zeros, so the result exponent is bounded by the operand's
    /// own digit count (input-proportional) — it cannot reach `i128::MAX` for any term that
    /// fits in memory. It canonicalizes WITHOUT the domain check (#2679): a promoted integer
    /// is an OPERAND, never a result, and an integer past `10^65536` (arithmetic can build one;
    /// a literal is capped at 4,096 digits) must still compare and promote. Every decimal an
    /// operation RETURNS goes through [`from_parts`](Self::from_parts), including [`add`](Self::add)'s
    /// zero short-circuits, which would otherwise hand such an operand back.
    pub fn from_bigint(n: BigInt) -> Self {
        BigDecimal::canonical(n, 0).expect("from_bigint exponent is bounded by digit count")
    }

    /// Parse a decimal **literal spelling** `[-+]?<digits>.<digits>` (a `.` with at least
    /// one digit on each side — exactly what the lexer's number rule produces). Returns
    /// `None` for any other shape (no dot, empty part, a non-digit, a second dot). The
    /// integer-and-fraction digits form the mantissa; the fraction length is the negative
    /// exponent (`"3.14"` → `mantissa 314, exponent −2`), then canonicalized.
    ///
    /// `None`, too, for a spelling whose value lies outside the domain (#2679, `seat:caa`'s
    /// ruling (a)): `"0."` followed by 65,536 zeros and a `1` is exponent −65537. It returns
    /// through [`from_parts`](Self::from_parts) like every arithmetic result, so "in-band is
    /// every value the parser admits" holds by construction.
    pub fn from_decimal_str(text: &str) -> Option<Self> {
        let (negative, rest) = match text.as_bytes().first() {
            Some(b'-') => (true, &text[1..]),
            Some(b'+') => (false, &text[1..]),
            _ => (false, text),
        };
        let dot = rest.find('.')?;
        let int_part = &rest[..dot];
        let frac_part = &rest[dot + 1..];
        if int_part.is_empty() || frac_part.is_empty() {
            return None;
        }
        if !int_part.bytes().all(|b| b.is_ascii_digit())
            || !frac_part.bytes().all(|b| b.is_ascii_digit())
        {
            return None;
        }
        // The mantissa is the integer and fraction digits concatenated (sign reapplied);
        // BigInt::from_decimal_str normalizes leading zeros. The exponent is −frac_len,
        // raised by however many trailing zeros we strip here.
        //
        // #1264: STRIP THE TRAILING ZEROS AS TEXT, before the BigInt exists. `from_parts`
        // canonicalizes by dividing by ten once PER trailing zero, and each division is a
        // full bignum operation over a shrinking value — O(n²) in the digit count. Doing it
        // on the string is one O(n) pass and leaves `from_parts` nothing to divide away.
        //
        // Measured, release build, `314` followed by N zeros:
        //
        //   N        before      after
        //   1,000    79.33 ms    10.30 µs
        //   4,000     1.70 s     20.60 µs
        //   10,000    9.95 s     33.10 µs
        //
        // ⚠ The obvious alternative — count the zeros from `to_decimal_string` and issue ONE
        // `div_exact(pow10(k))` — was measured and is NOT faster (10k: 6.92 s -> 8.41 s),
        // because `BigInt::to_decimal_string` is itself quadratic (4.51 s at 8,000 digits).
        // A single div-by-10 is cheap (766 µs at 8,000 digits) and near-linear; the cost was
        // never the divisions individually, it was doing k of them.
        let combined = format!("{int_part}{frac_part}");
        let trimmed = combined.trim_end_matches('0');
        // All-zero input ("0.000") trims to nothing; `from_decimal_str` wants a digit, and
        // the zero value carries exponent 0 by canonical form, so the shift is dropped.
        let (digits, stripped) = if trimmed.is_empty() {
            ("0", 0usize)
        } else {
            (trimmed, combined.len() - trimmed.len())
        };
        let magnitude = BigInt::from_decimal_str(digits)?;
        let mantissa = if negative {
            magnitude.negate()
        } else {
            magnitude
        };
        // The exponent is `−frac_len ≤ 0`, and canonicalization only carries it up, so the
        // i128 bound cannot overflow here. The DOMAIN can: a fraction longer than
        // MAX_DECIMAL_EXPONENT digits (after its trailing zeros are stripped) is refused by
        // `from_parts`, the one constructor (#2679).
        let exponent = -(frac_part.len() as i128) + stripped as i128;
        BigDecimal::from_parts(mantissa, exponent)
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.mantissa.is_zero()
    }

    /// Whether the value is strictly negative.
    pub fn is_negative(&self) -> bool {
        self.mantissa.is_negative()
    }

    /// `-self` (negation). Negating preserves the exponent and canonicality.
    pub fn negate(&self) -> Self {
        BigDecimal {
            mantissa: self.mantissa.negate(),
            exponent: self.exponent,
        }
    }

    /// `|self|`.
    pub fn abs(&self) -> Self {
        BigDecimal {
            mantissa: self.mantissa.abs(),
            exponent: self.exponent,
        }
    }

    /// `self + other` (exact), or [`DecimalError::AlignmentCap`] if the scale alignment exceeds
    /// [`MAX_DECIMAL_SCALE_SHIFT`] (not decided, #3126), or [`DecimalError::OutsideDomain`].
    /// Aligns both mantissas to the smaller exponent, adds, and re-canonicalizes.
    pub fn add(&self, other: &Self) -> Result<Self, DecimalError> {
        // A zero operand returns the other one, and that one may be a promoted integer outside
        // the domain (see `from_bigint`), so it is re-checked like every result (#2679).
        if self.is_zero() || other.is_zero() {
            let kept = if self.is_zero() { other } else { self };
            return BigDecimal::from_parts(kept.mantissa.clone(), kept.exponent)
                .ok_or_else(outside_domain);
        }
        let e_min = self.exponent.min(other.exponent);
        // Both shifts are ≥ 0; one is 0 and the other is the exponent gap Δ.
        // Every value is in the domain (#2679), so the gap is at most 2 × MAX_DECIMAL_EXPONENT;
        // the subtraction stays CHECKED anyway, as defence in depth (an overflowing gap is
        // astronomically past the bound and takes the same stop: a gap that cannot be aligned is
        // an inability, never a value the language lacks).
        // (Fuzz: run 33239317295, crash-a6ca2512… — subtract-with-overflow here.)
        let (Some(shift_self), Some(shift_other)) = (
            self.exponent.checked_sub(e_min),
            other.exponent.checked_sub(e_min),
        ) else {
            return Err(DecimalError::AlignmentCap);
        };
        if shift_self.max(shift_other) > MAX_DECIMAL_SCALE_SHIFT {
            return Err(DecimalError::AlignmentCap);
        }
        let m_self = self.mantissa.mul(&BigInt::pow10(shift_self as usize));
        let m_other = other.mantissa.mul(&BigInt::pow10(shift_other as usize));
        BigDecimal::from_parts(m_self.add(&m_other), e_min).ok_or_else(outside_domain)
    }

    /// `self - other` (exact); see [`add`](Self::add) for the scale-alignment bound.
    pub fn sub(&self, other: &Self) -> Result<Self, DecimalError> {
        self.add(&other.negate())
    }

    /// `self * other` (exact): multiply mantissas, add exponents (no alignment).
    /// [`DecimalError::OutsideDomain`] when the product lies outside the value domain (#1022, now
    /// through the one constructor, #2679).
    ///
    /// **The `i128` exponent overflow is `OutsideDomain` too, by an argument (research 0031 row
    /// 5), not by default.** For in-domain operands `|e₁ + e₂| <= 2 × MAX_DECIMAL_EXPONENT`, so the
    /// sum cannot overflow. Were it reached, the canonical exponent is `e₁ + e₂ + k`, where `k`
    /// (the product's stripped trailing zeros) is at most its digit count: an overflow past
    /// `i128::MAX` leaves it above the domain, and one below `i128::MIN` leaves it below
    /// `i128::MIN + k`, far outside the domain either way. So the result provably has no value.
    pub fn mul(&self, other: &Self) -> Result<Self, DecimalError> {
        if self.is_zero() || other.is_zero() {
            return Ok(BigDecimal::zero());
        }
        let exponent = self
            .exponent
            .checked_add(other.exponent)
            .ok_or_else(outside_domain)?;
        // #1022's cap, which `mul` alone used to carry, is `from_parts`'s now (#2679): the
        // domain is checked on the CANONICAL exponent, so #475's canonicalization boundary
        // (decimal(2, i128::MAX) * decimal(5, 0)) and an over-scale product are both refused
        // there, by the same constructor `/`, `mod` and the parser use.
        BigDecimal::from_parts(self.mantissa.mul(&other.mantissa), exponent)
            .ok_or_else(outside_domain)
    }

    /// **Exact terminating** division `self / other`: the quotient **iff** it terminates
    /// in base 10 (the reduced denominator's only prime factors are 2 and 5); otherwise
    /// `Err` (the goal fails — no rounding, no precision, no float, mirroring
    /// [`BigInt::div_exact`]'s fail-loud discipline). `Err` on a zero divisor.
    ///
    /// `self/other = (mₐ/m_b) × 10^(eₐ−e_b)`. Let `k = max(v₂(m_b), v₅(m_b))` (the 2/5
    /// content of the denominator). `m_b | mₐ·10^k` **iff** the part of `m_b` coprime to
    /// 10 divides `mₐ` **iff** the quotient terminates — so the single exact division
    /// `(mₐ·10^k) / m_b` both tests termination and yields the mantissa, exponent
    /// `eₐ − e_b − k`. `k` is bounded by `digit_count(m_b)`, so the work is bounded.
    ///
    /// The `i128` overflow of `eₐ − e_b − k` is [`DecimalError::OutsideDomain`] by the same
    /// argument as [`mul`](Self::mul)'s: for in-domain operands `|eₐ − e_b| <= 2 ×
    /// MAX_DECIMAL_EXPONENT` and `k` is bounded by a digit count, so it cannot overflow, and were
    /// it reached the canonical exponent stays within a digit count of it, far outside the domain.
    pub fn div_terminating(&self, other: &Self) -> Result<Self, DecimalError> {
        if other.is_zero() {
            return Err(DecimalError::DivisionByZero);
        }
        if self.is_zero() {
            return Ok(BigDecimal::zero());
        }
        let k = factor_count(&other.mantissa, 2).max(factor_count(&other.mantissa, 5));
        let scaled_num = self.mantissa.mul(&BigInt::pow10(k));
        let quotient = scaled_num
            .div_exact(&other.mantissa)
            .ok_or(DecimalError::NonTerminating)?;
        let exponent = self
            .exponent
            .checked_sub(other.exponent)
            .and_then(|e| e.checked_sub(k as i128))
            .ok_or_else(outside_domain)?;
        // #2679: `/` had no domain check, so `1e40000 / 1e-40000` minted decimal(1, 80000),
        // which `*` refuses and no core decodes. It returns through the one constructor now.
        BigDecimal::from_parts(quotient, exponent).ok_or_else(outside_domain)
    }

    /// Align `self` and `other` to their common (smaller) exponent and return the two
    /// **integer** mantissas at that scale plus the shared exponent, or
    /// [`DecimalError::AlignmentCap`] if the alignment shift exceeds [`MAX_DECIMAL_SCALE_SHIFT`]
    /// (not decided, #3126; never a panic or an unbounded allocation — the same DoS bound
    /// `add`/`sub` enforce). At the
    /// common scale `e_min` the values are `Xs × 10^e_min` and `Ys × 10^e_min`, so
    /// `self/other = Xs/Ys` **exactly** — the cancelling scale factor lets `//` and `mod`
    /// reduce to *integer* division on `(Xs, Ys)` with no decimal division at all (so no
    /// termination concern). Used by [`div_trunc_int`](Self::div_trunc_int) and
    /// [`modulo_floored`](Self::modulo_floored).
    fn aligned_mantissas(&self, other: &Self) -> Result<(BigInt, BigInt, i128), DecimalError> {
        let e_min = self.exponent.min(other.exponent);
        // Both shifts are ≥ 0; one is 0 and the other is the exponent gap Δ.
        // Every value is in the domain (#2679), so the gap is at most 2 × MAX_DECIMAL_EXPONENT;
        // the subtraction stays CHECKED anyway, as defence in depth (an overflowing gap is
        // astronomically past the bound and takes the same stop: a gap that cannot be aligned is
        // an inability, never a value the language lacks).
        // (Fuzz: run 33239317295, crash-a6ca2512… — subtract-with-overflow here.)
        let (Some(shift_self), Some(shift_other)) = (
            self.exponent.checked_sub(e_min),
            other.exponent.checked_sub(e_min),
        ) else {
            return Err(DecimalError::AlignmentCap);
        };
        if shift_self.max(shift_other) > MAX_DECIMAL_SCALE_SHIFT {
            return Err(DecimalError::AlignmentCap);
        }
        let xs = self.mantissa.mul(&BigInt::pow10(shift_self as usize));
        let ys = other.mantissa.mul(&BigInt::pow10(shift_other as usize));
        Ok((xs, ys, e_min))
    }

    /// `self // other` — **truncating** integer division (toward zero), the decimal lift
    /// of the integer `//` ([`BigInt::div_rem_trunc`]). The result is an exact **integer**
    /// (`BigInt`), not a decimal: `//` answers "how many whole `other`s fit in `self`",
    /// e.g. `7.5 // 2 = 3`, `-7.5 // 2 = -3` (toward zero, NOT floor −4). `Err` on a zero
    /// divisor (mirroring the integer `//`), or on an adversarial scale gap.
    ///
    /// Since `self/other = Xs/Ys` at the common scale ([`aligned_mantissas`](Self::aligned_mantissas)),
    /// the truncated quotient is exactly `trunc(Xs/Ys)` — a single integer division, no
    /// rounding/precision, never a float.
    pub fn div_trunc_int(&self, other: &Self) -> Result<BigInt, DecimalError> {
        let (xs, ys, _e_min) = self.aligned_mantissas(other)?;
        xs.div_rem_trunc(&ys)
            .map(|(q, _r)| q)
            .ok_or(DecimalError::DivisionByZero)
    }

    /// `self mod other` — ISO **floored** modulo (the result takes the sign of the
    /// divisor), the decimal lift of the integer `mod` ([`BigInt::modulo_floored`]). The
    /// result is an exact **decimal**: `self mod other = self − floor(self/other)·other`,
    /// always exact here (no division — pure mantissa subtraction/scaling), e.g.
    /// `7.5 mod 0.25 = 0.0`, `-7.5 mod 2 = 0.5` (sign follows the positive divisor). `Err`
    /// on a zero divisor (mirroring the integer `mod`), or on an adversarial scale gap.
    ///
    /// At the common scale `e_min` the floored remainder of the integer mantissas scaled
    /// back is the floored decimal remainder: `(Xs mod Ys) × 10^e_min = self mod other`
    /// (the shared `10^e_min` factors out of `self − floor(self/other)·other`), so the
    /// answer reduces to the integer floored modulo of `(Xs, Ys)`, then re-scaled.
    pub fn modulo_floored(&self, other: &Self) -> Result<Self, DecimalError> {
        let (xs, ys, e_min) = self.aligned_mantissas(other)?;
        let rem = xs.modulo_floored(&ys).ok_or(DecimalError::DivisionByZero)?;
        BigDecimal::from_parts(rem, e_min).ok_or_else(outside_domain)
    }

    /// Lower to the ground embedding `Tuple(Atom("decimal"), int(mantissa), int(exponent))`.
    /// Both children are the frozen `int` embedding via [`BigInt::to_int_term`], so the
    /// bytes are identical to `ontos_data::encode_decimal` for an in-range value and the
    /// unbounded-mantissa case is handled the same way [`BigInt`] handles a beyond-`i128`
    /// magnitude. Always canonical, so equal decimals lower to byte-identical terms.
    pub fn to_decimal_term(&self) -> Term {
        Term::tuple([
            Term::atom(DECIMAL_LABEL.to_vec()),
            self.mantissa.to_int_term(),
            BigInt::from_i128(self.exponent).to_int_term(),
        ])
    }

    /// Recognize the ontos/data `decimal` embedding and decode it, or `None` for any
    /// term that is not a **canonical** `decimal(int(mantissa), int(exponent))` — a wrong
    /// functor/arity, a non-canonical child, a non-canonical mantissa (divisible by 10),
    /// a non-ground term, **or** an exponent beyond `i128` (the #331 scale bound). The
    /// canonical-form gate is `ontos_data::recognize_decimal` (host-width-independent), so
    /// recognition agrees byte-for-byte across cores; the exponent is then narrowed to the
    /// bounded `i128` scale.
    pub fn from_decimal_term(term: &Term) -> Option<Self> {
        // #2275 layer 3: a `decimal(int(m), int(e))` nests exactly 3 deep, so anything deeper is
        // not one. Checked BEFORE the erase, which would build a deep `ontos::Value` whose own
        // `Drop` recurses per level (Bitspark/ontos#340); see `BigInt::from_int_term`.
        if !term.depth_le(3) {
            return None;
        }
        // Bridge to `ontos::Value`; a non-ground term is not a decimal. Validate the
        // canonical decimal structure (label, arity, canonical int children, mantissa not
        // divisible by 10) before decoding.
        let value = term.erase_ground()?;
        ontos_data::recognize_decimal(&value).ok()?;
        let Term::Tuple(children) = term else {
            return None;
        };
        let [Term::Atom(label), mantissa_term, exponent_term] = children.as_slice() else {
            return None;
        };
        if label.as_slice() != DECIMAL_LABEL {
            return None;
        }
        let mantissa = BigInt::from_int_term(mantissa_term)?;
        // The exponent rides as a frozen `int`; narrow to the bounded `i128` scale. A
        // canonical-but-beyond-`i128` exponent is rejected (not a well-formed number).
        let exponent = BigInt::from_int_term(exponent_term)?.to_i128()?;
        // #1385: the value domain is WIRE VOCABULARY at this seam. An exponent past
        // ±`MAX_DECIMAL_EXPONENT` is refused on decode rather than admitted as a
        // print-only value — every value narrowed away is one arithmetic already refuses
        // to combine, and admitting it was a live tri-core divergence (rs accepted
        // `i128::MIN`; go/ts rejected it). Decode-side only: `from_parts` is untouched.
        //
        // ⛔ A RANGE TEST, NEVER `abs()` — `i128::MIN.abs()` PANICS, and `i128::MIN` is
        // one of the three cases the conformance vector pins.
        if !in_domain(exponent) {
            return None;
        }
        // `recognize_decimal` already guaranteed the canonical invariant, so the pair is
        // canonical as-is.
        Some(BigDecimal { mantissa, exponent })
    }

    /// Render a decimal spelling of this value. **TOTAL** — it renders every value it is
    /// given, including ones no caller can re-read. Its callers are the pretty-printer and
    /// diagnostics, and a diagnostic that cannot print the offending value is worse
    /// diagnostics; not on a hot path.
    ///
    /// ⛔ **THE ROUND-TRIP IS BANDED, NOT UNCONDITIONAL. Read which band you are in before
    /// relying on the output** (#1264 — this doc claimed an unconditional round-trip, and
    /// that claim had been false BY DESIGN since #470):
    ///
    /// | band | spelling | `from_decimal_str` |
    /// |---|---|---|
    /// | **in-band** — `\|exponent\| ≤ ` [`MAX_DECIMAL_EXPONENT`], i.e. **every value the parser admits** (by construction since #2679: the parser returns through [`from_parts`](Self::from_parts)) | fixed-point, always carrying a `.` so it re-lexes as a decimal and never an integer | **round-trips, exactly** |
    /// | **past-band** — no public constructor builds one and the decode refuses it (#2679, #1385); the arm stays for TOTALITY | value-faithful **scientific** `<sign><digits>e<exponent>` | ⛔ **REFUSES it** |
    ///
    /// In-band examples: `0` → `"0.0"`; `decimal(314,−2)` → `"3.14"`; `decimal(5,−1)` →
    /// `"0.5"`; `decimal(1,−3)` → `"0.001"`; `decimal(5,1)` → `"50.0"`.
    ///
    /// **The past-band spelling is PRINT-ONLY.** The lexer TOKENIZES it (it is the shape the
    /// scientific-notation rule reads), but the parser's `lower_scientific` refuses it at the
    /// same limit and keeps it as an opaque atom, so no reader turns it back into a number. It
    /// is deliberately **not**
    /// [`from_decimal_str`](Self::from_decimal_str)-readable, because that parser accepts
    /// only fixed-point `<digits>.<digits>` by design, matching the lexer's number rule.
    /// Two deliberate decisions, jointly: this is not a gap to be closed here.
    ///
    /// **Why the band exists — bounded materialization (#470).** The fixed-point form
    /// expands `|exponent|` zeros (trailing for a positive scale, leading for a negative
    /// one); an adversarial value with a vast exponent — reachable only by *constructing* a
    /// `decimal` term directly, since the parser caps a literal's scale — would otherwise
    /// allocate gigabytes. The scientific fallback is `O(digits)` regardless of scale.
    ///
    /// ⚠ **Do not "fix" the past-band arm by making it fixed-point**: that reinstates the
    /// unbounded allocation #470 removed. And do not narrow the renderer to a partial
    /// function: the lie goes, the **totality stays** (#1264).
    pub fn to_decimal_string(&self) -> String {
        if self.is_zero() {
            return "0.0".to_string();
        }
        let sign = if self.mantissa.is_negative() { "-" } else { "" };
        let digits = self.mantissa.abs().to_decimal_string();
        // Defense in depth: never materialize an unbounded run of zeros. Past the scale
        // bound, render the scientific form (digit-proportional, still re-lexable).
        if !in_domain(self.exponent) {
            return format!("{sign}{digits}e{}", self.exponent);
        }
        if self.exponent >= 0 {
            // Integer-valued: digits, then `exponent` trailing zeros, then ".0".
            let zeros = "0".repeat(self.exponent as usize);
            format!("{sign}{digits}{zeros}.0")
        } else {
            let frac_len = (-self.exponent) as usize;
            let d = digits.len();
            if d > frac_len {
                // Split the digits `frac_len` from the right.
                let point = d - frac_len;
                format!("{sign}{}.{}", &digits[..point], &digits[point..])
            } else {
                // `0.<leading zeros><digits>` (value magnitude < 1).
                let leading = "0".repeat(frac_len - d);
                format!("{sign}0.{leading}{digits}")
            }
        }
    }
}

/// Total value order (consistent with `PartialEq`/`Eq`), **alignment-free** except when
/// two same-sign values share a decade. Sign decides first; for same-sign values the
/// **magnitude order** `digit_count(mantissa) + exponent` decides (a value `m × 10^e`
/// lies in `[10^(order−1), 10^order)`, so a strictly greater order is a strictly greater
/// magnitude — no scaling needed). Only when orders tie does it align, and then the shift
/// is bounded by the digit counts (an adversarial vast exponent gap is decided by order,
/// never materialized). Given the canonical-form invariant, `a == b ⟺ a.cmp(b) == Equal`.
impl Ord for BigDecimal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_negative(), other.is_negative()) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            // Same sign (incl. both non-negative, where zero sorts below positives via
            // the magnitude compare): compare magnitudes, reversing for two negatives.
            (false, false) => cmp_magnitude(self, other),
            (true, true) => cmp_magnitude(other, self),
        }
    }
}

impl PartialOrd for BigDecimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compare two **same-sign** decimals by magnitude (called with `(self, other)` for the
/// non-negative case and `(other, self)` for the negative case so the caller's reversal
/// is uniform). Decides by magnitude order; only aligns within a shared decade.
fn cmp_magnitude(a: &BigDecimal, b: &BigDecimal) -> Ordering {
    match (a.is_zero(), b.is_zero()) {
        (true, true) => return Ordering::Equal,
        (true, false) => return Ordering::Less, // 0 < positive magnitude
        (false, true) => return Ordering::Greater,
        (false, false) => {}
    }
    // order(x) = number of base-10 digits of |mantissa| + exponent. `m·10^e` lies in
    // `[10^(order−1), 10^order)`, so distinct orders decide the magnitude outright.
    let order_a = (digit_count(&a.mantissa) as i128).saturating_add(a.exponent);
    let order_b = (digit_count(&b.mantissa) as i128).saturating_add(b.exponent);
    match order_a.cmp(&order_b) {
        Ordering::Equal => {
            // Same decade ⇒ eₐ − e_b = digits_b − digits_a (small): align to the smaller
            // exponent (shift bounded by the digit counts) and compare magnitudes.
            let e_min = a.exponent.min(b.exponent);
            let mag_a = a
                .mantissa
                .abs()
                .mul(&BigInt::pow10((a.exponent - e_min) as usize));
            let mag_b = b
                .mantissa
                .abs()
                .mul(&BigInt::pow10((b.exponent - e_min) as usize));
            mag_a.cmp(&mag_b)
        }
        non_eq @ (Ordering::Less | Ordering::Greater) => non_eq,
    }
}

/// The number of base-10 digits of `|n|` (zero → `0`).
fn digit_count(n: &BigInt) -> usize {
    if n.is_zero() {
        0
    } else {
        n.abs().to_decimal_string().len()
    }
}

/// How many times `base` divides `|n|` (the multiplicity of the prime factor). Bounded by
/// `digit_count(n)`. Used to find the 2/5 content of a division denominator.
fn factor_count(n: &BigInt, base: i128) -> usize {
    if n.is_zero() {
        return 0;
    }
    let b = BigInt::from_i128(base);
    let mut cur = n.abs();
    let mut count = 0usize;
    while let Some((q, r)) = cur.div_rem_trunc(&b) {
        if r.is_zero() {
            cur = q;
            count += 1;
        } else {
            break;
        }
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(s: &str) -> BigDecimal {
        BigDecimal::from_decimal_str(s).unwrap_or_else(|| panic!("parse decimal {s}"))
    }
    pub(super) fn int(n: i128) -> BigDecimal {
        BigDecimal::from_bigint(BigInt::from_i128(n))
    }
    /// A value OUTSIDE the domain, built past the check (#2679): only this module can, so the
    /// tests of what the renderer and the operations do with one still have a subject.
    pub(super) fn unchecked(m: i128, e: i128) -> BigDecimal {
        BigDecimal::canonical(BigInt::from_i128(m), e).expect("canonical in i128")
    }

    // ----------------------------------------------- construction / canonical form --

    #[test]
    fn from_decimal_str_decomposes_and_canonicalizes() {
        // (mantissa, exponent) via the round-trip spelling.
        assert_eq!(dec("3.14").to_decimal_string(), "3.14");
        assert_eq!(dec("0.5").to_decimal_string(), "0.5");
        assert_eq!(dec("-3.14").to_decimal_string(), "-3.14");
        assert_eq!(dec("0.001").to_decimal_string(), "0.001");
        // Trailing zeros are stripped into the exponent (canonical, one spelling/value).
        assert_eq!(dec("5.0"), int(5).mul(&int(1)).unwrap());
        assert_eq!(dec("5.0").to_decimal_string(), "5.0");
        assert_eq!(dec("50.0").to_decimal_string(), "50.0");
        assert_eq!(dec("3.140").to_decimal_string(), "3.14"); // 3.140 == 3.14
        assert_eq!(dec("-0.0"), BigDecimal::zero()); // negative zero normalizes
        assert_eq!(dec("0.0"), BigDecimal::zero());
        assert_eq!(BigDecimal::zero().to_decimal_string(), "0.0");
    }

    #[test]
    fn to_decimal_string_caps_zero_materialization_at_the_scale_bound() {
        // #470 defense in depth: a directly-constructed decimal with a vast exponent must
        // NOT materialize `|exponent|` zeros (that 12-byte `decimal(9, 2e9)` term would
        // allocate ~2 GB). Past `MAX_DECIMAL_EXPONENT` the renderer falls back to the
        // digit-proportional scientific spelling. Since #2679 no public constructor and no
        // decode builds such a value, so this is the renderer's TOTALITY, kept on purpose.
        let huge_pos = unchecked(9, 2_000_000_000);
        let s = huge_pos.to_decimal_string();
        assert_eq!(
            s, "9e2000000000",
            "an over-scale positive must render scientific"
        );
        assert!(
            s.len() < 32,
            "the rendering must be digit-bounded, not scale-bounded"
        );

        let huge_neg = unchecked(9, -2_000_000_000);
        assert_eq!(huge_neg.to_decimal_string(), "9e-2000000000");

        // Just past the bound renders scientific; AT the bound still renders fixed-point.
        let over = unchecked(1, MAX_DECIMAL_EXPONENT + 1);
        assert_eq!(
            over.to_decimal_string(),
            format!("1e{}", MAX_DECIMAL_EXPONENT + 1)
        );
        let at = BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT).unwrap();
        let at_str = at.to_decimal_string();
        assert!(
            at_str.ends_with(".0") && !at_str.contains('e'),
            "at the bound the fixed-point form is retained, got {} chars",
            at_str.len()
        );
    }

    #[test]
    fn malformed_decimal_strings_are_none() {
        assert_eq!(BigDecimal::from_decimal_str("3"), None); // no dot (an integer)
        assert_eq!(BigDecimal::from_decimal_str("3."), None); // empty fraction
        assert_eq!(BigDecimal::from_decimal_str(".5"), None); // empty integer part
        assert_eq!(BigDecimal::from_decimal_str("3.1.4"), None); // second dot
        assert_eq!(BigDecimal::from_decimal_str("3.1a"), None);
        assert_eq!(BigDecimal::from_decimal_str("-"), None);
    }

    #[test]
    fn integral_decimals_stay_decimal_distinct_from_int() {
        // 5.0 is a DECIMAL, NOT the int 5 — distinct sorts (#331). Its embedding is the
        // decimal tuple, not int(5).
        assert_ne!(
            dec("5.0").to_decimal_term(),
            BigInt::from_i128(5).to_int_term()
        );
    }

    // ---------------------------------------------------------- value bridge / term --

    #[test]
    fn decimal_term_round_trips() {
        for s in [
            "3.14", "-3.14", "0.5", "0.001", "5.0", "50.0", "0.0", "123.456",
        ] {
            let d = dec(s);
            let term = d.to_decimal_term();
            assert_eq!(
                BigDecimal::from_decimal_term(&term),
                Some(d),
                "round-trip {s}"
            );
        }
    }

    /// In the `i128` range the lowered term must be byte-identical to
    /// `ontos_data::encode_decimal` (ontos owns the canonical decimal byte form).
    #[test]
    fn decimal_term_is_byte_identical_to_ontos_data_encode_decimal() {
        // (mantissa, exponent) canonical pairs.
        for (m, e) in [
            (314i128, -2i128),
            (5, -1),
            (1, -3),
            (5, 1),
            (0, 0),
            (-314, -2),
        ] {
            let from_logos = BigDecimal::from_parts(BigInt::from_i128(m), e)
                .unwrap()
                .to_decimal_term();
            let from_ontos = Term::from_value(&ontos_data::encode_decimal(m, e).expect("in range"));
            assert_eq!(
                from_logos, from_ontos,
                "to_decimal_term != encode_decimal for {m}e{e}"
            );
        }
    }

    #[test]
    fn non_canonical_or_huge_exponent_terms_do_not_decode() {
        // A non-decimal term.
        assert_eq!(
            BigDecimal::from_decimal_term(&BigInt::from_i128(5).to_int_term()),
            None
        );
        // A bare atom.
        assert_eq!(
            BigDecimal::from_decimal_term(&Term::atom(b"3.14".to_vec())),
            None
        );
        // Non-canonical mantissa (50 is divisible by 10) — recognize_decimal rejects.
        let non_canonical = Term::tuple([
            Term::atom(DECIMAL_LABEL.to_vec()),
            BigInt::from_i128(50).to_int_term(),
            BigInt::from_i128(-1).to_int_term(),
        ]);
        assert_eq!(BigDecimal::from_decimal_term(&non_canonical), None);
        // Exponent beyond i128 (the scale bound) — built as a canonical-but-huge int child.
        let huge_exp = BigInt::from_decimal_str(&("1".to_string() + &"0".repeat(40))).unwrap();
        let huge = Term::tuple([
            Term::atom(DECIMAL_LABEL.to_vec()),
            BigInt::from_i128(1).to_int_term(),
            huge_exp.to_int_term(),
        ]);
        assert_eq!(BigDecimal::from_decimal_term(&huge), None);
    }

    // ------------------------------------------------------------------- comparison --

    #[test]
    fn cmp_orders_by_value_across_scales() {
        assert_eq!(dec("0.5").cmp(&dec("0.5")), Ordering::Equal);
        assert_eq!(dec("0.5").cmp(&dec("0.50")), Ordering::Equal); // 0.50 == 0.5
        assert_eq!(dec("0.5").cmp(&dec("0.6")), Ordering::Less);
        assert_eq!(dec("2.5").cmp(&dec("10.0")), Ordering::Less); // different decades
        assert_eq!(dec("99.0").cmp(&dec("10.0")), Ordering::Greater); // same decade tie-break
        assert_eq!(dec("-3.14").cmp(&dec("3.14")), Ordering::Less);
        assert_eq!(dec("-3.14").cmp(&dec("-2.0")), Ordering::Less);
        assert_eq!(dec("0.0").cmp(&dec("0.5")), Ordering::Less);
        assert_eq!(dec("0.0").cmp(&dec("-0.5")), Ordering::Greater);
        // value equality across sorts is the caller's job (Num); here both are decimals.
        assert_eq!(int(2).cmp(&dec("2.0")), Ordering::Equal);
    }

    // ------------------------------------------------------------------- arithmetic --

    #[test]
    fn add_sub_align_scales() {
        assert_eq!(dec("1.5").add(&dec("2.5")).unwrap(), dec("4.0"));
        assert_eq!(dec("0.1").add(&dec("0.2")).unwrap(), dec("0.3")); // exact, unlike f64!
        assert_eq!(dec("3.14").add(&dec("0.001")).unwrap(), dec("3.141"));
        assert_eq!(dec("5.0").sub(&dec("0.5")).unwrap(), dec("4.5"));
        assert_eq!(dec("1.0").sub(&dec("1.0")).unwrap(), BigDecimal::zero());
        // mixed-scale add with an integer promoted in.
        assert_eq!(int(2).add(&dec("0.5")).unwrap(), dec("2.5"));
    }

    #[test]
    fn mul_adds_exponents() {
        assert_eq!(dec("1.5").mul(&dec("2.0")).unwrap(), dec("3.0"));
        assert_eq!(dec("0.1").mul(&dec("0.1")).unwrap(), dec("0.01"));
        assert_eq!(dec("2.5").mul(&int(4)).unwrap(), dec("10.0"));
        assert_eq!(
            dec("3.14").mul(&BigDecimal::zero()).unwrap(),
            BigDecimal::zero()
        );
    }

    #[test]
    fn mul_rejects_canonicalization_exponent_boundary() {
        // #475: both operands decode (the exponent SUM = i128::MAX is in band), but the
        // product mantissa 2*5 = 10 carries one trailing zero, so the canonical exponent
        // wants i128::MAX + 1 — out of the i128 scale band. The checked canonicalization
        // rejects rather than saturating to i128::MAX (which would lower to a decimal term
        // go/ts reject on re-decode — the divergence this pins). The div twin is the same
        // class (checked_sub + canonicalization).
        let two_at_max = unchecked(2, i128::MAX);
        let five = int(5);
        assert!(
            two_at_max.mul(&five).is_err(),
            "the i128::MAX+1 canonicalization boundary must be rejected, not saturated"
        );
        // ⚠ NARROWED BY #1022, DELIBERATELY — this assertion used to read:
        //
        //     let two_below = from_parts(2, i128::MAX - 1); // 2*5 = 10 → exponent i128::MAX
        //     assert_eq!(two_below.mul(&five).unwrap(), from_parts(1, i128::MAX));
        //
        // i.e. "a product that stays in band still succeeds", where BAND meant the `i128`
        // scale band. #1022 tightened the band: a product past MAX_DECIMAL_SCALE_SHIFT can
        // only be spelled scientifically, and the PARSER REFUSES THAT SPELLING — so logos
        // printed answers it could not read back. `mul` now caps at the scale bound, which
        // makes an exponent near `i128::MAX` unreachable through arithmetic by design.
        //
        // #475's invariant is UNTOUCHED and still asserted above: the boundary is REJECTED
        // rather than SATURATED. Only the second half — that a vast in-`i128` product is
        // permitted — is obsolete, and it is replaced rather than deleted so the narrowing
        // is visible to the next reader.
        let past = BigDecimal::from_parts(BigInt::from_i128(2), MAX_DECIMAL_EXPONENT).unwrap();
        assert!(
            past.mul(&five).is_err(),
            "a product past the SCALE bound must now be refused (#1022), not merely the              i128 boundary"
        );
        // The in-band case, at the tightened bound: a product that still round-trips succeeds.
        let two_below =
            BigDecimal::from_parts(BigInt::from_i128(2), MAX_DECIMAL_EXPONENT - 1).unwrap();
        // 2 * 5 = 10 → exponent (MAX - 1) + 1 = MAX, exactly at the inclusive bound.
        let prod = two_below.mul(&five).unwrap();
        assert_eq!(
            prod,
            BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT).unwrap(),
            "the bound itself must remain reachable — 1e65536 round-trips (measured)"
        );
    }

    #[test]
    fn div_rejects_canonicalization_exponent_boundary() {
        // #475 div twin: decimal(2, i128::MAX) / decimal(8, -3). Both operands decode; rs
        // rejects on the checked_sub of the exponent difference (e_a − e_b = i128::MAX + 3
        // overflows i128), while go/ts reach the canonicalization step (quotient 250 strips
        // to 25 at exponent i128::MAX + 1) — both now reject, so the `is`/comparison fails
        // tri-core. The pinned outcome is the same; only the rejection site differs.
        let two_at_max = unchecked(2, i128::MAX);
        let eighth = BigDecimal::from_parts(BigInt::from_i128(8), -3).unwrap();
        assert!(
            two_at_max.div_terminating(&eighth).is_err(),
            "the exponent-boundary division must be rejected, not saturated"
        );
    }

    #[test]
    fn div_terminating_succeeds_or_fails_exactly() {
        // Terminating quotients.
        assert_eq!(dec("1.0").div_terminating(&int(2)).unwrap(), dec("0.5"));
        assert_eq!(dec("1.0").div_terminating(&int(4)).unwrap(), dec("0.25"));
        assert_eq!(dec("1.0").div_terminating(&int(5)).unwrap(), dec("0.2"));
        assert_eq!(dec("10.0").div_terminating(&int(4)).unwrap(), dec("2.5"));
        assert_eq!(dec("3.0").div_terminating(&dec("1.5")).unwrap(), int(2)); // 2.0 → 2? no: stays decimal
        assert_eq!(
            dec("0.0").div_terminating(&int(3)).unwrap(),
            BigDecimal::zero()
        );
        // Non-terminating (denominator has a prime factor other than 2 and 5) → Err.
        assert!(dec("1.0").div_terminating(&int(3)).is_err());
        assert!(dec("1.0").div_terminating(&int(7)).is_err());
        assert!(dec("2.0").div_terminating(&int(6)).is_err()); // 1/3
                                                               // Division by zero → Err.
        assert!(dec("1.0").div_terminating(&BigDecimal::zero()).is_err());
    }

    #[test]
    fn div_terminating_result_canonicalizes_to_decimal() {
        // 3.0 / 1.5 == 2 exactly, but stays a DECIMAL value (2.0), distinct from int 2.
        let q = dec("3.0").div_terminating(&dec("1.5")).unwrap();
        assert_eq!(q.to_decimal_string(), "2.0");
        assert_eq!(q, int(2)); // equal as BigDecimal (both decimal(2,0))
    }

    #[test]
    fn floor_div_truncates_toward_zero_over_decimals() {
        // // is the truncating quotient (toward zero), result an INTEGER count.
        let bi = |n: i128| BigInt::from_i128(n);
        assert_eq!(dec("7.5").div_trunc_int(&int(2)).unwrap(), bi(3)); // 3.75 -> 3
        assert_eq!(dec("7.5").div_trunc_int(&dec("2.5")).unwrap(), bi(3)); // exactly 3
                                                                           // Negative dividend: toward zero, NOT floor. -7.5/2 = -3.75 -> -3 (floor would be -4).
        assert_eq!(dec("-7.5").div_trunc_int(&int(2)).unwrap(), bi(-3));
        // Negative divisor: 7.5/-2 = -3.75 -> -3.
        assert_eq!(dec("7.5").div_trunc_int(&int(-2)).unwrap(), bi(-3));
        // int // dec and dec // int both align via scaled mantissas.
        assert_eq!(int(7).div_trunc_int(&dec("2.5")).unwrap(), bi(2)); // 2.8 -> 2
                                                                       // Zero dividend.
        assert_eq!(BigDecimal::zero().div_trunc_int(&int(3)).unwrap(), bi(0));
        // Zero divisor -> Err (mirrors the integer //).
        assert!(dec("5.0").div_trunc_int(&BigDecimal::zero()).is_err());
    }

    #[test]
    fn modulo_floored_over_decimals_is_exact_and_sign_follows_divisor() {
        // mod is the ISO floored remainder (sign of the divisor), result a DECIMAL.
        assert_eq!(
            dec("7.5").modulo_floored(&dec("0.25")).unwrap(),
            BigDecimal::zero()
        ); // exact
        assert_eq!(dec("7.5").modulo_floored(&int(2)).unwrap(), dec("1.5")); // 7.5 - 3*2
                                                                             // Negative dividend, positive divisor -> result onto the positive side (0.5).
        assert_eq!(dec("-7.5").modulo_floored(&int(2)).unwrap(), dec("0.5"));
        // Positive dividend, negative divisor -> result onto the negative side (-0.5).
        assert_eq!(dec("7.5").modulo_floored(&int(-2)).unwrap(), dec("-0.5"));
        // Both negative.
        assert_eq!(dec("-7.5").modulo_floored(&int(-2)).unwrap(), dec("-1.5"));
        // The decimal identity x mod y == x - floor(x/y)*y holds (here floor(7.5/0.25)=30).
        assert_eq!(
            dec("7.5")
                .sub(
                    &dec("0.25")
                        .mul(&BigDecimal::from_bigint(BigInt::from_i128(30)))
                        .unwrap()
                )
                .unwrap(),
            dec("7.5").modulo_floored(&dec("0.25")).unwrap()
        );
        // Zero divisor -> Err (mirrors the integer mod).
        assert!(dec("5.0").modulo_floored(&BigDecimal::zero()).is_err());
    }

    #[test]
    fn floor_div_and_mod_refuse_an_adversarial_scale_gap() {
        // A vast exponent gap would need a giant scaling integer; fail fail-soft, like add.
        // #2679: both operands are IN the value domain and their GAP still exceeds the
        // alignment limit, which is why the two constants are different quantities.
        let huge = BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT).unwrap();
        let tenth = dec("0.1");
        assert!(huge.div_trunc_int(&tenth).is_err());
        assert!(huge.modulo_floored(&tenth).is_err());
    }

    #[test]
    fn add_refuses_an_alignment_gap_that_overflows_i128_1264() {
        // Two values near opposite i128 extremes make the alignment gap exceed i128. Since
        // #2679 neither is in the value domain, so only this module can build them: the
        // checked subtraction is defence in depth, and this pins that it still refuses.
        // Pre-fix this PANICS in debug (attempt to subtract with overflow) at the shift
        // computation — the fuzz crash of stress-nightly run 33239317295
        // (crash-a6ca2512…). Post-fix it is the documented refusal, like any over-bound
        // gap. Exercises BOTH aligners: `add` and (via `div_trunc_int`)
        // `aligned_mantissas`, which carried the identical unchecked subtraction.
        let hi = unchecked(3, i128::MAX - 3);
        let lo = unchecked(7, i128::MIN + 3);
        for (a, b) in [(&hi, &lo), (&lo, &hi)] {
            let err = a
                .add(b)
                .expect_err("an i128-overflowing gap must refuse, not panic");
            // #3126: the refusal is the alignment WORK CAP, which the evaluator reports as not
            // decided, never a domain failure.
            assert_eq!(err, DecimalError::AlignmentCap, "wrong refusal: {err}");
            let err = a
                .div_trunc_int(b)
                .expect_err("aligned_mantissas must refuse the same gap");
            assert_eq!(err, DecimalError::AlignmentCap, "wrong refusal: {err}");
        }
    }

    #[test]
    fn mul_refuses_an_over_scale_product_1022() {
        // #1022. `add`/`sub` refuse a scale past MAX_DECIMAL_SCALE_SHIFT; `mul` did not, so
        // ORDINARY ARITHMETIC could mint a value only the SCIENTIFIC renderer can spell — and
        // the parser refuses that spelling back (`parse.rs`: "out-of-range scale: keep the
        // opaque atom"). The product came back as an ATOM, so `X is <that> + 0` yielded no
        // solutions at exit 0: logos printing an answer it cannot read.
        //
        // The renderer's own cap test says "the parser caps literals long before this, so this
        // guards the construct-a-term-directly path" — `mul` was the path that reached it from
        // arithmetic, which is why the fallback stopped being defence-in-depth and became a lie.
        let half = MAX_DECIMAL_EXPONENT / 2 + 1; // two of these exceed the bound
        let a = BigDecimal::from_parts(BigInt::from_i128(1), half).unwrap();
        assert!(
            a.mul(&a).is_err(),
            "a product whose scale exceeds MAX_DECIMAL_SCALE_SHIFT must be refused, not minted              into a form the parser rejects"
        );

        // ⭐ The BOUNDARY, both sides — a cap that refuses everything is not a cap.
        let at = BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT).unwrap();
        let one = BigDecimal::from_parts(BigInt::from_i128(1), 0).unwrap();
        assert!(
            at.mul(&one).is_ok(),
            "EXACTLY at the bound must still multiply — 1e65536 round-trips (measured)"
        );
        // One past the bound is not constructible at all (#2679); an in-process one still
        // refuses to multiply, because the product returns through the same constructor.
        assert!(BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT + 1).is_none());
        assert!(
            unchecked(1, MAX_DECIMAL_EXPONENT + 1).mul(&one).is_err(),
            "one past the bound must refuse"
        );

        // The NEGATIVE scale direction too: the renderer materializes leading zeros there.
        let neg = BigDecimal::from_parts(BigInt::from_i128(1), -half).unwrap();
        assert!(
            neg.mul(&neg).is_err(),
            "an over-scale NEGATIVE product must refuse too"
        );
    }

    #[test]
    fn mul_output_always_round_trips_1022() {
        // The doc contract on `to_decimal_string` — "round-trips through from_decimal_str" —
        // as an executable property over `mul`, the op that falsified it.
        //
        // ⛔ THE FIRST VERSION OF THIS TEST PASSED BEFORE THE FIX AND WAS THEREFORE USELESS.
        // Every case multiplied by 1e0 with exponents under the bound, so no product ever
        // reached the scientific fallback — the property held vacuously, and its anti-vacuity
        // guard counted CASES THAT RAN rather than cases that REACHED THE SUBJECT. That is
        // this repo's form 33 inside a test written to catch form-33-shaped bugs.
        //
        // The discriminating case is a product whose scale EXCEEDS the bound: pre-fix `mul`
        // mints it and the renderer spells it scientifically; `from_decimal_str` then refuses
        // that spelling, which is the whole defect. Post-fix `mul` refuses and there is
        // nothing to render.
        let one = BigDecimal::from_parts(BigInt::from_i128(1), 0).unwrap();
        let half = MAX_DECIMAL_SCALE_SHIFT / 2 + 1;
        let over = BigDecimal::from_parts(BigInt::from_i128(1), half).unwrap();

        // THE case the defect lives in. Small exponents keep this fast: the fixed-point
        // renderer materializes |exponent| zeros, so a 30000-scale case cost 16 MINUTES.
        let mut reached_the_subject = false;
        if let Ok(prod) = over.mul(&over) {
            reached_the_subject = true; // pre-fix: mul minted an over-scale product
            let spelling = prod.to_decimal_string();
            assert!(
                BigDecimal::from_decimal_str(&spelling).is_some(),
                "mul minted {spelling}, which from_decimal_str CANNOT READ — logos would print                  an answer it cannot read back (#1022)"
            );
        }
        assert!(
            !reached_the_subject,
            "mul must refuse an over-scale product outright (post-fix this branch is unreachable)"
        );

        // ⭐ And the in-band control: products WITHIN the bound must still round-trip, or a cap
        // that refuses everything would satisfy the assertion above while breaking arithmetic.
        let mut checked = 0usize;
        for (m, e) in [(1i128, 10i128), (7, -12), (3, 64)] {
            let a = BigDecimal::from_parts(BigInt::from_i128(m), e).unwrap();
            let prod = a.mul(&one).expect("an in-band product must not be refused");
            let spelling = prod.to_decimal_string();
            let back = BigDecimal::from_decimal_str(&spelling)
                .unwrap_or_else(|| panic!("in-band product {spelling} did not read back"));
            assert_eq!(back, prod, "round-trip changed the value: {spelling}");
            checked += 1;
        }
        assert_eq!(
            checked, 3,
            "the in-band control must exercise all three cases"
        );
    }

    #[test]
    fn add_refuses_an_adversarial_scale_gap() {
        // A gap past MAX_DECIMAL_SCALE_SHIFT would need to materialize a vast integer; it fails
        // fail-soft instead (the goal fails, never a panic / OOM). Both operands are IN the
        // value domain (#2679): the alignment limit is a separate quantity and still binds.
        let huge = BigDecimal::from_parts(BigInt::from_i128(1), MAX_DECIMAL_EXPONENT).unwrap();
        assert!(huge.add(&dec("0.1")).is_err());
        // A gap within the bound is fine.
        let ok = BigDecimal::from_parts(BigInt::from_i128(1), -8).unwrap();
        assert!(int(1).add(&ok).is_ok());
    }

    #[test]
    fn unbounded_mantissa_is_supported() {
        // A 40-digit fractional part — mantissa far beyond i128, exponent small. The
        // value bridge round-trips it (unbounded mantissa, like BigInt).
        let s = format!("1.{}", "1".repeat(40));
        let d = dec(&s);
        assert_eq!(d.to_decimal_string(), s);
        assert_eq!(BigDecimal::from_decimal_term(&d.to_decimal_term()), Some(d));
    }
}

#[cfg(test)]
mod banded_round_trip_1264 {
    use super::tests::{int, unchecked};
    use super::*;

    /// ⭐ THE BANDED `to_decimal_string` CONTRACT, AS TWO SEPARATE CLAIMS (#1264).
    ///
    /// The old fuzz assertion was ONE unconditional claim — *"`to_decimal_string` round-trips
    /// through `from_decimal_str`"* — and it had been false BY DESIGN since #470. Two
    /// deliberate decisions jointly falsify it: the renderer spells a past-band value
    /// scientifically (bounded materialization), and `from_decimal_str` accepts only
    /// fixed-point `<digits>.<digits>` (matching the lexer's number rule). The ASSERTION was
    /// the defective artifact; the renderer stays TOTAL.
    ///
    /// ⛔ **ANTI-VACUITY, and it is the whole reason this test exists rather than just the
    /// fuzz split.** A property split into two arms passes trivially if one arm is never
    /// reached — and the nightly would go GREEN for the wrong reason, which is worse than the
    /// red it replaced, because a red at least tells the truth. So this counts cases that
    /// **REACH EACH BAND**, not cases that ran. That distinction is exactly what
    /// `mul_output_always_round_trips_1022` records getting wrong the first time: *"its
    /// anti-vacuity guard counted CASES THAT RAN rather than cases that REACHED THE SUBJECT."*
    #[test]
    fn to_decimal_string_is_banded_and_both_bands_are_reached() {
        let mut reached_in_band = 0usize;
        let mut reached_past_band = 0usize;

        // ---- IN-BAND: every value the parser admits. Fixed-point, exact round-trip. ----
        // Includes the bound ITSELF (65536), which is in-band — the edge is at bound+1.
        for (m, e) in [
            (7i128, 0i128),
            (7, 10),
            (314, -2),
            (5, -1),
            (1, -3),
            (-42, 3),
            (7, MAX_DECIMAL_EXPONENT),
            (7, -MAX_DECIMAL_EXPONENT),
        ] {
            let Some(v) = BigDecimal::from_parts(BigInt::from_i128(m), e) else {
                continue;
            };
            let s = v.to_decimal_string();
            assert!(
                s.contains('.') && !s.contains('e'),
                "in-band ({m}, {e}) must render FIXED-POINT carrying a '.'; got {s:?}"
            );
            assert_eq!(
                BigDecimal::from_decimal_str(&s).as_ref(),
                Some(&v),
                "in-band ({m}, {e}) must round-trip EXACTLY through from_decimal_str"
            );
            reached_in_band += 1;
        }

        // ---- PAST-BAND: no public constructor builds one and the decode refuses it (#2679);
        // only this module can, and the renderer stays TOTAL over it. ----
        // Scientific spelling AND deliberately NOT from_decimal_str-readable. Both signs,
        // because the renderer materializes leading zeros in the negative direction and a
        // one-sided test would miss a regression there.
        for (m, e) in [
            (7i128, MAX_DECIMAL_EXPONENT + 1),
            (7, -(MAX_DECIMAL_EXPONENT + 1)),
            (-3, MAX_DECIMAL_EXPONENT + 12345),
        ] {
            assert!(
                BigDecimal::from_parts(BigInt::from_i128(m), e).is_none(),
                "past-band ({m}, {e}) must not be constructible (#2679)"
            );
            let v = unchecked(m, e);
            let s = v.to_decimal_string();
            assert!(
                s.contains('e'),
                "past-band ({m}, {e}) must render the SCIENTIFIC spelling; got {s:?}"
            );
            assert!(
                BigDecimal::from_decimal_str(&s).is_none(),
                "past-band spelling {s:?} must NOT be from_decimal_str-readable — it is                  PRINT-ONLY by design (#470), and a reader that accepts it would reinstate                  the unbounded materialization the band exists to prevent"
            );
            reached_past_band += 1;
        }

        // ---- THE ANTI-VACUITY GUARD. Both arms must have been REACHED. ----
        assert!(
            reached_in_band > 0,
            "VACUOUS: no in-band case was reached — the round-trip claim asserted nothing"
        );
        assert!(
            reached_past_band > 0,
            "VACUOUS: no past-band case was reached — the scientific/print-only claim              asserted nothing, and this test would pass while the band went unexercised"
        );
    }

    /// The EDGE, pinned separately: the bound itself is IN-band and bound+1 is PAST it.
    ///
    /// Kept apart from the test above on purpose — that one proves both bands are reached,
    /// this one proves they are separated **where the contract says**. A single off-by-one in
    /// the renderer's comparison would leave both arms reachable and both counts non-zero,
    /// so the anti-vacuity guard cannot see it.
    #[test]
    fn the_band_edge_is_exactly_max_decimal_exponent() {
        let at = BigDecimal::from_parts(BigInt::from_i128(7), MAX_DECIMAL_EXPONENT)
            .expect("the bound itself must be constructible");
        assert!(
            !at.to_decimal_string().contains('e'),
            "EXACTLY at the bound is IN-band — it must still render fixed-point"
        );

        // #2679 REVERSES #1264's "past-band is constructible": the band is the value DOMAIN
        // now, a construction boundary, and the renderer's past-band arm is its totality.
        assert!(
            BigDecimal::from_parts(BigInt::from_i128(7), MAX_DECIMAL_EXPONENT + 1).is_none(),
            "one past the bound must NOT be constructible"
        );
        let past = unchecked(7, MAX_DECIMAL_EXPONENT + 1);
        assert!(
            past.to_decimal_string().contains('e'),
            "one past the bound is PAST-band — it must render scientifically"
        );
    }

    /// #2679: every decimal-producing path returns through the one constructor, so each refuses
    /// a past-band result and answers at the bound. A check that refuses everything is not a
    /// check, so every row has its in-domain control.
    #[test]
    fn every_producer_refuses_a_past_band_result_and_answers_at_the_bound_2679() {
        let e = |m: i128, x: i128| BigDecimal::from_parts(BigInt::from_i128(m), x).unwrap();
        // `/`: 1e40000 / 1e-40000 was decimal(1, 80000), check-accepted, and undecodable.
        assert!(e(1, 40000).div_terminating(&e(1, -40000)).is_err());
        assert_eq!(
            e(1, 30000).div_terminating(&e(1, -30000)).unwrap(),
            e(1, 60000)
        );
        assert_eq!(
            e(1, 32768).div_terminating(&e(1, -32768)).unwrap(),
            e(1, MAX_DECIMAL_EXPONENT)
        );
        // `*`, as #1022 had it, now through the same constructor.
        assert!(e(1, 40000).mul(&e(1, 40000)).is_err());
        assert_eq!(
            e(1, 32768).mul(&e(1, 32768)).unwrap(),
            e(1, MAX_DECIMAL_EXPONENT)
        );
        // The text parser: `0.` then 65,536 zeros then `1` is exponent -65537.
        let past = format!("0.{}1", "0".repeat(MAX_DECIMAL_EXPONENT as usize));
        assert_eq!(BigDecimal::from_decimal_str(&past), None);
        let at = format!("0.{}1", "0".repeat(MAX_DECIMAL_EXPONENT as usize - 1));
        assert_eq!(
            BigDecimal::from_decimal_str(&at),
            Some(e(1, -MAX_DECIMAL_EXPONENT))
        );
        // Trailing zeros are stripped first, so a long spelling of an in-domain value parses.
        let padded = format!("1.{}", "0".repeat(MAX_DECIMAL_EXPONENT as usize + 10));
        assert_eq!(BigDecimal::from_decimal_str(&padded), Some(int(1)));
    }

    /// #2679: a promoted integer is an operand, so it is canonicalized WITHOUT the domain check
    /// (it must still compare), and `add`'s zero short-circuit, which hands an operand back,
    /// returns through the constructor like every other result.
    ///
    /// `unchecked(1, MAX + 1)` stands in for `from_bigint(10^65537)`, which canonicalizes to exactly
    /// that value: building the real integer would strip 65,537 trailing zeros one bignum division
    /// at a time (quadratic, #1264), minutes of test time for the same subject.
    #[test]
    fn a_promoted_integer_past_the_domain_is_never_returned_as_a_decimal_2679() {
        let big = unchecked(1, MAX_DECIMAL_EXPONENT + 1);
        assert!(big > int(1), "it still compares");
        assert!(BigDecimal::zero().add(&big).is_err());
        assert!(big.add(&BigDecimal::zero()).is_err());
        let at = unchecked(1, MAX_DECIMAL_EXPONENT);
        assert!(
            BigDecimal::zero().add(&at).is_ok(),
            "at the bound it is a value"
        );
        // The promotion itself does not check: a small integer promotes as before.
        assert_eq!(BigDecimal::from_bigint(BigInt::pow10(3)), unchecked(1, 3));
    }
}
