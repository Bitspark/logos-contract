//! Exact integers over the **frozen `ontos/data` `int` embedding** — the Stage-B
//! numeric domain (plan 0001 §1.3).
//!
//! plexis evaluated arithmetic in `f64` (`lib/log/builtins` `eval_arith`). That is
//! deliberately **not** ported: the §1.3 prize is *structural* value equality, and
//! `f64` breaks it (`0.1 + 0.2 ≠ 0.3`, `NaN ≠ NaN`, multiple spellings of one
//! value). Instead the checkable arithmetic theory ([`crate::arithmetic`]) and the
//! search-side arithmetic builtins (`logos_core::builtins`) evaluate over an
//! **exact, unbounded integer** whose ground form *is* the frozen ontos/data `int`
//! datum — so two arithmetically-equal results are the *same* term, byte-for-byte.
//!
//! ## The embedding ([`ontos-data §5.1`], byte form FROZEN v1)
//!
//! The `int` **byte form is owned by the `ontos-data` crate** (the single source of
//! the §5.1 embedding, shared with every other ontos consumer). This module's
//! `Value` bridge — [`BigInt::to_int_term`]/[`BigInt::from_int_term`] — delegates to
//! `ontos_data::encode_int`/`ontos_data::read_int` for every value in the `i128`
//! range, so the canonical bytes are byte-identical across implementations. logos
//! keeps only the *arithmetic* (add/sub/mul/div/mod, ordering) and the *unbounded*
//! domain: a magnitude beyond `i128` is still a well-formed `int` at L0, decoded /
//! lowered via the direct sign-magnitude payload below, which reproduces the same
//! §5.1 bytes ontos-data would emit over an unbounded host type.
//!
//! An integer `n` is the labeled compound
//! `Tuple(Atom("int"), Atom(<payload>))`, where the **payload** is one **sign
//! byte** (`0x00` non-negative, `0x01` negative) followed by the **big-endian,
//! minimal-length magnitude** (most-significant byte first, *no* leading `0x00`):
//!
//! | integer | payload bytes |
//! |---|---|
//! | `0`   | `00`        (sign `00`, empty magnitude — there is no negative zero) |
//! | `1`   | `00 01`     |
//! | `-1`  | `01 01`     |
//! | `255` | `00 ff`     |
//! | `256` | `00 01 00`  |
//!
//! This gives **one spelling per integer**. A payload with a leading-`0x00`
//! magnitude byte, or a `0x01` (negative) sign with an empty magnitude
//! (negative zero), is **non-canonical**: it is a perfectly valid term but **not** a
//! well-formed `int`, so [`BigInt::from_int_term`] rejects it (`None`). Every
//! `BigInt` this module *produces* is canonical by construction
//! ([`BigInt::to_int_term`]), so the search ⇄ check round-trip is exact.
//!
//! ## Why a hand-rolled bignum (no `num-bigint`)
//!
//! The integer is **unbounded in principle** (the spec: "not bounded to 64-bit"),
//! so a fixed-width `i64`/`i128` working type would either overflow — forbidden
//! here: ADR 0004 is *fail-loud over silent wrap* — or have to reject large but
//! perfectly valid `int` data. Widening to a real bignum is the right answer, and
//! pulling a third-party crate into a *trust kernel* is a cost we avoid for ~300
//! lines of schoolbook sign-magnitude arithmetic that operates **directly on the
//! frozen payload's magnitude bytes** (big-endian, base-256). The operations are
//! total and allocate-bounded by operand size; there is no recursion (so no
//! stack-depth concern on untrusted input) and no `unsafe`.
//!
//! [`ontos-data §5.1`]: the embedding is pinned in `ontos/docs/spec/ontos-data.md`
//! and exercised by `ontos/vectors/data.json` (`int_0`, `int_1`, `int_neg1`,
//! `int_255`, `int_256`).

use std::cmp::Ordering;

use crate::Term;

/// The functor label of the ontos/data `int` embedding: `int(Atom(payload))`.
const INT_LABEL: &[u8] = b"int";

/// Extract the raw payload bytes of a `Tuple(Atom("int"), Atom(payload))` term, or
/// `None` if the term is not that shape. Used only on the unbounded fallback path,
/// after `ontos_data::read_int` has already confirmed the term is a *canonical*
/// `int` whose magnitude merely exceeds `i128`.
fn int_payload_bytes(term: &Term) -> Option<&[u8]> {
    let Term::Tuple(children) = term else {
        return None;
    };
    let [Term::Atom(label), Term::Atom(payload)] = children.as_slice() else {
        return None;
    };
    (label.as_slice() == INT_LABEL).then_some(payload.as_slice())
}

// ---------------------------------------------------------------------------
// BigInt — an exact, unbounded, sign-magnitude integer
// ---------------------------------------------------------------------------
// #region bigint

/// An exact integer of unbounded magnitude, stored in **sign-magnitude** form to
/// mirror the frozen ontos/data `int` payload directly.
///
/// Invariant (canonical, enforced by every constructor and operation): `magnitude`
/// is **big-endian** (most-significant byte first) with **no leading `0x00`
/// bytes**, and **zero is the empty magnitude with `negative == false`** — there is
/// no negative zero. Two `BigInt`s are equal iff they denote the same integer,
/// which (given the invariant) is iff their fields are equal — so the derived
/// `PartialEq`/`Eq` is exact arithmetic equality, the hand-written [`Ord`] is
/// consistent with it (`a == b ⟺ a.cmp(b) == Equal`), and the lowered [`Term`] is
/// unique per value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt {
    /// `true` iff the value is strictly negative. Always `false` for zero.
    negative: bool,
    /// `|value|` big-endian, leading-zero-stripped. Empty ⟺ the value is zero.
    magnitude: Vec<u8>,
}

impl BigInt {
    /// The integer zero (`negative = false`, empty magnitude).
    pub fn zero() -> Self {
        BigInt {
            negative: false,
            magnitude: Vec::new(),
        }
    }

    /// Construct from a sign and an arbitrary big-endian magnitude, **canonicalizing**:
    /// strips leading `0x00` bytes and forces a zero magnitude to be non-negative.
    fn from_sign_magnitude(negative: bool, magnitude: &[u8]) -> Self {
        let start = magnitude
            .iter()
            .position(|&b| b != 0)
            .unwrap_or(magnitude.len());
        let trimmed = &magnitude[start..];
        if trimmed.is_empty() {
            BigInt::zero()
        } else {
            BigInt {
                negative,
                magnitude: trimmed.to_vec(),
            }
        }
    }

    /// Build from a host `i128` (used by tests and small literals). Exact — `i128`
    /// always fits the unbounded magnitude.
    pub fn from_i128(value: i128) -> Self {
        if value == 0 {
            return BigInt::zero();
        }
        let negative = value < 0;
        // unsigned_abs avoids the `-i128::MIN` overflow trap.
        let magnitude = value.unsigned_abs().to_be_bytes();
        BigInt::from_sign_magnitude(negative, &magnitude)
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        self.magnitude.is_empty()
    }

    /// Whether the value is strictly negative.
    pub fn is_negative(&self) -> bool {
        self.negative
    }

    /// `|self|` — the non-negative value of the same magnitude.
    pub fn abs(&self) -> Self {
        BigInt {
            negative: false,
            magnitude: self.magnitude.clone(),
        }
    }

    /// `-self` (negation). Zero negates to itself (no negative zero).
    pub fn negate(&self) -> Self {
        if self.is_zero() {
            BigInt::zero()
        } else {
            BigInt {
                negative: !self.negative,
                magnitude: self.magnitude.clone(),
            }
        }
    }

    /// `self + other` (exact).
    pub fn add(&self, other: &Self) -> Self {
        if self.negative == other.negative {
            // Same sign: add magnitudes, keep the sign.
            BigInt::from_sign_magnitude(
                self.negative,
                &add_magnitude(&self.magnitude, &other.magnitude),
            )
        } else {
            // Opposite signs: subtract the smaller magnitude from the larger; the
            // result takes the sign of the larger-magnitude operand.
            match cmp_magnitude(&self.magnitude, &other.magnitude) {
                Ordering::Equal => BigInt::zero(),
                Ordering::Greater => BigInt::from_sign_magnitude(
                    self.negative,
                    &sub_magnitude(&self.magnitude, &other.magnitude),
                ),
                Ordering::Less => BigInt::from_sign_magnitude(
                    other.negative,
                    &sub_magnitude(&other.magnitude, &self.magnitude),
                ),
            }
        }
    }

    /// `self - other` (exact).
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.negate())
    }

    /// `self * other` (exact).
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return BigInt::zero();
        }
        let negative = self.negative != other.negative;
        BigInt::from_sign_magnitude(negative, &mul_magnitude(&self.magnitude, &other.magnitude))
    }

    /// Truncating integer division `self // other` and remainder `self mod other`,
    /// as the pair `(quotient, remainder)` — **`None` if `other` is zero**.
    ///
    /// This is **truncation toward zero** (Prolog `//` and the C-family `/`),
    /// matching plexis's `(a / b).trunc()`: the quotient drops the fractional part
    /// and the remainder takes the **sign of the dividend** (`self`), so the
    /// identity `quotient * other + remainder == self` holds. (`mod/2` below is the
    /// *separate* floored-modulo operation, per ISO Prolog, which can differ in sign
    /// from this remainder.)
    pub fn div_rem_trunc(&self, other: &Self) -> Option<(Self, Self)> {
        if other.is_zero() {
            return None;
        }
        let (q_mag, r_mag) = divmod_magnitude(&self.magnitude, &other.magnitude);
        // Quotient sign = XOR of operand signs; remainder sign = dividend sign.
        let quotient = BigInt::from_sign_magnitude(self.negative != other.negative, &q_mag);
        let remainder = BigInt::from_sign_magnitude(self.negative, &r_mag);
        Some((quotient, remainder))
    }

    /// **Exact** division `self / other`: the quotient **iff** `other` divides `self`
    /// evenly. Returns `None` on a zero divisor *or* a non-zero remainder — there is no
    /// fractional integer, so an inexact division is a domain error the caller maps to
    /// goal failure (never a silent truncation, never a float).
    ///
    /// This is the exact-integer analog of plexis's float `/` operator (`vals[0] /
    /// vals[1]`). plexis evaluated in `f64`, so `7 / 2` was `3.5`; here the domain is
    /// the exact `ontos/data` integer, which has no `3.5`, so `7 / 2` **fails** rather
    /// than fabricate a value or truncate (truncation is the *separate* `//` operator,
    /// [`div_rem_trunc`](Self::div_rem_trunc)). `6 / 3` → `2`; `7 / 2` → `None`.
    pub fn div_exact(&self, other: &Self) -> Option<Self> {
        let (quotient, remainder) = self.div_rem_trunc(other)?;
        remainder.is_zero().then_some(quotient)
    }

    /// ISO Prolog `mod/2` — the **floored** modulo, whose result takes the sign of
    /// the **divisor** (`other`). `None` if `other` is zero.
    ///
    /// plexis computed `a % b` in `f64`, which is C-style *truncated* remainder
    /// (sign of the dividend). That contradicts ISO Prolog, where `mod` is floored:
    /// `(-7) mod 3 =:= 2`, `7 mod (-3) =:= -2`. We implement the ISO semantics (the
    /// frozen account is exact-integer, so we follow the standard rather than
    /// replicate the f64 quirk). The companion truncated remainder is available via
    /// [`div_rem_trunc`](Self::div_rem_trunc).
    pub fn modulo_floored(&self, other: &Self) -> Option<Self> {
        let (_q, rem) = self.div_rem_trunc(other)?;
        // Truncated remainder `rem` has the sign of the dividend. Floored modulo
        // differs from it exactly when `rem` is non-zero and its sign differs from
        // the divisor's: then add the divisor to bring it onto the divisor's side.
        if !rem.is_zero() && rem.negative != other.negative {
            Some(rem.add(other))
        } else {
            Some(rem)
        }
    }

    /// `10^exp` as an exact non-negative integer (`exp` a host `usize`). Used by the
    /// decimal value type ([`crate::decval`]) to align scales (`+`/`−`) and to clear a
    /// terminating-division denominator to a power of ten. `exp` is bounded by the
    /// caller (a decimal scale / digit count), so the `O(exp)` multiply chain is bounded.
    pub fn pow10(exp: usize) -> Self {
        let ten = BigInt::from_i128(10);
        let mut acc = BigInt::from_i128(1);
        for _ in 0..exp {
            acc = acc.mul(&ten);
        }
        acc
    }

    // (`min`/`max` come from the [`Ord`] impl below — `a.clone().min(b.clone())`.)

    // -------------------------------------------------------------------- embedding
    //
    // The `int` *byte form* is owned by `ontos-data` (the frozen §5.1 embedding):
    // [`to_int_term`](Self::to_int_term)/[`from_int_term`](Self::from_int_term) are
    // the `Value` bridge and delegate to `ontos_data::{encode_int,read_int}` for
    // every value in the `i128` range — guaranteeing byte-identity with every other
    // ontos consumer. logos keeps its own *arithmetic* (add/sub/mul/div/mod above)
    // and its own *unbounded* domain: a magnitude beyond `i128` is still a
    // well-formed `int` at L0, so for that boundary we fall back to the direct
    // sign-magnitude form below — which reproduces the same §5.1 bytes ontos-data
    // would emit if it had an unbounded host type (the `i128` cases above prove the
    // two forms agree).

    /// Materialize as a host `i128`, or `None` if `|self|` exceeds the `i128` range.
    /// Drives `ontos_data::encode_int` for the in-range path and gates the unbounded
    /// fallback (`None` ⟺ the magnitude is beyond `i128`). `pub` so the decimal value
    /// type ([`crate::decval`]) can narrow a decimal's `exponent` child to the bounded
    /// `i128` scale (the §331 scale bound).
    pub fn to_i128(&self) -> Option<i128> {
        if self.is_zero() {
            return Some(0);
        }
        // |i128::MIN| = 2^127 needs the full u128; reconstruct the magnitude there,
        // then map into i128 respecting the sign (so i128::MIN itself round-trips).
        if self.magnitude.len() > core::mem::size_of::<u128>() {
            return None;
        }
        let mut mag: u128 = 0;
        for &b in &self.magnitude {
            mag = (mag << 8) | u128::from(b);
        }
        if self.negative {
            match i128::try_from(mag) {
                Ok(pos) => Some(-pos),
                // mag == 2^127 is exactly i128::MIN; larger does not fit.
                Err(_) if mag == 1u128 << 127 => Some(i128::MIN),
                Err(_) => None,
            }
        } else {
            i128::try_from(mag).ok()
        }
    }

    /// The canonical **payload bytes** of the ontos/data `int` embedding: one sign
    /// byte (`0x00`/`0x01`) followed by the minimal big-endian magnitude. Zero is the
    /// single byte `0x00`.
    ///
    /// This is the direct sign-magnitude form. For values in the `i128` range it is
    /// byte-identical to the payload inside `ontos_data::encode_int` (the canonical
    /// `int` bytes are owned by ontos-data; this form is used only as the
    /// *unbounded* fallback for magnitudes beyond `i128`, plus by decimal/literal
    /// helpers and tests).
    pub fn to_payload(&self) -> Vec<u8> {
        let mut payload = Vec::with_capacity(self.magnitude.len() + 1);
        payload.push(if self.negative { 0x01 } else { 0x00 });
        payload.extend_from_slice(&self.magnitude);
        payload
    }

    /// Parse a `BigInt` from the **payload bytes** of an `int` embedding, enforcing
    /// canonicality. Returns `None` if the payload is empty, has an unknown sign
    /// byte, carries a leading-`0x00` magnitude byte (non-minimal), or is a negative
    /// zero (`0x01` with empty magnitude) — none of which is a well-formed `int`.
    ///
    /// Same canonicality contract as `ontos_data::read_int`; this unbounded decoder
    /// is the fallback used when `read_int` recognizes a canonical `int` whose
    /// magnitude exceeds `i128` (`DataError::IntOutOfRange`).
    pub fn from_payload(payload: &[u8]) -> Option<Self> {
        let (&sign, magnitude) = payload.split_first()?;
        let negative = match sign {
            0x00 => false,
            0x01 => true,
            _ => return None,
        };
        match magnitude.first() {
            // Empty magnitude: only canonical as non-negative zero (sign 0x00).
            None => {
                if negative {
                    None // negative zero is non-canonical
                } else {
                    Some(BigInt::zero())
                }
            }
            // Non-empty magnitude must be minimal: no leading 0x00.
            Some(0x00) => None,
            Some(_) => Some(BigInt {
                negative,
                magnitude: magnitude.to_vec(),
            }),
        }
    }

    /// Lower to the ground embedding term `Tuple(Atom("int"), Atom(payload))`. Always
    /// canonical, so equal integers lower to byte-identical terms (the §1.3 prize).
    ///
    /// In the `i128` range the canonical `Value` comes from `ontos_data::encode_int`
    /// (the single source of the `int` byte form); a magnitude beyond `i128` uses the
    /// direct sign-magnitude payload, which reproduces the same §5.1 bytes.
    pub fn to_int_term(&self) -> Term {
        match self.to_i128() {
            Some(n) => Term::from_value(&ontos_data::encode_int(n)),
            None => Term::tuple([
                Term::atom(INT_LABEL.to_vec()),
                Term::atom(self.to_payload()),
            ]),
        }
    }

    /// Recognize the ontos/data `int` embedding term and decode it. Returns `None`
    /// for any term that is not a *canonical* `int(Atom(payload))` compound — a
    /// non-`int` functor, the wrong arity, a non-atom payload, a non-canonical
    /// payload, or a non-ground term (it contains a `Var`). The term is **not**
    /// walked here; callers that may hold a variable should resolve it first.
    ///
    /// Recognition delegates to `ontos_data::read_int` for canonicality. A canonical
    /// `int` whose magnitude exceeds `i128` (`DataError::IntOutOfRange`) is still a
    /// well-formed unbounded integer, so it is decoded via the direct payload path
    /// rather than rejected — logos's domain is unbounded.
    pub fn from_int_term(term: &Term) -> Option<Self> {
        // #2275 layer 3: an `int(Atom(payload))` nests exactly 2 deep, so anything deeper is not
        // one. Checked BEFORE the erase: erasing a deep term builds a deep `ontos::Value`, whose
        // own `Drop` recurses per level (Bitspark/ontos#340), and a caller that tries this on every
        // node of a long list (the term writer) would also pay quadratic work.
        if !term.depth_le(2) {
            return None;
        }
        // Bridge to `ontos::Value`; a non-ground term (any `Var`) is not an `int`.
        let value = term.erase_ground()?;
        match ontos_data::read_int(&value) {
            Ok(n) => Some(BigInt::from_i128(n)),
            // Canonical but beyond i128: recover the unbounded value from the
            // (already shape- and canonicality-validated) payload bytes.
            Err(ontos_data::DataError::IntOutOfRange) => {
                let payload = int_payload_bytes(term)?;
                BigInt::from_payload(payload)
            }
            // Not a well-formed canonical `int`.
            Err(_) => None,
        }
    }

    /// Render as a base-10 string (sign then decimal digits). Used for diagnostics
    /// and tests; not on any hot path. `0` renders as `"0"`.
    pub fn to_decimal_string(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let digits = magnitude_to_decimal(&self.magnitude);
        if self.negative {
            format!("-{digits}")
        } else {
            digits
        }
    }

    /// Parse a base-10 integer from an ASCII digit string with an optional leading
    /// `-`/`+`. Returns `None` if the text is not a well-formed decimal integer
    /// (empty, contains a non-digit, or is just a sign). Leading zeros are accepted
    /// and normalized (`"007"` → `7`); `"-0"`/`"0"` → zero.
    pub fn from_decimal_str(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        let (negative, digits) = match bytes.first() {
            Some(b'-') => (true, &bytes[1..]),
            Some(b'+') => (false, &bytes[1..]),
            _ => (false, bytes),
        };
        if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
            return None;
        }
        let magnitude = decimal_to_magnitude(digits);
        Some(BigInt::from_sign_magnitude(negative, &magnitude))
    }
}

/// Total order consistent with integer order **and** with `PartialEq`
/// (`a == b ⟺ a.cmp(b) == Equal`, given the canonical-form invariant): negatives
/// sort before non-negatives, then by magnitude (a larger magnitude is more positive
/// among non-negatives, more negative among negatives).
impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => cmp_magnitude(&self.magnitude, &other.magnitude),
            // Both negative: the larger magnitude is the *smaller* number.
            (true, true) => cmp_magnitude(&other.magnitude, &self.magnitude),
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// #endregion
// ---------------------------------------------------------------------------
// Magnitude arithmetic — big-endian, base-256, leading-zero-stripped
// ---------------------------------------------------------------------------
// #region magnitude-ops
//
// Each helper takes/returns *magnitudes* (big-endian byte slices/vectors, possibly
// with leading zeros on output — callers canonicalize via `from_sign_magnitude`).
// Sign handling lives entirely in `BigInt` above; these are pure unsigned routines.

/// Compare two magnitudes as unsigned big-endian integers.
fn cmp_magnitude(a: &[u8], b: &[u8]) -> Ordering {
    // Strip leading zeros so length reflects the true bit-size.
    let a = strip_leading_zeros(a);
    let b = strip_leading_zeros(b);
    match a.len().cmp(&b.len()) {
        Ordering::Equal => a.cmp(b),
        non_eq @ (Ordering::Less | Ordering::Greater) => non_eq,
    }
}

/// Drop leading `0x00` bytes from a big-endian magnitude (borrowing).
fn strip_leading_zeros(a: &[u8]) -> &[u8] {
    let start = a.iter().position(|&b| b != 0).unwrap_or(a.len());
    &a[start..]
}

/// `a + b` for magnitudes (big-endian). Result may carry a new leading byte.
fn add_magnitude(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut carry = 0u16;
    // Walk least-significant first (from the back).
    let mut ia = a.len();
    let mut ib = b.len();
    while ia > 0 || ib > 0 || carry != 0 {
        let da = if ia > 0 {
            ia -= 1;
            a[ia] as u16
        } else {
            0
        };
        let db = if ib > 0 {
            ib -= 1;
            b[ib] as u16
        } else {
            0
        };
        let sum = da + db + carry;
        result.push((sum & 0xff) as u8);
        carry = sum >> 8;
    }
    result.reverse();
    result
}

/// `a - b` for magnitudes, **requiring `a >= b`** (the caller guarantees this by
/// comparing first). Big-endian in/out.
fn sub_magnitude(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(a.len());
    let mut borrow = 0i16;
    let mut ia = a.len();
    let mut ib = b.len();
    while ia > 0 {
        ia -= 1;
        let da = a[ia] as i16;
        let db = if ib > 0 {
            ib -= 1;
            b[ib] as i16
        } else {
            0
        };
        let mut diff = da - db - borrow;
        if diff < 0 {
            diff += 256;
            borrow = 1;
        } else {
            borrow = 0;
        }
        result.push(diff as u8);
    }
    // borrow must be 0 here because a >= b (precondition).
    result.reverse();
    result
}

/// `a * b` for magnitudes (schoolbook long multiplication). Big-endian in/out.
fn mul_magnitude(a: &[u8], b: &[u8]) -> Vec<u8> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    // Accumulate into a little-endian scratch buffer, then reverse.
    let mut acc = vec![0u32; a.len() + b.len()];
    for (i, &ai) in a.iter().rev().enumerate() {
        let mut carry = 0u32;
        for (j, &bj) in b.iter().rev().enumerate() {
            let idx = i + j;
            let cur = acc[idx] + ai as u32 * bj as u32 + carry;
            acc[idx] = cur & 0xff;
            carry = cur >> 8;
        }
        // Propagate the final carry into the next column.
        let mut k = i + b.len();
        while carry != 0 {
            let cur = acc[k] + carry;
            acc[k] = cur & 0xff;
            carry = cur >> 8;
            k += 1;
        }
    }
    let mut result: Vec<u8> = acc.iter().rev().map(|&d| d as u8).collect();
    // Strip the leading zeros introduced by the oversized scratch buffer.
    let start = result.iter().position(|&b| b != 0).unwrap_or(result.len());
    result.drain(..start);
    result
}

/// `(a / b, a % b)` for magnitudes via bit-by-bit long division (restoring).
/// **Requires `b` non-empty (non-zero)**; the caller checks. Big-endian in/out;
/// outputs are leading-zero-stripped.
fn divmod_magnitude(a: &[u8], b: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let a = strip_leading_zeros(a);
    let b = strip_leading_zeros(b);
    // a < b → quotient 0, remainder a.
    if cmp_magnitude(a, b) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    let total_bits = a.len() * 8;
    let mut quotient_bits = vec![false; total_bits];
    let mut remainder: Vec<u8> = Vec::new(); // big-endian, grows as we shift bits in
    for bit_index in 0..total_bits {
        // remainder = (remainder << 1) | next bit of a (from MSB to LSB).
        let byte = a[bit_index / 8];
        let bit = (byte >> (7 - (bit_index % 8))) & 1;
        shl1_with_bit(&mut remainder, bit);
        // If remainder >= b, subtract and set the quotient bit.
        if cmp_magnitude(&remainder, b) != Ordering::Less {
            remainder = sub_magnitude(&remainder, b);
            quotient_bits[bit_index] = true;
        }
    }
    (
        bits_to_magnitude(&quotient_bits),
        strip_leading_zeros(&remainder).to_vec(),
    )
}

/// `value = (value << 1) | bit`, big-endian, growing as needed.
fn shl1_with_bit(value: &mut Vec<u8>, bit: u8) {
    let mut carry = bit;
    for byte in value.iter_mut().rev() {
        let shifted = ((*byte as u16) << 1) | carry as u16;
        *byte = (shifted & 0xff) as u8;
        carry = (shifted >> 8) as u8;
    }
    if carry != 0 {
        value.insert(0, carry);
    }
}

/// Pack a big-endian bit vector (index 0 = most significant) into magnitude bytes.
fn bits_to_magnitude(bits: &[bool]) -> Vec<u8> {
    if bits.is_empty() {
        return Vec::new();
    }
    // Pad on the left so the length is a multiple of 8.
    let pad = (8 - bits.len() % 8) % 8;
    let mut bytes = Vec::with_capacity((bits.len() + pad) / 8);
    let mut acc = 0u8;
    let mut count = 0usize;
    for &bit in std::iter::repeat_n(&false, pad).chain(bits.iter()) {
        acc = (acc << 1) | bit as u8;
        count += 1;
        if count == 8 {
            bytes.push(acc);
            acc = 0;
            count = 0;
        }
    }
    bytes
}

// #endregion
// ---------------------------------------------------------------------------
// Decimal ⇄ magnitude (diagnostics + literal parsing; not a hot path)
// ---------------------------------------------------------------------------
// #region decimal

/// Convert an ASCII decimal digit string (no sign) into a minimal big-endian
/// magnitude, by Horner evaluation in base-256.
///
/// ## Why this is not `mul_magnitude` + `add_magnitude` in a loop (#1264)
///
/// The obvious form — `acc = mul_magnitude(&acc, &[10]); acc = add_magnitude(&acc, &[d])`
/// — is **quadratic with an enormous constant**: each digit allocates a fresh
/// `vec![0u32; len+1]` inside `mul_magnitude`, reverses it, then allocates and reverses
/// again inside `add_magnitude`. Four allocations and two reverses **per digit**.
///
/// This version keeps ONE little-endian accumulator and fuses multiply-and-add into a
/// single carry pass with **no allocation per step**, and consumes [`CHUNK_DIGITS`] digits
/// at a time rather than one:
///
/// ⭐ **Multiplying by a scalar that fits in a register costs `O(len)` whatever the
/// scalar's magnitude.** So folding 9 digits into one `u32` multiplier (`10^9 < 2^32`)
/// does the work of nine passes in one, at the same cost per pass. That is where the bulk
/// of the win comes from; the allocation removal is the rest.
///
/// ⚠ Still **O(n²)** in the digit count — that is inherent to the schoolbook multiply this
/// module uses, and making the parse subquadratic would require a subquadratic multiply
/// (Karatsuba or better), which is a much larger decision than this fix. See #1264.
fn decimal_to_magnitude(digits: &[u8]) -> Vec<u8> {
    /// Digits folded into one `u32` multiplier per pass. `10^9 < 2^32`, and the pass
    /// arithmetic below is done in `u64`, so `255 * 10^9 + carry` cannot overflow.
    const CHUNK_DIGITS: usize = 9;
    /// `POW10[k] == 10^k` for `k <= CHUNK_DIGITS`.
    const POW10: [u32; CHUNK_DIGITS + 1] = [
        1,
        10,
        100,
        1_000,
        10_000,
        100_000,
        1_000_000,
        10_000_000,
        100_000_000,
        1_000_000_000,
    ];

    // Little-endian while accumulating; reversed to big-endian once at the end.
    // log256(10) ≈ 0.4152, so 108/256 over-reserves slightly rather than reallocating.
    let mut acc: Vec<u8> = Vec::with_capacity(digits.len() * 108 / 256 + 2);
    let mut i = 0;
    while i < digits.len() {
        let take = core::cmp::min(CHUNK_DIGITS, digits.len() - i);
        let mut chunk = 0u32;
        for &d in &digits[i..i + take] {
            chunk = chunk * 10 + u32::from(d - b'0');
        }
        // acc = acc * 10^take + chunk, in one pass.
        let multiplier = u64::from(POW10[take]);
        let mut carry = u64::from(chunk);
        for byte in acc.iter_mut() {
            let cur = u64::from(*byte) * multiplier + carry;
            *byte = (cur & 0xff) as u8;
            carry = cur >> 8;
        }
        while carry != 0 {
            acc.push((carry & 0xff) as u8);
            carry >>= 8;
        }
        i += take;
    }
    acc.reverse();
    strip_leading_zeros(&acc).to_vec()
}

/// Convert a minimal big-endian magnitude into its base-10 digit string, by
/// repeated division by 10. The magnitude must be non-empty (zero is handled by the
/// caller).
fn magnitude_to_decimal(magnitude: &[u8]) -> String {
    let ten = [10u8];
    let mut digits_rev = Vec::new();
    let mut current = strip_leading_zeros(magnitude).to_vec();
    while !current.is_empty() {
        let (q, r) = divmod_magnitude(&current, &ten);
        let digit = r.last().copied().unwrap_or(0);
        digits_rev.push(b'0' + digit);
        current = q;
    }
    digits_rev.reverse();
    // Safe: every pushed byte is an ASCII digit.
    String::from_utf8(digits_rev).unwrap_or_default()
}

// #endregion

#[cfg(test)]
mod tests {
    use super::*;

    fn big(n: i128) -> BigInt {
        BigInt::from_i128(n)
    }

    // -------------------------------------------------------------- construction --

    #[test]
    fn zero_is_canonical_and_non_negative() {
        let z = BigInt::zero();
        assert!(z.is_zero());
        assert!(!z.is_negative());
        assert_eq!(z.to_payload(), vec![0x00]);
        // i128 zero and negate-of-zero are the same canonical zero.
        assert_eq!(big(0), z);
        assert_eq!(big(0).negate(), z);
    }

    #[test]
    fn from_i128_round_trips_through_decimal() {
        for n in [
            0i128,
            1,
            -1,
            7,
            -7,
            255,
            256,
            -256,
            1000,
            -1000,
            65535,
            65536,
            i64::MAX as i128,
            i64::MIN as i128,
            i128::MAX,
            i128::MIN,
        ] {
            assert_eq!(big(n).to_decimal_string(), n.to_string(), "n = {n}");
        }
    }

    // ----------------------------------------------------- frozen embedding bytes --

    #[test]
    fn payload_matches_frozen_ontos_data_vectors() {
        // From ontos/vectors/data.json (int_0, int_1, int_neg1, int_255, int_256).
        assert_eq!(big(0).to_payload(), vec![0x00]);
        assert_eq!(big(1).to_payload(), vec![0x00, 0x01]);
        assert_eq!(big(-1).to_payload(), vec![0x01, 0x01]);
        assert_eq!(big(255).to_payload(), vec![0x00, 0xff]);
        assert_eq!(big(256).to_payload(), vec![0x00, 0x01, 0x00]);
    }

    #[test]
    fn int_term_is_the_labeled_compound() {
        // 7 → int(Atom([0x00, 0x07])) — the boundary.rs embedding example.
        let seven = big(7).to_int_term();
        assert_eq!(
            seven,
            Term::tuple([Term::atom(b"int".to_vec()), Term::atom(vec![0x00, 0x07])])
        );
        assert_eq!(BigInt::from_int_term(&seven), Some(big(7)));
    }

    /// The `Value` bridge must agree byte-for-byte with `ontos_data::encode_int` for
    /// every in-range value — ontos-data owns the canonical `int` byte form, and
    /// `to_int_term` is exactly `Term::from_value(&encode_int(n))` on this range. This
    /// also pins that the kept direct payload (the unbounded fallback) reproduces the
    /// same §5.1 bytes (`to_payload` == the atom inside `encode_int`).
    #[test]
    fn int_term_is_byte_identical_to_ontos_data_encode_int() {
        for n in [
            0i128,
            1,
            -1,
            7,
            255,
            256,
            -256,
            65535,
            65536,
            i64::MAX as i128,
            i64::MIN as i128,
            i128::MAX,
            i128::MIN,
        ] {
            let from_logos = big(n).to_int_term();
            let from_ontos = Term::from_value(&ontos_data::encode_int(n));
            assert_eq!(from_logos, from_ontos, "to_int_term != encode_int for {n}");
            // And the kept direct payload matches ontos-data's payload bytes.
            assert_eq!(
                Term::tuple([
                    Term::atom(INT_LABEL.to_vec()),
                    Term::atom(big(n).to_payload())
                ]),
                from_ontos,
                "to_payload != encode_int payload for {n}"
            );
            // round-trips back through the recognizer.
            assert_eq!(BigInt::from_int_term(&from_logos), Some(big(n)), "n = {n}");
        }
    }

    #[test]
    fn payload_round_trips_for_all_test_values() {
        for n in [0i128, 1, -1, 7, -7, 255, 256, -256, 123456789, -987654321] {
            let payload = big(n).to_payload();
            assert_eq!(BigInt::from_payload(&payload), Some(big(n)), "n = {n}");
        }
    }

    #[test]
    fn int_term_round_trips_for_all_test_values() {
        for n in [0i128, 1, -1, 42, -42, 255, 256, 1_000_000, -1_000_000] {
            let term = big(n).to_int_term();
            assert_eq!(BigInt::from_int_term(&term), Some(big(n)), "n = {n}");
        }
    }

    // ------------------------------------------------------ non-canonical rejection --

    #[test]
    fn non_canonical_payloads_are_rejected() {
        // Empty payload.
        assert_eq!(BigInt::from_payload(&[]), None);
        // Unknown sign byte.
        assert_eq!(BigInt::from_payload(&[0x02, 0x01]), None);
        // Leading-zero magnitude (non-minimal): 00 00 01.
        assert_eq!(BigInt::from_payload(&[0x00, 0x00, 0x01]), None);
        // Negative zero: 01 (sign neg) with empty magnitude.
        assert_eq!(BigInt::from_payload(&[0x01]), None);
        // Negative with leading-zero magnitude.
        assert_eq!(BigInt::from_payload(&[0x01, 0x00, 0x01]), None);
    }

    #[test]
    fn non_int_terms_do_not_decode() {
        // A bare atom is not an int.
        assert_eq!(BigInt::from_int_term(&Term::atom(b"42".to_vec())), None);
        // Wrong functor.
        assert_eq!(
            BigInt::from_int_term(&Term::tuple([
                Term::atom(b"float".to_vec()),
                Term::atom(vec![0x00, 0x01])
            ])),
            None
        );
        // Wrong arity (3 children).
        assert_eq!(
            BigInt::from_int_term(&Term::tuple([
                Term::atom(b"int".to_vec()),
                Term::atom(vec![0x00, 0x01]),
                Term::atom(vec![0x00])
            ])),
            None
        );
        // Non-atom payload.
        assert_eq!(
            BigInt::from_int_term(&Term::tuple([
                Term::atom(b"int".to_vec()),
                Term::tuple([Term::atom(b"x".to_vec())])
            ])),
            None
        );
        // Variable is not an int term.
        assert_eq!(BigInt::from_int_term(&Term::var("X")), None);
    }

    // ------------------------------------------------------------- decimal parsing --

    #[test]
    fn decimal_parsing_handles_signs_and_leading_zeros() {
        assert_eq!(BigInt::from_decimal_str("0"), Some(big(0)));
        assert_eq!(BigInt::from_decimal_str("007"), Some(big(7)));
        assert_eq!(BigInt::from_decimal_str("-0"), Some(big(0))); // negative zero normalizes
        assert_eq!(BigInt::from_decimal_str("-42"), Some(big(-42)));
        assert_eq!(BigInt::from_decimal_str("+42"), Some(big(42)));
        assert_eq!(BigInt::from_decimal_str("255"), Some(big(255)));
        // Malformed.
        assert_eq!(BigInt::from_decimal_str(""), None);
        assert_eq!(BigInt::from_decimal_str("-"), None);
        assert_eq!(BigInt::from_decimal_str("12a"), None);
        assert_eq!(BigInt::from_decimal_str("3.14"), None);
    }

    // ------------------------------------------------------------------ comparison --

    #[test]
    fn cmp_orders_integers() {
        assert_eq!(big(-5).cmp(&big(3)), Ordering::Less);
        assert_eq!(big(3).cmp(&big(-5)), Ordering::Greater);
        assert_eq!(big(-5).cmp(&big(-3)), Ordering::Less); // -5 < -3
        assert_eq!(big(-3).cmp(&big(-5)), Ordering::Greater);
        assert_eq!(big(7).cmp(&big(7)), Ordering::Equal);
        assert_eq!(big(0).cmp(&big(0)), Ordering::Equal);
        assert_eq!(big(0).cmp(&big(-1)), Ordering::Greater);
        assert_eq!(big(256).cmp(&big(255)), Ordering::Greater);
    }

    #[test]
    fn min_max_pick_correctly() {
        // `min`/`max` are the `Ord`-provided (owned) methods.
        assert_eq!(big(3).min(big(5)), big(3));
        assert_eq!(big(3).max(big(5)), big(5));
        assert_eq!(big(-3).min(big(-5)), big(-5));
        assert_eq!(big(-3).max(big(-5)), big(-3));
    }

    // ------------------------------------------------------------------ arithmetic --

    /// Exhaustively cross-check add/sub/mul/div/mod against host `i128` over a grid
    /// of small operands (the magnitude routines are the same regardless of size, so
    /// a dense small grid catches carry/borrow/sign bugs).
    #[test]
    fn arithmetic_agrees_with_i128_on_a_grid() {
        let values: Vec<i128> = (-20..=20)
            .chain([255, 256, -255, -256, 1000, -1000])
            .collect();
        for &a in &values {
            for &b in &values {
                let (ba, bb) = (big(a), big(b));
                assert_eq!(ba.add(&bb), big(a + b), "{a} + {b}");
                assert_eq!(ba.sub(&bb), big(a - b), "{a} - {b}");
                assert_eq!(ba.mul(&bb), big(a * b), "{a} * {b}");
                if b != 0 {
                    let (q, r) = ba.div_rem_trunc(&bb).unwrap();
                    assert_eq!(q, big(a / b), "{a} // {b} (trunc quotient)");
                    assert_eq!(r, big(a % b), "{a} rem {b} (trunc remainder)");
                    // The division identity must hold.
                    assert_eq!(q.mul(&bb).add(&r), big(a), "q*b + r == a for {a},{b}");
                    // Floored modulo matches Rust's rem_euclid sign convention only
                    // when divisor > 0; compute the ISO floored value directly.
                    let floored = ((a % b) + b) % b;
                    assert_eq!(ba.modulo_floored(&bb).unwrap(), big(floored), "{a} mod {b}");
                }
            }
        }
    }

    #[test]
    fn division_by_zero_is_none() {
        assert_eq!(big(5).div_rem_trunc(&big(0)), None);
        assert_eq!(big(5).modulo_floored(&big(0)), None);
        assert_eq!(big(0).div_rem_trunc(&big(0)), None);
    }

    #[test]
    fn floored_mod_sign_follows_divisor() {
        // ISO Prolog examples.
        assert_eq!(big(-7).modulo_floored(&big(3)).unwrap(), big(2));
        assert_eq!(big(7).modulo_floored(&big(-3)).unwrap(), big(-2));
        assert_eq!(big(7).modulo_floored(&big(3)).unwrap(), big(1));
        // floor(-7 / -3) = 2, so -7 - (-3)*2 = -1.
        assert_eq!(big(-7).modulo_floored(&big(-3)).unwrap(), big(-1));
        // Exact division → zero remainder regardless of sign.
        assert_eq!(big(6).modulo_floored(&big(3)).unwrap(), big(0));
        assert_eq!(big(-6).modulo_floored(&big(3)).unwrap(), big(0));
    }

    #[test]
    fn exact_division_only_when_even() {
        // Divides evenly → the exact quotient.
        assert_eq!(big(6).div_exact(&big(3)), Some(big(2)));
        assert_eq!(big(0).div_exact(&big(5)), Some(big(0)));
        assert_eq!(big(-6).div_exact(&big(3)), Some(big(-2)));
        assert_eq!(big(-6).div_exact(&big(-2)), Some(big(3)));
        assert_eq!(big(100).div_exact(&big(-4)), Some(big(-25)));
        // Does NOT divide evenly → None (no fractional integer, never truncates).
        assert_eq!(big(7).div_exact(&big(2)), None);
        assert_eq!(big(-7).div_exact(&big(2)), None);
        assert_eq!(big(1).div_exact(&big(3)), None);
        // Zero divisor → None (domain error, not a panic).
        assert_eq!(big(5).div_exact(&big(0)), None);
        assert_eq!(big(0).div_exact(&big(0)), None);
    }

    #[test]
    fn exact_division_on_large_values() {
        // (10^40) / (10^20) == 10^20 exactly; an off-by-one dividend is inexact.
        let a = BigInt::from_decimal_str(&("1".to_string() + &"0".repeat(40))).unwrap();
        let b = BigInt::from_decimal_str(&("1".to_string() + &"0".repeat(20))).unwrap();
        assert_eq!(a.div_exact(&b), Some(b.clone()));
        assert_eq!(a.add(&big(1)).div_exact(&b), None);
    }

    #[test]
    fn trunc_div_truncates_toward_zero() {
        // -7 // 2 == -3 (toward zero), not -4 (floored).
        assert_eq!(big(-7).div_rem_trunc(&big(2)).unwrap().0, big(-3));
        assert_eq!(big(7).div_rem_trunc(&big(-2)).unwrap().0, big(-3));
        assert_eq!(big(7).div_rem_trunc(&big(2)).unwrap().0, big(3));
    }

    // --------------------------------------------------------- unbounded (bignum) --

    #[test]
    fn handles_values_far_beyond_i128() {
        // 10^40 — well past i128::MAX (~1.7e38). Build it as a decimal literal.
        let huge = "10000000000000000000000000000000000000000";
        let a = BigInt::from_decimal_str(huge).expect("parse 10^40");
        // a round-trips through its own decimal rendering and its embedding payload.
        assert_eq!(a.to_decimal_string(), huge);
        assert_eq!(BigInt::from_payload(&a.to_payload()), Some(a.clone()));
        // (10^40) * (10^40) == 10^80, and dividing back recovers 10^40 exactly.
        let square = a.mul(&a);
        assert_eq!(
            square.to_decimal_string(),
            "1".to_string() + &"0".repeat(80)
        );
        let (q, r) = square.div_rem_trunc(&a).unwrap();
        assert_eq!(q, a);
        assert!(r.is_zero());
    }

    /// The unbounded boundary in the `Value` bridge: a magnitude beyond `i128` is
    /// **not** representable on ontos-data's `i128` surface (it answers
    /// `IntOutOfRange`), yet logos's domain is unbounded, so `to_int_term` lowers it
    /// via the direct §5.1 payload and `from_int_term` decodes it on the
    /// `IntOutOfRange` fallback — a full round-trip. The lowered term must still be a
    /// canonical `int` that ontos-data *recognizes* as out-of-range (not malformed).
    #[test]
    fn value_bridge_round_trips_beyond_i128() {
        // 10^40 is past i128::MAX (~1.7e38); also check its negation.
        let huge = "10000000000000000000000000000000000000000";
        for a in [
            BigInt::from_decimal_str(huge).expect("parse 10^40"),
            BigInt::from_decimal_str(&format!("-{huge}")).expect("parse -10^40"),
        ] {
            // Beyond i128 ⟹ ontos-data's typed surface reports out-of-range...
            let value = a.to_int_term().erase_ground().expect("ground int term");
            assert_eq!(
                ontos_data::read_int(&value),
                Err(ontos_data::DataError::IntOutOfRange),
                "ontos-data should recognize {} as a canonical-but-out-of-range int",
                a.to_decimal_string()
            );
            // ...but logos's unbounded bridge round-trips it exactly.
            let term = a.to_int_term();
            assert_eq!(BigInt::from_int_term(&term), Some(a.clone()));
            // And the lowered payload is the same direct §5.1 form.
            assert_eq!(int_payload_bytes(&term), Some(a.to_payload().as_slice()));
        }
    }

    #[test]
    fn big_addition_carries_across_many_bytes() {
        // (2^256 - 1) + 1 == 2^256: a full carry chain across 32 bytes.
        let all_ones = BigInt {
            negative: false,
            magnitude: vec![0xff; 32],
        };
        let one = big(1);
        let sum = all_ones.add(&one);
        let mut expected_payload = vec![0x00, 0x01];
        expected_payload.extend(std::iter::repeat_n(0x00, 32));
        assert_eq!(sum.to_payload(), expected_payload);
    }

    /// ⭐ **#1264 — `decimal_to_magnitude` against an INDEPENDENT oracle, across the chunk
    /// boundary.**
    ///
    /// The parse folds [`CHUNK_DIGITS`]` = 9` digits per pass, so the arithmetic differs
    /// either side of every multiple of 9 and at the ragged final chunk. `u128` is a
    /// genuinely independent implementation — a different base, a different algorithm, and
    /// one the compiler checks — for every value small enough to hold one.
    #[test]
    fn parsing_agrees_with_u128_across_the_chunk_boundary() {
        // 1..=38 covers four chunk boundaries (9, 18, 27, 36) and both ragged ends.
        for len in 1..=38usize {
            for pattern in ["1", "9", "7", "0"] {
                let digits: String = pattern.repeat(len);
                let Ok(want) = digits.parse::<u128>() else {
                    continue; // out of u128 range; the round-trip test below covers those
                };
                let got = BigInt::from_decimal_str(&digits).expect("parses");
                assert_eq!(
                    got.to_decimal_string(),
                    want.to_string(),
                    "len={len} pattern={pattern}: parse disagrees with u128"
                );
            }
        }
        // Mixed digits, so no run-length pattern can hide a carry defect.
        for len in [8usize, 9, 10, 17, 18, 19, 26, 27, 28] {
            let digits: String = (0..len)
                .map(|i| char::from(b'0' + (i % 10) as u8))
                .collect();
            let want: u128 = digits.parse().expect("fits");
            assert_eq!(
                BigInt::from_decimal_str(&digits)
                    .expect("parses")
                    .to_decimal_string(),
                want.to_string(),
                "len={len}: mixed-digit parse disagrees with u128"
            );
        }
    }

    /// #1264 — values far beyond `u128`, checked by ROUND TRIP rather than by an oracle.
    ///
    /// ⚠ The oracle above stops at 39 digits. This is the only check covering the sizes the
    /// issue is actually about, and it is why the render path is exercised too: a parse that
    /// silently dropped a chunk would render short.
    #[test]
    fn large_values_round_trip_through_the_decimal_string() {
        for len in [64usize, 128, 1_000, 4_096] {
            // A leading 1 keeps the value canonical (no leading zeros to strip).
            let digits: String = core::iter::once('1')
                .chain((1..len).map(|i| char::from(b'0' + (i % 10) as u8)))
                .collect();
            let parsed = BigInt::from_decimal_str(&digits).expect("parses");
            assert_eq!(
                parsed.to_decimal_string(),
                digits,
                "len={len}: round trip lost digits"
            );
        }
    }

    /// #1264 — leading zeros are stripped, and an all-zero string is canonical zero.
    ///
    /// The chunked pass pushes carry bytes as it goes, so an input that produces NO carry at
    /// all is the case most likely to leave an empty or all-zero accumulator behind.
    #[test]
    fn leading_and_all_zeros_stay_canonical() {
        for len in [1usize, 8, 9, 10, 18, 19, 100] {
            let zeros: String = "0".repeat(len);
            let z = BigInt::from_decimal_str(&zeros).expect("parses");
            assert!(z.is_zero(), "len={len}: all-zero input must be zero");
            assert_eq!(
                z.to_decimal_string(),
                "0",
                "len={len}: zero must render as \"0\""
            );

            let padded = format!("{zeros}7");
            assert_eq!(
                BigInt::from_decimal_str(&padded)
                    .expect("parses")
                    .to_decimal_string(),
                "7",
                "len={len}: leading zeros must be stripped"
            );
        }
    }
}
