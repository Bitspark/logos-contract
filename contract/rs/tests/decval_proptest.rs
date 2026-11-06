//! Generative cross-check of exact decimal arithmetic against an independent
//! big-RATIONAL reference (#488).
//!
//! The hand-rolled [`logos_contract::decval::BigDecimal`] evaluates the checker's
//! decimal arithmetic builtins. Its only generative coverage was the *integer-only*
//! fixed grid at `intval.rs:910`, which cannot reach the decimal scale logic
//! (alignment, exponent arithmetic, base-10 termination) nor values beyond `i128`.
//!
//! Here proptest draws random `(mantissa, exponent)` operands — including mantissas
//! that overflow `i128`, the whole point — and an **independent** reference computes
//! the exact value with `num-rational`'s `BigRational` (arbitrary-precision rationals,
//! a completely different implementation from the hand-rolled bignum). For each
//! operation we compare `decval`'s result, read back out as a rational via its public
//! `to_decimal_string`, against the reference. A carry/borrow/sign/scale bug shows as
//! a mismatch; a missing DoS guard shows as a hang the harness bounds.
//!
//! Why a rational, not `i128`: a decimal `m × 10^e` has an unbounded mantissa and an
//! `i128` exponent, so the value space is far outside `i128` — the reference must be a
//! big type. `BigRational` represents every exact decimal exactly (`m / 10^{-e}`), so
//! add/sub/mul/`//`/`mod` and the *terminating* `/` all have an exact oracle with no
//! rounding.

use logos_contract::decval::BigDecimal;
use logos_contract::intval::BigInt;

use num_bigint::BigInt as RefInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use proptest::prelude::*;

/// `MAX_DECIMAL_SCALE_SHIFT` from `decval` — the add/sub/`//`/`mod` alignment bound.
/// Re-stated here (it is `pub`) so the test's "would this op be refused?" predicate
/// matches the implementation exactly.
const MAX_SHIFT: i128 = logos_contract::decval::MAX_DECIMAL_SCALE_SHIFT;

// --- the reference ---------------------------------------------------------------

/// The exact rational value of `mantissa × 10^exponent`.
fn ref_value(mantissa: i128, exponent: i128) -> BigRational {
    let m = RefInt::from(mantissa);
    let ten = RefInt::from(10);
    if exponent >= 0 {
        BigRational::from_integer(m * ten.pow(exponent as u32))
    } else {
        BigRational::new(m, ten.pow((-exponent) as u32))
    }
}

/// Read a `decval::BigDecimal` back out as the exact rational it denotes, by parsing its
/// **fixed-point** decimal spelling (`±int.frac`). This is the bridge from the
/// type-under-test back to the reference domain.
///
/// ⛔ **IN-BAND ONLY, and that is a property of THIS FILE'S DRAWS, not of the renderer**
/// (#1264). `to_decimal_string` is banded: at `|exponent| > MAX_DECIMAL_SCALE_SHIFT`
/// (65536) it renders the **scientific** form, which has no dot and which
/// `from_decimal_str` deliberately refuses — print-only, by design since #470. This bridge
/// handles the fixed-point form only.
///
/// **Why no scientific branch here:** past-band is UNREACHABLE from these strategies, so
/// one would be dead code. Every draw is `mantissa: i128` with `|exponent| ≤ 300`;
/// canonicalization can only raise the exponent by the mantissa's trailing zeros (≤38 for
/// an `i128`), and `mul` — the only op that sums exponents — refuses past the bound
/// outright. Ceiling is ~±638, four orders inside 65536.
///
/// ⚠ **So the `expect` below is a BOUND CHECK, not an impossibility claim.** If someone
/// widens the exponent strategies past the band, it fires and says exactly why — which is
/// the behaviour we want, because the right response is then to add the scientific branch
/// deliberately, not to discover a panic and paper over it.
fn decimal_to_ref(d: &BigDecimal) -> BigRational {
    let s = d.to_decimal_string();
    let (neg, body) = match s.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, s.as_str()),
    };
    let (int_part, frac_part) = body.split_once('.').unwrap_or_else(|| {
        panic!(
            "decimal_to_ref got the PAST-BAND scientific spelling {s:?} — this bridge reads              the fixed-point form only. An exponent strategy in this file has been widened              past MAX_DECIMAL_SCALE_SHIFT (#1264); add the scientific branch deliberately              rather than removing this check."
        )
    });
    let combined = format!("{int_part}{frac_part}");
    let mag: RefInt = combined.parse().expect("digits parse as an integer");
    let ten = RefInt::from(10);
    let denom = ten.pow(frac_part.len() as u32);
    let mut r = BigRational::new(mag, denom);
    if neg {
        r = -r;
    }
    r
}

/// Build the type-under-test operand from the same parts the reference used.
fn build(mantissa: i128, exponent: i128) -> BigDecimal {
    BigDecimal::from_parts(BigInt::from_i128(mantissa), exponent)
        .expect("proptest exponents are bounded to -200..=200, well inside the i128 band")
}

/// The exponent gap that add/sub/`//`/`mod` must align before operating. Mirrors the
/// implementation's `max(shift_self, shift_other)` (the smaller-exponent operand has
/// shift 0). Used to predict when an op is refused for an adversarial scale gap.
fn align_shift(e_a: i128, e_b: i128, a_zero: bool, b_zero: bool) -> i128 {
    // `add`/`sub` short-circuit a zero operand before aligning, so no shift applies.
    if a_zero || b_zero {
        return 0;
    }
    let e_min = e_a.min(e_b);
    (e_a - e_min).max(e_b - e_min)
}

proptest! {
    // A wide, varied draw: mantissas spanning well past i128 magnitude (via the
    // i128 source × a separate exponent), exponents covering the alignment-bound
    // boundary on both sides of MAX_SHIFT. 2048 cases keeps the suite quick while
    // densely hitting carry/sign/scale corners; the nightly fuzz lane goes deeper.
    #![proptest_config(ProptestConfig { cases: 2048, ..ProptestConfig::default() })]

    #[test]
    #[ignore = "generative cross-check — heavy; runs in the nightly stress lane (release, -- --ignored), not the per-PR gate (#488)"]
    fn add_sub_mul_match_the_rational_reference(
        a_m in any::<i128>(),
        a_e in -200i128..=200,
        b_m in any::<i128>(),
        b_e in -200i128..=200,
    ) {
        let a = build(a_m, a_e);
        let b = build(b_m, b_e);
        let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));

        // `from_parts` is canonical and lossless: the operand denotes exactly its parts.
        prop_assert_eq!(decimal_to_ref(&a), ra.clone(), "build(a) must denote a_m·10^a_e");
        prop_assert_eq!(decimal_to_ref(&b), rb.clone(), "build(b) must denote b_m·10^b_e");

        let shift = align_shift(a_e, b_e, a_m == 0, b_m == 0);
        let refused = shift > MAX_SHIFT;

        match a.add(&b) {
            Ok(sum) => {
                prop_assert!(!refused, "add should have been refused for a {}-shift", shift);
                prop_assert_eq!(decimal_to_ref(&sum), &ra + &rb, "a + b");
            }
            Err(_) => prop_assert!(refused, "add refused but the {}-shift is within bound", shift),
        }
        match a.sub(&b) {
            Ok(diff) => {
                prop_assert!(!refused);
                prop_assert_eq!(decimal_to_ref(&diff), &ra - &rb, "a - b");
            }
            Err(_) => prop_assert!(refused),
        }
        // `*` never aligns (it adds exponents), so it only fails on astronomical
        // i128 exponent overflow — unreachable for these bounded exponents.
        let prod = a.mul(&b).expect("mul cannot overflow for |e| <= 200");
        prop_assert_eq!(decimal_to_ref(&prod), &ra * &rb, "a * b");
    }

    #[test]
    #[ignore = "generative cross-check — heavy; runs in the nightly stress lane (release, -- --ignored), not the per-PR gate (#488)"]
    fn terminating_division_matches_when_it_terminates(
        a_m in any::<i128>(),
        a_e in -60i128..=60,
        b_m in any::<i128>(),
        b_e in -60i128..=60,
    ) {
        let a = build(a_m, a_e);
        let b = build(b_m, b_e);

        match a.div_terminating(&b) {
            Ok(q) => {
                // It claimed the quotient terminates: verify q·b == a exactly, and
                // that the reference quotient really is a terminating decimal.
                prop_assert!(b_m != 0, "division by zero must be Err, not Ok");
                let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));
                let rq = decimal_to_ref(&q);
                prop_assert_eq!(&rq * &rb, ra, "q * b must equal a exactly");
            }
            Err(_) => {
                // Err is correct iff: divisor is zero, OR the exact quotient does not
                // terminate in base 10 (reduced denominator has a prime factor != 2,5).
                if b_m != 0 {
                    let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));
                    let q = &ra / &rb;
                    prop_assert!(
                        !terminates_base10(&q),
                        "div_terminating refused a quotient that DOES terminate: {}e{} / {}e{}",
                        a_m, a_e, b_m, b_e,
                    );
                }
            }
        }
    }

    #[test]
    #[ignore = "generative cross-check — heavy; runs in the nightly stress lane (release, -- --ignored), not the per-PR gate (#488)"]
    fn floor_div_and_mod_match_the_rational_reference(
        a_m in any::<i128>(),
        a_e in -120i128..=120,
        b_m in any::<i128>(),
        b_e in -120i128..=120,
    ) {
        let a = build(a_m, a_e);
        let b = build(b_m, b_e);
        let shift = align_shift(a_e, b_e, false, false);
        let refused = shift > MAX_SHIFT;

        // `//` — truncating (toward zero) integer division.
        match a.div_trunc_int(&b) {
            Ok(q) => {
                prop_assert!(b_m != 0 && !refused, "// of {}e{} by {}e{} should be Err", a_m, a_e, b_m, b_e);
                let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));
                let expected = ref_trunc(&(&ra / &rb));
                prop_assert_eq!(bigint_to_ref(&q), expected, "a // b (toward zero)");
            }
            Err(_) => prop_assert!(b_m == 0 || refused),
        }

        // `mod` — ISO floored modulo (sign follows the divisor).
        match a.modulo_floored(&b) {
            Ok(r) => {
                prop_assert!(b_m != 0 && !refused);
                let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));
                // floored remainder: r = a - floor(a/b)*b.
                let floor_q = ref_floor(&(&ra / &rb));
                let expected = &ra - &(BigRational::from_integer(floor_q) * &rb);
                prop_assert_eq!(decimal_to_ref(&r), expected, "a mod b (floored)");
            }
            Err(_) => prop_assert!(b_m == 0 || refused),
        }
    }

    #[test]
    #[ignore = "generative cross-check — heavy; runs in the nightly stress lane (release, -- --ignored), not the per-PR gate (#488)"]
    fn ordering_matches_the_rational_reference(
        a_m in any::<i128>(),
        a_e in -300i128..=300,
        b_m in any::<i128>(),
        b_e in -300i128..=300,
    ) {
        let a = build(a_m, a_e);
        let b = build(b_m, b_e);
        let (ra, rb) = (ref_value(a_m, a_e), ref_value(b_m, b_e));
        // The hand-rolled magnitude-order compare must agree with the rational order,
        // even for vast exponent gaps it decides without materializing the alignment.
        prop_assert_eq!(a.cmp(&b), ra.cmp(&rb), "cmp({}e{}, {}e{})", a_m, a_e, b_m, b_e);
    }
}

// --- reference helpers (all over the big rational/int domain) ---------------------

/// A `BigRational` is a terminating base-10 decimal iff its reduced denominator's
/// only prime factors are 2 and 5.
fn terminates_base10(q: &BigRational) -> bool {
    let mut d = q.denom().abs();
    let two = RefInt::from(2);
    let five = RefInt::from(5);
    while (&d % &two).is_zero() {
        d /= &two;
    }
    while (&d % &five).is_zero() {
        d /= &five;
    }
    d.is_one()
}

/// `trunc(q)` toward zero, as a big integer.
fn ref_trunc(q: &BigRational) -> RefInt {
    q.trunc().to_integer()
}

/// `floor(q)`, as a big integer.
fn ref_floor(q: &BigRational) -> RefInt {
    q.floor().to_integer()
}

/// Read a `decval::BigInt` (the `//` result) back out as a reference big integer via
/// its canonical decimal string.
fn bigint_to_ref(n: &BigInt) -> RefInt {
    n.to_decimal_string()
        .parse()
        .expect("BigInt decimal string parses")
}
