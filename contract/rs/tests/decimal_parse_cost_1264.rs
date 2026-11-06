//! #1264 — `from_decimal_str` must not be quadratic in the digit count.
//!
//! `from_parts` canonicalizes by dividing by ten once PER trailing zero. Each division is a
//! full bignum operation, so parsing a decimal whose spelling carries many trailing zeros
//! cost O(n²): measured at 9.95 s (release) for 10,000 zeros, and 376 s for the largest
//! IN-CONTRACT value (|exponent| = MAX_DECIMAL_SCALE_SHIFT). That is an availability surface
//! wherever a decimal literal crosses a trust boundary.
//!
//! The fix strips the zeros as TEXT before the BigInt exists. These tests pin BOTH halves:
//! the values are unchanged, and the cost is no longer quadratic.

use logos_contract::decval::BigDecimal;
use logos_contract::intval::BigInt;
use std::time::Instant;

fn parse(s: &str) -> Option<BigDecimal> {
    BigDecimal::from_decimal_str(s)
}

#[test]
fn trailing_zeros_do_not_change_the_value_1264() {
    // The strip is a canonicalization, so every spelling of the same number is one value.
    let base = parse("3.14").expect("base");
    for s in ["3.14", "3.140", "3.1400", "3.14000000"] {
        assert_eq!(parse(s), Some(base.clone()), "{s} must equal 3.14");
    }
    // …and it must not collapse DIFFERENT numbers.
    assert_ne!(parse("3.14"), parse("3.141"));
    assert_ne!(parse("314.0"), parse("3.14"));
}

#[test]
fn the_all_zero_and_edge_spellings_survive_the_strip_1264() {
    // Trimming every digit leaves an empty string; the strip must yield zero, not None.
    for s in ["0.0", "0.000", "000.000", "-0.0", "0.00000000000000000000"] {
        let v = parse(s).unwrap_or_else(|| panic!("{s} must parse"));
        assert!(
            v.is_zero(),
            "{s} must be zero, got {}",
            v.to_decimal_string()
        );
    }
    // A leading-zero integer part is unaffected.
    assert_eq!(parse("007.500"), parse("7.5"));
    // Negative keeps its sign through the strip.
    let neg = parse("-2.500").expect("neg");
    assert!(neg.is_negative(), "-2.500 must stay negative");
    assert_eq!(parse("-2.500"), parse("-2.5"));
    // No trailing zeros at all: the strip is a no-op.
    assert_eq!(parse("123.456"), parse("123.456"));
}

#[test]
fn parsing_is_not_quadratic_in_the_digit_count_1264() {
    // GUARD, not a benchmark: the old implementation took ~9.95 s (release) and 72.34 s in
    // debug for 10,000 trailing zeros. A generous ceiling still fails by orders of magnitude
    // if the per-zero division loop comes back, and will not flake on a loaded runner.
    //
    // ⚠ THIS IS THE REPO'S FIRST WALL-CLOCK ASSERTION, and that is a deliberate departure
    // rather than an oversight. Measured before adding it: 5 files use `Instant::now`
    // (`stats.rs`, `engine.rs`, the two engines, seminaive's tests) and NOT ONE asserts on a
    // duration — they measure and report. So this introduces a category of flake risk the
    // codebase has so far avoided, and it needs to earn that.
    //
    // Why it earns it: the defect IS a cost, so no value assertion can observe it — the old
    // code returns the RIGHT answer, just quadratically. The two tests above already pin
    // correctness and stay green under the regression (measured: 2 passed / 1 failed when the
    // fix is reverted), which is precisely why a third, timing test is the only thing that
    // catches this class.
    //
    // Why it should not flake: the margin is 55x against the observed pass (0.09 s debug) and
    // the ceiling sits 14x below the observed regression (72.34 s debug). A loaded runner that
    // turned 0.09 s into 5 s would be failing far more than this test.
    let s = format!("314{}.0", "0".repeat(10_000));
    let t = Instant::now();
    let v = parse(&s).expect("must parse");
    let elapsed = t.elapsed();

    // ANTI-VACUITY: assert the VALUE is right, or a parser that bailed early would pass the
    // timing trivially. "314" + 10,000 zeros + ".0" canonicalizes to mantissa 314 with
    // exponent 10,000 — the strip must move the exponent by exactly the zeros it removed
    // (10,000 from the integer part, less the one fractional digit).
    assert!(!v.is_zero(), "314 followed by zeros is not zero");
    let expected = BigDecimal::from_parts(BigInt::from_i128(314), 10_000).expect("expected");
    assert_eq!(
        v, expected,
        "the strip changed the value, not just the cost"
    );

    assert!(
        elapsed.as_secs() < 5,
        "from_decimal_str took {elapsed:?} for 10,000 trailing zeros — the per-zero \
         division loop is back (it measured 9.95 s in release, and this ceiling is \
         deliberately generous)"
    );
}
