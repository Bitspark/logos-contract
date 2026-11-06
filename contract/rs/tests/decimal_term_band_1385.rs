//! **The banded `to_decimal_term` contract (#1385), as two separate claims — pinned in the
//! PR gate because the lane that found it does not run on a PR.**
//!
//! `#1385` capped the exponent at DECODE: `from_decimal_term` refuses anything past
//! ±[`MAX_DECIMAL_SCALE_SHIFT`], and its own comment records the asymmetry deliberately —
//! *"Decode-side only: `from_parts` is untouched."* So construction still admits a canonical
//! value the decoder refuses, and the term round-trip is **banded, not unconditional**.
//!
//! ⛔ **WHY THIS FILE EXISTS.** The `decimal_eval` fuzz target asserted an UNCONDITIONAL term
//! round-trip (written 2026-06-13, #527 — true when written). `#1385` falsified it on
//! 2026-08-29, and `stress-nightly` went red on 08-30 and 08-31 with:
//!
//! ```text
//! assertion `left == right` failed: to_decimal_term/from_decimal_term must round-trip a canonical decimal
//!   left: None
//!  right: Some(BigDecimal { mantissa: 1, exponent: 2147680256 })
//! ```
//!
//! ⭐ **THIS IS #1264 ONE FUNCTION OVER.** That issue banded the STRING round-trip for the
//! identical reason (an unconditional claim, false by design since #470). The TERM claim was
//! left unconditional and was falsified two days after #1385 landed. `decval.rs`'s
//! `banded_round_trip_1264` covers the STRING codec; nothing covered the TERM codec's band —
//! the only `from_decimal_term` negatives there are a non-canonical mantissa and a
//! **beyond-`i128`** exponent, which is the `to_i128()` narrowing, not the ±65536 cap.
//!
//! ⚠ **And the fuzz target cannot pin it.** `fuzz/` is a separate workspace needing nightly +
//! Linux libFuzzer, so no required PR context builds it: a stale assertion there is invisible
//! until a nightly runs. These cases run in the required `rust` job.
//!
//! ⭐ **#2679 CLOSED THE ASYMMETRY this file used to pin.** The band is the VALUE DOMAIN now
//! ([`MAX_DECIMAL_EXPONENT`]), checked by `from_parts`, the one constructor every decimal
//! returns through, as well as at decode. So a past-band value is no longer constructible,
//! and this file builds its past-band subjects as raw decimal TERMS, the form the wire can
//! still deliver, and asserts that both construction and decode refuse them.

use logos_contract::decval::{BigDecimal, MAX_DECIMAL_EXPONENT};
use logos_contract::intval::BigInt;
use logos_contract::term::Term;

/// Read the exponent back off the ENCODED term — the third child of the decimal tuple.
///
/// ⭐ Deliberately NOT read off whether the decoder accepted: that would assert *"it refused
/// because it refuses"*. This is the same datum the decoder narrows, obtained without asking
/// the decoder, which is what makes the two arms below independent claims.
fn encoded_exponent(term: &Term) -> Option<i128> {
    match term {
        Term::Tuple(children) => match children.as_slice() {
            [_, _, exponent_term] => BigInt::from_int_term(exponent_term).and_then(|e| e.to_i128()),
            _ => None,
        },
        _ => None,
    }
}

fn in_band(term: &Term) -> bool {
    encoded_exponent(term)
        .is_some_and(|e| (-MAX_DECIMAL_EXPONENT..=MAX_DECIMAL_EXPONENT).contains(&e))
}

/// A canonical decimal TERM `decimal(int(m), int(e))`, built directly, as the wire can deliver
/// one. Since #2679 no constructor builds a past-band VALUE, so this is how a test reaches one.
fn decimal_term(m: i128, e: i128) -> Term {
    Term::tuple([
        Term::atom(b"decimal".to_vec()),
        BigInt::from_i128(m).to_int_term(),
        BigInt::from_i128(e).to_int_term(),
    ])
}

/// The exact input the 2026-08-31 nightly crashed on (run 33366556639), kept as a named case
/// so a regression reproduces the ORIGINAL finding rather than a re-derived approximation.
#[test]
fn the_nightly_crash_input_is_refused_at_construction_and_at_decode() {
    assert!(
        BigDecimal::from_parts(BigInt::from_i128(1), 2_147_680_256).is_none(),
        "#2679: construction refuses a past-band value, as decode does (#1385)"
    );
    let term = decimal_term(1, 2_147_680_256);

    assert_eq!(
        encoded_exponent(&term),
        Some(2_147_680_256),
        "the exponent must ride as the tuple's third child"
    );
    assert!(
        !in_band(&term),
        "2147680256 is past the ±{MAX_DECIMAL_EXPONENT} cap"
    );
    assert!(
        BigDecimal::from_decimal_term(&term).is_none(),
        "decode must REFUSE it — an accept here would reinstate the tri-core divergence #1385 closed",
    );
}

/// ⛔ **ANTI-VACUITY, per `banded_round_trip_1264`'s standing instruction:** a property split
/// into two arms passes trivially if one arm is never reached, and a green for that reason is
/// worse than the red it replaced. So this counts cases that **REACH EACH BAND**, not cases
/// that ran, and asserts both counters are non-zero.
#[test]
fn to_decimal_term_is_banded_and_both_bands_are_reached() {
    let mut reached_in_band = 0usize;
    let mut reached_past_band = 0usize;

    // IN-BAND — includes the bound ITSELF, which is in-band; the edge is at bound+1.
    for (m, e) in [
        (7i128, 0i128),
        (7, 10),
        (314, -2),
        (-42, 3),
        (7, MAX_DECIMAL_EXPONENT),
        (7, -MAX_DECIMAL_EXPONENT),
    ] {
        let Some(v) = BigDecimal::from_parts(BigInt::from_i128(m), e) else {
            continue;
        };
        let term = v.to_decimal_term();
        assert!(in_band(&term), "({m}, {e}) must read as IN band");
        assert_eq!(
            BigDecimal::from_decimal_term(&term).as_ref(),
            Some(&v),
            "in-band ({m}, {e}) must round-trip through the term EXACTLY",
        );
        reached_in_band += 1;
    }

    // PAST-BAND — NOT constructible since #2679, and NOT decodable (#1385). Both signs,
    // because a one-sided test would miss a regression in the negative direction.
    for (m, e) in [
        (7i128, MAX_DECIMAL_EXPONENT + 1),
        (7, -(MAX_DECIMAL_EXPONENT + 1)),
        (-3, MAX_DECIMAL_EXPONENT + 12345),
    ] {
        assert!(
            BigDecimal::from_parts(BigInt::from_i128(m), e).is_none(),
            "past-band ({m}, {e}) must not be constructible (#2679)"
        );
        let term = decimal_term(m, e);
        assert!(!in_band(&term), "({m}, {e}) must read as PAST band");
        assert!(
            BigDecimal::from_decimal_term(&term).is_none(),
            "past-band ({m}, {e}) must NOT decode — it is wire-refused by design (#1385)",
        );
        reached_past_band += 1;
    }

    assert!(
        reached_in_band > 0 && reached_past_band > 0,
        "VACUOUS: in-band={reached_in_band} past-band={reached_past_band} — a band with no \
         cases proves nothing, and this assert is the only thing that separates a real pass \
         from a loop whose every case was skipped by the else-continue guard",
    );
}
