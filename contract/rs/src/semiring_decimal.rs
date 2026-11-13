//! The two decimal core semirings of v2 §8.3 (ADR 0031 D2), `Tropical` and `Probability`, over
//! the contract's exact decimal ([`BigDecimal`], the frozen ontos-data `decimal` embedding).
//! **[PROPOSED]**
//!
//! Their carriers were ruled on #1821 (2026-11-11): exact only, no float (#331).
//!
//! - **An element is a CANONICAL non-negative decimal**: `decimal(int m, int e)` with a non-zero
//!   `m` not divisible by 10, zero only as `decimal(0, 0)`, and `e` inside the decimal value band
//!   (`|e| ≤ 65536`, #2679). An integer value is the decimal with `e ≥ 0` (`decimal(5, 0)`). An
//!   `int` embedding is NOT an element: two spellings of one value would break the axioms under
//!   value equality.
//! - **Tropical** adds `+∞`, the atom `inf`, as its zero.
//! - **Both carriers declare the decimal's capacity bounds** (ADR 0031 D1 as clarified on
//!   #1821): a sum whose operands need an alignment shift past the decimal's cap (#3126), or a
//!   result whose exponent leaves the band, is a capacity stop ([`SemiringAnswer::capacity`]):
//!   not decided, never an element and never a rejection. (The arithmetic theory reads an
//!   out-of-band result as the language's "no value"; a semiring carrier reads it as a bound it
//!   declares.)

use crate::decval::{BigDecimal, DecimalError};
use crate::intval::BigInt;
use crate::semiring::{LawDeclaration, Semiring, SemiringAnswer};
use crate::spi::ComponentIdentity;
use crate::term::Term;
use ontos_core::Value;

/// The atom Tropical's `+∞` is spelled with.
pub const TROPICAL_INFINITY: &[u8] = b"inf";

/// The canonical non-negative decimal `value` embeds, or `None` when it is not one.
fn non_negative(value: &Value) -> Option<BigDecimal> {
    let decimal = BigDecimal::from_decimal_term(&Term::from_value(value))?;
    (!decimal.is_negative()).then_some(decimal)
}

/// A decimal operation's result as a semiring answer: the element, or a capacity stop for a
/// result the decimal cannot carry.
fn decimal_answer(result: Result<BigDecimal, DecimalError>) -> SemiringAnswer {
    match result {
        Ok(decimal) => SemiringAnswer::Element(decimal.to_decimal_value()),
        Err(error) => capacity_of(error),
    }
}

/// Every decimal error a sum or a product meets is a bound the carrier declares. (`+` and `×`
/// never divide, so the two division errors cannot arise; they are read the same way.)
fn capacity_of(error: DecimalError) -> SemiringAnswer {
    match error {
        DecimalError::AlignmentCap
        | DecimalError::OutsideDomain
        | DecimalError::DivisionByZero
        | DecimalError::NonTerminating => SemiringAnswer::capacity(),
    }
}

/// A Tropical element: a finite cost or `+∞`.
enum Cost {
    Finite(BigDecimal),
    Infinite,
}

fn infinity() -> Value {
    Value::atom(TROPICAL_INFINITY.to_vec())
}

fn cost(value: &Value) -> Option<Cost> {
    if *value == infinity() {
        return Some(Cost::Infinite);
    }
    non_negative(value).map(Cost::Finite)
}

/// The tropical semiring `(ℚ≥0 ∪ {+∞}, min, +, +∞, 0)` over exact decimals (v2 §8.3
/// `Tropical`; ADR 0031 D2), a core semiring: shortest-path cost.
///
/// It declares `idempotent`, `bounded` (`min(0, a) = 0`, so recursion through it converges),
/// `monotone` and `commutative`; it does not support retraction. Identity
/// `logos-core/tropical-semiring@1.0.0`, zero configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TropicalSemiring;

impl TropicalSemiring {
    /// The tropical semiring.
    pub fn new() -> Self {
        TropicalSemiring
    }
}

impl Semiring for TropicalSemiring {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/tropical-semiring".to_vec(),
            b"1.0.0".to_vec(),
            [0u8; 32],
        )
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: true,
            bounded: true,
            monotone: true,
            commutative: true,
            supports_retraction: false,
        }
    }

    fn zero(&self) -> Value {
        infinity()
    }

    fn one(&self) -> Value {
        BigDecimal::zero().to_decimal_value()
    }

    fn is_element(&self, value: &Value) -> bool {
        cost(value).is_some()
    }

    /// `min(a, b)`; `+∞` is its identity.
    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (cost(a), cost(b)) {
            (Some(Cost::Infinite), Some(_)) => SemiringAnswer::Element(b.clone()),
            (Some(_), Some(Cost::Infinite)) => SemiringAnswer::Element(a.clone()),
            (Some(Cost::Finite(x)), Some(Cost::Finite(y))) => {
                SemiringAnswer::Element(if y < x { b.clone() } else { a.clone() })
            }
            _ => SemiringAnswer::NotAnElement,
        }
    }

    /// `a + b`; `+∞` absorbs.
    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (cost(a), cost(b)) {
            (Some(Cost::Finite(x)), Some(Cost::Finite(y))) => decimal_answer(x.add(&y)),
            (Some(_), Some(_)) => SemiringAnswer::Element(infinity()),
            _ => SemiringAnswer::NotAnElement,
        }
    }
}

/// The probability semiring `(ℚ≥0, +, ×, 0, 1)` over exact decimals (v2 §8.3
/// `Probability(Independence::Assumed)`, §14.4; ADR 0031 D2), a core semiring: sum-product, as
/// ruled on #1821.
///
/// The product assumes the facts of one derivation independent, and the sum assumes the
/// derivations of one answer disjoint. Derivations that share base facts are therefore counted
/// twice and a value can exceed 1: that is the declared interpretation §14.4 names, not an
/// error. It declares `monotone`, `commutative` and `supports_retraction`; it is neither
/// idempotent nor bounded, so recursion through it does not converge in general. Identity
/// `logos-core/probability-semiring@1.0.0`, zero configuration. (The best-single-derivation
/// semiring `(max, ×)` is a different semiring, and would be named differently.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProbabilitySemiring;

impl ProbabilitySemiring {
    /// The probability semiring.
    pub fn new() -> Self {
        ProbabilitySemiring
    }
}

impl Semiring for ProbabilitySemiring {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/probability-semiring".to_vec(),
            b"1.0.0".to_vec(),
            [0u8; 32],
        )
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: false,
            bounded: false,
            monotone: true,
            commutative: true,
            supports_retraction: true,
        }
    }

    fn zero(&self) -> Value {
        BigDecimal::zero().to_decimal_value()
    }

    fn one(&self) -> Value {
        BigDecimal::from_bigint(BigInt::from_i128(1)).to_decimal_value()
    }

    fn is_element(&self, value: &Value) -> bool {
        non_negative(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (non_negative(a), non_negative(b)) {
            (Some(x), Some(y)) => decimal_answer(x.add(&y)),
            _ => SemiringAnswer::NotAnElement,
        }
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (non_negative(a), non_negative(b)) {
            (Some(x), Some(y)) => decimal_answer(x.mul(&y)),
            _ => SemiringAnswer::NotAnElement,
        }
    }
}
