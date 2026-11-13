//! The provenance core semiring ℕ[X] (v2 §8.3 `Provenance`; ADR 0031 D2): polynomials with
//! natural coefficients over fact identities, the most general commutative semiring an
//! annotation can be read in (every other commutative semiring's value is an image of it).
//! **[PROPOSED]**
//!
//! Its carrier was ruled on #1821 (2026-11-11): one canonical sorted encoding with integer
//! coefficients. A polynomial is a Tuple of terms; a term is `Tuple[int c, Tuple[x…]]`, its
//! coefficient `c ≥ 1` in the frozen ontos-data `int` embedding and its monomial the multiset of
//! its variables, each any ground ontos value (a fact identity), in non-decreasing order of their
//! ontos-codec bytes. The terms are in strictly increasing order of their monomials' codec bytes,
//! so no monomial repeats. Zero is the empty Tuple; one is the single term `1·()`. Coefficients
//! are unbounded, so the operations never stop.

use std::collections::BTreeMap;

use crate::intval::BigInt;
use crate::semiring::{LawDeclaration, Semiring, SemiringAnswer};
use crate::spi::ComponentIdentity;
use crate::term::Term;
use ontos_core::Value;

/// A polynomial as its terms, keyed by the codec bytes of each monomial: (variables,
/// coefficient).
type Terms = BTreeMap<Vec<u8>, (Vec<Value>, BigInt)>;

/// The canonical polynomial `value` encodes, or `None` when it is not one.
fn polynomial(value: &Value) -> Option<Terms> {
    let mut terms = Terms::new();
    let mut last: Option<Vec<u8>> = None;
    for term in value.as_tuple()?.items() {
        let [coefficient, monomial] = term.as_tuple()?.items() else {
            return None;
        };
        let coefficient = BigInt::from_int_term(&Term::from_value(coefficient))?;
        if coefficient.is_negative() || coefficient.is_zero() {
            return None;
        }
        let variables = monomial.as_tuple()?.items().to_vec();
        if !variables.windows(2).all(in_order) {
            return None;
        }
        let key = ontos_codec::encode(monomial);
        if last.as_ref().is_some_and(|previous| *previous >= key) {
            return None;
        }
        last = Some(key.clone());
        terms.insert(key, (variables, coefficient));
    }
    Some(terms)
}

/// Two adjacent variables in non-decreasing codec order.
fn in_order(pair: &[Value]) -> bool {
    ontos_codec::encode(&pair[0]) <= ontos_codec::encode(&pair[1])
}

/// The canonical encoding of `terms`.
fn polynomial_value(terms: &Terms) -> Value {
    let mut items = Vec::with_capacity(terms.len());
    for (variables, coefficient) in terms.values() {
        let monomial = Value::tuple(variables.clone());
        items.push(Value::tuple(vec![coefficient.to_int_value(), monomial]));
    }
    Value::tuple(items)
}

/// Add `coefficient · variables` into `terms`.
fn accumulate(terms: &mut Terms, variables: Vec<Value>, coefficient: BigInt) {
    let key = ontos_codec::encode(&Value::tuple(variables.clone()));
    match terms.get_mut(&key) {
        Some((_, existing)) => *existing = existing.add(&coefficient),
        None => {
            terms.insert(key, (variables, coefficient));
        }
    }
}

/// The provenance semiring ℕ[X] (v2 §8.3 `Provenance`; ADR 0031 D2), a core semiring: an
/// annotation records which facts, how many times and in which combinations, an answer was
/// derived from.
///
/// It declares `monotone`, `commutative` and `supports_retraction`; it is neither idempotent
/// nor bounded. Identity `logos-core/provenance-semiring@1.0.0`, zero configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProvenanceSemiring;

impl ProvenanceSemiring {
    /// The provenance semiring.
    pub fn new() -> Self {
        ProvenanceSemiring
    }
}

impl Semiring for ProvenanceSemiring {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/provenance-semiring".to_vec(),
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
        polynomial_value(&Terms::new())
    }

    fn one(&self) -> Value {
        let mut terms = Terms::new();
        accumulate(&mut terms, Vec::new(), BigInt::from_i128(1));
        polynomial_value(&terms)
    }

    fn is_element(&self, value: &Value) -> bool {
        polynomial(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some(mut sum), Some(y)) = (polynomial(a), polynomial(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        for (variables, coefficient) in y.into_values() {
            accumulate(&mut sum, variables, coefficient);
        }
        SemiringAnswer::Element(polynomial_value(&sum))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some(x), Some(y)) = (polynomial(a), polynomial(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        let mut product = Terms::new();
        for (left, p) in x.values() {
            for (right, q) in y.values() {
                let mut variables = left.clone();
                variables.extend(right.iter().cloned());
                variables.sort_by_cached_key(ontos_codec::encode);
                accumulate(&mut product, variables, p.mul(q));
            }
        }
        SemiringAnswer::Element(polynomial_value(&product))
    }
}
