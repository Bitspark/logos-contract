//! The product semiring (v2 §14.2; ADR 0031 D1): two semirings combined componentwise, so one
//! annotation carries both at once (a count and a cost, say). **[PROPOSED]**
//!
//! As ruled on #1821 (Q23 to Q28), a product is binary, member 0 then member 1. Its element is a
//! bare `Tuple[a, b]`, `a` an element of the first member and `b` of the second, and its `zero`
//! and `one` are the pairs of the members' own. `add` and `mul` answer
//! [`SemiringAnswer::NotAnElement`] for an operand that is not an element before any member runs.
//! Otherwise the first member's operation runs first: its non-element or its stop is the
//! product's answer, and the second member is not consulted. A product declares exactly the laws
//! both members declare; no law is declarable on the product itself.
//!
//! Its declared identity is `logos-core/product-semiring@1.0.0`, its config digest
//! `SHA-256(PRODUCT_SEMIRING_PREFIX ‖ for each member in order: u64be(len id) ‖ id ‖
//! u64be(len version) ‖ version ‖ config_digest)` over each member's COMPUTED identity
//! ([`semiring_identity`]), in the per-member layout
//! [`compound_identity_of`](crate::compound_identity_of) folds. So the swapped product, or one
//! whose member declares one more law, is another identity. The identity a verdict names folds
//! the product's laws into that, as for every semiring.

use crate::semiring::{semiring_identity, LawDeclaration, Semiring, SemiringAnswer};
use crate::spi::{fold_component_identity, ComponentIdentity};
use ontos_core::Value;
use sha2::{Digest, Sha256};

/// Domain separator of a product semiring's declared config digest.
pub const PRODUCT_SEMIRING_PREFIX: &[u8] = b"logos-core/product-semiring/v1\n";

/// The product of two semirings (v2 §14.2), member 0 then member 1: elements are pairs, and
/// `add` and `mul` act componentwise. **[PROPOSED]**
///
/// See the module documentation for its carrier, the order its members run in, its laws and its
/// identity.
pub struct ProductSemiring {
    first: Box<dyn Semiring + Send + Sync>,
    second: Box<dyn Semiring + Send + Sync>,
}

impl ProductSemiring {
    /// The product of `first` and `second`, in that order.
    pub fn new(
        first: Box<dyn Semiring + Send + Sync>,
        second: Box<dyn Semiring + Send + Sync>,
    ) -> Self {
        ProductSemiring { first, second }
    }

    /// The two items of `value` when it is an element: an arity-2 Tuple whose first item is an
    /// element of the first member and whose second item is an element of the second.
    fn parts<'v>(&self, value: &'v Value) -> Option<(&'v Value, &'v Value)> {
        let [a, b] = value.as_tuple()?.items() else {
            return None;
        };
        let elements = self.first.is_element(a) && self.second.is_element(b);
        elements.then_some((a, b))
    }
}

impl Semiring for ProductSemiring {
    fn declared_identity(&self) -> ComponentIdentity {
        let mut hasher = Sha256::new();
        hasher.update(PRODUCT_SEMIRING_PREFIX);
        for member in [&*self.first, &*self.second] {
            fold_component_identity(&mut hasher, &semiring_identity(member));
        }
        ComponentIdentity::new(
            b"logos-core/product-semiring".to_vec(),
            b"1.0.0".to_vec(),
            hasher.finalize().into(),
        )
    }

    fn laws(&self) -> LawDeclaration {
        let (first, second) = (self.first.laws(), self.second.laws());
        LawDeclaration {
            idempotent: first.idempotent && second.idempotent,
            bounded: first.bounded && second.bounded,
            monotone: first.monotone && second.monotone,
            commutative: first.commutative && second.commutative,
            supports_retraction: first.supports_retraction && second.supports_retraction,
        }
    }

    fn zero(&self) -> Value {
        Value::tuple([self.first.zero(), self.second.zero()])
    }

    fn one(&self) -> Value {
        Value::tuple([self.first.one(), self.second.one()])
    }

    fn is_element(&self, value: &Value) -> bool {
        self.parts(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some((a0, a1)), Some((b0, b1))) = (self.parts(a), self.parts(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        pair_of(self.first.add(a0, b0), || self.second.add(a1, b1))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some((a0, a1)), Some((b0, b1))) = (self.parts(a), self.parts(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        pair_of(self.first.mul(a0, b0), || self.second.mul(a1, b1))
    }
}

/// The product's answer from the first member's answer and, only when that is an element, the
/// second member's: the first non-element or stop is the product's answer, and two elements are
/// their pair.
fn pair_of(first: SemiringAnswer, second: impl FnOnce() -> SemiringAnswer) -> SemiringAnswer {
    let head = match first {
        SemiringAnswer::Element(head) => head,
        SemiringAnswer::NotAnElement => return SemiringAnswer::NotAnElement,
        SemiringAnswer::Stopped(cause) => return SemiringAnswer::Stopped(cause),
    };
    match second() {
        SemiringAnswer::Element(tail) => SemiringAnswer::Element(Value::tuple([head, tail])),
        SemiringAnswer::NotAnElement => SemiringAnswer::NotAnElement,
        SemiringAnswer::Stopped(cause) => SemiringAnswer::Stopped(cause),
    }
}
