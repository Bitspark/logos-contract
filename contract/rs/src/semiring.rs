//! The `Semiring` SPI and its registration audit (ADR 0031 D1, G3; v2 §14.3). **[PROPOSED]**
//! (ADR 0035 D7: a new extension seam enters at `[PROPOSED]`; its vector parity is not a tier.)
//!
//! A semiring is the algebra an annotated evaluation combines values in: `add` (⊕) joins
//! alternative derivations, `mul` (⊗) joins the premises of one derivation, `zero` is the
//! value of no derivation and `one` the value of an empty conjunction. ADR 0031 puts it on the
//! path checkable theories already took: the checker may consult a semiring it did not link,
//! because the verdict NAMES it by identity and what it names is pure.
//!
//! # The obligations of an implementation
//!
//! - **Pure, total over its carrier up to its declared capacity bounds, deterministic.**
//!   [`Semiring::add`] and [`Semiring::mul`] answer [`SemiringAnswer::NotAnElement`] exactly when
//!   an operand is not an element ([`Semiring::is_element`]). On elements they answer an element,
//!   the same one every time, or, for a result past a bound the carrier declares,
//!   [`SemiringAnswer::Stopped`] with a capacity non-completion (ADR 0031 D1 as clarified on
//!   #1821): not decided, never "no such element". Configuration lives
//!   inside the value and is pinned by its declared identity, as for a [`Theory`](crate::Theory).
//! - **Laws declared, never inferred.** [`Semiring::laws`] declares the five optional laws of
//!   v2 §14.3 ([`LawDeclaration`]). The semiring axioms themselves are not declarable: ⊕ is
//!   associative and commutative with identity `zero`, ⊗ is associative with identity `one`,
//!   `zero` annihilates, and ⊗ distributes over ⊕. A semiring whose ⊗ is commutative declares
//!   [`LawDeclaration::commutative`]; ⊕ is always commutative.
//! - **Identity computed by the contract.** [`semiring_identity`] folds the declared laws into
//!   the declared `(id, version, config_digest)`, so changing a declared law changes the
//!   identity a verdict names, whatever the implementation reports (ADR 0031 D1).
//!
//! # What the audit can and cannot say
//!
//! [`audit_semiring`] evaluates every axiom and every declared law over a finite sample set,
//! in one pinned order ([`SemiringLaw::AUDIT_ORDER`]), and reports the first counterexample.
//! **A finite sample can only refute a law, never prove one.** A passing audit is therefore
//! [`SemiringAudit::NoCounterexample`]: no counterexample in these samples, not "verified". A
//! tuple on which an operation stopped is undecided, and a law no tuple decided is VACUOUS
//! ([`SemiringAudit::Vacuous`]), which is a state, never a pass.
//! Failing rejects registration (§14.3); passing admits a declared law as a claim the verdict
//! names, never as a premise it hides (ADR 0031 D5).
//!
//! The audit is deterministic, so its verdict, including the witness, is pinned tri-core by
//! `vectors/semiring.json`.

use crate::completion::{CauseScope, NonCompletion};
use crate::intval::BigInt;
use crate::spi::{fold_component_identity, ComponentIdentity};
use crate::term::Term;
use ontos_core::Value;
use sha2::{Digest, Sha256};

/// Domain separator of a semiring's computed identity digest ([`semiring_identity_of`]).
pub const SEMIRING_IDENTITY_PREFIX: &[u8] = b"logos-core/semiring-identity/v1\n";

/// The most caller samples [`audit_semiring`] evaluates. The audit is cubic in the sample
/// count (associativity, distributivity, retraction), so a larger set is refused by name
/// ([`SemiringAudit::SampleLimit`]) rather than run for an unbounded time.
pub const SEMIRING_AUDIT_SAMPLE_LIMIT: usize = 16;

/// The five optional laws a semiring declares (v2 §14.3; ADR 0031 D1). Each is a CLAIM the
/// audit tests on samples, never a fact it proves.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct LawDeclaration {
    /// `a ⊕ a = a`.
    pub idempotent: bool,
    /// `one ⊕ a = one` (absorptive): the law a fixpoint argument over recursion relies on.
    pub bounded: bool,
    /// The natural order (`a ≤ b` iff `a ⊕ c = b` for some `c`) is antisymmetric.
    pub monotone: bool,
    /// `a ⊗ b = b ⊗ a` (a commutative semiring; ⊕ is commutative by axiom).
    pub commutative: bool,
    /// ⊕ is cancellative (`a ⊕ b = a ⊕ c` implies `b = c`), so a contribution can be retracted.
    pub supports_retraction: bool,
}

impl LawDeclaration {
    /// The bit of [`idempotent`](Self::idempotent) in [`bits`](Self::bits).
    pub const IDEMPOTENT_BIT: u8 = 1;
    /// The bit of [`bounded`](Self::bounded).
    pub const BOUNDED_BIT: u8 = 2;
    /// The bit of [`monotone`](Self::monotone).
    pub const MONOTONE_BIT: u8 = 4;
    /// The bit of [`commutative`](Self::commutative).
    pub const COMMUTATIVE_BIT: u8 = 8;
    /// The bit of [`supports_retraction`](Self::supports_retraction).
    pub const SUPPORTS_RETRACTION_BIT: u8 = 16;

    /// The declaration as one byte, the form [`semiring_identity_of`] hashes.
    pub fn bits(&self) -> u8 {
        let mut bits = 0;
        if self.idempotent {
            bits |= Self::IDEMPOTENT_BIT;
        }
        if self.bounded {
            bits |= Self::BOUNDED_BIT;
        }
        if self.monotone {
            bits |= Self::MONOTONE_BIT;
        }
        if self.commutative {
            bits |= Self::COMMUTATIVE_BIT;
        }
        if self.supports_retraction {
            bits |= Self::SUPPORTS_RETRACTION_BIT;
        }
        bits
    }

    /// Whether the audit tests `law` for a semiring with this declaration: every axiom always,
    /// a declarable law only when it is declared.
    pub fn obliges(&self, law: SemiringLaw) -> bool {
        match law {
            SemiringLaw::Carrier
            | SemiringLaw::AddClosed
            | SemiringLaw::MulClosed
            | SemiringLaw::AddAssociative
            | SemiringLaw::AddCommutative
            | SemiringLaw::AddIdentity
            | SemiringLaw::MulAssociative
            | SemiringLaw::MulIdentity
            | SemiringLaw::Annihilation
            | SemiringLaw::Distributive => true,
            SemiringLaw::Idempotent => self.idempotent,
            SemiringLaw::Bounded => self.bounded,
            SemiringLaw::Monotone => self.monotone,
            SemiringLaw::Commutative => self.commutative,
            SemiringLaw::SupportsRetraction => self.supports_retraction,
        }
    }
}

/// A law [`audit_semiring`] tests: the ten axioms of a semiring over a carrier, then the five
/// declarable laws of [`LawDeclaration`]. The [`name`](Self::name)s are the wire spelling
/// `vectors/semiring.json` pins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SemiringLaw {
    /// `zero`, `one` and every sample are elements.
    Carrier,
    /// `a ⊕ b` is an element, and the same one when asked again.
    AddClosed,
    /// `a ⊗ b` is an element, and the same one when asked again.
    MulClosed,
    /// `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`.
    AddAssociative,
    /// `a ⊕ b = b ⊕ a`.
    AddCommutative,
    /// `zero ⊕ a = a = a ⊕ zero`.
    AddIdentity,
    /// `(a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)`.
    MulAssociative,
    /// `one ⊗ a = a = a ⊗ one`.
    MulIdentity,
    /// `zero ⊗ a = zero = a ⊗ zero`.
    Annihilation,
    /// `a ⊗ (b ⊕ c) = a ⊗ b ⊕ a ⊗ c` and `(a ⊕ b) ⊗ c = a ⊗ c ⊕ b ⊗ c`.
    Distributive,
    /// The declared [`LawDeclaration::idempotent`].
    Idempotent,
    /// The declared [`LawDeclaration::bounded`].
    Bounded,
    /// The declared [`LawDeclaration::monotone`].
    Monotone,
    /// The declared [`LawDeclaration::commutative`].
    Commutative,
    /// The declared [`LawDeclaration::supports_retraction`].
    SupportsRetraction,
}

impl SemiringLaw {
    /// The order [`audit_semiring`] tests the laws in; its first counterexample is the one it
    /// reports.
    pub const AUDIT_ORDER: [SemiringLaw; 15] = [
        SemiringLaw::Carrier,
        SemiringLaw::AddClosed,
        SemiringLaw::MulClosed,
        SemiringLaw::AddAssociative,
        SemiringLaw::AddCommutative,
        SemiringLaw::AddIdentity,
        SemiringLaw::MulAssociative,
        SemiringLaw::MulIdentity,
        SemiringLaw::Annihilation,
        SemiringLaw::Distributive,
        SemiringLaw::Idempotent,
        SemiringLaw::Bounded,
        SemiringLaw::Monotone,
        SemiringLaw::Commutative,
        SemiringLaw::SupportsRetraction,
    ];

    /// The law's wire name.
    pub fn name(self) -> &'static str {
        match self {
            SemiringLaw::Carrier => "carrier",
            SemiringLaw::AddClosed => "add_closed",
            SemiringLaw::MulClosed => "mul_closed",
            SemiringLaw::AddAssociative => "add_associative",
            SemiringLaw::AddCommutative => "add_commutative",
            SemiringLaw::AddIdentity => "add_identity",
            SemiringLaw::MulAssociative => "mul_associative",
            SemiringLaw::MulIdentity => "mul_identity",
            SemiringLaw::Annihilation => "annihilation",
            SemiringLaw::Distributive => "distributive",
            SemiringLaw::Idempotent => "idempotent",
            SemiringLaw::Bounded => "bounded",
            SemiringLaw::Monotone => "monotone",
            SemiringLaw::Commutative => "commutative",
            SemiringLaw::SupportsRetraction => "supports_retraction",
        }
    }
}

/// What a semiring operation answered (ADR 0031 D1, as clarified on #1821).
///
/// An operation is total over its carrier **up to the carrier's declared capacity bounds**: on
/// elements it answers an element, or, when the result lies past a bound the carrier declares (an
/// exact decimal's exponent band, say), it stops with a capacity [`NonCompletion`]. A stop is "not
/// decided", never "no such element", so a consumer reports it as a non-completion and never as a
/// rejection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemiringAnswer {
    /// The result, an element of the carrier.
    Element(Value),
    /// An operand is not an element of the carrier.
    NotAnElement,
    /// The operation stopped before establishing its result.
    Stopped(NonCompletion),
}

impl SemiringAnswer {
    /// The stop a carrier answers for a result past its declared capacity bound: a capacity
    /// non-completion of this one operation (literal scope).
    pub fn capacity() -> Self {
        SemiringAnswer::Stopped(NonCompletion::capacity(CauseScope::Literal))
    }

    /// Apply `op` to an element; a non-element or a stop is carried unchanged.
    fn then(self, op: impl FnOnce(Value) -> SemiringAnswer) -> SemiringAnswer {
        match self {
            SemiringAnswer::Element(value) => op(value),
            SemiringAnswer::NotAnElement => SemiringAnswer::NotAnElement,
            SemiringAnswer::Stopped(cause) => SemiringAnswer::Stopped(cause),
        }
    }
}

/// A semiring the checker may consult (ADR 0031 D1). **[PROPOSED]**
///
/// Elements are ontos [`Value`]s, so one object-safe trait carries every carrier and a
/// `Box<dyn Semiring>` can be bound like a `Box<dyn Theory>`. See the module documentation
/// for the obligations an implementation takes on.
pub trait Semiring {
    /// The `(id, version, config_digest)` the implementation declares. The identity a verdict
    /// names is [`semiring_identity`], which folds [`laws`](Self::laws) into it.
    fn declared_identity(&self) -> ComponentIdentity;
    /// The optional laws this semiring claims (v2 §14.3).
    fn laws(&self) -> LawDeclaration;
    /// The identity of ⊕: the value of no derivation.
    fn zero(&self) -> Value;
    /// The identity of ⊗: the value of an empty conjunction.
    fn one(&self) -> Value;
    /// Whether `value` is an element of the carrier.
    fn is_element(&self, value: &Value) -> bool;
    /// `a ⊕ b`; [`SemiringAnswer::NotAnElement`] exactly when an operand is not an element.
    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer;
    /// `a ⊗ b`; [`SemiringAnswer::NotAnElement`] exactly when an operand is not an element.
    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer;
}

/// The identity a semiring with this declared identity and these laws is named by:
/// `(id, version, SHA-256(prefix ‖ len(id) ‖ id ‖ len(version) ‖ version ‖ config_digest ‖
/// laws))`, each length a big-endian `u64` and the laws [`LawDeclaration::bits`]. The id and
/// version are kept; the digest commits to the configuration AND the declared laws (ADR 0031
/// D1), so two declarations that differ in one law are two identities.
pub fn semiring_identity_of(
    declared: &ComponentIdentity,
    laws: LawDeclaration,
) -> ComponentIdentity {
    let mut hasher = Sha256::new();
    hasher.update(SEMIRING_IDENTITY_PREFIX);
    fold_component_identity(&mut hasher, declared);
    hasher.update([laws.bits()]);
    ComponentIdentity::new(
        declared.id.clone(),
        declared.version.clone(),
        hasher.finalize().into(),
    )
}

/// The identity `semiring` is named by: [`semiring_identity_of`] over its declared identity
/// and its declared laws, each read once.
pub fn semiring_identity(semiring: &dyn Semiring) -> ComponentIdentity {
    semiring_identity_of(&semiring.declared_identity(), semiring.laws())
}

/// How many tuples of the evaluated set decided a law, and how many were undecided because an
/// operation the law names stopped. A law with no decided tuple is VACUOUS: the samples never
/// exercised it, which is a state of the audit, never a pass (design/0004).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LawTally {
    /// The law.
    pub law: SemiringLaw,
    /// Tuples on which every operation the law names answered, and the law held.
    pub decided: usize,
    /// Tuples on which an operation the law names stopped.
    pub undecided: usize,
}

impl LawTally {
    /// No decided tuple exercised the law.
    pub fn is_vacuous(&self) -> bool {
        self.decided == 0
    }
}

/// The verdict of [`audit_semiring`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemiringAudit {
    /// No counterexample in the samples, and every law tested was decided on at least one tuple.
    /// **Not a proof**: a finite sample can only refute a law.
    NoCounterexample {
        /// Every law evaluated, in audit order (the ten axioms and the declared laws), with its
        /// tally.
        laws: Vec<LawTally>,
    },
    /// No counterexample in the samples, but at least one law tested is vacuous: no tuple
    /// decided it, because every operation it needed stopped. Not a pass; registration needs
    /// samples that exercise every law.
    Vacuous {
        /// Every law evaluated, in audit order, with its tally; a vacuous law reads `decided: 0`.
        laws: Vec<LawTally>,
    },
    /// The first law, in audit order, a decided tuple refutes, with the elements that refute it
    /// (one, two or three, in the order the law names them). Registration is rejected.
    Counterexample {
        /// The refuted law.
        law: SemiringLaw,
        /// The refuting elements.
        witness: Vec<Value>,
    },
    /// More samples than [`SEMIRING_AUDIT_SAMPLE_LIMIT`]; nothing was evaluated.
    SampleLimit {
        /// The number of samples given.
        given: usize,
        /// [`SEMIRING_AUDIT_SAMPLE_LIMIT`].
        limit: usize,
    },
}

/// Audit `semiring` over `samples` (v2 §14.3 `logos::conformance::audit_semiring`; ADR 0031
/// G3).
///
/// The evaluated set is `[zero, one, samples…]` in that order. The laws are tested in
/// [`SemiringLaw::AUDIT_ORDER`], every axiom and each law [`laws`](Semiring::laws) declares;
/// within a law the elements are enumerated in set order, the first operand outermost. Each
/// tuple is read in three values: the law holds, fails, or is undecided because an operation
/// it names stopped (strong Kleene: a failing conjunct fails the tuple even beside a stop). An
/// operation answering [`SemiringAnswer::NotAnElement`] on elements fails the law it was
/// evaluated for. The first failing tuple is the verdict; otherwise a law no tuple decided makes
/// the verdict [`SemiringAudit::Vacuous`]. The declared laws are read once.
pub fn audit_semiring(semiring: &dyn Semiring, samples: &[Value]) -> SemiringAudit {
    if samples.len() > SEMIRING_AUDIT_SAMPLE_LIMIT {
        return SemiringAudit::SampleLimit {
            given: samples.len(),
            limit: SEMIRING_AUDIT_SAMPLE_LIMIT,
        };
    }
    let declared = semiring.laws();
    let zero = semiring.zero();
    let one = semiring.one();
    let mut set = Vec::with_capacity(samples.len() + 2);
    set.push(zero.clone());
    set.push(one.clone());
    set.extend(samples.iter().cloned());
    let audit = Audit {
        semiring,
        set: &set,
        zero: &zero,
        one: &one,
    };
    let mut laws = Vec::new();
    for law in SemiringLaw::AUDIT_ORDER {
        if !declared.obliges(law) {
            continue;
        }
        let mut tally = LawTally {
            law,
            decided: 0,
            undecided: 0,
        };
        if let Some(witness) = audit.counterexample(law, &mut tally) {
            return SemiringAudit::Counterexample { law, witness };
        }
        laws.push(tally);
    }
    if laws.iter().any(LawTally::is_vacuous) {
        SemiringAudit::Vacuous { laws }
    } else {
        SemiringAudit::NoCounterexample { laws }
    }
}

/// A law's reading on one tuple: strong Kleene over the operations' answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Truth {
    Holds,
    Fails,
    Undecided,
}

impl Truth {
    fn of(holds: bool) -> Truth {
        if holds {
            Truth::Holds
        } else {
            Truth::Fails
        }
    }
}

/// Strong Kleene conjunction: a failing side fails, two holding sides hold, otherwise undecided.
fn both(left: Truth, right: Truth) -> Truth {
    if left == Truth::Fails || right == Truth::Fails {
        Truth::Fails
    } else if left == Truth::Holds && right == Truth::Holds {
        Truth::Holds
    } else {
        Truth::Undecided
    }
}

/// Strong Kleene disjunction: a holding side holds, two failing sides fail, otherwise undecided.
fn either(left: Truth, right: Truth) -> Truth {
    if left == Truth::Holds || right == Truth::Holds {
        Truth::Holds
    } else if left == Truth::Fails && right == Truth::Fails {
        Truth::Fails
    } else {
        Truth::Undecided
    }
}

/// Strong Kleene negation.
fn not(truth: Truth) -> Truth {
    match truth {
        Truth::Holds => Truth::Fails,
        Truth::Fails => Truth::Holds,
        Truth::Undecided => Truth::Undecided,
    }
}

/// Both answers are the same element. A non-element on either side fails; otherwise a stop on
/// either side is undecided.
fn same(left: SemiringAnswer, right: SemiringAnswer) -> Truth {
    match (left, right) {
        (SemiringAnswer::Element(l), SemiringAnswer::Element(r)) => Truth::of(l == r),
        (SemiringAnswer::NotAnElement, _) | (_, SemiringAnswer::NotAnElement) => Truth::Fails,
        (SemiringAnswer::Stopped(_), _) | (_, SemiringAnswer::Stopped(_)) => Truth::Undecided,
    }
}

/// The answer is the element `expected`.
fn gives(answer: SemiringAnswer, expected: &Value) -> Truth {
    match answer {
        SemiringAnswer::Element(value) => Truth::of(value == *expected),
        SemiringAnswer::NotAnElement => Truth::Fails,
        SemiringAnswer::Stopped(_) => Truth::Undecided,
    }
}

/// One audit run: the semiring and the evaluated set.
struct Audit<'a> {
    semiring: &'a dyn Semiring,
    set: &'a [Value],
    zero: &'a Value,
    one: &'a Value,
}

impl Audit<'_> {
    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.semiring.add(a, b)
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.semiring.mul(a, b)
    }

    /// `p ⊕ q` over two answers.
    fn sum(&self, p: SemiringAnswer, q: SemiringAnswer) -> SemiringAnswer {
        p.then(|p| q.then(|q| self.add(&p, &q)))
    }

    /// `a ≤ b` in the natural order, witnessed inside the set: `a ⊕ c = b` for some sample `c`.
    fn below(&self, a: &Value, b: &Value) -> Truth {
        let mut found = Truth::Fails;
        for c in self.set {
            found = either(found, gives(self.add(a, c), b));
        }
        found
    }

    /// An operation's answer is an element, and the same one when asked again.
    fn closed(&self, first: SemiringAnswer, again: SemiringAnswer) -> Truth {
        match first {
            SemiringAnswer::Element(value) => {
                let member = Truth::of(self.semiring.is_element(&value));
                both(member, gives(again, &value))
            }
            SemiringAnswer::NotAnElement => Truth::Fails,
            SemiringAnswer::Stopped(_) => Truth::Undecided,
        }
    }

    /// The first tuple of the set on which `law` fails, or `None`; `tally` counts the decided
    /// and the undecided tuples.
    fn counterexample(&self, law: SemiringLaw, tally: &mut LawTally) -> Option<Vec<Value>> {
        match law {
            SemiringLaw::Carrier => self.each(tally, |a| Truth::of(self.semiring.is_element(a))),
            SemiringLaw::AddIdentity => self.each(tally, |a| {
                let left = gives(self.add(self.zero, a), a);
                both(left, gives(self.add(a, self.zero), a))
            }),
            SemiringLaw::MulIdentity => self.each(tally, |a| {
                let left = gives(self.mul(self.one, a), a);
                both(left, gives(self.mul(a, self.one), a))
            }),
            SemiringLaw::Annihilation => self.each(tally, |a| {
                let left = gives(self.mul(self.zero, a), self.zero);
                both(left, gives(self.mul(a, self.zero), self.zero))
            }),
            SemiringLaw::Idempotent => self.each(tally, |a| gives(self.add(a, a), a)),
            SemiringLaw::Bounded => self.each(tally, |a| gives(self.add(self.one, a), self.one)),
            SemiringLaw::AddClosed
            | SemiringLaw::MulClosed
            | SemiringLaw::AddCommutative
            | SemiringLaw::Monotone
            | SemiringLaw::Commutative => self.pairs(law, tally),
            SemiringLaw::AddAssociative
            | SemiringLaw::MulAssociative
            | SemiringLaw::Distributive
            | SemiringLaw::SupportsRetraction => self.triples(law, tally),
        }
    }

    /// A law over pairs, read on `(a, b)`. Only the pair laws reach it.
    fn on_pair(&self, law: SemiringLaw, a: &Value, b: &Value) -> Truth {
        match law {
            SemiringLaw::AddClosed => self.closed(self.add(a, b), self.add(a, b)),
            SemiringLaw::MulClosed => self.closed(self.mul(a, b), self.mul(a, b)),
            SemiringLaw::AddCommutative => same(self.add(a, b), self.add(b, a)),
            SemiringLaw::Monotone => {
                let up = self.below(a, b);
                let down = self.below(b, a);
                either(Truth::of(a == b), either(not(up), not(down)))
            }
            SemiringLaw::Commutative => same(self.mul(a, b), self.mul(b, a)),
            SemiringLaw::Carrier
            | SemiringLaw::AddAssociative
            | SemiringLaw::AddIdentity
            | SemiringLaw::MulAssociative
            | SemiringLaw::MulIdentity
            | SemiringLaw::Annihilation
            | SemiringLaw::Distributive
            | SemiringLaw::Idempotent
            | SemiringLaw::Bounded
            | SemiringLaw::SupportsRetraction => Truth::Undecided,
        }
    }

    /// A law over triples, read on `(a, b, c)`. Only the triple laws reach it.
    fn on_triple(&self, law: SemiringLaw, a: &Value, b: &Value, c: &Value) -> Truth {
        match law {
            SemiringLaw::AddAssociative => same(
                self.add(a, b).then(|ab| self.add(&ab, c)),
                self.add(b, c).then(|bc| self.add(a, &bc)),
            ),
            SemiringLaw::MulAssociative => same(
                self.mul(a, b).then(|ab| self.mul(&ab, c)),
                self.mul(b, c).then(|bc| self.mul(a, &bc)),
            ),
            SemiringLaw::Distributive => {
                let left = same(
                    self.add(b, c).then(|bc| self.mul(a, &bc)),
                    self.sum(self.mul(a, b), self.mul(a, c)),
                );
                let right = same(
                    self.add(a, b).then(|ab| self.mul(&ab, c)),
                    self.sum(self.mul(a, c), self.mul(b, c)),
                );
                both(left, right)
            }
            SemiringLaw::SupportsRetraction => {
                let unequal = not(same(self.add(a, b), self.add(a, c)));
                either(Truth::of(b == c), unequal)
            }
            SemiringLaw::Carrier
            | SemiringLaw::AddClosed
            | SemiringLaw::MulClosed
            | SemiringLaw::AddCommutative
            | SemiringLaw::AddIdentity
            | SemiringLaw::MulIdentity
            | SemiringLaw::Annihilation
            | SemiringLaw::Idempotent
            | SemiringLaw::Bounded
            | SemiringLaw::Monotone
            | SemiringLaw::Commutative => Truth::Undecided,
        }
    }

    fn each(&self, tally: &mut LawTally, holds: impl Fn(&Value) -> Truth) -> Option<Vec<Value>> {
        for a in self.set {
            if tally.count(holds(a)) {
                return Some(vec![a.clone()]);
            }
        }
        None
    }

    fn pairs(&self, law: SemiringLaw, tally: &mut LawTally) -> Option<Vec<Value>> {
        for a in self.set {
            for b in self.set {
                if tally.count(self.on_pair(law, a, b)) {
                    return Some(vec![a.clone(), b.clone()]);
                }
            }
        }
        None
    }

    fn triples(&self, law: SemiringLaw, tally: &mut LawTally) -> Option<Vec<Value>> {
        for a in self.set {
            for b in self.set {
                for c in self.set {
                    if tally.count(self.on_triple(law, a, b, c)) {
                        return Some(vec![a.clone(), b.clone(), c.clone()]);
                    }
                }
            }
        }
        None
    }
}

impl LawTally {
    /// Count one tuple's reading; `true` when it refutes the law.
    fn count(&mut self, truth: Truth) -> bool {
        match truth {
            Truth::Holds => {
                self.decided += 1;
                false
            }
            Truth::Undecided => {
                self.undecided += 1;
                false
            }
            Truth::Fails => true,
        }
    }
}

/// The counting semiring `(ℕ, +, ×, 0, 1)` (v2 §8.3 `Counting`; ADR 0031 D2), a core semiring.
///
/// Its carrier is the non-negative integers in the frozen ontos-data `int` embedding, unbounded
/// (the contract's [`BigInt`]), so `add` and `mul` are exact and total on elements. It declares
/// `monotone`, `commutative` and `supports_retraction`; it is neither idempotent nor bounded,
/// so recursion through it does not converge in general. Identity
/// `logos-core/counting-semiring@1.0.0`, zero configuration.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CountingSemiring;

impl CountingSemiring {
    /// The counting semiring.
    pub fn new() -> Self {
        CountingSemiring
    }
}

impl Semiring for CountingSemiring {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/counting-semiring".to_vec(),
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
        BigInt::zero().to_int_value()
    }

    fn one(&self) -> Value {
        BigInt::from_i128(1).to_int_value()
    }

    fn is_element(&self, value: &Value) -> bool {
        natural(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (natural(a), natural(b)) {
            (Some(x), Some(y)) => SemiringAnswer::Element(x.add(&y).to_int_value()),
            _ => SemiringAnswer::NotAnElement,
        }
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        match (natural(a), natural(b)) {
            (Some(x), Some(y)) => SemiringAnswer::Element(x.mul(&y).to_int_value()),
            _ => SemiringAnswer::NotAnElement,
        }
    }
}

/// The non-negative integer `value` embeds, or `None` when it is not one.
fn natural(value: &Value) -> Option<BigInt> {
    let n = BigInt::from_int_term(&Term::from_value(value))?;
    (!n.is_negative()).then_some(n)
}
