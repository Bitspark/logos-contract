//! **[PROPOSED] — the completion algebra**: an outcome that keeps "established false" apart from
//! "did not finish", and the three-valued `not`/`and`/`or` over it (research 0031 row 15, #3164).
//!
//! # Why this exists
//!
//! A decider that stops before it establishes a fact must not report that fact as false. An answer
//! with no arm for "not decided" (the checker SPI's v1 theory outcome had none) reads a stop as
//! `Fails`, and under negation or in the closure check a stop turns into a false positive
//! (research 0031; #3123 is the measured instance). This module is the vocabulary that keeps the
//! three answers apart, and the combinators that compose them without losing the difference.
//!
//! A theory reports "not decided" through
//! [`Theory::decide_ground`](crate::spi::Theory::decide_ground) (#3126, seat:caa's ruling of
//! 2026-09-27; required since checker SPI v2, ADR 0036 D8 change 3): it returns a
//! [`TheoryGround`](crate::TheoryGround), a [`TheoryDecision`] inside a [`Completion`], and
//! [`decision_of`] brings it into the algebra. The search report (#3162), the closure check and
//! `check`'s builtin verification (#3165) read it. The shapes are PROPOSED until the ADR for
//! research 0030 and 0031 (#3147) ratifies them.
//!
//! # The outcome
//!
//! [`Completion<T, L>`] is `Completed(T) | LimitExceeded(L) | NotCompleted(NonCompletion)`, and a
//! ground literal's outcome is [`GroundOutcome<L>`] = `Completion<Decision, L>`, where
//! [`Decision`] is `Holds | Fails { code }`:
//!
//! - `Completed(Holds)` / `Completed(Fails { code })`: the language decided the literal.
//!   `Fails` means the language says the literal is false, never "the implementation reached a
//!   return without a value". [`FalseCode`] says why, and nothing converts a non-completion into it.
//! - `NotCompleted(cause)`: the producer did not decide. [`NonCompletion`] names why.
//! - `LimitExceeded(limit)`: a limit the caller set was reached. The layer that sets a limit owns
//!   its vocabulary (the checker's [`CheckLimits`](crate::check::CheckLimits), the kernel's
//!   `LimitKind`), so the algebra is generic over `L` and only carries it.
//!
//! # Stops and faults
//!
//! A non-completion is one of two things, and its [kind](NonCompletionKind) says which:
//!
//! - A **stop**: the producer ran out of something before it decided. A stop's evidence is not
//!   wrong, only incomplete, so it carries the [scope](CauseScope) its effect reaches.
//!   `capacity`, `work_cap` and `instantiation` take any scope. `host_refusal` and
//!   `reply_unreadable` are request-wide: the host refusal channel is sticky for the whole run.
//! - A **fault**: `inconsistent_theory` and `malformed_outcome` say the evidence itself is
//!   invalid. A fault carries no chosen scope: its reach is everything.
//!
//! [`NonCompletion`]'s fields are private, and its constructors build only these pairs, so a fault
//! at a local scope cannot be constructed (seat:caa's ruling on #3179). The Go and TypeScript
//! twins refuse such a pair at construction and read a hand-built one as `malformed_outcome`.
//!
//! # The algebra
//!
//! Read `H`, `F` and `U` as established true, established false, and not decided. `not`, `and`
//! and `or` are strong Kleene: `¬U = U`, `F ∧ U = F`, `H ∨ U = H`, and the Boolean rules
//! elsewhere. `U` is incomplete knowledge, not a new truth value of the language: `F ∧ U = F`
//! because every way the undecided operand could resolve gives `F`.
//!
//! **Absorption is scoped.** `F ∧ U = F` is sound only if the false conjunct's justification does
//! not rest on whatever stopped. A stop local to one literal, one branch or one enumeration
//! ([`CauseScope::is_absorbable`]) cannot undermine another operand's evidence, so it may be
//! absorbed. A stop at dependency, theory-snapshot or request scope may have compromised every
//! operand's evidence, and a caller's limit is the request's own disposition, so those are
//! **dominant**: never absorbed, by `and` or by `or`. A **fault** outranks even those: reporting
//! a fault as a limit would tell the caller to raise a budget over a defect.
//!
//! Each operand therefore falls in one of five classes, and `and`/`or` return the operand of the
//! highest class, the leftmost one on a tie:
//!
//! ```text
//!          lowest                                                       highest
//! and      Holds  <  absorbable stop  <  Fails  <  dominant stop or limit  <  fault
//! or       Fails  <  absorbable stop  <  Holds  <  dominant stop or limit  <  fault
//! ```
//!
//! The leftmost-on-a-tie rule makes the reported CAUSE depend on operand order, deliberately: two
//! stops of one class carry no order of importance, and inventing one would claim a ranking the
//! vocabulary does not have. The CLASS of the result never depends on order, so neither does a
//! verdict built from it, nor the kernel arm a class maps to. `vectors/completion_algebra.json`
//! pins both halves in every core, and `tests/completion_laws.rs` checks the laws over every
//! outcome the vocabulary can form.

use std::fmt;

/// Where a stop's effect reaches, which decides whether another operand may absorb it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CauseScope {
    /// One ground literal's decision stopped (an arithmetic work cap on one comparison).
    Literal,
    /// One alternative of a search or a disjunction stopped.
    Branch,
    /// An enumeration inside one literal stopped (a collection or aggregate's members).
    Enumeration,
    /// A lower certificate or table this result depends on could not be established.
    Dependency,
    /// The theory's snapshot could not be read completely.
    TheorySnapshot,
    /// The whole request stopped.
    Request,
}

impl CauseScope {
    /// Whether a stop at this scope may be absorbed by an independently established operand
    /// (`F ∧ U = F`, `H ∨ U = H`). Only a stop local to one literal, branch or enumeration can: a
    /// wider stop may have compromised the other operand's evidence too.
    pub fn is_absorbable(self) -> bool {
        match self {
            CauseScope::Literal | CauseScope::Branch | CauseScope::Enumeration => true,
            CauseScope::Dependency | CauseScope::TheorySnapshot | CauseScope::Request => false,
        }
    }

    /// The scope's stable name, as `vectors/completion_algebra.json` spells it.
    pub fn tag(self) -> &'static str {
        match self {
            CauseScope::Literal => "literal",
            CauseScope::Branch => "branch",
            CauseScope::Enumeration => "enumeration",
            CauseScope::Dependency => "dependency",
            CauseScope::TheorySnapshot => "theory_snapshot",
            CauseScope::Request => "request",
        }
    }
}

/// Why a producer did not decide (research 0031's classification table).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NonCompletionKind {
    /// A stop: an implementation capacity, such as native stack depth. Any scope.
    Capacity,
    /// A stop: an internal bounded-work cap the language does not define as failure. Any scope.
    WorkCap,
    /// A stop: an argument was not instantiated enough for the decider to run. Any scope.
    Instantiation,
    /// A stop: a host refused to answer. Request scope: the refusal channel is sticky for the run.
    HostRefusal,
    /// A stop: a host's reply could not be read. Request scope, through the same channel.
    ReplyUnreadable,
    /// A fault: a decider disowned a literal it was routed, so the theory contradicts its own
    /// routing.
    InconsistentTheory,
    /// A fault: an outcome value no constructor could have built (a Go zero value, a TypeScript
    /// object of unknown kind), or a host's reply to a declared builtin that is not a value of the
    /// reply type (bytes that are not a value, or a value that is not `Tuple[subst…]`): the host
    /// broke its channel's contract (#2734 3e-iii, the logos coordinator's ruling on #2734). A reply
    /// that is well-formed but nested past the reader's depth is NOT this fault: it is the
    /// `ReplyUnreadable` stop, a capacity of the reader.
    MalformedOutcome,
}

impl NonCompletionKind {
    /// Whether this kind is a fault: the evidence is invalid, not merely incomplete.
    pub fn is_fault(self) -> bool {
        match self {
            NonCompletionKind::InconsistentTheory | NonCompletionKind::MalformedOutcome => true,
            NonCompletionKind::Capacity
            | NonCompletionKind::WorkCap
            | NonCompletionKind::Instantiation
            | NonCompletionKind::HostRefusal
            | NonCompletionKind::ReplyUnreadable => false,
        }
    }

    /// The kind's stable name, as `vectors/completion_algebra.json` spells it.
    pub fn tag(self) -> &'static str {
        match self {
            NonCompletionKind::Capacity => "capacity",
            NonCompletionKind::WorkCap => "work_cap",
            NonCompletionKind::Instantiation => "instantiation",
            NonCompletionKind::HostRefusal => "host_refusal",
            NonCompletionKind::ReplyUnreadable => "reply_unreadable",
            NonCompletionKind::InconsistentTheory => "inconsistent_theory",
            NonCompletionKind::MalformedOutcome => "malformed_outcome",
        }
    }
}

/// Why a producer did not decide: a stop with the scope its effect reaches, or a fault. The
/// fields are private, so only the pairs the constructors build exist.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NonCompletion {
    kind: NonCompletionKind,
    scope: Option<CauseScope>,
}

/// A kind and scope that do not form a [`NonCompletion`]: a fault with a scope, a request-wide
/// stop at a narrower scope, or a stop with none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IllegalCause {
    pub kind: NonCompletionKind,
    pub scope: Option<CauseScope>,
}

impl fmt::Display for IllegalCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.scope {
            Some(scope) => write!(
                f,
                "illegal_cause: {} at {} scope",
                self.kind.tag(),
                scope.tag()
            ),
            None => write!(f, "illegal_cause: {} with no scope", self.kind.tag()),
        }
    }
}

impl std::error::Error for IllegalCause {}

impl NonCompletion {
    /// A capacity stop, reaching `scope`.
    pub fn capacity(scope: CauseScope) -> Self {
        NonCompletion {
            kind: NonCompletionKind::Capacity,
            scope: Some(scope),
        }
    }

    /// A bounded-work stop, reaching `scope`.
    pub fn work_cap(scope: CauseScope) -> Self {
        NonCompletion {
            kind: NonCompletionKind::WorkCap,
            scope: Some(scope),
        }
    }

    /// An instantiation stop, reaching `scope`.
    pub fn instantiation(scope: CauseScope) -> Self {
        NonCompletion {
            kind: NonCompletionKind::Instantiation,
            scope: Some(scope),
        }
    }

    /// A host refusal, request-wide.
    pub fn host_refusal() -> Self {
        NonCompletion {
            kind: NonCompletionKind::HostRefusal,
            scope: Some(CauseScope::Request),
        }
    }

    /// An unreadable host reply, request-wide.
    pub fn reply_unreadable() -> Self {
        NonCompletion {
            kind: NonCompletionKind::ReplyUnreadable,
            scope: Some(CauseScope::Request),
        }
    }

    /// The fault that a theory contradicts its own routing.
    pub fn inconsistent_theory() -> Self {
        NonCompletion {
            kind: NonCompletionKind::InconsistentTheory,
            scope: None,
        }
    }

    /// The fault that an outcome value is none a constructor could have built, or that a host's
    /// reply is not a value of the reply type (#2734 3e-iii).
    pub fn malformed_outcome() -> Self {
        NonCompletion {
            kind: NonCompletionKind::MalformedOutcome,
            scope: None,
        }
    }

    /// The checked constructor, for a decoder: the cause a kind and scope name, or the refusal
    /// when they do not form one (a fault with a scope, a request-wide stop at a narrower scope,
    /// or a stop with none).
    pub fn from_parts(
        kind: NonCompletionKind,
        scope: Option<CauseScope>,
    ) -> Result<Self, IllegalCause> {
        let legal = match kind {
            NonCompletionKind::Capacity
            | NonCompletionKind::WorkCap
            | NonCompletionKind::Instantiation => scope.is_some(),
            NonCompletionKind::HostRefusal | NonCompletionKind::ReplyUnreadable => {
                scope == Some(CauseScope::Request)
            }
            NonCompletionKind::InconsistentTheory | NonCompletionKind::MalformedOutcome => {
                scope.is_none()
            }
        };
        if legal {
            Ok(NonCompletion { kind, scope })
        } else {
            Err(IllegalCause { kind, scope })
        }
    }

    /// Why the producer did not decide.
    pub fn kind(self) -> NonCompletionKind {
        self.kind
    }

    /// How far a stop reaches; `None` for a fault, whose reach is everything.
    pub fn scope(self) -> Option<CauseScope> {
        self.scope
    }
}

/// Why the language says a literal is false. The arithmetic evaluator's domain failures join it
/// with #3161. No conversion from a [`NonCompletion`] or an arbitrary error exists, on purpose.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FalseCode {
    /// The relation was evaluated and does not hold (`1 > 2`; `\+ G` where `G` holds).
    Unsatisfied,
}

impl FalseCode {
    /// The code's stable name, as `vectors/completion_algebra.json` spells it.
    pub fn tag(self) -> &'static str {
        match self {
            FalseCode::Unsatisfied => "unsatisfied",
        }
    }
}

/// The language's decision on a ground literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Decision {
    Holds,
    Fails { code: FalseCode },
}

/// A producer's result: the value, a caller's limit reached, or a stop before the value was
/// established. `L` is the caller's limit vocabulary; see the module docs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Completion<T, L> {
    Completed(T),
    LimitExceeded(L),
    NotCompleted(NonCompletion),
}

/// A ground literal's outcome: decided true or false, a caller's limit, or not decided.
pub type GroundOutcome<L> = Completion<Decision, L>;

/// A theory's decision on a ground literal (#3126, seat:caa's ruling (C)): what
/// [`Theory::decide_ground`](crate::spi::Theory::decide_ground) returns inside a [`Completion`].
///
/// Two vocabularies, each with one owner. [`FalseCode`] is the LANGUAGE's closed vocabulary, and
/// the combinators fold over it. A theory's `Fails { code }` is an OPEN value space: every theory
/// and every consumer owns its codes, and `check` carries them as the `builtin_failed` detail. So
/// the theory's code rides here as data, and [`decision_of`] is the one way into the algebra.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TheoryDecision {
    /// The atom holds.
    Holds,
    /// The theory decided the atom does not hold; `code` is the theory's own name for why.
    Fails { code: String },
}

/// The ONE conversion from a theory's answer to the algebra's [`GroundOutcome`] (#3126, seat:caa's
/// ruling (C)). A theory's false code is the theory's own, so it becomes the language's
/// [`FalseCode::Unsatisfied`]. A non-completion and a limit pass through unchanged: nothing here
/// turns "not decided" into a decision. Every site that folds a theory's answer with
/// [`not`]/[`and`]/[`or`] calls it; a reader that reports the theory's code (`check`'s
/// `builtin_failed` detail) reads the [`TheoryDecision`] before converting.
pub fn decision_of<L>(outcome: Completion<TheoryDecision, L>) -> GroundOutcome<L> {
    match outcome {
        Completion::Completed(TheoryDecision::Holds) => Completion::Completed(Decision::Holds),
        Completion::Completed(TheoryDecision::Fails { .. }) => {
            Completion::Completed(Decision::Fails {
                code: FalseCode::Unsatisfied,
            })
        }
        Completion::LimitExceeded(limit) => Completion::LimitExceeded(limit),
        Completion::NotCompleted(cause) => Completion::NotCompleted(cause),
    }
}

/// The five classes the combinators order (see the module docs).
#[derive(Clone, Copy)]
enum Class {
    Holds,
    Fails,
    Absorbable,
    Dominant,
    Fault,
}

fn class<L>(outcome: &GroundOutcome<L>) -> Class {
    match outcome {
        Completion::Completed(Decision::Holds) => Class::Holds,
        Completion::Completed(Decision::Fails { .. }) => Class::Fails,
        Completion::NotCompleted(cause) => match cause.scope {
            None => Class::Fault,
            Some(scope) if scope.is_absorbable() => Class::Absorbable,
            Some(_) => Class::Dominant,
        },
        Completion::LimitExceeded(_) => Class::Dominant,
    }
}

fn and_rank(class: Class) -> u8 {
    match class {
        Class::Holds => 0,
        Class::Absorbable => 1,
        Class::Fails => 2,
        Class::Dominant => 3,
        Class::Fault => 4,
    }
}

fn or_rank(class: Class) -> u8 {
    match class {
        Class::Fails => 0,
        Class::Absorbable => 1,
        Class::Holds => 2,
        Class::Dominant => 3,
        Class::Fault => 4,
    }
}

/// The operand of the higher rank; `a` on a tie.
fn higher<L>(a: GroundOutcome<L>, b: GroundOutcome<L>, rank: fn(Class) -> u8) -> GroundOutcome<L> {
    if rank(class(&b)) > rank(class(&a)) {
        b
    } else {
        a
    }
}

/// Strong-Kleene negation: `¬H = F`, `¬F = H`, and an undecided outcome or a limit is returned
/// unchanged (`¬U = U`).
pub fn not<L>(a: GroundOutcome<L>) -> GroundOutcome<L> {
    match a {
        Completion::Completed(Decision::Holds) => Completion::Completed(Decision::Fails {
            code: FalseCode::Unsatisfied,
        }),
        Completion::Completed(Decision::Fails { .. }) => Completion::Completed(Decision::Holds),
        Completion::LimitExceeded(limit) => Completion::LimitExceeded(limit),
        Completion::NotCompleted(cause) => Completion::NotCompleted(cause),
    }
}

/// Strong-Kleene conjunction with scoped absorption: `F ∧ U = F` only when `U` is an absorbable
/// stop; a dominant stop or a limit is never absorbed, and a fault outranks both. Returns the
/// higher-class operand, `a` on a tie.
pub fn and<L>(a: GroundOutcome<L>, b: GroundOutcome<L>) -> GroundOutcome<L> {
    higher(a, b, and_rank)
}

/// Strong-Kleene disjunction with scoped absorption: `H ∨ U = H` only when `U` is an absorbable
/// stop; a dominant stop or a limit is never absorbed, and a fault outranks both. Returns the
/// higher-class operand, `a` on a tie.
pub fn or<L>(a: GroundOutcome<L>, b: GroundOutcome<L>) -> GroundOutcome<L> {
    higher(a, b, or_rank)
}
