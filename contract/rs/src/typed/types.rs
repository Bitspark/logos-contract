use super::{foundation, Expr};
use std::collections::BTreeSet;

pub const FOUNDATION: &str = "logos/dependent-fragment-1/edition-1";
pub const CHECKER: &str = "logos/typed-check-only-v1/rust";
pub const MAX_INPUT_DEPTH: u32 = 128;
pub const MAX_DEPTH: u32 = 512;

/// Receiver-owned declarations, checked in order on every call. Identities use
/// exact UTF-8 byte equality, without normalization. Duplicate dependency entries
/// count physically toward limits and form a set in the accepted result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Assume {
        name: String,
        ty: Expr,
        dependencies: Vec<String>,
    },
    Define {
        name: String,
        ty: Expr,
        value: Expr,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement {
    pub foundation: String,
    pub declarations: Vec<Declaration>,
    pub context: Vec<Expr>,
    pub expected: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Policy {
    pub foundation: String,
    pub checker: String,
    pub dependencies: Vec<String>,
}

/// Limits use the same exact u32 range in all three bindings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub input_nodes: u32,
    pub input_depth: u32,
    pub collection_entries: u32,
    pub name_bytes: u32,
    pub work: u32,
    pub depth: u32,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input_nodes: 100_000,
            input_depth: MAX_INPUT_DEPTH,
            collection_entries: 4_096,
            name_bytes: 256,
            work: 1_000_000,
            depth: MAX_DEPTH,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Invalid {
    MalformedInput,
    EscapedVariable,
    UnknownConstant(String),
    DuplicateConstant,
    MissingAssumptions,
    EmptyConstantName,
    ExpectedUniverse,
    ExpectedFunction,
    ExpectedSigma,
    TypeMismatch,
}

impl Invalid {
    pub fn code(&self) -> &'static str {
        match self {
            Self::MalformedInput => "malformed-input",
            Self::EscapedVariable => "escaped-variable",
            Self::UnknownConstant(_) => "unknown-constant",
            Self::DuplicateConstant => "duplicate-constant",
            Self::MissingAssumptions => "missing-assumptions",
            Self::EmptyConstantName => "empty-constant-name",
            Self::ExpectedUniverse => "expected-universe",
            Self::ExpectedFunction => "expected-function",
            Self::ExpectedSigma => "expected-sigma",
            Self::TypeMismatch => "type-mismatch",
        }
    }
}

impl From<foundation::Error> for Invalid {
    fn from(value: foundation::Error) -> Self {
        match value {
            foundation::Error::EscapedVariable => Self::EscapedVariable,
            foundation::Error::UnknownConstant(name) => Self::UnknownConstant(name),
            foundation::Error::DuplicateConstant => Self::DuplicateConstant,
            foundation::Error::MissingAssumptions => Self::MissingAssumptions,
            foundation::Error::EmptyConstantName => Self::EmptyConstantName,
            foundation::Error::ExpectedUniverse => Self::ExpectedUniverse,
            foundation::Error::ExpectedFunction => Self::ExpectedFunction,
            foundation::Error::ExpectedSigma => Self::ExpectedSigma,
            foundation::Error::TypeMismatch => Self::TypeMismatch,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Incomplete {
    InputNodes,
    InputDepth,
    CollectionEntries,
    NameBytes,
    Work,
    Depth,
    UniverseCapacity,
    IndexCapacity,
}

impl Incomplete {
    pub fn code(self) -> &'static str {
        match self {
            Self::InputNodes => "input-nodes",
            Self::InputDepth => "input-depth",
            Self::CollectionEntries => "collection-entries",
            Self::NameBytes => "name-bytes",
            Self::Work => "work",
            Self::Depth => "depth",
            Self::UniverseCapacity => "universe-capacity",
            Self::IndexCapacity => "index-capacity",
        }
    }
}

impl From<foundation::Limit> for Incomplete {
    fn from(value: foundation::Limit) -> Self {
        match value {
            foundation::Limit::Work => Self::Work,
            foundation::Limit::Depth => Self::Depth,
            foundation::Limit::UniverseCapacity => Self::UniverseCapacity,
            foundation::Limit::IndexCapacity => Self::IndexCapacity,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unsupported {
    Foundation,
    UnadmittedFoundation,
    UnadmittedChecker,
    UnadmittedDependency(String),
}

impl Unsupported {
    pub fn code(&self) -> &'static str {
        match self {
            Self::Foundation => "foundation",
            Self::UnadmittedFoundation => "unadmitted-foundation",
            Self::UnadmittedChecker => "unadmitted-checker",
            Self::UnadmittedDependency(_) => "unadmitted-dependency",
        }
    }
}

/// A checking result; rejection and noncompletion are never logical negation.
#[derive(Debug)]
pub enum Outcome {
    Accepted(Box<Accepted>),
    Invalid(Diagnostic<Invalid>),
    Incomplete(Diagnostic<Incomplete>),
    Unsupported(Diagnostic<Unsupported>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Preflight,
    Declaration,
    Context,
    Expected,
    Candidate,
    Policy,
    Snapshot,
}

impl Phase {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Preflight => "preflight",
            Self::Declaration => "declaration",
            Self::Context => "context",
            Self::Expected => "expected",
            Self::Candidate => "candidate",
            Self::Policy => "policy",
            Self::Snapshot => "snapshot",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Location {
    pub phase: Phase,
    pub index: Option<u32>,
}

impl Location {
    pub fn new(phase: Phase) -> Self {
        Self { phase, index: None }
    }

    pub fn indexed(phase: Phase, index: u32) -> Self {
        Self {
            phase,
            index: Some(index),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic<T> {
    pub cause: T,
    pub location: Location,
}

impl Outcome {
    pub fn status(&self) -> &'static str {
        match self {
            Self::Accepted(_) => "accepted",
            Self::Invalid(_) => "invalid",
            Self::Incomplete(_) => "incomplete",
            Self::Unsupported(_) => "unsupported",
        }
    }

    pub fn code(&self) -> Option<&'static str> {
        match self {
            Self::Accepted(_) => None,
            Self::Invalid(diagnostic) => Some(diagnostic.cause.code()),
            Self::Incomplete(diagnostic) => Some(diagnostic.cause.code()),
            Self::Unsupported(diagnostic) => Some(diagnostic.cause.code()),
        }
    }

    pub fn location(&self) -> Option<Location> {
        match self {
            Self::Accepted(_) => None,
            Self::Invalid(diagnostic) => Some(diagnostic.location),
            Self::Incomplete(diagnostic) => Some(diagnostic.location),
            Self::Unsupported(diagnostic) => Some(diagnostic.location),
        }
    }

    pub(super) fn at(mut self, location: Location) -> Self {
        match &mut self {
            Self::Accepted(_) => {}
            Self::Invalid(diagnostic) => diagnostic.location = location,
            Self::Incomplete(diagnostic) => diagnostic.location = location,
            Self::Unsupported(diagnostic) => diagnostic.location = location,
        }
        self
    }

    pub(super) fn invalid(cause: Invalid) -> Self {
        Self::Invalid(Diagnostic {
            cause,
            location: Location::new(Phase::Preflight),
        })
    }

    pub(super) fn incomplete(cause: Incomplete) -> Self {
        Self::Incomplete(Diagnostic {
            cause,
            location: Location::new(Phase::Preflight),
        })
    }

    pub(super) fn unsupported(cause: Unsupported) -> Self {
        Self::Unsupported(Diagnostic {
            cause,
            location: Location::new(Phase::Policy),
        })
    }
}

/// Only the production gate constructs this immutable, invocation-bound value.
#[derive(Debug)]
pub struct Accepted {
    pub(super) statement: Statement,
    pub(super) candidate: Expr,
    pub(super) policy: Policy,
    pub(super) used_constants: BTreeSet<String>,
    pub(super) dependencies: BTreeSet<String>,
    pub(super) steps: u64,
}

impl Accepted {
    pub fn statement(&self) -> &Statement {
        &self.statement
    }

    pub fn candidate(&self) -> &Expr {
        &self.candidate
    }

    pub fn policy(&self) -> &Policy {
        &self.policy
    }

    pub fn used_constants(&self) -> &BTreeSet<String> {
        &self.used_constants
    }

    pub fn dependencies(&self) -> &BTreeSet<String> {
        &self.dependencies
    }

    pub fn steps(&self) -> u64 {
        self.steps
    }

    pub fn foundation(&self) -> &'static str {
        FOUNDATION
    }

    pub fn checker(&self) -> &'static str {
        CHECKER
    }
}
