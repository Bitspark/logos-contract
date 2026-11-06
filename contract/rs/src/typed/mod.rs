//! In-process typed checking against an independently fixed receiver statement.
//!
//! See `docs/spec/typed-check-only.md`. This service checks supplied evidence;
//! interpretation and authenticity of imported semantic premises remain with
//! the receiver. It has no serialized ingress or proof-search operation.

pub mod foundation;
mod gate;
mod preflight;
mod types;

pub use foundation::Expr;
pub use gate::check;
pub use types::{
    Accepted, Declaration, Diagnostic, Incomplete, Invalid, Limits, Location, Outcome, Phase,
    Policy, Statement, Unsupported,
};
pub use types::{CHECKER, FOUNDATION, MAX_DEPTH, MAX_INPUT_DEPTH};
