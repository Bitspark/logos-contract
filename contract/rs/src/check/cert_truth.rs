//! #3165: a closure literal's THREE-VALUED truth (research 0031; seat:caa's rulings on #3126).
//! Split out of `cert.rs` when the three-valued fold took that file past the 2 000 impl-LOC
//! ceiling. A theory literal is read through the theory's `decide_ground` and the one conversion
//! into the completion algebra ([`decision_of`]); a stop stays NOT DECIDED, never false, and the
//! join ([`super::cert`]) folds a tuple's body with [`completion::and`]. The soundness argument is
//! the banner in `cert.rs`.

use super::cert::count_join_step;
use super::cert_stack::CertView;
use super::{builtin_not_decided, is_disowned, CheckLimits, RejectionCode};
use crate::completion::{self, decision_of, Completion, Decision, FalseCode, GroundOutcome};
use crate::engine::NoCallerLimit;
use crate::literal::GroundLiteral;
use crate::program::BodyLit;
use crate::spi::Theory;
use crate::term::Term;

/// A decided truth value in the completion algebra.
pub(super) fn truth(holds: bool) -> GroundOutcome<NoCallerLimit> {
    if holds {
        Completion::Completed(Decision::Holds)
    } else {
        Completion::Completed(Decision::Fails {
            code: FalseCode::Unsatisfied,
        })
    }
}

/// #3165: what a tuple's body, folded so far with [`completion::and`], lets the join do.
/// `Ok(false)` prunes the tuple: a decided false makes the rule instance hold whatever the head,
/// and it absorbs a literal-scoped stop (`F ∧ U = F`). `Ok(true)` continues, the body true so far
/// or not decided at a scope another literal's false may still absorb. A stop no false can absorb
/// is refused at once (`builtin_not_decided`): the instance's truth cannot be established.
///
/// The join prunes at the FIRST decided false and evaluates nothing after it, as its pinned cost
/// model requires, so a stop in a later literal is never seen. That is sound: the false is a
/// completed decision, and the instance it falsifies holds whatever the later literal is.
pub(super) fn body_continues(
    body: &GroundOutcome<NoCallerLimit>,
) -> Result<bool, (RejectionCode, String)> {
    match body {
        Completion::Completed(Decision::Holds) => Ok(true),
        Completion::Completed(Decision::Fails { .. }) => Ok(false),
        Completion::LimitExceeded(never) => match *never {},
        Completion::NotCompleted(cause) if cause.scope().is_some_and(|s| s.is_absorbable()) => {
            Ok(true)
        }
        Completion::NotCompleted(cause) => Err(builtin_not_decided(*cause)),
    }
}

/// Evaluate one FILTER literal at its evaluation point: it must be ground there (§3.2), and
/// is decided against `E` (+ the pinned Theory) with polarity by [`eval_body_literal`]. Costs
/// one join step. Never a silent false: a literal that is not ground at its point is a HARD
/// error (`cert_scope_incomplete`), the same backstop the enumeration carried. #3165: the
/// outcome is three-valued, since a theory literal may not be decided.
pub(super) fn filter_outcome(
    body_lit: &BodyLit<Term>,
    subst: &crate::term::Subst,
    view: &CertView<'_>,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
    joins: &mut usize,
) -> Result<GroundOutcome<NoCallerLimit>, (RejectionCode, String)> {
    count_join_step(joins, view.cert, limits, verify)?;
    let Some(grounded) = body_lit
        .substitute(subst)
        .as_inner()
        .and_then(|goal| goal.as_ground())
    else {
        return Err((
            RejectionCode::CertScopeIncomplete,
            format!(
                "closure body literal on predicate {:?} is not ground at its evaluation point (unsafe existential)",
                String::from_utf8_lossy(body_lit.pred().bytes())
            ),
        ));
    };
    eval_body_literal(body_lit, &grounded, view, theory)
}

/// One grounded body literal's truth against `E` (+ theory), with polarity (#3165: three-valued;
/// a theory literal may be not decided, and `not(U) = U`): a `Pos` literal must be present
/// (sealed-table membership or `Holds`);
/// a `Neg` literal must be ABSENT from its sealed table — this cert's own, or the exact table
/// of the strictly lower certificate it reads the predicate from (#2258 (a)). An undecidable
/// literal — a predicate neither sealed for this cert nor theory-owned — is a HARD error
/// (`cert_scope_incomplete`): §3.2 has already proved this is unreachable for an
/// in-scope clause, so this is the defensive backstop that guarantees closure never
/// silently treats an undecidable (possibly-true) literal as false and under-fires.
fn eval_body_literal(
    body_lit: &BodyLit<Term>,
    grounded: &GroundLiteral,
    view: &CertView<'_>,
    theory: &dyn Theory,
) -> Result<GroundOutcome<NoCallerLimit>, (RejectionCode, String)> {
    let undecidable = || {
        (
            RejectionCode::CertScopeIncomplete,
            format!(
                "closure body literal on predicate {:?} is neither sealed nor theory-owned (undecidable)",
                String::from_utf8_lossy(grounded.pred.bytes())
            ),
        )
    };
    match body_lit {
        BodyLit::Pos(_) => {
            if theory.owns(&grounded.pred) {
                return theory_truth(view, theory, grounded);
            }
            match view.table(&grounded.pred) {
                Some(t) => Ok(truth(view.contains(t, grounded))),
                None => Err(undecidable()),
            }
        }
        BodyLit::Neg(_) => {
            // Mirror the Pos branch: a negated theory-owned (builtin) literal is
            // decided LIVE by the theory (`\+ b` is true iff `b` does NOT Hold), so a
            // `\+ builtin` in a sealed-stratum rule body is certifiable rather than
            // hard-rejected. The `undecidable()` backstop remains only for a predicate
            // neither sealed nor theory-owned. (Paired with the safety gate, a negated
            // builtin still cannot smuggle an unbounded existential.)
            if theory.owns(&grounded.pred) {
                return theory_truth(view, theory, grounded).map(completion::not);
            }
            match view.table(&grounded.pred) {
                Some(t) => Ok(truth(!view.contains(t, grounded))),
                None => Err(undecidable()),
            }
        }
        // ADR 0023 / #2258 L3.3b: a count is a count STAGE in the closure (`Step::Count`) and a
        // `CountLower` ref in support, never a filter, so it never reaches here: a hard error
        // rather than a silent false (closure must never under-fire).
        BodyLit::Count(_) => Err((
            RejectionCode::CertScopeIncomplete,
            "closure body literal is a count over a sealed-scope clause (must target a lower stratum)".into(),
        )),
    }
}

/// A theory-owned literal's truth inside the closure (#3022 step 4, research 0028 A8; #3165):
/// the theory's [`decide_ground`](Theory::decide_ground), through the ONE conversion into the
/// algebra ([`decision_of`]). `Holds` is true, `Fails` false, and a stop stays NOT DECIDED, never
/// false: the join folds it and refuses the instance unless a false absorbs it or the head is
/// present. The disowning fault (`NotMine` after `owns()` said yes) is an inconsistent theory, and
/// it REFUSES by name (`predicate_partition_violation`, as a `Builtin` node's does), never reads
/// as false: a positive filter read false would let the closure under-fire and pass a table that
/// is not closed.
fn theory_truth(
    view: &CertView<'_>,
    theory: &dyn Theory,
    grounded: &GroundLiteral,
) -> Result<GroundOutcome<NoCallerLimit>, (RejectionCode, String)> {
    // theory_decisions: one `decide_ground` call, counted on the view.
    view.count_decision();
    let ground = theory.decide_ground(grounded);
    if let Completion::NotCompleted(cause) = &ground {
        if is_disowned(cause) {
            return Err((
                RejectionCode::PredicatePartitionViolation,
                format!(
                    "closure body literal on predicate {:?}: the theory owns it but returned NotMine",
                    String::from_utf8_lossy(grounded.pred.bytes())
                ),
            ));
        }
    }
    Ok(decision_of(ground))
}
