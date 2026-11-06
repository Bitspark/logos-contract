//! #2258 lane 3's L3.3b: a COUNT (ADR 0023) inside a sealed clause, over a relation a strictly
//! lower certificate seals.
//!
//! Admission is the `NegLower` rule (#2344, `seat:caa`'s Q2): the counted predicate must resolve,
//! through [`resolve_lower_seals`](super::cert_stack::resolve_lower_seals), to the unique, exact,
//! Valid certificate at a strictly lower level that seals it. Counting the certificate's OWN table
//! stays `cert_scope_incomplete`, because for a non-monotone operator that table would be the one
//! under construction.
//!
//! Two places evaluate such a count, and both read the lower table through the certificate's
//! [`CertView`], with ADR 0023's one fold (`crate::aggregate::evaluate_aggregate`):
//!
//! - the CLOSURE join, as a count stage ([`count_stage`]): it binds its result variable, or tests
//!   it when the variable is already ground, and costs one join step per lower row it scans
//!   (`seat:caa`'s Q4, the binder convention);
//! - the SUPPORT gate, for a [`SupportRef::CountLower`](crate::cert::SupportRef::CountLower) ref
//!   ([`resolve_count_lower`]): the edge's substitution fixes the filter and the claimed result,
//!   and the recomputed aggregate must equal it.
//!
//! The fold's own outcomes keep their meaning in both places. `min`/`max` over no matching row has
//! no value (`agg_empty_undefined`), so the count literal is false: the closure emits no tuple, and
//! a support ref citing a result is unsupported. A non-integer column under `sum`/`min`/`max` is an
//! unserved semantics (v1 is integer-only), refused as `count_attr_out_of_range`.

use super::cert::CertPlace;
use super::cert_stack::CertView;
use super::join_index::charge_join_steps;
use super::{CheckLimits, RejectionCode};
use crate::cert::{CertId, RelationTable};
use crate::derivation::GroundFilter;
use crate::intval::BigInt;
use crate::program::CountLit;
use crate::term::{Subst, Term, VarId};

/// The aggregate of `count` over `table` under the ground `filter`. The counted relation's arity
/// must agree with the table's, and every filter position and the projected column must lie inside
/// it (`count_attr_out_of_range`, the structural checks `verify_count_premise` runs before its
/// fold); then ADR 0023's one fold, whose errors are its own codes.
pub(super) fn aggregate_over(
    count: &CountLit<Term>,
    filter: &GroundFilter,
    table: &RelationTable,
) -> Result<BigInt, (RejectionCode, String)> {
    let arity = table.arity;
    let out_of_range = |detail: String| (RejectionCode::CountAttrOutOfRange, detail);
    if count.pred.arity != arity {
        return Err(out_of_range(format!(
            "count predicate arity {} does not match the sealed table arity {arity}",
            count.pred.arity
        )));
    }
    if let Some((pos, _)) = filter.iter().find(|(pos, _)| *pos >= arity) {
        return Err(out_of_range(format!(
            "count filter position {pos} is outside predicate arity {arity}"
        )));
    }
    if let Some(attr) = count.project.attr().filter(|attr| *attr >= arity) {
        return Err(out_of_range(format!(
            "aggregate projection attr {attr} is outside predicate arity {arity}"
        )));
    }
    crate::aggregate::evaluate_aggregate(&count.pred.pred, table.rows.iter(), filter, count.project)
}

/// The count's filter under `subst`, each value ground, or `None` if one is not.
fn ground_filter(count: &CountLit<Term>, subst: &Subst) -> Option<GroundFilter> {
    count
        .filter
        .iter()
        .map(|(pos, term)| term.substitute(subst).erase_ground().map(|v| (*pos, v)))
        .collect()
}

/// The lower table a count reads, or `cert_scope_incomplete`: the scope gate admits a count only
/// over a predicate resolved to a strictly lower certificate, so this is the defensive backstop.
fn lower_table<'a>(
    count: &CountLit<Term>,
    view: &CertView<'a>,
) -> Result<&'a RelationTable, (RejectionCode, String)> {
    let pred = &count.pred.pred;
    if !view.reads_lower(pred) {
        return Err((
            RejectionCode::CertScopeIncomplete,
            format!(
                "count over predicate {:?}, which no strictly lower certificate seals",
                String::from_utf8_lossy(pred.bytes())
            ),
        ));
    }
    view.table(pred).ok_or_else(|| {
        (
            RejectionCode::CertScopeIncomplete,
            format!(
                "count over predicate {:?}, whose lower certificate has no sealed extension",
                String::from_utf8_lossy(pred.bytes())
            ),
        )
    })
}

/// One CLOSURE COUNT STAGE at its evaluation point: charge one join step per row of the lower
/// table it scans, fold, then bind the result variable (recorded in `newly`, so the caller can
/// undo it) or test a result already ground. `Ok(false)` when the count has no value
/// (`agg_empty_undefined`) or differs from a ground result; the filter must be ground here (the
/// scope gate's safety rule), else `cert_scope_incomplete`, never a silent false.
pub(super) fn count_stage(
    count: &CountLit<Term>,
    subst: &mut Subst,
    view: &CertView<'_>,
    limits: &CheckLimits,
    verify: bool,
    joins: &mut usize,
    newly: &mut Vec<VarId>,
) -> Result<bool, (RejectionCode, String)> {
    let table = lower_table(count, view)?;
    charge_join_steps(joins, table.rows.len(), view.cert, limits, verify)?;
    let Some(filter) = ground_filter(count, subst) else {
        return Err((
            RejectionCode::CertScopeIncomplete,
            format!(
                "closure count over predicate {:?} has a filter that is not ground at its evaluation point (unsafe existential)",
                String::from_utf8_lossy(count.pred.pred.bytes())
            ),
        ));
    };
    let folded = match aggregate_over(count, &filter, table) {
        Ok(n) => n.to_int_term(),
        Err((RejectionCode::AggEmptyUndefined, _)) => return Ok(false),
        Err(e) => return Err(e),
    };
    // `Term` implements `Drop`, so the slot is matched by reference.
    match &count.count.substitute(subst) {
        Term::Var(v) => {
            subst.insert(v.clone(), folded);
            newly.push(v.clone());
            Ok(true)
        }
        bound @ (Term::Atom(_) | Term::Tuple(_)) => Ok(matches!(
            (bound.erase_ground(), folded.erase_ground()),
            (Some(a), Some(b)) if a == b
        )),
    }
}

/// Resolve a support edge's `CountLower { cert }` ref for body literal `k`, a count: `cited` must
/// be the strictly lower certificate the counted predicate resolved to (its own certificate is
/// refused, a count never reads the table under construction), the filter and the result must be
/// ground under the edge's `subst`, and the aggregate recomputed over the lower table must equal
/// the result. A count with no value (`agg_empty_undefined`) supports nothing.
pub(super) fn resolve_count_lower(
    k: usize,
    count: &CountLit<Term>,
    cited: CertId,
    subst: &Subst,
    view: &CertView<'_>,
    place: CertPlace,
) -> Result<(), (RejectionCode, String)> {
    let unsupported = |detail: String| (RejectionCode::CertUnsupported, detail);
    let pred = &count.pred.pred;
    let Some((index, table)) =
        super::cert_support::check_support_ref_cert(k, cited, pred, view, place)?
    else {
        return Err(unsupported(format!(
            "support body ref {k}: CountLower cites its own certificate for predicate {:?} (a count must read a strictly lower certificate)",
            String::from_utf8_lossy(pred.bytes())
        )));
    };
    let Some(filter) = ground_filter(count, subst) else {
        return Err(unsupported(format!(
            "support body ref {k}: count filter not ground under subst"
        )));
    };
    let Some(claimed) = count.count.substitute(subst).erase_ground() else {
        return Err(unsupported(format!(
            "support body ref {k}: count result not ground under subst"
        )));
    };
    let recomputed = match aggregate_over(count, &filter, table) {
        Ok(n) => n,
        Err((RejectionCode::AggEmptyUndefined, detail)) => {
            return Err(unsupported(format!(
                "support body ref {k}: the count has no value over certificate {index}'s table ({detail})"
            )))
        }
        Err(e) => return Err(e),
    };
    if BigInt::from_int_term(&Term::from_value(&claimed)) == Some(recomputed.clone()) {
        Ok(())
    } else {
        Err(unsupported(format!(
            "support body ref {k}: count result does not equal the aggregate recomputed over certificate {index}'s table ({})",
            recomputed.to_decimal_string()
        )))
    }
}
