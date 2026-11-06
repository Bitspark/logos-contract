//! ADR 0023's ONE aggregate semantics (#2258 lane 3's L3.3, `seat:caa`'s condition (1)): the fold a
//! `count`, `count_distinct`, `sum`, `min` or `max` literal denotes over the rows of a relation.
//!
//! The checker verifies a claimed aggregate with it (the count-premise gate in `check`), the
//! certificate producer computes the `k` it claims with it, and a bottom-up engine evaluates a count
//! clause with it. So no engine can derive a value the checker would not recompute: a second
//! implementation of the fold is exactly what would break dual conformance.

use crate::check::RejectionCode;
use crate::derivation::GroundFilter;
use crate::intval::BigInt;
use crate::literal::{GroundLiteral, Symbol};
use crate::program::ProjectSpec;
use crate::term::Term;
use ontos_core::Value;

/// The canonical `null()` marker value (ADR 0023 Phase 0 null handling). With ontos's
/// nullary-compound convention, `null()` is `Tuple[Atom("null")]`, the same shape a nullary goal
/// `p()` reads as. `count_distinct` **excludes** a projected value equal to this marker (SQL-style).
/// Recognized structurally so the rs oracle does not depend on a newer ontos `null()` constructor;
/// the go/ts mirrors recognize the same shape.
pub fn is_null_value(v: &Value) -> bool {
    matches!(v.as_tuple(), Some(t) if t.items() == [Value::atom(b"null".to_vec())])
}

/// Fold the rows of `pred` that match `filter` under `project`, in ONE linear scan:
///
/// ```text
/// Rows              the number of matching rows
/// Distinct { attr } the number of distinct values of column attr, by canonical encoding,
///                   EXCLUDING null()
/// Sum { attr }      the integer sum of column attr; empty sums to 0
/// Min/Max { attr }  the integer extreme of column attr; empty is UNDEFINED
/// ```
///
/// `rows` are read as a SET: the caller hands each distinct row once (a sealed table is sorted and
/// deduplicated, a least model holds each fact once), so `Rows` counts facts, not proofs. A filter
/// position or projection column outside a row's arity simply does not match; checking both
/// against the relation's arity is the caller's (the checker does it against the sealed table
/// first, with its own codes).
///
/// # Errors
///
/// The checker's own codes, so a caller that surfaces them reports what `check` would:
/// `count_attr_out_of_range` when a matching row's column is not a canonical integer under
/// `sum`/`min`/`max` (v1 folds are integer-only), and `agg_empty_undefined` for `min`/`max` over no
/// matching row (no infinities, no sentinels).
pub fn evaluate_aggregate<'a>(
    pred: &Symbol,
    rows: impl IntoIterator<Item = &'a GroundLiteral>,
    filter: &GroundFilter,
    project: ProjectSpec,
) -> Result<BigInt, (RejectionCode, String)> {
    let matching: Vec<&GroundLiteral> = rows
        .into_iter()
        .filter(|row| {
            filter
                .iter()
                .all(|(pos, val)| row.args.get(*pos as usize) == Some(val))
        })
        .collect();
    let name = || String::from_utf8_lossy(pred.bytes()).into_owned();
    // A matching row's `attr` column as a canonical integer, for a numeric fold.
    let int_column = |attr: u32| -> Result<Vec<BigInt>, (RejectionCode, String)> {
        let mut values = Vec::with_capacity(matching.len());
        for row in &matching {
            let Some(projected) = row.args.get(attr as usize) else {
                continue;
            };
            match BigInt::from_int_term(&Term::from_value(projected)) {
                Some(v) => values.push(v),
                None => {
                    return Err((
                        RejectionCode::CountAttrOutOfRange,
                        format!(
                            "aggregate column {attr} of {:?} is not a sealed numeric (int) value — v1 sum/min/max are integer-only",
                            name()
                        ),
                    ));
                }
            }
        }
        Ok(values)
    };
    match project {
        ProjectSpec::Rows => Ok(BigInt::from_i128(matching.len() as i128)),
        ProjectSpec::Distinct { attr } => {
            let mut keys: Vec<Vec<u8>> = Vec::with_capacity(matching.len());
            for row in &matching {
                let Some(projected) = row.args.get(attr as usize) else {
                    continue;
                };
                if is_null_value(projected) {
                    continue; // count_distinct EXCLUDES null() (ADR 0023 Phase 0).
                }
                keys.push(ontos_codec::encode(projected));
            }
            keys.sort();
            keys.dedup();
            Ok(BigInt::from_i128(keys.len() as i128))
        }
        // SUM: set semantics over the distinct rows; empty ⇒ 0 (#587).
        ProjectSpec::Sum { attr } => Ok(int_column(attr)?
            .iter()
            .fold(BigInt::zero(), |acc, v| acc.add(v))),
        // MIN / MAX: empty ⇒ UNDEFINED (#587: no infinities, no sentinels). Otherwise the exact
        // integer extreme (BigInt total order).
        ProjectSpec::Min { attr } | ProjectSpec::Max { attr } => {
            let values = int_column(attr)?;
            let is_min = matches!(project, ProjectSpec::Min { .. });
            let Some(first) = values.first() else {
                return Err((
                    RejectionCode::AggEmptyUndefined,
                    format!(
                        "{} over {:?} has no matching rows — the {} of an empty set is undefined",
                        if is_min { "min" } else { "max" },
                        name(),
                        if is_min { "minimum" } else { "maximum" },
                    ),
                ));
            };
            let mut extreme = first.clone();
            for v in &values[1..] {
                let take = if is_min { v < &extreme } else { v > &extreme };
                if take {
                    extreme = v.clone();
                }
            }
            Ok(extreme)
        }
    }
}
