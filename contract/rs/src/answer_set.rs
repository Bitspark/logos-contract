//! G4, the completeness gate's set comparison, as one contract operation (design 0008 section 1.4.4;
//! research 0028 row A16, `seat:caa`'s ruling on #3023). Each kernel's gate calls it after G2 and
//! G3, and `vectors/exact_answer_set.json` replays it in all three cores.
//!
//! The emitted answers must be exactly the sealed rows that are instances of the goal. A row is an
//! instance when one binding of the goal's variables makes the goal structurally equal to it
//! ([`Term::match_value`](crate::Term::match_value), the one matcher, where a repeated variable binds
//! one value). Two answers are one answer exactly when they are structurally equal ([`ground_key`]).
//!
//! The precedence is normative: the first emitted answer that is not a sealed instance, in claim
//! order; otherwise the first sealed instance that was not emitted, in `ground_key` order.

use std::collections::{BTreeMap, BTreeSet};

use crate::cert::ground_key;
use crate::literal::{Goal, GroundLiteral};
use crate::term::Subst;

/// How an answer set fails G4. These are exactly the two ways a set comparison fails, so the enum
/// is exhaustive (`seat:caa`'s ruling on #3023): a third member would be a contract v2 item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnswerSetMismatch {
    /// An emitted answer that is not a sealed row matching the goal: the first, in claim order.
    Extra(GroundLiteral),
    /// A sealed row matching the goal that was not emitted: the first, in `ground_key` order.
    Missing(GroundLiteral),
}

/// G4: `Ok` when `claims` is exactly the set of `sealed` rows that are instances of `goal`, and
/// otherwise the first difference by the normative precedence.
pub fn check_answer_set(
    goal: &Goal,
    sealed: &[GroundLiteral],
    claims: &[GroundLiteral],
) -> Result<(), AnswerSetMismatch> {
    let instances: BTreeMap<Vec<u8>, &GroundLiteral> = sealed
        .iter()
        .filter(|row| is_instance(goal, row))
        .map(|row| (ground_key(row), row))
        .collect();
    let emitted: BTreeSet<Vec<u8>> = claims.iter().map(ground_key).collect();
    if let Some(extra) = claims
        .iter()
        .find(|claim| !instances.contains_key(&ground_key(claim)))
    {
        return Err(AnswerSetMismatch::Extra(extra.clone()));
    }
    if let Some((_, missing)) = instances.iter().find(|(key, _)| !emitted.contains(*key)) {
        return Err(AnswerSetMismatch::Missing((*missing).clone()));
    }
    Ok(())
}

/// Whether `row` is an instance of `goal`: the same predicate and arity, and one binding of the
/// goal's variables under which every argument matches.
fn is_instance(goal: &Goal, row: &GroundLiteral) -> bool {
    if goal.pred != row.pred || goal.args.len() != row.args.len() {
        return false;
    }
    let mut subst = Subst::new();
    goal.args
        .iter()
        .zip(&row.args)
        .all(|(term, value)| term.match_value(value, &mut subst))
}
