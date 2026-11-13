//! The closure join's candidate index (#2511).
//!
//! The closure join is a declared-order nested loop, and its COST MODEL counts it that way: one
//! join step per table row offered to a binder (see `join_groundings` in `cert.rs`). Offering
//! every row is also what the join used to DO, so a binder whose table is keyed by an argument an
//! earlier binder already bound examined the whole table per partial tuple. On a right-recursive
//! chain, `reach(X, Z) :- edge(X, Y), reach(Y, Z)`, that is N x closure rows, about closure^1.5,
//! and it ran twice per complete seal: counted by the producer, then verified by the checker.
//!
//! This index keeps the model and changes the work. A binder's KEY positions are the argument
//! positions that are ground once the earlier binders have bound: a constant, or a term over
//! variables they bound. A row whose values differ at a key position cannot unify with the
//! binder, so in the loop it was offered, charged one join step, and refused, with no other
//! effect. The join now visits only the rows whose key matches, in table order, and charges the
//! refused rows between them arithmetically ([`charge_join_steps`]), so the counters,
//! the budget and declaration trips, and their texts are the ones the loop produced.
//!
//! ⛔ **VALID ONLY WHILE CLOSURE UNIFICATION IS STRUCTURAL.** A key position is compared by `Term`
//! equality and hashing, which is exactly the relation `unify_ground` applies to a bound variable
//! or a constant: structural (seat:caa's condition on #2516; the term identity it once had to be
//! blind to was deleted in checker SPI v2, #3111). If the closure join ever unifies under a term
//! identity (reified lists, say), the key must be canonicalized the same way. Otherwise the index skips a row the unifier would accept,
//! a satisfied grounding goes unchecked, and the checker accepts a certificate that is not closed.

use std::cell::OnceCell;
use std::collections::HashMap;

use super::cert::count_join_step;
use super::{CheckLimits, RejectionCode};
use crate::cert::{ClosedModelCert, RelationTable};
use crate::literal::Goal;
use crate::term::{Subst, Term, VarId};

/// One binder's candidate index: its key positions, and the table's rows grouped by their values
/// there. Built on first use, since a binder the join never reaches costs nothing.
pub(super) struct BinderIndex {
    keys: Vec<usize>,
    rows: OnceCell<HashMap<Vec<Term>, Vec<usize>>>,
}

impl BinderIndex {
    /// The index of `goal`, a binder reached once the variables in `bound` (sorted) are bound.
    pub(super) fn new(goal: &Goal, bound: &[VarId]) -> Self {
        let keys = goal
            .args
            .iter()
            .enumerate()
            .filter(|(_, arg)| {
                let mut ground = true;
                arg.for_each_var(|v| ground &= bound.binary_search(v).is_ok());
                ground
            })
            .map(|(i, _)| i)
            .collect();
        BinderIndex {
            keys,
            rows: OnceCell::new(),
        }
    }

    /// The positions, ascending, of the rows of `table` that can unify with `goal` under `subst`:
    /// a SUPERSET of the rows that do, since the non-key positions are left to the unifier.
    /// `None` means every row is a candidate: the binder has no key position, or (defensively) a
    /// key term is not ground under `subst`.
    pub(super) fn candidates(
        &self,
        goal: &Goal,
        table: &RelationTable,
        subst: &Subst,
    ) -> Option<&[usize]> {
        if self.keys.is_empty() {
            return None;
        }
        #[cfg(test)]
        if FULL_SCAN.with(std::cell::Cell::get) {
            return None;
        }
        let mut key = Vec::with_capacity(self.keys.len());
        for &i in &self.keys {
            let term = goal.args.get(i)?.substitute(subst);
            if !term.is_ground() {
                return None;
            }
            key.push(term);
        }
        let rows = self.rows.get_or_init(|| self.build(goal, table));
        Some(rows.get(&key).map_or(&[], Vec::as_slice))
    }

    fn build(&self, goal: &Goal, table: &RelationTable) -> HashMap<Vec<Term>, Vec<usize>> {
        let mut rows: HashMap<Vec<Term>, Vec<usize>> = HashMap::new();
        for (position, row) in table.rows.iter().enumerate() {
            // A row of another predicate or arity is refused by the unifier whatever its values,
            // so it is never a candidate.
            if row.pred != goal.pred || row.args.len() != goal.args.len() {
                continue;
            }
            let key = self
                .keys
                .iter()
                .map(|&i| Term::from_value(&row.args[i]))
                .collect();
            rows.entry(key).or_default().push(position);
        }
        rows
    }
}

#[cfg(test)]
thread_local! {
    /// Test-only: every binder takes the full scan, the reference #2511's differential row
    /// compares the index against.
    static FULL_SCAN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` with the index off: the declared-order full scan the index must reproduce.
#[cfg(test)]
fn full_scan<T>(f: impl FnOnce() -> T) -> T {
    FULL_SCAN.with(|flag| flag.set(true));
    let out = f();
    FULL_SCAN.with(|flag| flag.set(false));
    out
}

/// Charge `k` join steps at once (#2511): the rows a binder's index skipped, each of which the
/// full scan charged with [`count_join_step`] and refused. The result is the scan's own: the same
/// final count, or, if one of those steps would trip, the same trip at the same count, the budget
/// tested before the declaration as there.
pub(super) fn charge_join_steps(
    joins: &mut usize,
    k: usize,
    cert: &ClosedModelCert,
    limits: &CheckLimits,
    verify: bool,
) -> Result<(), (RejectionCode, String)> {
    if k == 0 {
        return Ok(());
    }
    // The first count at which a single step fails: past the budget, or on the checker's path
    // past the declaration. Every count below it passes both tests.
    let budget_trip = limits.max_join_steps.saturating_add(1);
    // The declaration is a protocol count (#2735): past what a host counter can reach, it never
    // trips, so it saturates rather than being narrowed.
    let declared_trip = if verify {
        usize::try_from(cert.limits_decl.join_steps.saturating_add(1)).unwrap_or(usize::MAX)
    } else {
        usize::MAX
    };
    let trip = budget_trip.min(declared_trip);
    let target = joins.saturating_add(k);
    if target < trip {
        *joins = target;
        return Ok(());
    }
    // Step to just below the trip and let the single step there name it, text and all.
    *joins = (trip - 1).max(*joins);
    count_join_step(joins, cert, limits, verify)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cert::{CertSizeDecl, ClosureWitness, StratumPrefix, SupportWitness};

    fn cert(declared: u64) -> ClosedModelCert {
        ClosedModelCert {
            scope: StratumPrefix::new(0, std::iter::empty::<crate::literal::Symbol>()),
            program_hash: [0; 32],
            profile_hash: [0; 32],
            ctx_hash: [0; 32],
            theory_config_hash: [0; 32],
            edb_snapshot_hashes: vec![],
            domains: vec![],
            extensions: vec![],
            supports: SupportWitness(vec![]),
            closure: ClosureWitness,
            decomposition_witness: None,
            partial_scope: None,
            limits_decl: CertSizeDecl {
                cert_facts: 0,
                domain_values: 0,
                support_edges: 0,
                rule_groundings: 0,
                join_steps: declared,
                cert_bytes: 0,
            },
        }
    }

    /// The batch IS `k` single steps: the same final count and the same verdict, trip text
    /// included, from every count the scan can be at (never past a wall it would have tripped),
    /// across budgets, declarations, both paths and every batch size up past both walls.
    #[test]
    fn a_batch_charge_is_k_single_steps_2511() {
        let mut compared = 0usize;
        for budget in 0..7 {
            let limits = CheckLimits {
                max_join_steps: budget,
                ..CheckLimits::default()
            };
            for declared in 0..7 {
                let cert = cert(declared as u64);
                for verify in [false, true] {
                    let wall = if verify { budget.min(declared) } else { budget };
                    for start in 0..=wall {
                        for k in 0..12 {
                            let mut batched = start;
                            let batch = charge_join_steps(&mut batched, k, &cert, &limits, verify);
                            let mut stepped = start;
                            let steps = (0..k).try_for_each(|_| {
                                count_join_step(&mut stepped, &cert, &limits, verify)
                            });
                            assert_eq!(
                                (batched, &batch),
                                (stepped, &steps),
                                "budget {budget} declared {declared} verify {verify} start {start} k {k}"
                            );
                            compared += 1;
                        }
                    }
                }
            }
        }
        assert!(compared > 1_000, "the grid compared {compared} cases");
    }
}

/// #2516, `seat:caa`'s condition 1: the indexed join against the full scan it replaces, on both
/// paths, over every trip point. Each run is compared on its verdict (text included), its
/// groundings and its join steps.
#[cfg(test)]
mod differential {
    use super::{full_scan, BinderIndex};
    use crate::cert::{
        CertSizeDecl, ClosedModelCert, ClosureWitness, FiniteDomain, RelationTable, StratumPrefix,
        SupportWitness,
    };
    use crate::check::cert::closure_join_trace;
    use crate::check::cert_stack::CertView;
    use crate::check::CheckLimits;
    use crate::literal::{Goal, GroundLiteral, Symbol};
    use crate::program::{Clause, MapProgram};
    use crate::spi::{Theory, TheoryGround};
    use crate::term::{Subst, Term, VarId};
    use ontos_core::Value;

    struct NoTheory;
    // test-double: consumer(owns no predicate)
    impl Theory for NoTheory {
        crate::cannot_copy!(
            Theory,
            "a test double: declines to copy, as the defaulted method did before #2722"
        );
        fn owns(&self, _: &Symbol) -> bool {
            false
        }
        fn decide_ground(&self, _: &GroundLiteral) -> TheoryGround {
            TheoryGround::disowned()
        }
    }

    fn a(s: &str) -> Value {
        Value::atom(s.as_bytes().to_vec())
    }
    fn lit(pred: &str, args: Vec<Value>) -> GroundLiteral {
        GroundLiteral::new(pred, args)
    }
    fn var(v: &str) -> Term {
        Term::var(v)
    }
    fn goal(pred: &str, args: Vec<Term>) -> Goal {
        Goal::new(pred, args)
    }
    fn pair(x: &str, y: &str) -> Value {
        Value::tuple([a("pair"), a(x), a(y)])
    }

    /// One clause per shape the index treats differently: a keyed chain binder, a CONSTANT key, a
    /// variable REPEATED inside one binder (no key), a COMPOUND key over bound variables, and a
    /// negated FILTER that charges a join step per candidate the keyed binder admits.
    fn program() -> MapProgram {
        MapProgram::new()
            .with(
                "c1_reach_base",
                Clause::new(
                    goal("reach", vec![var("X"), var("Y")]),
                    [goal("edge", vec![var("X"), var("Y")])],
                ),
            )
            .with(
                "c2_reach_step",
                Clause::new(
                    goal("reach", vec![var("X"), var("Z")]),
                    [
                        goal("edge", vec![var("X"), var("Y")]),
                        goal("reach", vec![var("Y"), var("Z")]),
                    ],
                ),
            )
            .with(
                "c3_constant",
                Clause::new(
                    goal("p", vec![var("X")]),
                    [goal("q", vec![Term::atom(b"a".to_vec()), var("X")])],
                ),
            )
            .with(
                "c4_repeated",
                Clause::new(
                    goal("r", vec![var("X")]),
                    [goal("s", vec![var("X"), var("X")])],
                ),
            )
            .with(
                "c5_compound",
                Clause::new(
                    goal("w", vec![var("X"), var("Y")]),
                    [
                        goal("e", vec![var("X"), var("Y")]),
                        goal(
                            "f",
                            vec![Term::Tuple(vec![
                                Term::atom(b"pair".to_vec()),
                                var("X"),
                                var("Y"),
                            ])],
                        ),
                    ],
                ),
            )
            .with(
                "c6_filter",
                Clause::with_neg(
                    goal("t", vec![var("X"), var("Z")]),
                    [
                        goal("e", vec![var("X"), var("Y")]),
                        goal("e2", vec![var("Y"), var("Z")]),
                    ],
                    [goal("g", vec![var("Z")])],
                ),
            )
    }

    /// The sealed model, exact when `closed`, else missing one head row (`t(b, y)`), so the
    /// checker's path refuses it `cert_not_closed` mid-join. `q` and `e2` keep a written order
    /// (struct literals): `q` INTERLEAVES a row of another predicate and one of another arity
    /// between its candidates, and `e2` puts a refused row between the two rows `Y = b` admits.
    fn cert(closed: bool, declared_groundings: u64, declared_joins: u64) -> ClosedModelCert {
        let node = |i: usize| a(&format!("n{i}"));
        let edges: Vec<GroundLiteral> = (0..4)
            .map(|i| lit("edge", vec![node(i), node(i + 1)]))
            .collect();
        let reach: Vec<GroundLiteral> = (0..4)
            .flat_map(|i| (i + 1..=4).map(move |j| (i, j)))
            .map(|(i, j)| lit("reach", vec![node(i), node(j)]))
            .collect();
        let mut t = vec![lit("t", vec![a("a"), a("z")])];
        if closed {
            t.push(lit("t", vec![a("b"), a("y")]));
        }
        let tables = vec![
            RelationTable::new("edge", 2, edges),
            RelationTable::new("reach", 2, reach),
            RelationTable {
                pred: "q".into(),
                arity: 2,
                rows: vec![
                    lit("q", vec![a("a"), a("1")]),
                    lit("zz", vec![a("a"), a("9")]),
                    lit("q", vec![a("b"), a("3")]),
                    lit("q", vec![a("a")]),
                    lit("q", vec![a("a"), a("2")]),
                ],
            },
            RelationTable::new(
                "s",
                2,
                [
                    lit("s", vec![a("1"), a("1")]),
                    lit("s", vec![a("1"), a("2")]),
                    lit("s", vec![a("2"), a("2")]),
                ],
            ),
            RelationTable::new(
                "e",
                2,
                [
                    lit("e", vec![a("a"), a("b")]),
                    lit("e", vec![a("b"), a("c")]),
                    lit("e", vec![a("c"), a("d")]),
                ],
            ),
            RelationTable::new(
                "f",
                1,
                [
                    lit("f", vec![pair("a", "b")]),
                    lit("f", vec![pair("b", "c")]),
                    lit("f", vec![pair("z", "z")]),
                ],
            ),
            RelationTable {
                pred: "e2".into(),
                arity: 2,
                rows: vec![
                    lit("e2", vec![a("b"), a("x")]),
                    lit("e2", vec![a("c"), a("y")]),
                    lit("e2", vec![a("b"), a("z")]),
                    lit("e2", vec![a("d"), a("x")]),
                ],
            },
            RelationTable::new("g", 1, [lit("g", vec![a("x")])]),
            RelationTable::new("p", 1, [lit("p", vec![a("1")]), lit("p", vec![a("2")])]),
            RelationTable::new("r", 1, [lit("r", vec![a("1")]), lit("r", vec![a("2")])]),
            RelationTable::new(
                "w",
                2,
                [
                    lit("w", vec![a("a"), a("b")]),
                    lit("w", vec![a("b"), a("c")]),
                ],
            ),
            RelationTable::new("t", 2, t),
        ];
        let values = [
            "n0", "n1", "n2", "n3", "n4", "a", "b", "c", "d", "x", "y", "z", "1", "2", "3", "9",
        ]
        .map(a);
        let preds: Vec<Symbol> = tables.iter().map(|t| t.pred.clone()).collect();
        ClosedModelCert {
            scope: StratumPrefix::new(1, preds),
            program_hash: [0; 32],
            profile_hash: [0; 32],
            ctx_hash: [0; 32],
            theory_config_hash: [0; 32],
            edb_snapshot_hashes: vec![],
            domains: vec![FiniteDomain::new(Symbol::new(b"d".to_vec()), values)],
            extensions: tables,
            supports: SupportWitness(vec![]),
            closure: ClosureWitness,
            decomposition_witness: None,
            partial_scope: None,
            limits_decl: CertSizeDecl {
                cert_facts: 0,
                domain_values: 0,
                support_edges: 0,
                rule_groundings: declared_groundings,
                join_steps: declared_joins,
                cert_bytes: 0,
            },
        }
    }

    type Trace = (
        Result<(), (crate::check::RejectionCode, String)>,
        usize,
        usize,
    );

    fn run(cert: &ClosedModelCert, limits: &CheckLimits, verify: bool) -> Trace {
        closure_join_trace(&CertView::own(cert), &program(), &NoTheory, limits, verify)
    }

    fn both(cert: &ClosedModelCert, limits: &CheckLimits, verify: bool, case: &str) {
        let indexed = run(cert, limits, verify);
        let scanned = full_scan(|| run(cert, limits, verify));
        assert_eq!(indexed, scanned, "{case} (verify {verify})");
    }

    /// ⭐ The positive control, FIRST: in this fixture the index is really engaged, so the rows
    /// below compare two different walks and not the scan with itself.
    #[test]
    fn the_index_is_engaged_and_the_switch_turns_it_off_2516() {
        let reach = RelationTable::new(
            "reach",
            2,
            [
                lit("reach", vec![a("n1"), a("n2")]),
                lit("reach", vec![a("n0"), a("n1")]),
                lit("reach", vec![a("n1"), a("n3")]),
            ],
        );
        let mut bound: Vec<VarId> = vec!["X".into(), "Y".into()];
        bound.sort();
        let index = BinderIndex::new(&goal("reach", vec![var("Y"), var("Z")]), &bound);
        let mut subst = Subst::new();
        subst.insert("Y".into(), Term::from_value(&a("n1")));
        let keyed = index.candidates(&goal("reach", vec![var("Y"), var("Z")]), &reach, &subst);
        assert_eq!(
            keyed.map(<[usize]>::len),
            Some(2),
            "two of three rows admitted"
        );
        let off = full_scan(|| {
            index
                .candidates(&goal("reach", vec![var("Y"), var("Z")]), &reach, &subst)
                .is_none()
        });
        assert!(off, "the switch forces the full scan");
    }

    /// Every join budget from 0 past the total, so every trip lands somewhere (inside a batch of
    /// skipped rows, on a candidate, on a filter), on both paths and on a closed and an unclosed
    /// model; then every grounding budget, and on the checker's path every declaration.
    #[test]
    fn the_indexed_join_is_the_full_scan_at_every_trip_2516() {
        let open = CheckLimits::default();
        let exact = cert(true, u64::MAX, u64::MAX);
        let (verdict, groundings, joins) = full_scan(|| run(&exact, &open, true));
        assert_eq!(verdict, Ok(()), "the exact model is closed");
        assert!(
            groundings > 10 && joins > groundings,
            "{groundings} / {joins}"
        );
        let mut compared = 0usize;
        for closed in [true, false] {
            let unlimited = cert(closed, u64::MAX, u64::MAX);
            for verify in [false, true] {
                for budget in 0..=joins + 1 {
                    let limits = CheckLimits {
                        max_join_steps: budget,
                        ..CheckLimits::default()
                    };
                    both(
                        &unlimited,
                        &limits,
                        verify,
                        &format!("join budget {budget}"),
                    );
                    compared += 1;
                }
                for budget in 0..=groundings + 1 {
                    let limits = CheckLimits {
                        max_rule_groundings: budget,
                        ..CheckLimits::default()
                    };
                    both(
                        &unlimited,
                        &limits,
                        verify,
                        &format!("grounding budget {budget}"),
                    );
                    compared += 1;
                }
            }
            for declared in 0..=joins + 1 {
                let c = cert(closed, u64::MAX, declared as u64);
                both(&c, &open, true, &format!("declared joins {declared}"));
                compared += 1;
            }
            for declared in 0..=groundings + 1 {
                let c = cert(closed, declared as u64, u64::MAX);
                both(&c, &open, true, &format!("declared groundings {declared}"));
                compared += 1;
            }
        }
        assert!(compared > 4 * joins, "compared {compared} runs");
    }
}
