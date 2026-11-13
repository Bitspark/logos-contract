//! #2511: the closure join visits only the rows a binder's bound positions admit, and COUNTS what
//! the declared-order nested loop offers. The cost model is the one `closure_join_cost` declares
//! and `check` holds a certificate to (one join step per row offered to a binder, one grounding
//! per body-true tuple), so every expected number below is derived from that definition by hand,
//! not read off an implementation.
//!
//! The chain is #2497's measured shape: `reach(X, Z) :- edge(X, Y), reach(Y, Z)` over N edges
//! `n0 -> n1 -> ... -> nN`. Its closure has C = N(N+1)/2 rows, and the loop offers the whole of
//! `reach` to every `edge` row, so the model counts N x C join steps there. That is the count the
//! index must preserve while no longer paying for it.

use logos_contract::{
    closure_join_cost, CertSizeDecl, CheckLimits, Clause, ClosedModelCert, ClosureWitness,
    FiniteDomain, Goal, GroundLiteral, MapProgram, RejectionCode, RelationTable, StratumPrefix,
    SupportWitness, Symbol, Term, Theory, TheoryGround,
};
use ontos_core::Value;

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _: &Symbol) -> bool {
        false
    }
    fn decide_ground(&self, _: &GroundLiteral) -> TheoryGround {
        TheoryGround::fails("not_mine")
    }
}

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn node(i: usize) -> Value {
    atom(&format!("n{i}"))
}
fn var(v: &str) -> Term {
    Term::var(v)
}
fn goal(pred: &str, args: Vec<Term>) -> Goal {
    Goal::new(pred, args)
}

/// A certificate sealing `tables`, declaring nothing the count-only path reads.
fn cert(tables: Vec<RelationTable>) -> ClosedModelCert {
    let preds: Vec<Symbol> = tables.iter().map(|t| t.pred.clone()).collect();
    ClosedModelCert {
        scope: StratumPrefix::new(1, preds),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(Symbol::new(b"d".to_vec()), [atom("a")])],
        extensions: tables,
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 0,
            domain_values: 0,
            support_edges: 0,
            rule_groundings: 0,
            join_steps: 0,
            cert_bytes: 0,
        },
    }
}

fn chain_program() -> MapProgram {
    MapProgram::new()
        .with(
            "reach_base",
            Clause::new(
                goal("reach", vec![var("X"), var("Y")]),
                [goal("edge", vec![var("X"), var("Y")])],
            ),
        )
        .with(
            "reach_step",
            Clause::new(
                goal("reach", vec![var("X"), var("Z")]),
                [
                    goal("edge", vec![var("X"), var("Y")]),
                    goal("reach", vec![var("Y"), var("Z")]),
                ],
            ),
        )
}

/// The N-edge chain sealed with its exact closure.
fn chain_cert(n: usize) -> ClosedModelCert {
    let edges = (0..n).map(|i| GroundLiteral::new("edge", [node(i), node(i + 1)]));
    let reach = (0..n).flat_map(|i| (i + 1..=n).map(move |j| (i, j)));
    cert(vec![
        RelationTable::new("edge", 2, edges),
        RelationTable::new(
            "reach",
            2,
            reach.map(|(i, j)| GroundLiteral::new("reach", [node(i), node(j)])),
        ),
    ])
}

/// The model's count for the N-edge chain: `reach_base` offers the N edges and grounds each;
/// `reach_step` offers the N edges, then the whole closure (C rows) to each of them, and grounds
/// one tuple per path of length >= 2, N(N-1)/2 of them.
fn chain_count(n: usize) -> (usize, usize) {
    let closure = n * (n + 1) / 2;
    let groundings = n + n * (n - 1) / 2;
    let joins = n + (n + n * closure);
    (groundings, joins)
}

#[test]
fn the_chain_counts_what_the_nested_loop_offers_at_every_size_2511() {
    for n in [1, 2, 5, 40, 120] {
        assert_eq!(
            closure_join_cost(
                &chain_cert(n),
                &chain_program(),
                &NoTheory,
                &CheckLimits::default()
            ),
            Ok(chain_count(n)),
            "chain of {n} edges"
        );
    }
    // The positive control on the arithmetic itself: at N = 5 the closure is 15 and the loop
    // offers 5 + 5 + 5 x 15 rows.
    assert_eq!(chain_count(5), (15, 85));
}

/// The budget trips at the SAME count the full scan tripped at. At N = 5 the scan passes the
/// 50th join step inside `reach_step`'s third offer of the closure whichever clause runs first,
/// so the trip reads 51 however the rows between candidates were charged.
#[test]
fn a_join_budget_trips_at_the_count_the_scan_tripped_at_2511() {
    let limits = CheckLimits {
        max_join_steps: 50,
        ..CheckLimits::default()
    };
    assert_eq!(
        closure_join_cost(&chain_cert(5), &chain_program(), &NoTheory, &limits),
        Err((
            RejectionCode::CertBudgetExceeded,
            "counted join_steps 51 exceeds budget 50".to_string()
        ))
    );
    // Exactly the whole count passes: the trip is past the budget, never at it.
    let at_count = CheckLimits {
        max_join_steps: 85,
        ..CheckLimits::default()
    };
    assert_eq!(
        closure_join_cost(&chain_cert(5), &chain_program(), &NoTheory, &at_count),
        Ok((15, 85))
    );
}

/// The index keys a CONSTANT and a COMPOUND term over bound variables, and leaves a variable
/// repeated inside one binder to the unifier. Each clause's count is derived by hand below.
#[test]
fn constant_compound_and_repeated_variable_binders_count_as_the_loop_did_2511() {
    let pair = |x: &str, y: &str| Value::tuple([atom("pair"), atom(x), atom(y)]);
    let program = MapProgram::new()
        // p(X) :- q(a, X). q holds 3 rows, 2 with `a` first: 3 steps, 2 groundings.
        .with(
            "p_rule",
            Clause::new(
                goal("p", vec![var("X")]),
                [goal("q", vec![Term::atom(b"a".to_vec()), var("X")])],
            ),
        )
        // r(X) :- s(X, X). s holds 3 rows, 2 reflexive: 3 steps, 2 groundings.
        .with(
            "r_rule",
            Clause::new(
                goal("r", vec![var("X")]),
                [goal("s", vec![var("X"), var("X")])],
            ),
        )
        // w(X, Y) :- e(X, Y), f(pair(X, Y)). e holds 3 rows and f 3 rows, of which the pairs of
        // two e rows: 3 + 3 x 3 = 12 steps, 2 groundings.
        .with(
            "w_rule",
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
        );
    let lit = |pred: &str, args: Vec<Value>| GroundLiteral::new(pred, args);
    let tables = vec![
        RelationTable::new(
            "q",
            2,
            [
                lit("q", vec![atom("a"), atom("1")]),
                lit("q", vec![atom("a"), atom("2")]),
                lit("q", vec![atom("b"), atom("3")]),
            ],
        ),
        RelationTable::new(
            "s",
            2,
            [
                lit("s", vec![atom("1"), atom("1")]),
                lit("s", vec![atom("1"), atom("2")]),
                lit("s", vec![atom("2"), atom("2")]),
            ],
        ),
        RelationTable::new(
            "e",
            2,
            [
                lit("e", vec![atom("a"), atom("b")]),
                lit("e", vec![atom("b"), atom("c")]),
                lit("e", vec![atom("c"), atom("d")]),
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
        RelationTable::new("p", 1, Vec::<GroundLiteral>::new()),
        RelationTable::new("r", 1, Vec::<GroundLiteral>::new()),
        RelationTable::new("w", 2, Vec::<GroundLiteral>::new()),
    ];
    assert_eq!(
        closure_join_cost(&cert(tables), &program, &NoTheory, &CheckLimits::default()),
        Ok((2 + 2 + 2, 3 + 3 + 12))
    );
}
