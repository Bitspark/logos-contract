//! #2258 lane 2 (stacked certificates): the producer's cost model over a stacked world, pinned
//! (seat:caa's design review, Q4). `closure_join_cost_in_world` reads a predicate the cert does not
//! seal from the strictly lower certificate that seals it, and counts the rows offered to that
//! binder as the cert's own join steps, exactly as the checker will. The one-cert
//! `closure_join_cost` is unchanged, so a cert that reads nothing from below costs the same under
//! both. The checker's verdicts over stacked worlds are pinned tri-core by the `stacked_2258_*`
//! cases in `vectors/negation.json`.
//!
//! Program: `stk_low(X) :- stk_item(X), \+ stk_flag(X).` over EDB `stk_item(a)`, `stk_item(b)`,
//! `stk_flag(a)`, so `stk_low = {b}`.

use logos_contract::{
    closure_join_cost, closure_join_cost_in_world, CertId, CertSizeDecl, CheckLimits, Clause,
    ClauseId, ClosedModelCert, ClosureWitness, FiniteDomain, Goal, GroundLiteral, MapProgram,
    RelationTable, StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term,
    Theory, TheoryOutcome,
};
use ontos_core::Value;
use std::collections::BTreeMap;

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
    fn decide(&self, _: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Fails {
            code: "not_mine".into(),
        }
    }
}

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn g(pred: &str, arg: &str) -> GroundLiteral {
    GroundLiteral::new(pred, [v(arg)])
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}
fn x_is(a: &str) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert("X".into(), Term::atom(a.as_bytes().to_vec()));
    s
}

fn program() -> MapProgram {
    MapProgram::new().with(
        "stk_low_rule",
        Clause::with_neg(
            Goal::new("stk_low", [Term::var("X")]),
            [Goal::new("stk_item", [Term::var("X")])],
            [Goal::new("stk_flag", [Term::var("X")])],
        ),
    )
}

fn cert(
    level: u32,
    preds: &[&str],
    tables: Vec<RelationTable>,
    supports: Vec<SupportEdge>,
) -> ClosedModelCert {
    let facts: usize = tables.iter().map(|t| t.rows.len()).sum();
    let edges = supports.len();
    ClosedModelCert {
        scope: StratumPrefix::new(level, preds.iter().map(|p| sym(p))),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("a"), v("b")])],
        extensions: tables,
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: facts as u64,
            domain_values: 2,
            support_edges: edges as u64,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    }
}

fn item() -> RelationTable {
    RelationTable::new("stk_item", 1, [g("stk_item", "a"), g("stk_item", "b")])
}
fn flag() -> RelationTable {
    RelationTable::new("stk_flag", 1, [g("stk_flag", "a")])
}
fn low() -> RelationTable {
    RelationTable::new("stk_low", 1, [g("stk_low", "b")])
}
fn low_edge(item_cert: usize, flag_cert: usize) -> SupportEdge {
    SupportEdge {
        fact: g("stk_low", "b"),
        clause: ClauseId::new("stk_low_rule"),
        subst: x_is("b"),
        body_refs: vec![
            SupportRef::LowerStratum {
                cert: CertId(item_cert as u64),
                atom: g("stk_item", "b"),
            },
            SupportRef::NegLower {
                cert: CertId(flag_cert as u64),
                atom: g("stk_flag", "b"),
            },
        ],
        rank: 1,
    }
}

/// The EDB sealed once at the bottom (cert 0, level 1) and `stk_low` above it (cert 1, level 2).
fn stacked_world() -> Vec<ClosedModelCert> {
    vec![
        cert(1, &["stk_flag", "stk_item"], vec![flag(), item()], vec![]),
        cert(2, &["stk_low"], vec![low()], vec![low_edge(0, 0)]),
    ]
}

#[test]
fn the_stacked_cost_counts_the_lower_binders_rows_as_the_certs_join_steps_2258() {
    let world = stacked_world();
    // One grounding (X = b). Join steps: 2 rows of cert 0's stk_item offered to the binder, and
    // the \+ stk_flag(X) filter once per matching row (2): 4.
    assert_eq!(
        closure_join_cost_in_world(&world, 1, &program(), &NoTheory, &CheckLimits::default()),
        Ok((1, 4))
    );
}

#[test]
fn the_one_cert_cost_cannot_plan_a_cert_that_reads_from_below_2258() {
    // Alone, cert 1 has no binder for X: stk_item is neither sealed by it nor resolvable.
    let world = stacked_world();
    let err = closure_join_cost(&world[1], &program(), &NoTheory, &CheckLimits::default())
        .expect_err("a cert that reads from below cannot be costed alone");
    assert_eq!(err.0.code(), "cert_scope_incomplete", "{}", err.1);
}

#[test]
fn a_cert_that_reads_nothing_from_below_costs_the_same_either_way_2258() {
    // One cert sealing all three (the issue's M3 shape; the scope gate would refuse its
    // intra-scope negation, but the cost model only plans and counts the join).
    let single = cert(
        1,
        &["stk_flag", "stk_item", "stk_low"],
        vec![flag(), item(), low()],
        vec![low_edge(0, 0)],
    );
    let alone = closure_join_cost(&single, &program(), &NoTheory, &CheckLimits::default());
    assert_eq!(alone, Ok((1, 4)));
    assert_eq!(
        closure_join_cost_in_world(&[single], 0, &program(), &NoTheory, &CheckLimits::default()),
        alone
    );
}

#[test]
fn an_index_outside_the_world_is_refused_by_name_2258() {
    let err = closure_join_cost_in_world(
        &stacked_world(),
        2,
        &program(),
        &NoTheory,
        &CheckLimits::default(),
    )
    .expect_err("index 2 is outside a two-cert world");
    assert_eq!(err.0.code(), "cert_out_of_range", "{}", err.1);
}
