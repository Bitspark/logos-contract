//! **All four conserved-fold conjuncts over ONE relation** — the single-relation shape of
//! the property `conserved_flow_balance.rs` exercises conjunct-by-conjunct.
//!
//! # The domain here is INVENTED (ADR 0025 D3)
//!
//! The same synthetic material-flow junction as its sibling, widened so every conjunct
//! projects off one arity-6 relation instead of two purpose-built ones. That is the shape a
//! real program tends to have — one fact table, many folds — so it is worth pinning that the
//! checker behaves identically when the folds share a relation. Nothing here is imported from
//! a consumer; a consumer with a similar law binds its own vocabulary on its own side of the
//! SPI (ADR 0025 D1, ADR 0018).
//!
//! EDB: `flow(J, CiteIdx, Side, Kind, Origin, Qty)` — arity 6, sealed as a ClosedModelCert:
//!   0 J         junction id
//!   1 CiteIdx   distinctness key — so the SAME parcel cited twice is TWO distinct facts.
//!               Load-bearing: a relation is a SET, so without it a duplicate row collapses
//!               and the dedup fold can never observe the duplicate it exists to catch.
//!   2 Side      atom `in`/`out` — the partition attribute
//!   3 Kind      material-kind id, an ATOM not an int, so the single-kind conjunct must use
//!               count_distinct and cannot use Min/Max (there is no order on kinds)
//!   4 Origin    source-parcel identity — the dedup key
//!   5 Qty       signed integer quantity
//!
//! `balanced(J)` in the order dedup → single-kind → sums → positivity. **The order is part of
//! what is asserted**, for a reason logos owns: a duplicated or mixed-kind flow set makes the
//! conservation sum meaningless — it would sum an already-inflated set, or sum across
//! incommensurable kinds — so the sum must not be the first thing checked.
//!
//! 1. DEDUP — count(in flows) =:= count_distinct(in flows by Origin).
//! 2. SINGLE-KIND — count_distinct(all flows by Kind) =:= 1. A sum over two different kinds
//!    is not a conserved quantity at all, so this must hold for the sums to mean anything.
//! 3. CONSERVATION — sum(in Qty) =:= sum(out Qty). The side-only filter is sound here
//!    *because* single-kind already established one kind by sum time — the conjuncts compose.
//! 4. POSITIVITY — min(out Qty) > 0, strict (see the sibling file for why the zero edge is a
//!    primary case and not defence-in-depth).
//!
//! All four rejects surface the same FIRM code, `builtin_failed`, distinguished by WHICH
//! builtin node fails. logos deliberately does not widen its reject taxonomy to give each
//! conjunct a domain-specific name; a consumer wanting finer names maps them on its side.

use logos_contract::{
    check_with_cert_context, edb_table_hash, intval::BigInt, program_digest, ArithmeticTheory,
    BodyLit, CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId,
    ClosedModelCert, ClosureWitness, CountLit, Derivation, Evidence, FiniteDomain, Goal,
    GroundLiteral, Hash, LeafOutcome, LeafVerifier, Literal, MapProgram, Node, NodeMeta, Outcome,
    PredicateRef, PredicateSet, Premise, Program, ProjectSpec, RelationTable, StratumPrefix, Subst,
    SupportWitness, Symbol, Term,
};
use ontos_core::Value;
use std::collections::BTreeMap;

struct FlowLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for FlowLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _ctx: &()) -> Option<Hash> {
        match self.edb.get(pred.bytes()) {
            Some(rows) => Some(edb_table_hash(pred, rows)),
            None if self.extensional.contains(pred) => Some(edb_table_hash(pred, &[])),
            None => None,
        }
    }
}

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn int_v(n: i128) -> Value {
    BigInt::from_i128(n)
        .to_int_term()
        .erase_ground()
        .expect("ground int")
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}
/// `flow(C, CiteIdx, Side, Kind, Origin, Qty)`.
fn flow(c: &str, cite: i128, side: &str, kind: &str, origin: &str, qty: i128) -> GroundLiteral {
    GroundLiteral::new(
        "flow",
        [v(c), int_v(cite), v(side), v(kind), v(origin), int_v(qty)],
    )
}

fn bound_context(program: &dyn Program) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

const C_BALANCED: &str = "balanced_rule";

// Filter helpers: Side at attr 2.
fn f_in_t() -> Vec<(u32, Term)> {
    vec![(2, Term::from_value(&v("in")))]
}
fn f_out_t() -> Vec<(u32, Term)> {
    vec![(2, Term::from_value(&v("out")))]
}
fn f_in_g() -> Vec<(u32, Value)> {
    vec![(2, v("in"))]
}
fn f_out_g() -> Vec<(u32, Value)> {
    vec![(2, v("out"))]
}

fn balanced_program() -> MapProgram {
    let clause = Clause {
        head: Goal::new("balanced", [Term::var("C")]),
        body: vec![
            // 1-3: DEDUP — count(in) =:= count_distinct(in by Origin attr 4).
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_t(),
                project: ProjectSpec::Rows,
                count: Term::var("Total"),
            }),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_t(),
                project: ProjectSpec::Distinct { attr: 4 },
                count: Term::var("DistinctOut"),
            }),
            BodyLit::Pos(Literal::new(
                "=:=",
                [Term::var("Total"), Term::var("DistinctOut")],
            )),
            // 4-5: SINGLE-KIND — count_distinct(all flows by Kind attr 3) =:= 1.
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: vec![],
                project: ProjectSpec::Distinct { attr: 3 },
                count: Term::var("DistinctKind"),
            }),
            BodyLit::Pos(Literal::new(
                "=:=",
                [Term::var("DistinctKind"), Term::from_value(&int_v(1))],
            )),
            // 6-8: CONSERVATION — sum(in Qty attr 5) =:= sum(out Qty).
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_t(),
                project: ProjectSpec::Sum { attr: 5 },
                count: Term::var("SumIn"),
            }),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: f_out_t(),
                project: ProjectSpec::Sum { attr: 5 },
                count: Term::var("SumOut"),
            }),
            BodyLit::Pos(Literal::new(
                "=:=",
                [Term::var("SumIn"), Term::var("SumOut")],
            )),
            // 9-10: POSITIVITY — min(out Qty) > 0.
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 6),
                filter: f_out_t(),
                project: ProjectSpec::Min { attr: 5 },
                count: Term::var("MinOut"),
            }),
            BodyLit::Pos(Literal::new(
                ">",
                [Term::var("MinOut"), Term::from_value(&int_v(0))],
            )),
        ],
    };
    MapProgram::new().with(C_BALANCED, clause)
}

fn profile(edb_rows: Vec<GroundLiteral>) -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"flow".to_vec(), edb_rows);
    CheckProfile {
        theory: Box::new(ArithmeticTheory::new()),
        leaves: Box::new(FlowLeaves {
            extensional: PredicateSet::from_iter(["flow"]),
            edb,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

/// Sealed cert over `{flow}`; the domain must cover every atom/int appearing in a row.
fn flow_cert(rows: &[GroundLiteral], domain_vals: Vec<Value>) -> ClosedModelCert {
    let n = domain_vals.len();
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("flow")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), domain_vals)],
        extensions: vec![RelationTable::new("flow", 6, rows.to_vec())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: rows.len() as u64,
            domain_values: n as u64,
            support_edges: 0,
            rule_groundings: 2_000,
            join_steps: 20_000,
            cert_bytes: 16_384,
        },
    };
    let cx = bound_context(&balanced_program());
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
    cert
}

/// Build `balanced(C)` citing the sealed flow cert. The claimed aggregate results are
/// passed explicitly; the checker re-derives each fold + decides the four builtins.
#[allow(clippy::too_many_arguments)]
fn balanced_derivation(
    c: &str,
    total: i128,
    distinct_out: i128,
    distinct_kind: i128,
    sum_in: i128,
    sum_out: i128,
    min_out: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("C".into(), Term::atom(c.as_bytes().to_vec()));
    subst.insert("Total".into(), Term::from_value(&int_v(total)));
    subst.insert("DistinctOut".into(), Term::from_value(&int_v(distinct_out)));
    subst.insert(
        "DistinctKind".into(),
        Term::from_value(&int_v(distinct_kind)),
    );
    subst.insert("SumIn".into(), Term::from_value(&int_v(sum_in)));
    subst.insert("SumOut".into(), Term::from_value(&int_v(sum_out)));
    subst.insert("MinOut".into(), Term::from_value(&int_v(min_out)));

    // node 0 dedup =:=, node 1 mixed-kind =:=, node 2 conservation =:=, node 3 positivity >.
    let dedup = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(total), int_v(distinct_out)]),
    };
    let cross = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(distinct_kind), int_v(1)]),
    };
    let cons = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(sum_in), int_v(sum_out)]),
    };
    let parcel = Node::Builtin {
        conclusion: GroundLiteral::new(">", [int_v(min_out), int_v(0)]),
    };
    let rule = Node::Rule {
        conclusion: GroundLiteral::new("balanced", [v(c)]),
        clause: ClauseId::new(C_BALANCED),
        subst,
        premises: vec![
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_g(),
                project: ProjectSpec::Rows,
                k: int_v(total),
                cert: CertId(0),
            },
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_g(),
                project: ProjectSpec::Distinct { attr: 4 },
                k: int_v(distinct_out),
                cert: CertId(0),
            },
            Premise::pos(0),
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: vec![],
                project: ProjectSpec::Distinct { attr: 3 },
                k: int_v(distinct_kind),
                cert: CertId(0),
            },
            Premise::pos(1),
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: f_in_g(),
                project: ProjectSpec::Sum { attr: 5 },
                k: int_v(sum_in),
                cert: CertId(0),
            },
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: f_out_g(),
                project: ProjectSpec::Sum { attr: 5 },
                k: int_v(sum_out),
                cert: CertId(0),
            },
            Premise::pos(2),
            Premise::Count {
                pred: PredicateRef::new("flow", 6),
                filter: f_out_g(),
                project: ProjectSpec::Min { attr: 5 },
                k: int_v(min_out),
                cert: CertId(0),
            },
            Premise::pos(3),
        ],
        meta: NodeMeta::none(),
    };
    Derivation::with_closed_world([dedup, cross, cons, parcel, rule], 4, [cert])
}

fn run(rows: Vec<GroundLiteral>, deriv: &Derivation, c: &str) -> Outcome {
    let program = balanced_program();
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &GroundLiteral::new("balanced", [v(c)]),
        deriv,
        &(),
        &profile(rows),
        &cx,
    )
}

fn assert_reject(outcome: Outcome, expected: &str) {
    match outcome {
        Outcome::Reject { code, detail } => assert_eq!(
            code.code(),
            expected,
            "expected {expected}, got {} ({detail})",
            code.code()
        ),
        Outcome::Accept => panic!("expected reject {expected}, got Accept"),
    }
}

/// Domain over the fixed vocabulary + the ints a fixture needs.
fn dom(kinds: &[&str], origins: &[&str], ints: &[i128]) -> Vec<Value> {
    let mut d = vec![v("j1"), v("in"), v("out")];
    for a in kinds {
        d.push(v(a));
    }
    for o in origins {
        d.push(v(o));
    }
    for n in ints {
        d.push(int_v(*n));
    }
    d
}

// ================================= FIXTURES =================================

/// accept: 1500 in (op1:1000 + op2:500) → 1500 out (op3:900 + op4:600), single kind aAA.
/// dedup ok (2 distinct in-origins), one kind, conserved, all out qty > 0 → ACCEPT.
#[test]
fn accept_wellformed_junction() {
    let rows = vec![
        flow("j1", 0, "in", "aAA", "op1", 1000),
        flow("j1", 1, "in", "aAA", "op2", 500),
        flow("j1", 2, "out", "aAA", "op3", 900),
        flow("j1", 3, "out", "aAA", "op4", 600),
    ];
    let cert = flow_cert(
        &rows,
        dom(
            &["aAA"],
            &["op1", "op2", "op3", "op4"],
            &[0, 1, 2, 3, 1000, 500, 900, 600, 1500],
        ),
    );
    let deriv = balanced_derivation("j1", 2, 2, 1, 1500, 1500, 600, cert);
    assert!(
        run(rows, &deriv, "j1").is_accept(),
        "well-formed junction must ACCEPT"
    );
}

/// reject-conservation: 1000 in → 600 out (Σin=1000 ≠ Σout=600). dedup ok, one kind, then
/// the conservation `=:=(1000, 600)` fails.
#[test]
fn reject_conservation() {
    let rows = vec![
        flow("j1", 0, "in", "aAA", "op1", 1000),
        flow("j1", 1, "out", "aAA", "op3", 600),
    ];
    let cert = flow_cert(&rows, dom(&["aAA"], &["op1", "op3"], &[0, 1, 1000, 600]));
    let deriv = balanced_derivation("j1", 1, 1, 1, 1000, 600, 600, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-positivity: 1000 in → 1000 + 0 out. Conserved, one kind, no dup, yet min(out)=0
/// fails the strict `>(0, 0)`.
#[test]
fn reject_positive_qty_zero() {
    let rows = vec![
        flow("j1", 0, "in", "aAA", "op1", 1000),
        flow("j1", 1, "out", "aAA", "op3", 1000),
        flow("j1", 2, "out", "aAA", "op4", 0),
    ];
    let cert = flow_cert(
        &rows,
        dom(&["aAA"], &["op1", "op3", "op4"], &[0, 1, 2, 1000, 0]),
    );
    let deriv = balanced_derivation("j1", 1, 1, 1, 1000, 1000, 0, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-double-count (the balanced-duplicate killer): origin op1 cited TWICE in, 1000
/// each → out 2000. Conservation HOLDS (Σin=2000=Σout) yet count(in)=2 ≠ count_distinct(
/// origin)=1 → the dedup `=:=(2, 1)` fails. Dedup fires BEFORE conservation (order).
#[test]
fn reject_double_count() {
    let rows = vec![
        flow("j1", 0, "in", "aAA", "op1", 1000),
        flow("j1", 1, "in", "aAA", "op1", 1000), // SAME origin op1 — the double-count
        flow("j1", 2, "out", "aAA", "op3", 2000),
    ];
    let cert = flow_cert(
        &rows,
        dom(&["aAA"], &["op1", "op3"], &[0, 1, 2, 1000, 2000]),
    );
    // dedup: Total=2, DistinctOut=1 (FAILS); (conservation would hold: 2000==2000).
    let deriv = balanced_derivation("j1", 2, 1, 1, 2000, 2000, 2000, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-mixed-kind (N15): two DIFFERENT kinds aAA + aBB in the flow-set. dedup ok
/// (op1, op2 distinct), then count_distinct(all flows by Kind)=2 ≠ 1 → the mixed-kind
/// `=:=(2, 1)` fails. Fires BEFORE the conservation sum (a mixed-kind sum is meaningless).
#[test]
fn reject_mixed_kind() {
    let rows = vec![
        flow("j1", 0, "in", "aAA", "op1", 1000),
        flow("j1", 1, "in", "aBB", "op2", 1000), // DIFFERENT kind aBB
        flow("j1", 2, "out", "aAA", "op3", 2000),
    ];
    let cert = flow_cert(
        &rows,
        dom(
            &["aAA", "aBB"],
            &["op1", "op2", "op3"],
            &[0, 1, 2, 1000, 2000],
        ),
    );
    // dedup: Total=2==DistinctOut=2 (ok); mixed-kind: DistinctKind=2 ≠ 1 (FAILS).
    let deriv = balanced_derivation("j1", 2, 2, 2, 2000, 2000, 2000, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}
