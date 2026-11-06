//! **Conserved integer folds over a partitioned relation** — the check-layer behaviour of
//! ADR-0023 aggregation when several folds over one sealed relation must agree.
//!
//! # The domain here is INVENTED (ADR 0025 D3)
//!
//! It is a **material-flow junction**: `flow(J, Side, Qty)` says an integer quantity of
//! material entered (`in`) or left (`out`) junction `J`. `balanced(J)` holds when the
//! junction conserves what passes through it. Nothing about this domain is imported from a
//! consumer — it is mass balance / Kirchhoff's current law, chosen because it is the
//! smallest realistic setting in which the generic property below has teeth. A consumer
//! whose own law happens to look like this binds its vocabulary on ITS side of the SPI;
//! logos names the seam and nothing else (ADR 0025 D1, ADR 0018).
//!
//! # The generic property under test
//!
//! A conserved integer quantity over a relation partitioned by an attribute, with a
//! positivity side-condition, deduplicated by an identity attribute. Each conjunct is a
//! SEPARATE claim, and this file's value is proving they are independent — a derivation can
//! satisfy any one while violating another, so a checker that collapsed them would accept a
//! bad proof. No new kernel primitive: these are the ADR-0023 integer folds plus
//! `ArithmeticTheory`.
//!
//!   - **CONSERVATION.** Σ(qty over input flows) == Σ(qty over output flows), integer-exact.
//!     Two `ProjectSpec::Sum` folds over the sealed `flow` relation + an `=:=` equality. A
//!     violation ⇒ the `=:=` builtin node's theory decision fails: reject `builtin_failed`,
//!     detail `arith_does_not_hold`.
//!
//!   - **POSITIVITY.** Every output quantity is STRICTLY positive. `ProjectSpec::Min` over
//!     the output flows + `>` against 0.
//!
//!     *Why logos asserts this as a DISTINCT conjunct, not a corollary:* positivity can fail
//!     while conservation HOLDS — `1000 = 1500 + (−500)` balances with a negative parcel, and
//!     `1000 = 1000 + 0` balances with a zero one. Conservation is blind to both, so a
//!     checker relying on the sum alone would admit them.
//!
//!     *Why STRICTLY `> 0` and not `>= 0`:* a zero-quantity flow is Σ-neutral — it can never
//!     move the conservation equality — so it is invisible to every other conjunct while
//!     admitting unbounded growth of the flow set. `>= 0` would leave that hole open, which
//!     is why `reject_zero_qty` is a primary case here and not defence-in-depth. Both signs
//!     are REPRESENTABLE in the underlying integer (there is no unsigned type and negative
//!     and zero encode canonically), so this must be a CHECK-layer predicate; it cannot be
//!     delegated to the encoding.
//!
//!   - **DEDUP by origin.** The effective conservation set is deduplicated by an identity
//!     attribute, as a DISTINCT builtin firing BEFORE the sum:
//!     `count(input flows) =:= count_distinct(input flows by origin)`.
//!
//!     *Why logos asserts dedup separately, and first:* `reject_balanced_duplicate` (in X:1000,
//!     in X:1000, out Y:2000) SATISFIES conservation exactly — Σin = 2000 = Σout — while
//!     counting one source parcel twice. Only the dedup fold sees it. Ordering matters for the
//!     same reason: a duplicate inflates the total, so checking the sum first would validate an
//!     already-inflated set. This is a property of certified aggregation generally, not of any
//!     particular application.
//!
//! Every reject in this file surfaces the same FIRM code, `builtin_failed`; the conjuncts are
//! distinguished by WHICH builtin node fails — `=:=` on the sums (conservation), `>` on the
//! Min (positivity), and `=:=` on (count vs count_distinct), a node distinct from the
//! conservation `=:=` (dedup). A consumer that wants finer-grained names maps them on its own
//! side; logos does not widen its taxonomy to carry a consumer's vocabulary.

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

// ================================= profile =================================
// `flow(C, Side, Qty)` is a PURE EDB leaf (a junction's admitted parcel flows); Side is
// the atom `in`/`out`, Qty the integer quantity. `ArithmeticTheory`
// owns the `=:=` (conservation equality) and `>` (positivity) builtins.

struct FlowLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
impl FlowLeaves {
    fn new(edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>) -> Self {
        FlowLeaves {
            extensional: PredicateSet::from_iter(["flow"]),
            edb,
        }
    }
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
/// `flow(junction, side, qty)` — a parcel flow fact.
fn flow(c: &str, side: &str, qty: i128) -> GroundLiteral {
    GroundLiteral::new("flow", [v(c), v(side), int_v(qty)])
}

fn bound_context(program: &dyn Program) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}
fn bind_cert(cert: &mut ClosedModelCert, program: &dyn Program) {
    let cx = bound_context(program);
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
}

// ================================ the program ===================================
// balanced(C) :-
//   sum(flow(C, in,  D) over D) = S_in,      -- conservation: Σ inputs
//   sum(flow(C, out, D) over D) = S_out,     -- conservation: Σ outputs
//   =:=(S_in, S_out),                        -- conservation: Σin == Σout
//   min(flow(C, out, D) over D) = M_out,     -- positivity: minimum output qty
//   >(M_out, 0).                             -- positivity: every output qty > 0 (strict)

const C_BALANCED: &str = "balanced_rule";

fn in_filter() -> Vec<(u32, Term)> {
    vec![(1, Term::from_value(&v("in")))]
}
fn out_filter() -> Vec<(u32, Term)> {
    vec![(1, Term::from_value(&v("out")))]
}
fn in_gfilter() -> Vec<(u32, Value)> {
    vec![(1, v("in"))]
}
fn out_gfilter() -> Vec<(u32, Value)> {
    vec![(1, v("out"))]
}

fn base_program() -> MapProgram {
    let clause = Clause {
        head: Goal::new("balanced", [Term::var("C")]),
        body: vec![
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 3),
                filter: in_filter(),
                project: ProjectSpec::Sum { attr: 2 },
                count: Term::var("S_in"),
            }),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 3),
                filter: out_filter(),
                project: ProjectSpec::Sum { attr: 2 },
                count: Term::var("S_out"),
            }),
            BodyLit::Pos(Literal::new("=:=", [Term::var("S_in"), Term::var("S_out")])),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("flow", 3),
                filter: out_filter(),
                project: ProjectSpec::Min { attr: 2 },
                count: Term::var("M_out"),
            }),
            BodyLit::Pos(Literal::new(
                ">",
                [Term::var("M_out"), Term::from_value(&int_v(0))],
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
        leaves: Box::new(FlowLeaves::new(edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

/// The sealed cert over `{flow}` (level 0): flow = the live EDB snapshot. Domain covers the
/// junction atom, both sides, and every integer quantity appearing in a flow.
fn flow_cert(junction: &str, edb_rows: &[GroundLiteral], qtys: &[i128]) -> ClosedModelCert {
    let mut domain_vals: Vec<Value> = vec![v(junction), v("in"), v("out")];
    for d in qtys {
        domain_vals.push(int_v(*d));
    }
    let domain_count = domain_vals.len();
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("flow")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), domain_vals)],
        extensions: vec![RelationTable::new("flow", 3, edb_rows.to_vec())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: edb_rows.len() as u64,
            domain_values: domain_count as u64,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 8_192,
        },
    };
    bind_cert(&mut cert, &base_program());
    cert
}

/// Build the `balanced(C)` derivation citing the sealed flow cert. `s_in`/`s_out` are
/// the CLAIMED integer sums; `m_out` the CLAIMED minimum output qty. The checker
/// re-derives each fold from the sealed table and decides the two builtins.
#[allow(clippy::too_many_arguments)]
fn balanced_derivation(
    junction: &str,
    s_in: i128,
    s_out: i128,
    m_out: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("C".into(), Term::atom(junction.as_bytes().to_vec()));
    subst.insert("S_in".into(), Term::from_value(&int_v(s_in)));
    subst.insert("S_out".into(), Term::from_value(&int_v(s_out)));
    subst.insert("M_out".into(), Term::from_value(&int_v(m_out)));

    // node 0: =:=(S_in, S_out) builtin; node 1: >(M_out, 0) builtin; node 2: root rule.
    let eq_node = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(s_in), int_v(s_out)]),
    };
    let ge_node = Node::Builtin {
        conclusion: GroundLiteral::new(">", [int_v(m_out), int_v(0)]),
    };
    let rule_node = Node::Rule {
        conclusion: GroundLiteral::new("balanced", [v(junction)]),
        clause: ClauseId::new(C_BALANCED),
        subst,
        premises: vec![
            Premise::Count {
                pred: PredicateRef::new("flow", 3),
                filter: in_gfilter(),
                project: ProjectSpec::Sum { attr: 2 },
                k: int_v(s_in),
                cert: CertId(0),
            },
            Premise::Count {
                pred: PredicateRef::new("flow", 3),
                filter: out_gfilter(),
                project: ProjectSpec::Sum { attr: 2 },
                k: int_v(s_out),
                cert: CertId(0),
            },
            Premise::pos(0),
            Premise::Count {
                pred: PredicateRef::new("flow", 3),
                filter: out_gfilter(),
                project: ProjectSpec::Min { attr: 2 },
                k: int_v(m_out),
                cert: CertId(0),
            },
            Premise::pos(1),
        ],
        meta: NodeMeta::none(),
    };
    Derivation::with_closed_world([eq_node, ge_node, rule_node], 2, [cert])
}

fn run(edb_rows: Vec<GroundLiteral>, deriv: &Derivation, junction: &str) -> Outcome {
    let program = base_program();
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &GroundLiteral::new("balanced", [v(junction)]),
        deriv,
        &(),
        &profile(edb_rows),
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

// =================================== FIXTURES ===================================
// Junction "j1" splits a single 1000-unit input into outputs. Each negative below breaks
// exactly ONE conjunct while leaving the others satisfiable, which is what makes it a
// witness that the conjuncts are independent rather than redundant.

/// accept-conserved: 1000 in → 600 + 400 out (Σin = Σout = 1000, all qty ≥ 0). ACCEPT.
#[test]
fn accept_conserved() {
    let rows = vec![
        flow("j1", "in", 1000),
        flow("j1", "out", 600),
        flow("j1", "out", 400),
    ];
    let cert = flow_cert("j1", &rows, &[1000, 600, 400]);
    let deriv = balanced_derivation("j1", 1000, 1000, 400, cert);
    assert!(
        run(rows, &deriv, "j1").is_accept(),
        "conserved junction must ACCEPT"
    );
}

/// reject-under-sum (Σ<): the input is present but the outputs are missing entirely →
/// Σout = 0 < Σin = 1000. The conservation `=:=(1000, 0)` fails.
#[test]
fn reject_under_sum() {
    // Input present, outputs absent (Σout = 0).
    let rows = vec![flow("j1", "in", 1000)];
    let cert = flow_cert("j1", &rows, &[1000, 0]);
    let deriv = balanced_derivation("j1", 1000, 0, 0, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-duplicated-output (Σ>): the full output set appears twice alongside the input →
/// Σout = 2000 > Σin = 1000. The conservation `=:=(1000, 2000)` fails.
#[test]
fn reject_duplicated_output() {
    let rows = vec![
        flow("j1", "in", 1000),
        flow("j1", "out", 1000),
        flow("j1", "out", 1000),
    ];
    let cert = flow_cert("j1", &rows, &[1000, 2000]);
    let deriv = balanced_derivation("j1", 1000, 2000, 1000, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-oversum (Σ>, non-crash): split 1000 → 600 + 600 (Σout = 1200 > 1000). The 2nd
/// conservation witness; `=:=(1000, 1200)` fails.
#[test]
fn reject_oversum() {
    let rows = vec![
        flow("j1", "in", 1000),
        flow("j1", "out", 600),
        flow("j1", "out", 600),
    ];
    let cert = flow_cert("j1", &rows, &[1000, 1200, 600]);
    let deriv = balanced_derivation("j1", 1000, 1200, 600, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-negative-qty (positivity): split 1000 → 1500 + (−500). Σ is CONSERVED (1000 =
/// 1000) yet the −500 output flow is ill-formed → `min(out qtys) = −500`, `>(−500, 0)`
/// fails. The sign guard is check-enforced, not structural — a negative integer is
/// representable — and this is the witness that positivity is a DISTINCT conjunct from
/// conservation: the sum balances exactly while the flow set is ill-formed.
#[test]
fn reject_negative_qty() {
    let rows = vec![
        flow("j1", "in", 1000),
        flow("j1", "out", 1500),
        flow("j1", "out", -500),
    ];
    let cert = flow_cert("j1", &rows, &[1000, 1500, -500]);
    // Σin = 1000, Σout = 1000 (conserved); min output qty = −500 (positivity > 0 fails).
    let deriv = balanced_derivation("j1", 1000, 1000, -500, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

/// reject-zero-qty (positivity): split 1000 → 1000 + 0. Σ is CONSERVED (1000 = 1000) yet the
/// 0-qty output flow is Σ-neutral — it can never move the conservation equality — so it is
/// invisible to every other conjunct while admitting unbounded growth of the flow set. That
/// is exactly why the predicate is strict: `min(out qtys) = 0`, `>(0, 0)` fails. Distinct
/// from the negative case — the value is non-negative but not positive, the zero edge a
/// `>= 0` predicate would let through.
#[test]
fn reject_zero_qty() {
    let rows = vec![
        flow("j1", "in", 1000),
        flow("j1", "out", 1000),
        flow("j1", "out", 0),
    ];
    let cert = flow_cert("j1", &rows, &[1000, 0]);
    // Σin = 1000, Σout = 1000 (conserved); min output qty = 0 (positivity > 0 fails).
    let deriv = balanced_derivation("j1", 1000, 1000, 0, cert);
    assert_reject(run(rows, &deriv, "j1"), "builtin_failed");
}

// ===================== DEDUP: no source parcel counted twice (by origin) =====================
// The effective conservation set is deduplicated by an identity attribute, as a DISTINCT
// builtin `count(inputs) =:= count_distinct(inputs by origin)` firing alongside conservation.
// A `transfer(J, CiteIdx, Side, Origin, Qty)` relation carries that identity.
//
// CiteIdx is load-bearing, not decoration: a relation is a SET, so without a distinctness key
// two citations of the same parcel would collapse into one row and the dedup fold could never
// observe the duplicate. With it, a double-count is two distinct facts sharing an origin —
// which is the only shape in which `count > count_distinct` can be true at all.
//
//   balanced_v2(C) :-
//     sum(transfer(C,in) over Qty) = S_in, sum(transfer(C,out) over Qty) = S_out, =:=(S_in,S_out),
//     count(transfer(C,in) rows) = Total, count_distinct(transfer(C,in) by Origin) = Distinct,
//     =:=(Total, Distinct).                 -- dedup: no input parcel cited twice

const C_BALANCED_V2: &str = "balanced_v2_rule";

/// `transfer(junction, cite_idx, side, origin, qty)`.
fn transfer(c: &str, cite: i128, side: &str, origin: &str, qty: i128) -> GroundLiteral {
    GroundLiteral::new(
        "transfer",
        [v(c), int_v(cite), v(side), v(origin), int_v(qty)],
    )
}

fn v2_program() -> MapProgram {
    let clause = Clause {
        head: Goal::new("balanced_v2", [Term::var("C")]),
        body: vec![
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, Term::from_value(&v("in")))],
                project: ProjectSpec::Sum { attr: 4 },
                count: Term::var("S_in"),
            }),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, Term::from_value(&v("out")))],
                project: ProjectSpec::Sum { attr: 4 },
                count: Term::var("S_out"),
            }),
            BodyLit::Pos(Literal::new("=:=", [Term::var("S_in"), Term::var("S_out")])),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, Term::from_value(&v("in")))],
                project: ProjectSpec::Rows,
                count: Term::var("Total"),
            }),
            BodyLit::Count(CountLit {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, Term::from_value(&v("in")))],
                project: ProjectSpec::Distinct { attr: 3 },
                count: Term::var("Distinct"),
            }),
            BodyLit::Pos(Literal::new(
                "=:=",
                [Term::var("Total"), Term::var("Distinct")],
            )),
        ],
    };
    MapProgram::new().with(C_BALANCED_V2, clause)
}

fn v2_profile(edb_rows: Vec<GroundLiteral>) -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"transfer".to_vec(), edb_rows);
    CheckProfile {
        theory: Box::new(ArithmeticTheory::new()),
        leaves: Box::new(FlowLeaves {
            extensional: PredicateSet::from_iter(["transfer"]),
            edb,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

/// Sealed cert over `{transfer}`; domain covers C, cite indices, both sides, origins, ints.
fn v2_cert(
    junction: &str,
    edb_rows: &[GroundLiteral],
    cites: &[i128],
    origins: &[&str],
    ints: &[i128],
) -> ClosedModelCert {
    let mut domain_vals: Vec<Value> = vec![v(junction), v("in"), v("out")];
    for c in cites {
        domain_vals.push(int_v(*c));
    }
    for o in origins {
        domain_vals.push(v(o));
    }
    for n in ints {
        domain_vals.push(int_v(*n));
    }
    let domain_count = domain_vals.len();
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("transfer")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), domain_vals)],
        extensions: vec![RelationTable::new("transfer", 5, edb_rows.to_vec())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: edb_rows.len() as u64,
            domain_values: domain_count as u64,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 8_192,
        },
    };
    let program = v2_program();
    let cx = bound_context(&program);
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
    cert
}

#[allow(clippy::too_many_arguments)]
fn v2_derivation(
    junction: &str,
    s_in: i128,
    s_out: i128,
    total: i128,
    distinct: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("C".into(), Term::atom(junction.as_bytes().to_vec()));
    subst.insert("S_in".into(), Term::from_value(&int_v(s_in)));
    subst.insert("S_out".into(), Term::from_value(&int_v(s_out)));
    subst.insert("Total".into(), Term::from_value(&int_v(total)));
    subst.insert("Distinct".into(), Term::from_value(&int_v(distinct)));

    // node 0: =:=(S_in,S_out) conservation; node 1: =:=(Total,Distinct) dedup; node 2: root.
    let cons_node = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(s_in), int_v(s_out)]),
    };
    let dedup_node = Node::Builtin {
        conclusion: GroundLiteral::new("=:=", [int_v(total), int_v(distinct)]),
    };
    let rule_node = Node::Rule {
        conclusion: GroundLiteral::new("balanced_v2", [v(junction)]),
        clause: ClauseId::new(C_BALANCED_V2),
        subst,
        premises: vec![
            Premise::Count {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, v("in"))],
                project: ProjectSpec::Sum { attr: 4 },
                k: int_v(s_in),
                cert: CertId(0),
            },
            Premise::Count {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, v("out"))],
                project: ProjectSpec::Sum { attr: 4 },
                k: int_v(s_out),
                cert: CertId(0),
            },
            Premise::pos(0),
            Premise::Count {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, v("in"))],
                project: ProjectSpec::Rows,
                k: int_v(total),
                cert: CertId(0),
            },
            Premise::Count {
                pred: PredicateRef::new("transfer", 5),
                filter: vec![(2, v("in"))],
                project: ProjectSpec::Distinct { attr: 3 },
                k: int_v(distinct),
                cert: CertId(0),
            },
            Premise::pos(1),
        ],
        meta: NodeMeta::none(),
    };
    Derivation::with_closed_world([cons_node, dedup_node, rule_node], 2, [cert])
}

fn run_v2(edb_rows: Vec<GroundLiteral>, deriv: &Derivation, junction: &str) -> Outcome {
    let program = v2_program();
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &GroundLiteral::new("balanced_v2", [v(junction)]),
        deriv,
        &(),
        &v2_profile(edb_rows),
        &cx,
    )
}

/// accept-no-double-count: two DISTINCT input parcels (origins o1, o2) 1000 each → out 2000.
/// Σin = Σout = 2000 AND count(inputs) = 2 == count_distinct(origins) = 2 → ACCEPT.
#[test]
fn accept_no_double_count() {
    let rows = vec![
        transfer("j1", 0, "in", "o1", 1000),
        transfer("j1", 1, "in", "o2", 1000),
        transfer("j1", 2, "out", "o3", 2000),
    ];
    let cert = v2_cert("j1", &rows, &[0, 1, 2], &["o1", "o2", "o3"], &[1000, 2000]);
    let deriv = v2_derivation("j1", 2000, 2000, 2, 2, cert);
    assert!(
        run_v2(rows, &deriv, "j1").is_accept(),
        "distinct-parcel junction must ACCEPT"
    );
}

/// reject-balanced-duplicate (double-count): the SAME input parcel (origin o1)
/// cited TWICE, 1000 each → out 2000. THE KILLER case: conservation HOLDS (Σin = 2000 = Σout,
/// so the conservation `=:=(2000, 2000)` PASSES) yet it is a double-count — caught ONLY by the
/// dedup builtin: count(inputs) = 2 ≠ count_distinct(origins) = 1 → `=:=(2, 1)` FAILS →
/// builtin_failed. Proves dedup must be a DISTINCT conjunct firing independently of the
/// conservation sum (the inflation stop-ship).
#[test]
fn reject_balanced_duplicate() {
    let rows = vec![
        transfer("j1", 0, "in", "o1", 1000),
        transfer("j1", 1, "in", "o1", 1000), // SAME origin o1 — the double-count
        transfer("j1", 2, "out", "o3", 2000),
    ];
    let cert = v2_cert("j1", &rows, &[0, 1, 2], &["o1", "o3"], &[1000, 2000, 1]);
    // conservation: S_in = 2000 = S_out (HOLDS); dedup: Total = 2, Distinct = 1 (FAILS).
    let deriv = v2_derivation("j1", 2000, 2000, 2, 1, cert);
    assert_reject(run_v2(rows, &deriv, "j1"), "builtin_failed");
}
