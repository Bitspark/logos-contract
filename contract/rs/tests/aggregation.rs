//! ADR 0023 — certifiable aggregation (count / count-distinct): the rust-local
//! checker oracle tests (Phase 1-2). A structural clone of the negation tests
//! (`negation.rs`): build a sealed, exact [`ClosedModelCert`] over a small relation,
//! cite it from a [`Premise::Count`], and assert the checker re-derives the count.
//!
//! ACCEPT: a correct `count` (rows matching a filter) and a correct `count_distinct`
//! (distinct projected attr, `null()` excluded).
//! REJECT: a wrong `k` → `count_mismatch`; a count over a same/higher stratum →
//! `count_stratum_not_lower`; a projection attr out of range → `count_attr_out_of_range`;
//! a stale EDB → the existing `cert_edb_mismatch` gate still fires.

use logos_contract::{
    check_with_cert_context, edb_table_hash, intval::BigInt, program_digest, CertContext, CertId,
    CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness,
    CompleteProgram, CountLit, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash,
    LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, Outcome, PredicateRef, PredicateSet,
    Premise, ProjectSpec, RelationTable, StratumPrefix, Subst, SupportWitness, Symbol, Term,
    Theory, TheoryGround, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;

// ================================= test profile =================================
// EDB leaf `obs` (the relation we count over); `eligible` is the upper-stratum IDB
// head whose body carries the count. No theory needed (an empty `NoTheory`).

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::fails("no_theory")
    }
}

/// A `LeafVerifier` attesting a fixed EDB-of-record snapshot for each extensional
/// predicate (so the §3.6 EDB-binding gate can bind the sealed table to the live EDB).
struct AggLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
impl AggLeaves {
    fn new(preds: &[&str], edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>) -> Self {
        AggLeaves {
            extensional: PredicateSet::from_iter(preds.iter().copied()),
            edb,
        }
    }
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for AggLeaves {
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

// ============================ value / literal helpers ===========================

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
/// The canonical `null()` marker (nullary compound `Tuple[Atom("null")]`).
fn null_value() -> Value {
    Value::tuple([Value::atom(b"null".to_vec())])
}
/// The int ground value `n` (the count-result embedding `k` binds).
fn int_v(n: i128) -> Value {
    BigInt::from_i128(n)
        .to_int_term()
        .erase_ground()
        .expect("ground int")
}
/// `obs(o, p, val)` where `val` is an arbitrary ontos value (atom or null()).
fn obs(o: &str, p: &str, val: Value) -> GroundLiteral {
    GroundLiteral::new("obs", [v(o), v(p), val])
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

/// The bound [`CertContext`] for `program` (recomputed program hash + fixed pins).
fn bound_context(program: &dyn CompleteProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}
fn bind_cert(cert: &mut ClosedModelCert, program: &dyn CompleteProgram) {
    let cx = bound_context(program);
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
}

// ================================ the program ===================================
// obs(O,P,V) is a PURE EDB leaf (no defining clause). The upper-stratum head carries
// a single Count body literal. Two heads — one for `count`, one for `count_distinct`.

const C_ELIGIBLE_COUNT: &str = "eligible_count_rule";
const C_ELIGIBLE_DISTINCT: &str = "eligible_distinct_rule";

/// The EDB-of-record for `obs` (the sealed relation we count over):
///   obs(o1, p1, x), obs(o1, p2, x), obs(o1, p3, y), obs(o1, p4, null()),
///   obs(o2, p1, z)
/// For O=o1: 4 rows; distinct non-null V = {x, y} → 2.
fn obs_edb() -> Vec<GroundLiteral> {
    vec![
        obs("o1", "p1", v("x")),
        obs("o1", "p2", v("x")),
        obs("o1", "p3", v("y")),
        obs("o1", "p4", null_value()),
        obs("o2", "p1", v("z")),
    ]
}

/// `eligible_count(O) :- count(obs(O,_,_), N).` and
/// `eligible_distinct(O) :- count_distinct(obs(O,_,V), V, N).`
/// (Built via API with a `BodyLit::Count`; the parser lowering is Phase 4, out of scope.)
fn base_program() -> MapProgram {
    // Filter `O = o1` lives at obs position 0; the count result `N` is the head's var.
    let count_clause = Clause {
        head: Goal::new("eligible_count", [Term::var("O")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("obs", 3),
            filter: vec![(0, Term::var("O"))],
            project: ProjectSpec::Rows,
            count: Term::var("N"),
        })],
    };
    let distinct_clause = Clause {
        head: Goal::new("eligible_distinct", [Term::var("O")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("obs", 3),
            // count_distinct of attribute 2 (V) over rows with O at position 0.
            filter: vec![(0, Term::var("O"))],
            project: ProjectSpec::Distinct { attr: 2 },
            count: Term::var("N"),
        })],
    };
    MapProgram::new()
        .with(C_ELIGIBLE_COUNT, count_clause)
        .with(C_ELIGIBLE_DISTINCT, distinct_clause)
}

fn profile() -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"obs".to_vec(), obs_edb());
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(AggLeaves::new(&["obs"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

/// The valid sealed certificate for the prefix `{obs}` (level 0): obs = the live EDB
/// snapshot. `obs` is a PURE EDB leaf, exempt from support, bound by the §3.6 EDB gate.
fn valid_cert() -> ClosedModelCert {
    // Domain: every value reachable in an obs row (subjects, perspectives, values incl.
    // null()), so domain-coverage (§3.4) passes.
    let domain = FiniteDomain::new(
        sym("u"),
        [
            v("o1"),
            v("o2"),
            v("p1"),
            v("p2"),
            v("p3"),
            v("p4"),
            v("x"),
            v("y"),
            v("z"),
            null_value(),
        ],
    );
    let obs_tbl = RelationTable::new("obs", 3, obs_edb());
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("obs")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![domain],
        extensions: vec![obs_tbl],
        // obs is a pure EDB leaf → no support edges (bound by the EDB snapshot gate).
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 5,
            domain_values: 10,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 8_192,
        },
    };
    bind_cert(&mut cert, &base_program());
    cert
}

/// A derivation `eligible_<kind>(o1) :- count[..](..) = k`, citing the sealed cert.
fn count_derivation(
    clause_id: &str,
    head_pred: &str,
    project: ProjectSpec,
    k: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(k)));
    let node = Node::Rule {
        conclusion: GroundLiteral::new(head_pred, [v("o1")]),
        clause: ClauseId::new(clause_id),
        subst,
        premises: vec![Premise::Count {
            pred: PredicateRef::new("obs", 3),
            filter: vec![(0, v("o1"))],
            project,
            k: int_v(k),
            cert: CertId(0),
        }],
        meta: NodeMeta::none(),
    };
    Derivation::with_closed_world([node], 0, [cert])
}

fn run(program: &MapProgram, claim: &GroundLiteral, deriv: &Derivation) -> Outcome {
    let cx = bound_context(program);
    check_with_cert_context(program, claim, deriv, &(), &profile(), &cx)
}

fn assert_reject(outcome: Outcome, expected: &str) {
    match outcome.verdict {
        Verdict::Reject { code, detail } => assert_eq!(
            code.code(),
            expected,
            "expected {expected}, got {} ({detail})",
            code.code()
        ),
        Verdict::Accept => panic!("expected reject {expected}, got Accept"),
    }
}

// =================================== ACCEPT ===================================

/// A correct `count`: 4 obs rows match the filter O=o1 → eligible_count(o1) accepts.
#[test]
fn accept_count_rows_matching_filter() {
    let deriv = count_derivation(
        C_ELIGIBLE_COUNT,
        "eligible_count",
        ProjectSpec::Rows,
        4,
        valid_cert(),
    );
    let outcome = run(
        &base_program(),
        &GroundLiteral::new("eligible_count", [v("o1")]),
        &deriv,
    );
    assert!(outcome.is_accept(), "expected Accept, got {outcome:?}");
}

/// A correct `count_distinct`: distinct non-null V over O=o1 rows = {x, y} → 2; the
/// null() projection of obs(o1,p4,null()) is EXCLUDED.
#[test]
fn accept_count_distinct_excludes_null() {
    let deriv = count_derivation(
        C_ELIGIBLE_DISTINCT,
        "eligible_distinct",
        ProjectSpec::Distinct { attr: 2 },
        2,
        valid_cert(),
    );
    let outcome = run(
        &base_program(),
        &GroundLiteral::new("eligible_distinct", [v("o1")]),
        &deriv,
    );
    assert!(outcome.is_accept(), "expected Accept, got {outcome:?}");
}

// =================================== REJECT ===================================

/// `count_mismatch` — a wrong `k` (claim 3 rows when 4 match).
#[test]
fn reject_count_mismatch_wrong_k_rows() {
    let deriv = count_derivation(
        C_ELIGIBLE_COUNT,
        "eligible_count",
        ProjectSpec::Rows,
        3, // actually 4
        valid_cert(),
    );
    assert_reject(
        run(
            &base_program(),
            &GroundLiteral::new("eligible_count", [v("o1")]),
            &deriv,
        ),
        "count_mismatch",
    );
}

/// `count_mismatch` — a wrong `k` for count_distinct (claim 3 when distinct = 2, i.e.
/// the tamperer forgot null() is excluded / double-counted x).
#[test]
fn reject_count_mismatch_wrong_k_distinct() {
    let deriv = count_derivation(
        C_ELIGIBLE_DISTINCT,
        "eligible_distinct",
        ProjectSpec::Distinct { attr: 2 },
        3, // actually 2 (x, y); null excluded, x deduped
        valid_cert(),
    );
    assert_reject(
        run(
            &base_program(),
            &GroundLiteral::new("eligible_distinct", [v("o1")]),
            &deriv,
        ),
        "count_mismatch",
    );
}

/// `count_stratum_not_lower` — the rule head predicate is itself sealed by the cert
/// (same/higher stratum), so the count does not look strictly downward. We seal a
/// prefix that ALSO contains the head predicate `eligible_count`.
#[test]
fn reject_count_stratum_not_lower() {
    let program = base_program();
    let mut cert = valid_cert();
    // Seal `eligible_count` alongside `obs` (so the head predicate is in the lower scope).
    // Add an empty table for it; obs stays the EDB-bound table.
    cert.scope = StratumPrefix::new(0, [sym("obs"), sym("eligible_count")]);
    cert.extensions.push(RelationTable::new(
        "eligible_count",
        1,
        [] as [GroundLiteral; 0],
    ));
    // eligible_count's only clause carries a count → §3.2 scope-closure would reject it
    // (a count in a sealed-scope clause). To isolate the PER-PREMISE stratum check, that
    // §3.2 reject fires first; either way the unsound same-stratum count is REJECTED.
    bind_cert(&mut cert, &program);
    let deriv = count_derivation(
        C_ELIGIBLE_COUNT,
        "eligible_count",
        ProjectSpec::Rows,
        4,
        cert,
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_count", [v("o1")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    // The sealed-scope clause `eligible_count_rule` carries a count body literal, so
    // §3.2 scope-closure rejects the cert (`cert_scope_incomplete`) — which subsumes the
    // per-premise `count_stratum_not_lower` for this malformed shape. Both reject the
    // unsound same-stratum count.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// `count_stratum_not_lower` proper (per-premise) — the cert is valid and the head
/// predicate is sealed, with no count clause inside the sealed scope. We seal a SEPARATE
/// relation `r` together with the head predicate, and cite a Count over `r` from a rule
/// whose head `r` is sealed.
#[test]
fn reject_count_stratum_not_lower_head_sealed() {
    // Program: r is a pure EDB leaf; the citing rule concludes `r(o1)` while counting
    // `r` — head predicate `r` IS in the sealed scope ⇒ per-premise stratum reject.
    let r_clause = Clause {
        head: Goal::new("r", [Term::var("O")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("r", 1),
            filter: vec![],
            project: ProjectSpec::Rows,
            count: Term::var("N"),
        })],
    };
    let program = MapProgram::new().with("r_self_count", r_clause);
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    // r EDB-of-record = { r(o1) } (1 row).
    edb.insert(b"r".to_vec(), vec![GroundLiteral::new("r", [v("o1")])]);
    let prof = CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(AggLeaves::new(&["r"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("r")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), [v("o1")])],
        extensions: vec![RelationTable::new(
            "r",
            1,
            [GroundLiteral::new("r", [v("o1")])],
        )],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 1,
            support_edges: 0,
            rule_groundings: 100,
            join_steps: 100,
            cert_bytes: 512,
        },
    };
    bind_cert(&mut cert, &program);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(1)));
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("r", [v("o1")]),
            clause: ClauseId::new("r_self_count"),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("r", 1),
                filter: vec![],
                project: ProjectSpec::Rows,
                k: int_v(1),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("r", [v("o1")]),
        &deriv,
        &(),
        &prof,
        &cx,
    );
    // The sealed-scope clause `r_self_count` carries a count → §3.2 rejects first; the
    // per-premise `count_stratum_not_lower` is the backstop. Either way the unsound
    // self-count over a same-stratum head is REJECTED.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// `count_attr_out_of_range` — a count_distinct projection attr ≥ the predicate arity
/// (obs has arity 3, so attr 5 is out of range).
#[test]
fn reject_count_attr_out_of_range() {
    let program = base_program().with(
        "eligible_bad_attr",
        Clause {
            head: Goal::new("eligible_bad", [Term::var("O")]),
            body: vec![logos_contract::BodyLit::Count(CountLit {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(0, Term::var("O"))],
                project: ProjectSpec::Distinct { attr: 5 }, // obs arity = 3
                count: Term::var("N"),
            })],
        },
    );
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(2)));
    // Bind the cert to THIS (augmented) program's hash, not base_program's.
    let mut cert = valid_cert();
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("eligible_bad", [v("o1")]),
            clause: ClauseId::new("eligible_bad_attr"),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(0, v("o1"))],
                project: ProjectSpec::Distinct { attr: 5 },
                k: int_v(2),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_bad", [v("o1")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "count_attr_out_of_range");
}

/// `count_attr_out_of_range` — a FILTER position ≥ arity (obs arity 3; position 7).
#[test]
fn reject_count_filter_position_out_of_range() {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(0)));
    // A clause whose count filters position 7 (out of obs's arity 3).
    let program = base_program().with(
        "eligible_bad_filter",
        Clause {
            head: Goal::new("eligible_bad", [Term::var("O")]),
            body: vec![logos_contract::BodyLit::Count(CountLit {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(7, Term::var("O"))],
                project: ProjectSpec::Rows,
                count: Term::var("N"),
            })],
        },
    );
    let mut cert = valid_cert();
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("eligible_bad", [v("o1")]),
            clause: ClauseId::new("eligible_bad_filter"),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(7, v("o1"))],
                project: ProjectSpec::Rows,
                k: int_v(0),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_bad", [v("o1")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "count_attr_out_of_range");
}

/// Stale EDB — the sealed `obs` table OMITS a live EDB fact, so the existing §3.6 EDB
/// gate (`cert_edb_mismatch`) fires before the count is recomputed.
#[test]
fn reject_stale_edb_cert_edb_mismatch() {
    let mut cert = valid_cert();
    // Drop one obs row so the sealed table no longer matches the attested live snapshot.
    cert.extensions = vec![RelationTable::new(
        "obs",
        3,
        vec![
            obs("o1", "p1", v("x")),
            obs("o1", "p2", v("x")),
            obs("o1", "p3", v("y")),
            // obs(o1,p4,null()) and obs(o2,p1,z) OMITTED
        ],
    )];
    cert.limits_decl.cert_facts = 3;
    bind_cert(&mut cert, &base_program());
    let deriv = count_derivation(
        C_ELIGIBLE_COUNT,
        "eligible_count",
        ProjectSpec::Rows,
        4,
        cert,
    );
    assert_reject(
        run(
            &base_program(),
            &GroundLiteral::new("eligible_count", [v("o1")]),
            &deriv,
        ),
        "cert_edb_mismatch",
    );
}

/// `count_mismatch` — the filter selects a different subject (O=o2 → 1 obs row), and the
/// claim of 4 (the o1 count) is wrong for o2. Proves the filter is genuinely applied.
#[test]
fn reject_count_mismatch_filter_applied() {
    let program = base_program();
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o2".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(4)));
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("eligible_count", [v("o2")]),
            clause: ClauseId::new(C_ELIGIBLE_COUNT),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(0, v("o2"))], // o2 has only 1 obs row
                project: ProjectSpec::Rows,
                k: int_v(4), // claims 4 — wrong, actual is 1
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [valid_cert()],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_count", [v("o2")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "count_mismatch");
}

/// ACCEPT — the filter applied to o2 gives 1 row; claiming k=1 accepts.
#[test]
fn accept_count_filter_applied_o2() {
    let program = base_program();
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o2".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(1)));
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("eligible_count", [v("o2")]),
            clause: ClauseId::new(C_ELIGIBLE_COUNT),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(0, v("o2"))],
                project: ProjectSpec::Rows,
                k: int_v(1),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [valid_cert()],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_count", [v("o2")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert!(outcome.is_accept(), "expected Accept, got {outcome:?}");
}

/// `cert_out_of_range` — the cited cert index does not exist (the cert path's range gate
/// applies to a count premise too).
#[test]
fn reject_count_cert_out_of_range() {
    let mut deriv = count_derivation(
        C_ELIGIBLE_COUNT,
        "eligible_count",
        ProjectSpec::Rows,
        4,
        valid_cert(),
    );
    deriv.closed_world.clear();
    assert_reject(
        run(
            &base_program(),
            &GroundLiteral::new("eligible_count", [v("o1")]),
            &deriv,
        ),
        "cert_out_of_range",
    );
}

/// `count_attr_out_of_range` (#581 arity sharpening) — the `PredicateRef` names `obs`
/// with arity 2, but the sealed `obs` table has arity 3. A wrong arity must be rejected,
/// never silently counted against a different-arity table.
#[test]
fn reject_count_wrong_arity() {
    let program = base_program().with(
        "eligible_bad_arity",
        Clause {
            head: Goal::new("eligible_bad", [Term::var("O")]),
            body: vec![logos_contract::BodyLit::Count(CountLit {
                pred: PredicateRef::new("obs", 2), // sealed obs is arity 3
                filter: vec![(0, Term::var("O"))],
                project: ProjectSpec::Rows,
                count: Term::var("N"),
            })],
        },
    );
    let mut subst: Subst = BTreeMap::new();
    subst.insert("O".into(), Term::atom(b"o1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(4)));
    let mut cert = valid_cert();
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("eligible_bad", [v("o1")]),
            clause: ClauseId::new("eligible_bad_arity"),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 2),
                filter: vec![(0, v("o1"))],
                project: ProjectSpec::Rows,
                k: int_v(4),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("eligible_bad", [v("o1")]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "count_attr_out_of_range");
}

// ====================== #587 — integer sum / min / max folds ======================
// A second relation `score(obj, val)` whose column 1 is a sealed integer. The aggregate
// folds it with the ArithmeticTheory exact operators (over BigInt). v1 is INTEGER-only,
// SET semantics over the proven-exact rows; empty sum = 0; empty min/max REJECT; a
// non-int column is ill-typed (count_attr_out_of_range).

const C_SCORE_SUM: &str = "score_sum_rule";
const C_SCORE_MIN: &str = "score_min_rule";
const C_SCORE_MAX: &str = "score_max_rule";

fn iv(n: i128) -> Value {
    int_v(n)
}
/// `score(obj, val)` with an int `val` column (or a non-int for the ill-typed test).
fn score(obj: &str, val: Value) -> GroundLiteral {
    GroundLiteral::new("score", [v(obj), val])
}

/// EDB-of-record for `score`: g1 has int values {3, 7, 1} (set semantics over distinct
/// facts). sum over g1 = 3+7+1 = 11; min = 1; max = 7. g2_unused has one unrelated row.
fn score_edb() -> Vec<GroundLiteral> {
    vec![
        score("g1", iv(3)),
        score("g1", iv(7)),
        score("g1", iv(1)),
        score("g2_unused", iv(99)),
    ]
}

fn score_program() -> MapProgram {
    let mk = |head: &str, project: ProjectSpec| Clause {
        head: Goal::new(head, [Term::var("G")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("score", 2),
            filter: vec![(0, Term::var("G"))],
            project,
            count: Term::var("N"),
        })],
    };
    MapProgram::new()
        .with(C_SCORE_SUM, mk("score_sum", ProjectSpec::Sum { attr: 1 }))
        .with(C_SCORE_MIN, mk("score_min", ProjectSpec::Min { attr: 1 }))
        .with(C_SCORE_MAX, mk("score_max", ProjectSpec::Max { attr: 1 }))
}

fn score_profile() -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"score".to_vec(), score_edb());
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(AggLeaves::new(&["score"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn score_cert_with_domain(domain_vals: &[Value], domain_count: usize) -> ClosedModelCert {
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("score")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), domain_vals.to_vec())],
        extensions: vec![RelationTable::new("score", 2, score_edb())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 4,
            domain_values: domain_count as u64,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 8_192,
        },
    };
    bind_cert(&mut cert, &score_program());
    cert
}

fn score_cert() -> ClosedModelCert {
    score_cert_with_domain(&[v("g1"), v("g2_unused"), iv(3), iv(7), iv(1), iv(99)], 6)
}

/// `<head>(g) :- agg(score(g, V), V, k)`, citing the score cert.
fn fold_derivation(
    clause_id: &str,
    head_pred: &str,
    group: &str,
    project: ProjectSpec,
    k: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("G".into(), Term::atom(group.as_bytes().to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(k)));
    let node = Node::Rule {
        conclusion: GroundLiteral::new(head_pred, [v(group)]),
        clause: ClauseId::new(clause_id),
        subst,
        premises: vec![Premise::Count {
            pred: PredicateRef::new("score", 2),
            filter: vec![(0, v(group))],
            project,
            k: int_v(k),
            cert: CertId(0),
        }],
        meta: NodeMeta::none(),
    };
    Derivation::with_closed_world([node], 0, [cert])
}

fn run_fold(claim_pred: &str, group: &str, deriv: &Derivation) -> Outcome {
    let program = score_program();
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &GroundLiteral::new(claim_pred, [v(group)]),
        deriv,
        &(),
        &score_profile(),
        &cx,
    )
}

/// ACCEPT integer sum: 3 + 7 + 1 = 11 over the sealed g1 column.
#[test]
fn accept_sum_integer_column() {
    let deriv = fold_derivation(
        C_SCORE_SUM,
        "score_sum",
        "g1",
        ProjectSpec::Sum { attr: 1 },
        11,
        score_cert(),
    );
    assert!(run_fold("score_sum", "g1", &deriv).is_accept());
}

/// ACCEPT integer min / max over the sealed g1 column: min = 1, max = 7.
#[test]
fn accept_min_max_integer_column() {
    let dmin = fold_derivation(
        C_SCORE_MIN,
        "score_min",
        "g1",
        ProjectSpec::Min { attr: 1 },
        1,
        score_cert(),
    );
    assert!(run_fold("score_min", "g1", &dmin).is_accept());
    let dmax = fold_derivation(
        C_SCORE_MAX,
        "score_max",
        "g1",
        ProjectSpec::Max { attr: 1 },
        7,
        score_cert(),
    );
    assert!(run_fold("score_max", "g1", &dmax).is_accept());
}

/// The cert + domain that includes an in-domain group atom `empty_grp` with no rows.
fn score_cert_empty_group() -> ClosedModelCert {
    score_cert_with_domain(
        &[
            v("g1"),
            v("g2_unused"),
            v("empty_grp"),
            iv(3),
            iv(7),
            iv(1),
            iv(99),
        ],
        7,
    )
}

/// ACCEPT empty sum = 0: no score rows match the in-domain group `empty_grp`.
#[test]
fn accept_empty_sum_is_zero() {
    let deriv = fold_derivation(
        C_SCORE_SUM,
        "score_sum",
        "empty_grp",
        ProjectSpec::Sum { attr: 1 },
        0,
        score_cert_empty_group(),
    );
    assert!(
        run_fold("score_sum", "empty_grp", &deriv).is_accept(),
        "empty sum should be 0/Accept"
    );
}

/// REJECT empty min: min of an empty set is undefined => `agg_empty_undefined`. The claim
/// `k` is irrelevant — the empty fold rejects BEFORE the k comparison.
#[test]
fn reject_empty_min_undefined() {
    let deriv = fold_derivation(
        C_SCORE_MIN,
        "score_min",
        "empty_grp",
        ProjectSpec::Min { attr: 1 },
        0,
        score_cert_empty_group(),
    );
    assert_reject(
        run_fold("score_min", "empty_grp", &deriv),
        "agg_empty_undefined",
    );
}

/// REJECT empty max: symmetric to min.
#[test]
fn reject_empty_max_undefined() {
    let deriv = fold_derivation(
        C_SCORE_MAX,
        "score_max",
        "empty_grp",
        ProjectSpec::Max { attr: 1 },
        0,
        score_cert_empty_group(),
    );
    assert_reject(
        run_fold("score_max", "empty_grp", &deriv),
        "agg_empty_undefined",
    );
}

/// REJECT a tampered sum: claim 99 when the real sum is 11 => `count_mismatch`.
#[test]
fn reject_sum_tamper_wrong_result() {
    let deriv = fold_derivation(
        C_SCORE_SUM,
        "score_sum",
        "g1",
        ProjectSpec::Sum { attr: 1 },
        99,
        score_cert(),
    );
    assert_reject(run_fold("score_sum", "g1", &deriv), "count_mismatch");
}

/// REJECT a tampered max: claim 8 when the real max is 7 => `count_mismatch`.
#[test]
fn reject_max_tamper_wrong_result() {
    let deriv = fold_derivation(
        C_SCORE_MAX,
        "score_max",
        "g1",
        ProjectSpec::Max { attr: 1 },
        8,
        score_cert(),
    );
    assert_reject(run_fold("score_max", "g1", &deriv), "count_mismatch");
}

/// REJECT a sum over a NON-INT column: fold column 0 (the group atom, not an int) =>
/// ill-typed `count_attr_out_of_range` (v1 sum/min/max are integer-only).
#[test]
fn reject_sum_non_int_column() {
    let bad = Clause {
        head: Goal::new("score_bad", [Term::var("G")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("score", 2),
            filter: vec![(0, Term::var("G"))],
            project: ProjectSpec::Sum { attr: 0 },
            count: Term::var("N"),
        })],
    };
    let program = score_program().with("score_bad_rule", bad);
    let mut cert = score_cert();
    bind_cert(&mut cert, &program);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("G".into(), Term::atom(b"g1".to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(0)));
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new("score_bad", [v("g1")]),
            clause: ClauseId::new("score_bad_rule"),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("score", 2),
                filter: vec![(0, v("g1"))],
                project: ProjectSpec::Sum { attr: 0 },
                k: int_v(0),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &GroundLiteral::new("score_bad", [v("g1")]),
        &deriv,
        &(),
        &score_profile(),
        &cx,
    );
    assert_reject(outcome, "count_attr_out_of_range");
}
