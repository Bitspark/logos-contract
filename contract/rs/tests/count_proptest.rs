//! Generative cross-check of the certifiable `count` / `count_distinct` checker against
//! an INDEPENDENT reference, over random sealed relations (ADR 0023 Phase 5, #585 — the
//! generative companion to the hand-authored `vectors/aggregation.json`; extends the #488
//! nightly fuzz lane).
//!
//! The checker recomputes a count by a sort+dedup over canonical ontos-codec `ground_key`
//! bytes (contract/rs/src/check/cert.rs::verify_count_premise step 5c). Here proptest
//! draws a random `obs(subject, perspective, value)` relation — with deliberate row
//! duplicates, repeated projected values, and `null()` markers — and a SEPARATE reference
//! recomputes the same two cardinalities by a completely different route: a `Vec` membership
//! scan for `count` and a `HashSet<String>` of stringified projected values (null excluded)
//! for `count_distinct`. For each random relation + filter subject we assert:
//!   1. the checker ACCEPTS the reference's count `n` (it agrees), and
//!   2. the checker REJECTS `n+1` and (when `n > 0`) `n-1` with `count_mismatch` — the
//!      tamper guard holds for arbitrary relations, not just the pinned vector.
//!
//! A miscount in either direction (a dedup bug, a forgotten null() exclusion, a filter
//! mis-application) shows as an accept/reject disagreement the harness flags.
//!
//! `#[ignore]`'d so it lands in the nightly stress lane (`cargo test --workspace --release
//! -- --ignored`, .github/workflows/stress-nightly.yml), not the per-PR gate.

use std::collections::{BTreeMap, HashSet};

use logos_contract::{
    check_with_cert_context, edb_table_hash, intval::BigInt, program_digest, CertContext, CertId,
    CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness,
    CountLit, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome,
    LeafVerifier, MapProgram, Node, NodeMeta, Outcome, PredicateRef, PredicateSet, Premise,
    ProjectSpec, RelationTable, StratumPrefix, Subst, SupportWitness, Symbol, Term, Theory,
    TheoryOutcome,
};
use ontos_core::Value;
use proptest::prelude::*;

// ----------------------------------- the profile ---------------------------------

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
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Fails {
            code: "no_theory".into(),
        }
    }
}

struct ObsLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for ObsLeaves {
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

// -------------------------------- value / term helpers ---------------------------

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn null_value() -> Value {
    Value::tuple([Value::atom(b"null".to_vec())])
}
fn int_v(n: i128) -> Value {
    BigInt::from_i128(n)
        .to_int_term()
        .erase_ground()
        .expect("ground int")
}
fn obs(s: &str, p: &str, val: Value) -> GroundLiteral {
    GroundLiteral::new("obs", [v(s), v(p), val])
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

const C_COUNT: &str = "obs_count_rule";
const C_DISTINCT: &str = "obs_distinct_rule";

/// `obs_count(S) :- count(obs(S,_,_), N).` and
/// `obs_distinct(S) :- count_distinct(obs(S,_,V), V, N).`
fn program() -> MapProgram {
    let count_clause = Clause {
        head: Goal::new("obs_count", [Term::var("S")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("obs", 3),
            filter: vec![(0, Term::var("S"))],
            project: ProjectSpec::Rows,
            count: Term::var("N"),
        })],
    };
    let distinct_clause = Clause {
        head: Goal::new("obs_distinct", [Term::var("S")]),
        body: vec![logos_contract::BodyLit::Count(CountLit {
            pred: PredicateRef::new("obs", 3),
            filter: vec![(0, Term::var("S"))],
            project: ProjectSpec::Distinct { attr: 2 },
            count: Term::var("N"),
        })],
    };
    MapProgram::new()
        .with(C_COUNT, count_clause)
        .with(C_DISTINCT, distinct_clause)
}

fn bound_context(program: &MapProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

/// The valid sealed cert for `{obs}` over the given rows + the value universe seen.
fn valid_cert(rows: &[GroundLiteral], universe: &[Value], program: &MapProgram) -> ClosedModelCert {
    let cx = bound_context(program);
    ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("obs")]),
        program_hash: cx.program_hash,
        profile_hash: cx.profile_hash,
        ctx_hash: cx.ctx_hash,
        theory_config_hash: cx.theory_config_hash,
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), universe.to_vec())],
        extensions: vec![RelationTable::new("obs", 3, rows.to_vec())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: rows.len() as u64,
            domain_values: universe.len() as u64,
            support_edges: 0,
            rule_groundings: 1_000_000,
            join_steps: 10_000_000,
            cert_bytes: 1_000_000,
        },
    }
}

fn run(
    program: &MapProgram,
    profile: &CheckProfile<()>,
    claim: &GroundLiteral,
    deriv: &Derivation,
) -> Outcome {
    let cx = bound_context(program);
    check_with_cert_context(program, claim, deriv, &(), profile, &cx)
}

fn count_deriv(
    clause_id: &str,
    head_pred: &str,
    subject: &str,
    project: ProjectSpec,
    k: i128,
    cert: ClosedModelCert,
) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("S".into(), Term::atom(subject.as_bytes().to_vec()));
    subst.insert("N".into(), Term::from_value(&int_v(k)));
    Derivation::with_closed_world(
        [Node::Rule {
            conclusion: GroundLiteral::new(head_pred, [v(subject)]),
            clause: ClauseId::new(clause_id),
            subst,
            premises: vec![Premise::Count {
                pred: PredicateRef::new("obs", 3),
                filter: vec![(0, v(subject))],
                project,
                k: int_v(k),
                cert: CertId(0),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    )
}

// ------------------------------- the independent reference ------------------------

/// The string spelling of an obs value for the reference set (a route distinct from the
/// checker's canonical-codec key): `null()` → the sentinel "\u{0}null", an atom → its UTF-8
/// (lossless for the ASCII generators here). Two values collide here iff equal, matching the
/// codec's dedup but via a different mechanism.
fn ref_key(val: &Value) -> String {
    if matches!(val.as_tuple(), Some(t) if t.items() == [Value::atom(b"null".to_vec())]) {
        return "\u{0}null".to_string();
    }
    match val.as_atom() {
        Some(a) => format!("a:{}", String::from_utf8_lossy(a.bytes())),
        None => format!("t:{val:?}"),
    }
}

/// Reference `count` of rows whose subject == `subject`.
fn ref_count_rows(rows: &[(String, String, Value)], subject: &str) -> i128 {
    rows.iter().filter(|(s, _, _)| s == subject).count() as i128
}

/// Reference `count_distinct` of the projected value column over the subject's rows,
/// EXCLUDING null(), deduped by `ref_key` (a HashSet — not the codec sort+dedup).
fn ref_count_distinct(rows: &[(String, String, Value)], subject: &str) -> i128 {
    let mut set: HashSet<String> = HashSet::new();
    for (s, _, val) in rows.iter().filter(|(s, _, _)| s == subject) {
        let _ = s;
        let key = ref_key(val);
        if key == "\u{0}null" {
            continue; // null() excluded
        }
        set.insert(key);
    }
    set.len() as i128
}

// --------------------------------- the generators --------------------------------

/// A subject atom from a tiny pool (so collisions on the filter subject are common).
fn subject_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec!["s0", "s1", "s2"]).prop_map(String::from)
}
/// A projected value: a small atom pool with frequent repeats + occasional null().
fn value_strategy() -> impl Strategy<Value = Value> {
    prop_oneof![
        8 => prop::sample::select(vec!["a", "b", "c", "d"]).prop_map(v),
        2 => Just(null_value()),
    ]
}
/// A perspective atom (the unused middle column; varied so rows can fully duplicate).
fn persp_strategy() -> impl Strategy<Value = String> {
    prop::sample::select(vec!["p0", "p1", "p2"]).prop_map(String::from)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1024, ..ProptestConfig::default() })]

    #[test]
    #[ignore = "generative cross-check — heavy; runs in the nightly stress lane (release, -- --ignored), not the per-PR gate (#585/#488)"]
    fn count_and_distinct_match_an_independent_reference(
        raw_rows in prop::collection::vec(
            (subject_strategy(), persp_strategy(), value_strategy()),
            0..16usize,
        ),
        filter_subject in subject_strategy(),
    ) {
        // Build the relation. Duplicate (s,p,v) triples are intentional: the cert's
        // RelationTable sorts+dedups them, so the count is over the SET — the reference
        // must match that, which is why it scans `rows` (the deduped facts), not raw draws.
        let mut seen: HashSet<(String, String, String)> = HashSet::new();
        let mut rows: Vec<(String, String, Value)> = Vec::new();
        for (s, p, val) in &raw_rows {
            let dedup_key = (s.clone(), p.clone(), ref_key(val));
            if seen.insert(dedup_key) {
                rows.push((s.clone(), p.clone(), val.clone()));
            }
        }
        let glits: Vec<GroundLiteral> = rows.iter().map(|(s, p, val)| obs(s, p, val.clone())).collect();

        // The value universe the cert seals (domain coverage §3.4): every subject/perspective
        // in the pools + every projected value + null() (a fixed, complete set covering every
        // value any generated row or the filter subject can take, so domain coverage holds).
        let universe: Vec<Value> = vec![
            v("s0"), v("s1"), v("s2"), v("p0"), v("p1"), v("p2"),
            v("a"), v("b"), v("c"), v("d"), null_value(),
        ];

        let prog = program();
        let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
        edb.insert(b"obs".to_vec(), glits.clone());
        let profile = CheckProfile {
            theory: Box::new(NoTheory),
            leaves: Box::new(ObsLeaves {
                extensional: PredicateSet::from_iter(["obs"]),
                edb,
            }),
            admit: Box::new(logos_contract::AlwaysAdmit),
            limits: CheckLimits::default(),
        };

        let cert = || valid_cert(&glits, &universe, &prog);

        // ---- count (rows) ----
        let n_rows = ref_count_rows(&rows, &filter_subject);
        let claim_count = GroundLiteral::new("obs_count", [v(&filter_subject)]);

        // 1. the checker ACCEPTS the reference count.
        let accept = run(&prog, &profile, &claim_count,
            &count_deriv(C_COUNT, "obs_count", &filter_subject, ProjectSpec::Rows, n_rows, cert()));
        prop_assert!(accept.is_accept(),
            "count: checker rejected the reference n={n_rows}: {accept:?}");

        // 2. the checker REJECTS n+1 (and n-1 when n>0) with count_mismatch.
        let plus = run(&prog, &profile, &claim_count,
            &count_deriv(C_COUNT, "obs_count", &filter_subject, ProjectSpec::Rows, n_rows + 1, cert()));
        assert_count_mismatch(&plus, n_rows + 1, n_rows, "count");
        if n_rows > 0 {
            let minus = run(&prog, &profile, &claim_count,
                &count_deriv(C_COUNT, "obs_count", &filter_subject, ProjectSpec::Rows, n_rows - 1, cert()));
            assert_count_mismatch(&minus, n_rows - 1, n_rows, "count");
        }

        // ---- count_distinct (column 2, null excluded) ----
        let n_distinct = ref_count_distinct(&rows, &filter_subject);
        let claim_distinct = GroundLiteral::new("obs_distinct", [v(&filter_subject)]);

        let accept_d = run(&prog, &profile, &claim_distinct,
            &count_deriv(C_DISTINCT, "obs_distinct", &filter_subject, ProjectSpec::Distinct { attr: 2 }, n_distinct, cert()));
        prop_assert!(accept_d.is_accept(),
            "count_distinct: checker rejected the reference n={n_distinct}: {accept_d:?}");

        let plus_d = run(&prog, &profile, &claim_distinct,
            &count_deriv(C_DISTINCT, "obs_distinct", &filter_subject, ProjectSpec::Distinct { attr: 2 }, n_distinct + 1, cert()));
        assert_count_mismatch(&plus_d, n_distinct + 1, n_distinct, "count_distinct");
        if n_distinct > 0 {
            let minus_d = run(&prog, &profile, &claim_distinct,
                &count_deriv(C_DISTINCT, "obs_distinct", &filter_subject, ProjectSpec::Distinct { attr: 2 }, n_distinct - 1, cert()));
            assert_count_mismatch(&minus_d, n_distinct - 1, n_distinct, "count_distinct");
        }
    }
}

fn assert_count_mismatch(outcome: &Outcome, claimed: i128, actual: i128, which: &str) {
    match outcome {
        Outcome::Reject { code, .. } => assert_eq!(
            code.code(),
            "count_mismatch",
            "{which}: tampered k={claimed} (actual {actual}) must be count_mismatch, got {}",
            code.code()
        ),
        Outcome::Accept => panic!("{which}: tampered k={claimed} (actual {actual}) was ACCEPTED — the gate failed to recompute"),
    }
}
