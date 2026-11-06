//! #2313 (design 0008 §1.4.3): `check_closed_model_chain` verifies a closed-model certificate
//! chain that no derivation cites, by the verification a `Neg`-cited cert already passes in
//! `check_with_cert_context`.
//!
//! The fixture is `negation.rs`'s sealed prefix (`revoked` EDB, `denied :- revoked`), copied rather
//! than shared because an integration test is its own crate. The controlled pair is the point: the
//! SAME cert accepts through the chain entry and through a derivation that cites it, and the same
//! tamper rejects through both with the same code. The chain entry adds only what a standalone
//! chain needs: a named refusal for an empty chain, and the index in the detail.

use logos_contract::{
    check_closed_model_chain, check_with_cert_context, edb_table_hash, program_digest, CertContext,
    CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert,
    ClosureWitness, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome,
    LeafVerifier, MapProgram, Node, NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise,
    Program, RelationTable, StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol,
    Term, Theory, TheoryOutcome,
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
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Fails {
            code: "no_theory".into(),
        }
    }
}

struct Leaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for Leaves {
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
fn g(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| v(a)))
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}
fn subst2(a: (&str, &str), b: (&str, &str)) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert(a.0.into(), Term::atom(a.1.as_bytes().to_vec()));
    s.insert(b.0.into(), Term::atom(b.1.as_bytes().to_vec()));
    s
}

fn bound_context(program: &dyn Program) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

const C_DENIED_RULE: &str = "denied_rule";
const C_PERMIT_RULE: &str = "permit_rule";

fn program() -> MapProgram {
    MapProgram::new()
        .with(
            C_DENIED_RULE,
            Clause::new(
                Goal::new("denied", [Term::var("S"), Term::var("A")]),
                [Goal::new("revoked", [Term::var("S"), Term::var("A")])],
            ),
        )
        .with(
            C_PERMIT_RULE,
            Clause::with_neg(
                Goal::new("permit", [Term::var("S"), Term::var("A")]),
                [Goal::new("grant", [Term::var("S"), Term::var("A")])],
                [Goal::new("denied", [Term::var("S"), Term::var("A")])],
            ),
        )
}

fn profile_with(limits: CheckLimits) -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"revoked".to_vec(), vec![g("revoked", &["s2", "a2"])]);
    edb.insert(b"grant".to_vec(), vec![g("grant", &["s1", "a1"])]);
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(["grant", "revoked"]),
            edb,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    }
}

fn profile() -> CheckProfile<()> {
    profile_with(CheckLimits::default())
}

/// The sealed prefix `{revoked, denied}` with the one derivable `denied(s2, a2)`.
fn valid_cert() -> ClosedModelCert {
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("revoked"), sym("denied")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![
            FiniteDomain::new(sym("subject"), [v("s1"), v("s2")]),
            FiniteDomain::new(sym("action"), [v("a1"), v("a2")]),
        ],
        extensions: vec![
            RelationTable::new("revoked", 2, [g("revoked", &["s2", "a2"])]),
            RelationTable::new("denied", 2, [g("denied", &["s2", "a2"])]),
        ],
        supports: SupportWitness(vec![SupportEdge {
            fact: g("denied", &["s2", "a2"]),
            clause: ClauseId::new(C_DENIED_RULE),
            subst: subst2(("S", "s2"), ("A", "a2")),
            body_refs: vec![SupportRef::LowerStratum {
                cert: CertId(0),
                atom: g("revoked", &["s2", "a2"]),
            }],
            rank: 1,
        }]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 4,
            support_edges: 1,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    let cx = bound_context(&program());
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
    cert
}

/// The same cert cited by a `Neg` premise: `permit(s1, a1)` because `denied(s1, a1)` is absent.
fn citing_derivation(cert: ClosedModelCert) -> Derivation {
    let nodes = vec![
        Node::Leaf {
            conclusion: g("grant", &["s1", "a1"]),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("permit", &["s1", "a1"]),
            clause: ClauseId::new(C_PERMIT_RULE),
            subst: subst2(("S", "s1"), ("A", "a1")),
            premises: vec![
                Premise::pos(0),
                Premise::Neg {
                    atom: g("denied", &["s1", "a1"]),
                    cert: CertId(0),
                    nonmember: NonMemberProof::DirectLookup,
                },
            ],
            meta: NodeMeta::none(),
        },
    ];
    Derivation::with_closed_world(nodes, 1, [cert])
}

fn chain(certs: &[ClosedModelCert]) -> Outcome {
    let p = program();
    check_closed_model_chain(&p, certs, &(), &profile(), &bound_context(&p))
}

fn cited(cert: ClosedModelCert) -> Outcome {
    let p = program();
    check_with_cert_context(
        &p,
        &g("permit", &["s1", "a1"]),
        &citing_derivation(cert),
        &(),
        &profile(),
        &bound_context(&p),
    )
}

fn reject_code(outcome: &Outcome) -> (&'static str, String) {
    match outcome {
        Outcome::Reject { code, detail } => (code.code(), detail.clone()),
        Outcome::Accept => panic!("expected a rejection, got Accept"),
    }
}

#[test]
fn a_valid_cert_accepts_through_the_chain_and_through_a_citing_derivation() {
    // The positive control first: the fixture is a real, valid seal, or every rejection below
    // would be vacuous.
    assert_eq!(
        cited(valid_cert()),
        Outcome::Accept,
        "fixture: the cited cert must verify"
    );
    assert_eq!(chain(&[valid_cert()]), Outcome::Accept);
}

#[test]
fn an_empty_chain_is_refused_by_name_never_accepted_vacuously() {
    let (code, detail) = reject_code(&chain(&[]));
    assert_eq!(code, "cert_out_of_range");
    assert!(detail.contains("empty certificate chain"), "{detail}");
}

#[test]
fn an_unbound_context_refuses_the_chain() {
    let p = program();
    let out = check_closed_model_chain(&p, &[valid_cert()], &(), &profile(), &CertContext::zero());
    assert_eq!(reject_code(&out).0, "cert_context_unbound");
}

#[test]
fn a_cert_missing_a_derivable_row_is_rejected_the_same_way_both_paths() {
    // Drop `denied(s2, a2)`: `denied :- revoked` still fires on `revoked(s2, a2)`, so the table
    // is no longer closed. The support edge now names a fact outside the table, so the verdict is
    // whichever gate reaches it first. The claim is only that both paths agree on the code.
    let mut tampered = valid_cert();
    tampered.extensions[1] = RelationTable::new("denied", 2, Vec::<GroundLiteral>::new());
    tampered.supports = SupportWitness(vec![]);
    tampered.limits_decl.cert_facts = 1;
    tampered.limits_decl.support_edges = 0;

    let via_citation = reject_code(&cited(tampered.clone())).0;
    let (via_chain, detail) = reject_code(&chain(&[tampered]));
    assert_eq!(
        via_chain, via_citation,
        "the chain reuses verify_cert unchanged"
    );
    assert_eq!(
        via_chain, "cert_not_closed",
        "closure catches the missing head: {detail}"
    );
    assert!(
        detail.starts_with("chain cert 0: "),
        "the detail names the index: {detail}"
    );
}

#[test]
fn the_first_invalid_cert_is_named_by_its_index() {
    let mut bad = valid_cert();
    bad.program_hash = [9u8; 32];
    let (code, detail) = reject_code(&chain(&[valid_cert(), bad]));
    assert_eq!(code, "cert_context_mismatch");
    assert!(detail.starts_with("chain cert 1: "), "{detail}");
}

#[test]
fn a_cert_value_deeper_than_the_cap_is_term_too_deep_before_any_scan() {
    let mut deep = Value::atom(b"x".to_vec());
    for _ in 0..8 {
        deep = Value::tuple([v("box"), deep]);
    }
    let mut cert = valid_cert();
    cert.domains[0] = FiniteDomain::new(sym("subject"), [v("s1"), v("s2"), deep]);
    let limits = CheckLimits {
        max_term_depth: 4,
        ..CheckLimits::default()
    };
    let p = program();
    let out = check_closed_model_chain(&p, &[cert], &(), &profile_with(limits), &bound_context(&p));
    let (code, detail) = reject_code(&out);
    assert_eq!(code, "term_too_deep");
    assert!(detail.contains("certificate domain value"), "{detail}");
}
