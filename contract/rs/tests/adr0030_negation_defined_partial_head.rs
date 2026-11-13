//! ADR 0030, measured at the checker: a PARTIAL-marked table whose defining clause carries a
//! `\+` over a COMPLETE table of the same certificate is refused `cert_scope_incomplete` by
//! §3.2's scope gate — before the mark is ever consulted. D2 leaves that gate untouched, so
//! the D3 shape "seal the tripping QUERY stratum partial" (a recursive query stratum negating
//! a lower one) cannot pass `check()` as a single certificate today; the finding is reported
//! on #1652 rather than built around.
//!
//! Both branches of the gate close the door: a negated predicate sealed by this cert is an
//! intra-scope negation, and one NOT sealed by it is "neither sealed nor theory-owned".

use logos_contract::{
    check_with_cert_context, edb_table_hash, program_digest, CertContext, CertId, CertSizeDecl,
    CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness, CompleteProgram,
    Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier,
    MapProgram, Node, NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise, RelationTable,
    StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term, Theory,
    TheoryGround, Verdict,
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
    fn decide_ground(&self, _: &GroundLiteral) -> TheoryGround {
        TheoryGround::fails("no_theory")
    }
}

struct Leaves {
    extensional: PredicateSet,
    link: Vec<GroundLiteral>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for Leaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _: &()) -> Option<Hash> {
        if pred.bytes() == b"link" {
            Some(edb_table_hash(pred, &self.link))
        } else if self.extensional.contains(pred) {
            Some(edb_table_hash(pred, &[]))
        } else {
            None
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

/// `permit(X,Y) :- link(X,Y), \+ blocked(Y)` and its recursive twin — the re-scope's own
/// fixture shape (#1652): the query stratum negates a lower one and reads itself.
fn program() -> MapProgram {
    MapProgram::new()
        .with(
            "permit_base",
            Clause::with_neg(
                Goal::new("permit", [Term::var("X"), Term::var("Y")]),
                [Goal::new("link", [Term::var("X"), Term::var("Y")])],
                [Goal::new("blocked", [Term::var("Y")])],
            ),
        )
        .with(
            "permit_rec",
            Clause::with_neg(
                Goal::new("permit", [Term::var("X"), Term::var("Z")]),
                [
                    Goal::new("permit", [Term::var("X"), Term::var("Y")]),
                    Goal::new("link", [Term::var("Y"), Term::var("Z")]),
                ],
                [Goal::new("blocked", [Term::var("Y")])],
            ),
        )
}

fn profile() -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(["link", "blocked"]),
            link: vec![g("link", &["a", "b"])],
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn context(program: &dyn CompleteProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

/// The certificate D3 describes for a trip inside the query stratum: `blocked` and `link`
/// sealed complete, `permit` sealed PARTIAL with the one row derived before the trip and a
/// support edge citing the same cert (`link` present, `blocked(b)` absent).
fn cert(program: &dyn CompleteProgram, seal_blocked: bool) -> ClosedModelCert {
    let cx = context(program);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    subst.insert("Y".into(), Term::atom(b"b".to_vec()));
    let edge = SupportEdge {
        fact: g("permit", &["a", "b"]),
        clause: ClauseId::new("permit_base"),
        subst,
        body_refs: vec![
            SupportRef::LowerStratum {
                cert: CertId(0),
                atom: g("link", &["a", "b"]),
            },
            SupportRef::NegLower {
                cert: CertId(0),
                atom: g("blocked", &["b"]),
            },
        ],
        rank: 1,
    };
    let mut preds = vec![sym("link"), sym("permit")];
    let mut extensions = vec![
        RelationTable::new("link", 2, [g("link", &["a", "b"])]),
        RelationTable::new("permit", 2, [g("permit", &["a", "b"])]),
    ];
    if seal_blocked {
        preds.push(sym("blocked"));
        extensions.push(RelationTable::new("blocked", 1, []));
    }
    ClosedModelCert {
        scope: StratumPrefix::new(1, preds),
        program_hash: cx.program_hash,
        profile_hash: cx.profile_hash,
        ctx_hash: cx.ctx_hash,
        theory_config_hash: cx.theory_config_hash,
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("a"), v("b")])],
        extensions,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 2,
            support_edges: 1,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
        supports: SupportWitness(vec![edge]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: Some(StratumPrefix::new(1, [sym("permit")])),
    }
}

fn derivation(cert: ClosedModelCert) -> Derivation {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    subst.insert("Y".into(), Term::atom(b"b".to_vec()));
    Derivation::with_closed_world(
        vec![
            Node::Leaf {
                conclusion: g("link", &["a", "b"]),
                evidence: Evidence::none(),
            },
            Node::Rule {
                conclusion: g("permit", &["a", "b"]),
                clause: ClauseId::new("permit_base"),
                subst,
                premises: vec![
                    Premise::Pos { node: 0 },
                    Premise::Neg {
                        atom: g("blocked", &["b"]),
                        cert: CertId(0),
                        nonmember: NonMemberProof::DirectLookup,
                    },
                ],
                meta: NodeMeta::none(),
            },
        ],
        1,
        [cert],
    )
}

fn code(outcome: Outcome) -> String {
    match outcome.verdict {
        Verdict::Accept => "accept".into(),
        Verdict::Reject { code, .. } => code.code().to_string(),
    }
}

/// MEASURED: the scope gate refuses the negation-defined partial head in BOTH of its
/// branches, so the mark is never reached. This pins the boundary D3 must be built against.
#[test]
fn a_partial_head_defined_by_a_same_cert_negation_is_cert_scope_incomplete_today() {
    let program = program();
    let cx = context(&program);
    let claim = g("permit", &["a", "b"]);
    for seal_blocked in [true, false] {
        let deriv = derivation(cert(&program, seal_blocked));
        let out = check_with_cert_context(&program, &claim, &deriv, &(), &profile(), &cx);
        assert_eq!(
            code(out),
            "cert_scope_incomplete",
            "seal_blocked={seal_blocked}: a sealed clause carrying a negation is refused by \
             the scope gate whether or not the negated table is in the same scope"
        );
    }
}
