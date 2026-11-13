//! #3424 (research 0035 lane 8, row B17): a STACKED world reads its certificates' scope levels
//! (#2344). The checker verifies certificates in ascending level, whatever their index in
//! `closed_world`, and a certificate reads a predicate only from a strictly lower seal. So a wrong
//! level changes the verdict, where a single full-scope certificate's does not
//! (`scope_level_is_inert_for_a_single_full_scope_certificate_1567` in negation.rs).
//!
//! The world is `vectors/negation.json`'s `stacked_2258_*` shape, built here through the full
//! `check_with_cert_context`:
//!   stk_low(X) :- stk_item(X), \+ stk_flag(X).      sealed by the upper certificate
//!   stk_top(X) :- stk_item(X), \+ stk_low(X).       the claim, stk_top(a), negates stk_low(a)
//! over EDB stk_item(a), stk_item(b), stk_flag(a): the base certificate seals the EDB, and the
//! upper one reads stk_item and \+ stk_flag from it. The go and ts counterparts replay the vector
//! cases with changed levels (contract/go/scope_level_consulted_3424_test.go,
//! contract/ts/test/negation_vectors.test.ts).
//!
//! §7.7: a checker that orders by index alone (`verification_order` without the level) verifies the
//! upper certificate first, before the base it reads, and refuses the upper-first world;
//! `stacked_certificates_are_verified_in_level_order_whatever_their_index_3424` reds on it.

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
        TheoryGround::fails("not_mine")
    }
}

/// The EDB of record: stk_item(a), stk_item(b), stk_flag(a), each attested by its snapshot.
struct StackLeaves {
    extensional: PredicateSet,
}
// test-double: consumer(admits every leaf of its extensional set and attests the EDB snapshot)
impl LeafVerifier<()> for StackLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _: &()) -> Option<Hash> {
        match pred.bytes() {
            b"stk_item" => Some(edb_table_hash(
                pred,
                &[g("stk_item", "a"), g("stk_item", "b")],
            )),
            b"stk_flag" => Some(edb_table_hash(pred, &[g("stk_flag", "a")])),
            _ => None,
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
    MapProgram::new()
        .with(
            "stk_low_rule",
            Clause::with_neg(
                Goal::new("stk_low", [Term::var("X")]),
                [Goal::new("stk_item", [Term::var("X")])],
                [Goal::new("stk_flag", [Term::var("X")])],
            ),
        )
        .with(
            "stk_top_rule",
            Clause::with_neg(
                Goal::new("stk_top", [Term::var("X")]),
                [Goal::new("stk_item", [Term::var("X")])],
                [Goal::new("stk_low", [Term::var("X")])],
            ),
        )
}

fn profile() -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(StackLeaves {
            extensional: PredicateSet::from_iter(["stk_flag", "stk_item"]),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn bound_context(program: &dyn CompleteProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

/// A certificate bound to the program's context, its size declaration matching what it carries.
fn cert(
    level: u32,
    preds: &[&str],
    tables: Vec<RelationTable>,
    supports: Vec<SupportEdge>,
) -> ClosedModelCert {
    let facts: usize = tables.iter().map(|t| t.rows.len()).sum();
    let edges = supports.len();
    let cx = bound_context(&program());
    ClosedModelCert {
        scope: StratumPrefix::new(level, preds.iter().map(|p| sym(p))),
        program_hash: cx.program_hash,
        profile_hash: cx.profile_hash,
        ctx_hash: cx.ctx_hash,
        theory_config_hash: cx.theory_config_hash,
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

/// The two-certificate world at the given levels, the base listed first or second. Returns the
/// world and the upper certificate's index.
fn world(base_first: bool, base_level: u32, upper_level: u32) -> (Vec<ClosedModelCert>, usize) {
    let (base_ix, upper_ix) = if base_first { (0, 1) } else { (1, 0) };
    let base = cert(
        base_level,
        &["stk_flag", "stk_item"],
        vec![
            RelationTable::new("stk_flag", 1, [g("stk_flag", "a")]),
            RelationTable::new("stk_item", 1, [g("stk_item", "a"), g("stk_item", "b")]),
        ],
        vec![],
    );
    let upper = cert(
        upper_level,
        &["stk_low"],
        vec![RelationTable::new("stk_low", 1, [g("stk_low", "b")])],
        vec![SupportEdge {
            fact: g("stk_low", "b"),
            clause: ClauseId::new("stk_low_rule"),
            subst: x_is("b"),
            body_refs: vec![
                SupportRef::LowerStratum {
                    cert: CertId(base_ix as u64),
                    atom: g("stk_item", "b"),
                },
                SupportRef::NegLower {
                    cert: CertId(base_ix as u64),
                    atom: g("stk_flag", "b"),
                },
            ],
            rank: 1,
        }],
    );
    let certs = if base_first {
        vec![base, upper]
    } else {
        vec![upper, base]
    };
    (certs, upper_ix)
}

/// Check the claim stk_top(a) :- stk_item(a), \+ stk_low(a), the negation citing the upper cert.
fn run(base_first: bool, base_level: u32, upper_level: u32) -> Outcome {
    let (certs, upper_ix) = world(base_first, base_level, upper_level);
    let nodes = vec![
        Node::Leaf {
            conclusion: g("stk_item", "a"),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("stk_top", "a"),
            clause: ClauseId::new("stk_top_rule"),
            subst: x_is("a"),
            premises: vec![
                Premise::pos(0),
                Premise::Neg {
                    atom: g("stk_low", "a"),
                    cert: CertId(upper_ix as u64),
                    nonmember: NonMemberProof::DirectLookup,
                },
            ],
            meta: NodeMeta::none(),
        },
    ];
    let program = program();
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &g("stk_top", "a"),
        &Derivation::with_closed_world(nodes, 1, certs),
        &(),
        &profile(),
        &cx,
    )
}

fn code_of(outcome: Outcome) -> String {
    match outcome.verdict {
        Verdict::Accept => "accept".to_string(),
        Verdict::Reject { code, detail } => format!("{} ({detail})", code.code()),
    }
}

/// The base at level 1 and the upper certificate at level 2 accept in either order: the upper one
/// is verified after the base it reads because the checker orders by LEVEL, not by index.
#[test]
fn stacked_certificates_are_verified_in_level_order_whatever_their_index_3424() {
    assert_eq!(
        code_of(run(true, 1, 2)),
        "accept",
        "control: the base listed first"
    );
    assert_eq!(
        code_of(run(false, 1, 2)),
        "accept",
        "the upper certificate listed first must still be verified after the base"
    );
}

/// A wrong level changes the verdict: with the base at the upper's level, or above it, the upper
/// certificate has no strictly lower seal for stk_item and stk_flag, and its scope is incomplete.
#[test]
fn a_wrong_level_in_a_stacked_world_changes_the_verdict_3424() {
    for (base_level, upper_level) in [(1u32, 1u32), (3, 2)] {
        for base_first in [true, false] {
            let got = code_of(run(base_first, base_level, upper_level));
            assert!(
                got.starts_with("cert_scope_incomplete"),
                "base at level {base_level}, upper at {upper_level} (base first: {base_first}): got {got}"
            );
        }
    }
}
