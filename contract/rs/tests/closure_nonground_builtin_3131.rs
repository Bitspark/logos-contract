//! #3131 done-when 4: the checker side of "an unbound variable in an arithmetic builtin". The
//! closure decides a theory-owned literal through `theory_truth`, and `theory_truth` only ever
//! sees a GROUND literal: a builtin literal whose variable no positive sealed literal binds is
//! refused by the closure's own safety gate (`cert_scope_incomplete`), before any theory is
//! asked. So the checker already refuses the non-ground case; this pins it for `>` over the
//! standard arithmetic theory, beside the ground controls that it still decides.
//!
//! The program: `p :- <left> > 1.  q :- \+ p.`, with a certificate sealing `p` as EMPTY and a
//! derivation of `q` that discharges `\+ p` against it.

use logos_contract::intval::BigInt;
use logos_contract::{
    check_with_cert_context, program_digest, AlwaysAdmit, ArithmeticTheory, CertContext, CertId,
    CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness,
    Derivation, Evidence, Goal, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node,
    NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise, RejectionCode, RelationTable,
    StratumPrefix, Subst, SupportWitness, Symbol, Term,
};

struct NoLeaves(PredicateSet);
// test-double: consumer(a program with no extensional predicate)
impl LeafVerifier<()> for NoLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.0
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn int(i: i128) -> Term {
    BigInt::from_i128(i).to_int_term()
}
fn goal0(pred: &str) -> Goal {
    Goal::new(pred, [] as [Term; 0])
}
fn ground0(pred: &str) -> GroundLiteral {
    goal0(pred).as_ground().expect("a 0-ary atom is ground")
}

/// Check `q` over `p :- <left> > 1.  q :- \+ p.` with `p` sealed empty.
fn check_q(left: Term) -> Outcome {
    let program = MapProgram::new()
        .with(
            "p_rule",
            Clause::new(goal0("p"), [Goal::new(">", [left, int(1)])]),
        )
        .with(
            "q_rule",
            Clause::with_neg(goal0("q"), [] as [Goal; 0], [goal0("p")]),
        );
    let cx = CertContext::new(program_digest(&program), [1u8; 32], [2u8; 32], [3u8; 32]);
    let cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [Symbol::new(b"p".to_vec())]),
        program_hash: cx.program_hash,
        profile_hash: cx.profile_hash,
        ctx_hash: cx.ctx_hash,
        theory_config_hash: cx.theory_config_hash,
        edb_snapshot_hashes: vec![],
        domains: vec![],
        extensions: vec![RelationTable::new("p", 0, [] as [GroundLiteral; 0])],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 0,
            domain_values: 0,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    let derivation = Derivation::with_closed_world(
        vec![Node::Rule {
            conclusion: ground0("q"),
            clause: ClauseId::new("q_rule"),
            subst: Subst::new(),
            premises: vec![Premise::Neg {
                atom: ground0("p"),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let profile = CheckProfile {
        theory: Box::new(ArithmeticTheory::new()),
        leaves: Box::new(NoLeaves(PredicateSet::new())),
        admit: Box::new(AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    check_with_cert_context(&program, &ground0("q"), &derivation, &(), &profile, &cx)
}

/// The rejection's typed code, `None` on an accept. Asserted by the code, never by its prose.
fn code(outcome: &Outcome) -> Option<RejectionCode> {
    match outcome {
        Outcome::Accept => None,
        Outcome::Reject { code, .. } => Some(*code),
    }
}

/// `p :- X > 1.`: the closure never reads `X > 1` as false (which would let an empty `p` pass and
/// `\+ p` be certified). It refuses the clause as an unsafe existential.
#[test]
fn a_nonground_comparison_in_a_sealed_clause_is_refused() {
    let outcome = check_q(Term::var("X"));
    assert_eq!(
        code(&outcome),
        Some(RejectionCode::CertScopeIncomplete),
        "{outcome:?}"
    );
}

/// The controls: a ground `0 > 1` is decided false, so the empty `p` is closed and `q` is
/// certified; a ground `2 > 1` is decided true, so the empty `p` is not closed.
#[test]
fn a_ground_comparison_is_decided_by_the_closure() {
    let false_left = check_q(int(0));
    assert_eq!(code(&false_left), None, "{false_left:?}");
    let true_left = check_q(int(2));
    assert_eq!(
        code(&true_left),
        Some(RejectionCode::CertNotClosed),
        "{true_left:?}"
    );
}
