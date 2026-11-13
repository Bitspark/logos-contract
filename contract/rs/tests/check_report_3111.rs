//! #3111 (checker SPI v2, ADR 0036 D8 change 5): `check` returns `Outcome { verdict, report }`,
//! and the report counts the work the check did by the rules in the module doc of
//! `contract/rs/src/check/report.rs`. These tests pin those rules on tiny hand-built derivations.
//! Every expected count below is computed by hand from the rules, never read back from a run.

use logos_contract::{
    check, AlwaysAdmit, CertId, CheckLimits, CheckProfile, CheckReport, Clause, ClauseId,
    Derivation, Evidence, Goal, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node,
    NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise, RejectionCode, ReportCount, Subst,
    Symbol, Term, Theory, TheoryGround, Verdict, CHECK_REPORT_COUNTERS_VERSION,
};
use ontos_core::Value;
use std::collections::BTreeMap;

/// Owns `lt`: `lt(a, b)` holds iff both arguments are atoms and `a < b` bytewise.
struct LtTheory;
// test-double: consumer(a less-than theory over atoms)
impl Theory for LtTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"lt"
    }
    fn decide_ground(&self, atom: &GroundLiteral) -> TheoryGround {
        match atom.args.as_slice() {
            [a, b] => match (a.as_atom(), b.as_atom()) {
                (Some(a), Some(b)) if a.bytes() < b.bytes() => TheoryGround::holds(),
                _ => TheoryGround::fails("not_less_than"),
            },
            _ => TheoryGround::fails("lt_arity"),
        }
    }
}

/// `edge` is extensional, and every `edge` leaf is admitted.
struct EdgeLeaves(PredicateSet);
// test-double: consumer(admits every leaf of its extensional set)
impl LeafVerifier<()> for EdgeLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.0
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn profile(limits: CheckLimits) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(EdgeLeaves(PredicateSet::from_iter(["edge"]))),
        admit: Box::new(AlwaysAdmit),
        limits,
    }
}

/// `path(X, Y) :- edge(X, Y).` and `step(X, Y) :- edge(X, Y), lt(X, Y).`
fn program() -> MapProgram {
    let args = || [Term::var("X"), Term::var("Y")];
    MapProgram::new()
        .with(
            "path_edge",
            Clause::new(Goal::new("path", args()), [Goal::new("edge", args())]),
        )
        .with(
            "step",
            Clause::new(
                Goal::new("step", args()),
                [Goal::new("edge", args()), Goal::new("lt", args())],
            ),
        )
}

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

fn lit(pred: &str, x: &str, y: &str) -> GroundLiteral {
    GroundLiteral::new(pred, [atom(x), atom(y)])
}

/// `X = x, Y = y`.
fn xy(x: &str, y: &str) -> Subst {
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(x.as_bytes().to_vec()));
    subst.insert("Y".into(), Term::atom(y.as_bytes().to_vec()));
    subst
}

fn leaf(x: &str, y: &str) -> Node {
    Node::Leaf {
        conclusion: lit("edge", x, y),
        evidence: Evidence::none(),
    }
}

fn rule(pred: &str, clause: &str, x: &str, y: &str, premises: Vec<Premise>) -> Node {
    Node::Rule {
        conclusion: lit(pred, x, y),
        clause: ClauseId::new(clause),
        subst: xy(x, y),
        premises,
        meta: NodeMeta::none(),
    }
}

fn run(claim: &GroundLiteral, deriv: &Derivation, limits: CheckLimits) -> Outcome {
    check(&program(), claim, deriv, &(), &profile(limits))
}

fn counted(n: u64) -> ReportCount {
    ReportCount::Counted(n)
}

/// The rejection's code, `None` on an accept.
fn code(outcome: &Outcome) -> Option<RejectionCode> {
    match &outcome.verdict {
        Verdict::Accept => None,
        Verdict::Reject { code, .. } => Some(*code),
    }
}

/// `path(a, b)` from one `edge(a, b)` leaf: two nodes.
fn small() -> (GroundLiteral, Derivation) {
    let deriv = Derivation::new(
        vec![
            leaf("a", "b"),
            rule("path", "path_edge", "a", "b", vec![Premise::pos(0)]),
        ],
        1,
    );
    (lit("path", "a", "b"), deriv)
}

/// `step(a, b)` from an `edge(a, b)` leaf and an `lt(a, b)` builtin: three nodes.
fn larger() -> (GroundLiteral, Derivation) {
    let premises = vec![Premise::pos(0), Premise::pos(1)];
    let deriv = Derivation::new(
        vec![
            leaf("a", "b"),
            Node::Builtin {
                conclusion: lit("lt", "a", "b"),
            },
            rule("step", "step", "a", "b", premises),
        ],
        2,
    );
    (lit("step", "a", "b"), deriv)
}

/// `step(a, b)` whose second premise cites `lt(a, c)`, which holds but is not the grounded body
/// literal `lt(a, b)`: the rule node rejects at premise 1.
fn wrong_second_premise() -> (GroundLiteral, Derivation) {
    let premises = vec![Premise::pos(0), Premise::pos(1)];
    let deriv = Derivation::new(
        vec![
            leaf("a", "b"),
            Node::Builtin {
                conclusion: lit("lt", "a", "c"),
            },
            rule("step", "step", "a", "b", premises),
        ],
        2,
    );
    (lit("step", "a", "b"), deriv)
}

/// `step(b, a)` over an `lt(b, a)` builtin the theory decides false: the builtin node rejects
/// before the rule node is walked.
fn failing_builtin() -> (GroundLiteral, Derivation) {
    let premises = vec![Premise::pos(0), Premise::pos(1)];
    let deriv = Derivation::new(
        vec![
            leaf("b", "a"),
            Node::Builtin {
                conclusion: lit("lt", "b", "a"),
            },
            rule("step", "step", "b", "a", premises),
        ],
        2,
    );
    (lit("step", "b", "a"), deriv)
}

/// `path(a, b)` whose one premise is NEGATIVE against the clause's positive body literal: counted
/// as a negative premise, then refused on its polarity.
fn negative_against_positive() -> (GroundLiteral, Derivation) {
    let neg = Premise::Neg {
        atom: lit("edge", "a", "b"),
        cert: CertId(0),
        nonmember: NonMemberProof::DirectLookup,
    };
    let deriv = Derivation::new(vec![rule("path", "path_edge", "a", "b", vec![neg])], 0);
    (lit("path", "a", "b"), deriv)
}

#[test]
fn outcome_equality_is_the_verdicts() {
    let (small_claim, small_deriv) = small();
    let (larger_claim, larger_deriv) = larger();
    let a = run(&small_claim, &small_deriv, CheckLimits::default());
    let b = run(&larger_claim, &larger_deriv, CheckLimits::default());
    assert_eq!(a.verdict, Verdict::Accept);
    assert_eq!(b.verdict, Verdict::Accept);
    // Two different-sized derivations, two different reports, one verdict: equal outcomes.
    assert_ne!(a.report, b.report, "two sizes, two reports");
    assert_eq!(a, b, "an outcome's equality is its verdict's");
    // And the converse: equal work, different verdicts, unequal outcomes.
    let (wrong_claim, wrong_deriv) = wrong_second_premise();
    let rejected = run(&wrong_claim, &wrong_deriv, CheckLimits::default());
    assert_ne!(rejected, b);
}

#[test]
fn node_kinds_sum() {
    let cases = [
        ("small", small()),
        ("larger", larger()),
        ("wrong second premise", wrong_second_premise()),
        ("failing builtin", failing_builtin()),
        ("negative against positive", negative_against_positive()),
    ];
    for (name, (claim, deriv)) in cases {
        let outcome = run(&claim, &deriv, CheckLimits::default());
        assert!(
            outcome.report.node_kinds_sum(),
            "{name}: the node kinds must sum to nodes_walked, got {:?}",
            outcome.report
        );
    }
    // The control: a report whose kinds do not sum fails the check.
    let broken = CheckReport {
        nodes_walked: counted(2),
        leaf_nodes: counted(1),
        ..CheckReport::zero()
    };
    assert!(!broken.node_kinds_sum());
}

#[test]
fn a_rejection_reports_the_work_up_to_the_rejecting_node() {
    // Node 0, the leaf: walked, depth 1, one leaf verification. Node 1, the builtin: walked,
    // depth 1, one theory decision (it holds). Node 2, the rule: walked, depth 2; step (f) counts
    // premise 0 (it matches), then premise 1, which rejects. No admissibility call is reached.
    let (claim, deriv) = wrong_second_premise();
    let outcome = run(&claim, &deriv, CheckLimits::default());
    assert_eq!(code(&outcome), Some(RejectionCode::InstantiationMismatch));
    let r = &outcome.report;
    assert_eq!(r.nodes_walked, counted(3));
    assert_eq!(r.rule_nodes, counted(1));
    assert_eq!(r.builtin_nodes, counted(1));
    assert_eq!(r.leaf_nodes, counted(1));
    assert_eq!(r.premises_pos, counted(2));
    assert_eq!(r.premises_neg, counted(0));
    assert_eq!(r.theory_decisions, counted(1));
    assert_eq!(r.leaf_verifications, counted(1));
    assert_eq!(r.admissibility_checks, counted(0));
    assert_eq!(r.max_depth_reached, counted(2));

    // The builtin decided false: nodes 0 and 1 are walked, node 2 never is.
    let (claim, deriv) = failing_builtin();
    let outcome = run(&claim, &deriv, CheckLimits::default());
    assert_eq!(code(&outcome), Some(RejectionCode::BuiltinFailed));
    let expected = CheckReport {
        nodes_walked: counted(2),
        builtin_nodes: counted(1),
        leaf_nodes: counted(1),
        theory_decisions: counted(1),
        leaf_verifications: counted(1),
        max_depth_reached: counted(1),
        max_term_depth_reached: counted(1),
        ..CheckReport::zero()
    };
    assert_eq!(outcome.report, expected);

    // A negative premise is counted as negative before its polarity is checked.
    let (claim, deriv) = negative_against_positive();
    let outcome = run(&claim, &deriv, CheckLimits::default());
    assert_eq!(code(&outcome), Some(RejectionCode::InstantiationMismatch));
    let expected = CheckReport {
        nodes_walked: counted(1),
        rule_nodes: counted(1),
        premises_neg: counted(1),
        max_depth_reached: counted(1),
        max_term_depth_reached: counted(1),
        ..CheckReport::zero()
    };
    assert_eq!(outcome.report, expected);
}

#[test]
#[cfg(target_pointer_width = "64")]
fn a_limits_refusal_reports_zeros() {
    let (claim, deriv) = small();
    // A budget past the protocol index domain (a 64-bit `usize::MAX` is): the configuration is
    // refused before any node is read.
    let limits = CheckLimits {
        max_nodes: usize::MAX,
        ..CheckLimits::default()
    };
    let outcome = run(&claim, &deriv, limits);
    assert_eq!(code(&outcome), Some(RejectionCode::InvalidCheckLimits));
    assert_eq!(outcome.report, CheckReport::zero());
}

#[test]
fn the_other_refusals_before_the_walk_report_what_they_did() {
    // The node cap reads no node: zeros.
    let (claim, deriv) = small();
    let limits = CheckLimits {
        max_nodes: 1,
        ..CheckLimits::default()
    };
    let outcome = run(&claim, &deriv, limits);
    assert_eq!(code(&outcome), Some(RejectionCode::TooManyNodes));
    assert_eq!(outcome.report, CheckReport::zero());

    // The term-depth cap measured the claim's first argument, `t(a)` (depth 2), against a cap of
    // 1, and stopped there: zeros, except the depth it measured.
    let deep = Value::tuple([atom("t"), atom("a")]);
    let claim = GroundLiteral::new("path", [deep, atom("b")]);
    let limits = CheckLimits {
        max_term_depth: 1,
        ..CheckLimits::default()
    };
    let outcome = run(&claim, &deriv, limits);
    assert_eq!(code(&outcome), Some(RejectionCode::TermTooDeep));
    let expected = CheckReport {
        max_term_depth_reached: counted(2),
        ..CheckReport::zero()
    };
    assert_eq!(outcome.report, expected);
}

#[test]
fn an_accepted_check_reports_its_exact_work() {
    // Node 0, the leaf: depth 1, one leaf verification. Node 1, the builtin: depth 1, one theory
    // decision. Node 2, the rule: depth 2, two positive premises, one admissibility call. Every
    // term is an atom, so the deepest term is 1. No certificate is cited.
    let (claim, deriv) = larger();
    let outcome = run(&claim, &deriv, CheckLimits::default());
    assert_eq!(outcome.verdict, Verdict::Accept);
    let expected = CheckReport {
        counters_version: CHECK_REPORT_COUNTERS_VERSION,
        nodes_walked: counted(3),
        rule_nodes: counted(1),
        builtin_nodes: counted(1),
        leaf_nodes: counted(1),
        premises_pos: counted(2),
        premises_neg: counted(0),
        theory_decisions: counted(1),
        leaf_verifications: counted(1),
        admissibility_checks: counted(1),
        certs_verified: counted(0),
        certs_memo_hits: counted(0),
        cert_tables_read: counted(0),
        cert_rows_read: counted(0),
        join_steps_used: counted(0),
        groundings_enumerated: counted(0),
        max_depth_reached: counted(2),
        max_term_depth_reached: counted(1),
    };
    assert_eq!(outcome.report, expected);

    // The smaller derivation: one leaf and one rule over it.
    let (claim, deriv) = small();
    let outcome = run(&claim, &deriv, CheckLimits::default());
    assert_eq!(outcome.verdict, Verdict::Accept);
    let expected = CheckReport {
        nodes_walked: counted(2),
        rule_nodes: counted(1),
        leaf_nodes: counted(1),
        premises_pos: counted(1),
        leaf_verifications: counted(1),
        admissibility_checks: counted(1),
        max_depth_reached: counted(2),
        max_term_depth_reached: counted(1),
        ..CheckReport::zero()
    };
    assert_eq!(outcome.report, expected);
}
