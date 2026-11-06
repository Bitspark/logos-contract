//! Language-local tests for the Rust binding's **host-extension band** and the two
//! rule-head **sealing/partition** branches — the parts NOT pinned by the shared,
//! cross-language oracle.
//!
//! The shared `check.json`/`account.json` vectors are no longer replayed here: that is
//! the **differential CLI harness** (`conformance/`, ADR 0006), which drives the
//! per-language `check` CLIs as black boxes over the one oracle. This file keeps only
//! what is language-local — the host band (`builtin_failed` / `leaf_rejected` /
//! `rule_inadmissible`) and the rule-head branches.

use logos_contract::{
    check, CheckLimits, CheckProfile, Clause, ClauseId, Derivation, Evidence, Goal, GroundLiteral,
    LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, Outcome, PredicateSet, Premise,
    RuleAdmissibility, RuleOutcome, Subst, Symbol, Term, Theory, TheoryOutcome,
    MAX_TERM_DEPTH_DEFAULT,
};
use std::collections::BTreeMap;

// =================== the `demo_v1` profile (shared by name) ===================
// Implemented identically in each language binding; the JSON pins program +
// derivation + claim + outcome. Context is unit.

/// Theory owning `lt`: `lt(a, b)` Holds iff both args are atoms and `a < b`
/// bytewise. Pure, total, config-free.
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
    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome {
        match atom.args.as_slice() {
            [a, b] => match (a.as_atom(), b.as_atom()) {
                (Some(a), Some(b)) if a.bytes() < b.bytes() => TheoryOutcome::Holds,
                _ => TheoryOutcome::Fails {
                    code: "not_less_than".into(),
                },
            },
            _ => TheoryOutcome::Fails {
                code: "lt_arity".into(),
            },
        }
    }
}

/// LeafVerifier with `edge` extensional; admits any `edge` leaf (trusted facts).
struct EdgeLeaves {
    extensional: PredicateSet,
}
impl EdgeLeaves {
    fn new() -> Self {
        EdgeLeaves {
            extensional: PredicateSet::from_iter(["edge"]),
        }
    }
}
// test-double: consumer(admits every leaf of its extensional set)
impl LeafVerifier<()> for EdgeLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn demo_profile(limits: CheckLimits) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(EdgeLeaves::new()),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    }
}

// ===== language-local host-extension band tests (NOT in the shared vectors) =====
// The host band's sub-codes are an open set pinned only in a consumer's own suite;
// here we verify the three wrapper codes + that the seam's sub-code reaches detail.

fn lt(a: &str, b: &str) -> GroundLiteral {
    GroundLiteral::new("lt", [ontos_value(a), ontos_value(b)])
}
fn ontos_value(s: &str) -> ontos_core::Value {
    ontos_core::Value::atom(s.as_bytes().to_vec())
}

#[test]
fn host_band_builtin_failed() {
    // lt(b, a): b > a, so the theory Fails -> builtin_failed, sub-code in detail.
    let deriv = Derivation::new(
        [Node::Builtin {
            conclusion: lt("b", "a"),
        }],
        0,
    );
    let profile = demo_profile(CheckLimits::default());
    match check(&MapProgram::new(), &lt("b", "a"), &deriv, &(), &profile) {
        Outcome::Reject { code, detail } => {
            assert_eq!(code.code(), "builtin_failed");
            assert_eq!(detail, "not_less_than");
            assert!(!code.is_structural());
        }
        other => panic!("expected builtin_failed, got {other:?}"),
    }
}

#[test]
fn host_band_leaf_rejected() {
    // A LeafVerifier that always rejects with a custom sub-code.
    struct RejectingLeaves(PredicateSet);
    // test-double: adversarial(rejects every leaf with a custom sub-code)
    impl LeafVerifier<()> for RejectingLeaves {
        fn extensional(&self) -> &PredicateSet {
            &self.0
        }
        fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
            LeafOutcome::Reject {
                code: "no_attestation".into(),
            }
        }
    }
    let edge = GroundLiteral::new("edge", [ontos_value("a"), ontos_value("b")]);
    let deriv = Derivation::new(
        [Node::Leaf {
            conclusion: edge.clone(),
            evidence: Evidence::default(),
        }],
        0,
    );
    let profile = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(RejectingLeaves(PredicateSet::from_iter(["edge"]))),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    match check(&MapProgram::new(), &edge, &deriv, &(), &profile) {
        Outcome::Reject { code, detail } => {
            assert_eq!(code.code(), "leaf_rejected");
            assert_eq!(detail, "no_attestation");
        }
        other => panic!("expected leaf_rejected, got {other:?}"),
    }
}

#[test]
fn host_band_rule_inadmissible() {
    // A RuleAdmissibility that always rejects; the rule is otherwise valid.
    struct DenyAdmit;
    // test-double: adversarial(rejects every otherwise-valid rule)
    impl RuleAdmissibility<()> for DenyAdmit {
        fn admissible(&self, _: &Clause, _: &NodeMeta, _: &()) -> RuleOutcome {
            RuleOutcome::Reject {
                code: "placement_mismatch".into(),
            }
        }
    }
    // program: greet(X) :- edge(X, X).  (intensional head greet, extensional body edge)
    let program = MapProgram::new().with(
        "greet_rule",
        Clause::new(
            Goal::new("greet", [Term::var("X")]),
            [Goal::new("edge", [Term::var("X"), Term::var("X")])],
        ),
    );
    let edge_aa = GroundLiteral::new("edge", [ontos_value("a"), ontos_value("a")]);
    let greet_a = GroundLiteral::new("greet", [ontos_value("a")]);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: edge_aa,
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: greet_a.clone(),
                clause: ClauseId::new("greet_rule"),
                subst,
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    let profile = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(EdgeLeaves::new()),
        admit: Box::new(DenyAdmit),
        limits: CheckLimits::default(),
    };
    match check(&program, &greet_a, &deriv, &(), &profile) {
        Outcome::Reject { code, detail } => {
            assert_eq!(code.code(), "rule_inadmissible");
            assert_eq!(detail, "placement_mismatch");
        }
        other => panic!("expected rule_inadmissible, got {other:?}"),
    }
}

// ===== sealing/partition branches on a Rule head (rs-local; shared program is clean) =====

#[test]
fn rule_head_collides_with_extensional_is_sealed() {
    // edge_sym: edge(X,Y) :- edge(Y,X). `edge` is extensional, so a rule concluding
    // it is the §4.2 "rule head collides with an extensional predicate" error.
    let program = MapProgram::new().with(
        "edge_sym",
        Clause::new(
            Goal::new("edge", [Term::var("X"), Term::var("Y")]),
            [Goal::new("edge", [Term::var("Y"), Term::var("X")])],
        ),
    );
    let edge_ba = GroundLiteral::new("edge", [ontos_value("b"), ontos_value("a")]);
    let edge_ab = GroundLiteral::new("edge", [ontos_value("a"), ontos_value("b")]);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    subst.insert("Y".into(), Term::atom(b"b".to_vec()));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: edge_ba,
                evidence: Evidence::none(),
            },
            Node::Rule {
                conclusion: edge_ab.clone(),
                clause: ClauseId::new("edge_sym"),
                subst,
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::none(),
            },
        ],
        1,
    );
    let profile = demo_profile(CheckLimits::default());
    match check(&program, &edge_ab, &deriv, &(), &profile) {
        Outcome::Reject { code, .. } => assert_eq!(code.code(), "sealed_violation"),
        other => panic!("expected sealed_violation, got {other:?}"),
    }
}

#[test]
fn rule_head_owned_by_theory_is_partition_violation() {
    // lt_rule: lt(X,Y) :- edge(X,Y). `lt` is theory-owned, so a rule concluding it
    // is a §4.4 predicate-partition violation.
    let program = MapProgram::new().with(
        "lt_rule",
        Clause::new(
            Goal::new("lt", [Term::var("X"), Term::var("Y")]),
            [Goal::new("edge", [Term::var("X"), Term::var("Y")])],
        ),
    );
    let edge_ab = GroundLiteral::new("edge", [ontos_value("a"), ontos_value("b")]);
    let lt_ab = GroundLiteral::new("lt", [ontos_value("a"), ontos_value("b")]);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    subst.insert("Y".into(), Term::atom(b"b".to_vec()));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: edge_ab,
                evidence: Evidence::none(),
            },
            Node::Rule {
                conclusion: lt_ab.clone(),
                clause: ClauseId::new("lt_rule"),
                subst,
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::none(),
            },
        ],
        1,
    );
    let profile = demo_profile(CheckLimits::default());
    match check(&program, &lt_ab, &deriv, &(), &profile) {
        Outcome::Reject { code, .. } => assert_eq!(code.code(), "predicate_partition_violation"),
        other => panic!("expected predicate_partition_violation, got {other:?}"),
    }
}

// ============ issue #253: term-nesting depth bound (DoS hardening) ============
// A deeply-NESTED single TERM in the trusted check/decode path must be REJECTED
// gracefully (`term_too_deep`), never overflow the OS stack and abort the process.
// These tests actually exercise a depth FAR past the empirical ~670-level debug
// overflow boundary, proving the iterative guard refuses it without crashing.

/// Build a ground `ontos::Value` nested `depth` levels deep **iteratively** (so the
/// fixture itself never recurses / overflows): `f(f(…f(a)…))`.
fn deep_value(depth: usize) -> ontos_core::Value {
    let mut v = ontos_core::Value::atom(*b"a");
    for _ in 0..depth {
        v = ontos_core::Value::tuple([ontos_core::Value::atom(*b"f"), v]);
    }
    v
}

/// Leak a fixture instead of dropping it. A depth-50_000 `Value`/`Derivation` cannot
/// be dropped normally — the derived `Drop` for `ontos::Value` is RECURSIVE and would
/// overflow the stack on cleanup (the same DoS class, on the test's teardown path).
/// `check` only BORROWS the derivation, so leaking after the assertion is sound and
/// keeps the test honest (the pathological value was really constructed + checked).
fn leak<T>(t: T) {
    std::mem::forget(t);
}

/// A single `edge` leaf concluding `edge(<arg>, b)` — `edge` is extensional in the
/// demo profile, so a one-node derivation reaches the depth guard before any leaf
/// delegation. The claim mirrors the conclusion (so a within-bound term is accepted).
///
/// We build the conclusion value TWICE from a builder closure rather than `.clone()`
/// the deep value — `ontos::Value`'s derived `Clone` is recursive and would overflow
/// on a pathological depth. The closure constructs each copy iteratively.
fn edge_leaf_deriv(build_arg: impl Fn() -> ontos_core::Value) -> (GroundLiteral, Derivation) {
    let claim = GroundLiteral::new("edge", [build_arg(), ontos_core::Value::atom(*b"b")]);
    let conclusion = GroundLiteral::new("edge", [build_arg(), ontos_core::Value::atom(*b"b")]);
    let deriv = Derivation::new(
        [Node::Leaf {
            conclusion,
            evidence: Evidence::none(),
        }],
        0,
    );
    (claim, deriv)
}

#[test]
fn over_deep_term_is_rejected_term_too_deep_not_a_crash() {
    // 50_000 levels — ~75× past the ~670-level debug stack-overflow boundary. A
    // recursive check would abort the process here; the iterative guard rejects it.
    let (claim, deriv) = edge_leaf_deriv(|| deep_value(50_000));
    let profile = demo_profile(CheckLimits::default());
    let outcome = check(&MapProgram::new(), &claim, &deriv, &(), &profile);
    // Leak BEFORE matching is unnecessary (check only borrows); leak after so the
    // recursive Drop of the depth-50_000 fixture never runs.
    match &outcome {
        Outcome::Reject { code, .. } => {
            assert_eq!(code.code(), "term_too_deep");
            assert!(
                code.is_structural(),
                "term_too_deep is a structural-band code"
            );
        }
        other => panic!("expected term_too_deep, got {other:?}"),
    }
    leak(deriv);
    leak(claim);
}

#[test]
fn within_bound_term_is_still_accepted() {
    // A term ONE LEVEL under the bound is accepted — the guard refuses only the
    // pathological case and never weakens the accept path.
    let (claim, deriv) = edge_leaf_deriv(|| deep_value(MAX_TERM_DEPTH_DEFAULT - 2));
    let profile = demo_profile(CheckLimits::default());
    assert!(
        check(&MapProgram::new(), &claim, &deriv, &(), &profile).is_accept(),
        "a within-bound term must still be accepted"
    );
}

#[test]
fn term_depth_bound_is_exact_at_the_boundary() {
    // edge(arg, b) is depth `value_depth(arg) + 1` at the literal level? No — the
    // GUARD measures each ARGUMENT independently (arg's own nesting), so a value of
    // structural depth == max_term_depth is the last accepted, and +1 is rejected.
    let profile = demo_profile(CheckLimits::default());

    // value depth = MAX (deep_value(n) has structural depth n+1: n tuples + 1 atom).
    // These boundary depths (~256) are safely droppable, so no leak needed.
    let (claim, deriv) = edge_leaf_deriv(|| deep_value(MAX_TERM_DEPTH_DEFAULT - 1));
    assert!(
        check(&MapProgram::new(), &claim, &deriv, &(), &profile).is_accept(),
        "a term at exactly max_term_depth must be accepted"
    );

    // value depth = MAX + 1 → rejected.
    let (claim, deriv) = edge_leaf_deriv(|| deep_value(MAX_TERM_DEPTH_DEFAULT));
    match check(&MapProgram::new(), &claim, &deriv, &(), &profile) {
        Outcome::Reject { code, .. } => assert_eq!(code.code(), "term_too_deep"),
        other => panic!("expected term_too_deep at boundary+1, got {other:?}"),
    }
}

#[test]
fn over_deep_subst_image_in_a_rule_is_rejected() {
    // The depth guard also covers a Rule node's subst image terms — a deep term
    // smuggled through the substitution, not just a node conclusion. greet(X) :-
    // edge(X, X); the conclusion is shallow but the subst binds X to a deep term.
    let program = MapProgram::new().with(
        "greet_rule",
        Clause::new(
            Goal::new("greet", [Term::var("X")]),
            [Goal::new("edge", [Term::var("X"), Term::var("X")])],
        ),
    );
    // Build a deep TERM iteratively for the subst image. The source value is leaked
    // (its recursive Drop would overflow); the Term goes into the leaked derivation.
    let deep_value_src = deep_value(50_000);
    let deep_term = Term::from_value(&deep_value_src);
    leak(deep_value_src);
    let edge_leaf = GroundLiteral::new(
        "edge",
        [
            ontos_core::Value::atom(*b"a"),
            ontos_core::Value::atom(*b"a"),
        ],
    );
    let greet = GroundLiteral::new("greet", [ontos_core::Value::atom(*b"a")]);
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), deep_term);
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: edge_leaf,
                evidence: Evidence::none(),
            },
            Node::Rule {
                conclusion: greet.clone(),
                clause: ClauseId::new("greet_rule"),
                subst,
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::none(),
            },
        ],
        1,
    );
    let profile = demo_profile(CheckLimits::default());
    let outcome = check(&program, &greet, &deriv, &(), &profile);
    match &outcome {
        Outcome::Reject { code, .. } => assert_eq!(code.code(), "term_too_deep"),
        other => panic!("expected term_too_deep for a deep subst image, got {other:?}"),
    }
    leak(deriv); // the deep subst image term is inside; leak to avoid recursive Drop.
}
