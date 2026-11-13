//! §4 core obligation 6 — **no reachability requirement** (frozen; downstream-load-bearing).
//!
//! `check` verifies obligations 1–5 — each node locally valid, the root concluding the
//! claim — and **nothing about node connectivity beyond the per-`Rule` premise edges**.
//! A locally-valid node the root does not transitively cite is neither rejected nor
//! required. This *absence* is consumed as law by a downstream verifier (thesmos
//! **CD-015**, "reach-as-non-op / enforcement-by-absence"), so it is pinned here as a
//! CI guard: **adding** a reachability check to `check` fails this suite, not the
//! consumer's shipped law. Named frozen in `docs/spec/logos-contract.md` §4 (PR #705,
//! the load-bearing register / consumer change gate).
//!
//! Two halves, both load-bearing:
//!   1. ACCEPT — an extra, locally-valid, root-UNREACHABLE node does not reject.
//!   2. REJECT — an extra root-unreachable node is still LOCALLY verified (obligations
//!      1–5 range over *every* node, cited or not): an invalid uncited node rejects.
//!      "No reachability requirement" means unreachable ≠ exempt, not unreachable ≠ seen.

use logos_contract::{
    check, AlwaysAdmit, CheckLimits, CheckProfile, Clause, ClauseId, Derivation, Evidence, Goal,
    GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, PredicateSet, Premise,
    Subst, Symbol, Term, Theory, TheoryGround, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;

// ---------------------------------------------------------------- tiny profile --

/// A theory that owns nothing (this suite needs no builtins).
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
        TheoryGround::disowned()
    }
}

/// A leaf verifier that declares `grant`/`audit` extensional and admits any leaf.
struct PlainLeaves {
    extensional: PredicateSet,
}
impl PlainLeaves {
    fn new() -> Self {
        PlainLeaves {
            extensional: PredicateSet::from_iter(["grant", "audit"]),
        }
    }
}
// test-double: consumer(admits every leaf of its extensional set)
impl LeafVerifier<()> for PlainLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn profile() -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(PlainLeaves::new()),
        admit: Box::new(AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

// ---------------------------------------------------------------- fixture bits --

const C_PERMIT: &str = "permit_rule";

/// `permit(S) :- grant(S).` — `grant`/`audit` are extensional (leaves).
fn program() -> MapProgram {
    MapProgram::new().with(
        C_PERMIT,
        Clause::new(
            Goal::new("permit", [Term::var("S")]),
            [Goal::new("grant", [Term::var("S")])],
        ),
    )
}

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn g(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| v(a)))
}
fn subst_s(to: &str) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert("S".into(), Term::atom(to.as_bytes().to_vec()));
    s
}

/// Nodes [0] leaf grant(s1) ← cited, [1] rule permit(s1) = root. `extra` (if any) is
/// appended as node [2]: present in the DAG, **cited by nothing, unreachable from root**.
fn derivation(extra: Option<Node>) -> Derivation {
    let mut nodes = vec![
        Node::Leaf {
            conclusion: g("grant", &["s1"]),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("permit", &["s1"]),
            clause: ClauseId::new(C_PERMIT),
            subst: subst_s("s1"),
            premises: vec![Premise::pos(0)],
            meta: NodeMeta::none(),
        },
    ];
    if let Some(n) = extra {
        nodes.push(n);
    }
    Derivation::new(nodes, 1)
}

// --------------------------------------------------------------------- tests --

/// Baseline: the two-node derivation (no extra node) accepts.
#[test]
fn accept_baseline_without_extra_node() {
    let outcome = check(
        &program(),
        &g("permit", &["s1"]),
        &derivation(None),
        &(),
        &profile(),
    );
    assert!(outcome.is_accept(), "baseline must accept, got {outcome:?}");
}

/// THE FROZEN ABSENCE (obligation 6): a locally-valid extensional leaf the root never
/// cites — node [2] `audit(x9)`, reachable from nothing — must NOT cause rejection.
/// A future reachability requirement in `check` turns this test red before it turns
/// thesmos CD-015 wrong.
#[test]
fn accept_locally_valid_root_unreachable_node() {
    let extra = Node::Leaf {
        conclusion: g("audit", &["x9"]),
        evidence: Evidence::none(),
    };
    let outcome = check(
        &program(),
        &g("permit", &["s1"]),
        &derivation(Some(extra)),
        &(),
        &profile(),
    );
    assert!(
        outcome.is_accept(),
        "a locally-valid, root-unreachable node must be neither rejected nor required \
         (§4 obligation 6, frozen; thesmos CD-015 rests on this) — got {outcome:?}"
    );
}

/// The other half: unreachable does NOT mean exempt. Obligations 1–5 range over every
/// node — an *invalid* uncited node (a `Leaf` concluding the intensional `permit`, the
/// §4.2 sealing violation) still rejects, even though the root never cites it.
#[test]
fn reject_locally_invalid_root_unreachable_node() {
    let extra = Node::Leaf {
        conclusion: g("permit", &["x9"]), // intensional head as a leaf → sealed_violation
        evidence: Evidence::none(),
    };
    let outcome = check(
        &program(),
        &g("permit", &["s1"]),
        &derivation(Some(extra)),
        &(),
        &profile(),
    );
    match outcome.verdict {
        Verdict::Reject { ref code, .. } => assert_eq!(
            code.code(),
            "sealed_violation",
            "an invalid uncited node must reject with its own local error, got {outcome:?}"
        ),
        Verdict::Accept => {
            panic!("an invalid (sealing-violating) uncited node must still reject")
        }
    }
}
