//! The pre-check capability query (#1371 stage 1).
//!
//! `unowned_builtin_predicates` answers *"can this host decide the builtins this account
//! cites?"* **before** `check` runs, so a later `predicate_partition_violation` on a
//! `Builtin` node can be read as what it is rather than as an account defect.
//!
//! The tests that matter here are the two NEGATIVE ones:
//!
//!   * `empty_result_does_not_promise_acceptance` — the form-33 guard. An empty result
//!     means *no capability refusal will occur*, NOT *check will accept*.
//!   * `never_calls_decide` — proven by a theory whose `decide` panics.

use logos_contract::{
    check, profile_decides_all_builtins, unowned_builtin_predicates, CheckLimits, CheckProfile,
    Derivation, Evidence, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node, Outcome,
    PredicateSet, RejectionCode, Symbol, Theory, TheoryOutcome,
};
use ontos_core::Value;

// --------------------------------- theories ---------------------------------

/// Binds nothing — the theory-less host #1371 is about.
struct UnboundTheory;
// test-double: consumer(owns no predicate: the theory-less host)
impl Theory for UnboundTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::NotMine
    }
}

/// Owns everything and decides it holds.
struct OwningTheory;
// test-double: consumer(owns every predicate and holds it)
impl Theory for OwningTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        true
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Holds
    }
}

/// Owns exactly one named predicate — for the mixed case.
struct OwnsOnly(&'static str);
// test-double: consumer(owns exactly one named predicate and holds it)
impl Theory for OwnsOnly {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == self.0.as_bytes()
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Holds
    }
}

/// Owns everything, and **panics if asked to decide**. The query must never call `decide`,
/// so this theory is safe for it and fatal for anything that reaches through.
struct ExplodingTheory;
// test-double: adversarial(panics if asked to decide)
impl Theory for ExplodingTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        true
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        panic!("the pre-check query must not call decide()");
    }
}

// ---------------------------------- leaves ----------------------------------

struct Leaves {
    extensional: PredicateSet,
}
impl Leaves {
    fn empty() -> Self {
        Leaves {
            extensional: PredicateSet::new(),
        }
    }
    fn with(pred: &str) -> Self {
        let mut extensional = PredicateSet::new();
        extensional.insert(pred);
        Leaves { extensional }
    }
}
// test-double: consumer(admits no leaf)
impl LeafVerifier<()> for Leaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Reject {
            code: "not_a_leaf_test".into(),
        }
    }
}

// ---------------------------------- harness ----------------------------------

fn atom_v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

fn builtin_node(pred: &str) -> Node {
    Node::Builtin {
        conclusion: GroundLiteral::new(pred, [atom_v("a"), atom_v("a")]),
    }
}

fn deriv(preds: &[&str]) -> Derivation {
    Derivation::new(preds.iter().map(|p| builtin_node(p)), 0)
}

fn profile(theory: Box<dyn Theory>, leaves: Leaves) -> CheckProfile<()> {
    CheckProfile {
        theory,
        leaves: Box::new(leaves),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn names(v: &[Symbol]) -> Vec<String> {
    v.iter()
        .map(|s| String::from_utf8_lossy(s.bytes()).into_owned())
        .collect()
}

// ----------------------------------- tests -----------------------------------

/// A theory-less host names the predicate it cannot decide.
#[test]
fn unbound_theory_names_the_predicate() {
    let p = profile(Box::new(UnboundTheory), Leaves::empty());
    let d = deriv(&["=:="]);
    assert_eq!(names(&unowned_builtin_predicates(&d, &p)), vec!["=:="]);
    assert!(!profile_decides_all_builtins(&d, &p));
}

/// A host that binds an owning theory reports nothing outstanding.
#[test]
fn bound_theory_reports_nothing() {
    let p = profile(Box::new(OwningTheory), Leaves::empty());
    let d = deriv(&["=:="]);
    assert!(unowned_builtin_predicates(&d, &p).is_empty());
    assert!(profile_decides_all_builtins(&d, &p));
}

/// Only the unowned predicates are named — the owned one is absent.
#[test]
fn mixed_ownership_names_only_the_unowned() {
    let p = profile(Box::new(OwnsOnly("=:=")), Leaves::empty());
    let d = deriv(&["=:=", ">", "<"]);
    assert_eq!(names(&unowned_builtin_predicates(&d, &p)), vec![">", "<"]);
}

/// Deduplicated on first appearance, in derivation node order — so the report is
/// deterministic for a given derivation rather than merely a set.
#[test]
fn deduplicated_in_node_order() {
    let p = profile(Box::new(UnboundTheory), Leaves::empty());
    let d = deriv(&[">", "=:=", ">", "<", "=:="]);
    assert_eq!(
        names(&unowned_builtin_predicates(&d, &p)),
        vec![">", "=:=", "<"]
    );
}

/// ⭐ **THE FORM-33 GUARD.** An empty result must NOT be read as "check will accept".
///
/// Here the theory owns the predicate — so the query is EMPTY, the strongest possible
/// "no capability problem" answer — and `check` still rejects, because the predicate is
/// also extensional (a genuine §4.4 partition overlap). The two are independent, and this
/// test is what stops the query being documented as a verifiability oracle.
#[test]
fn empty_result_does_not_promise_acceptance() {
    let p = profile(Box::new(OwningTheory), Leaves::with("=:="));
    let d = deriv(&["=:="]);

    assert!(
        unowned_builtin_predicates(&d, &p).is_empty(),
        "precondition: the capability query must be clean here"
    );

    let claim = GroundLiteral::new("=:=", [atom_v("a"), atom_v("a")]);
    let outcome = check(&MapProgram::new(), &claim, &d, &(), &p);

    match outcome {
        Outcome::Reject { code, .. } => assert_eq!(
            code,
            RejectionCode::PredicatePartitionViolation,
            "a clean capability query coexists with a structural rejection — that is the point"
        ),
        Outcome::Accept => panic!(
            "expected a structural rejection: an empty capability report does not make an \
             overlapping account valid"
        ),
    }
}

/// ⭐ The query is **total and side-effect-free**: it consults `owns()` only. Proven rather
/// than asserted — this theory panics if `decide` is ever reached, so a query that touched
/// it would fail this test loudly instead of silently costing a caller real work.
#[test]
fn never_calls_decide() {
    let p = profile(Box::new(ExplodingTheory), Leaves::empty());
    let d = deriv(&["=:=", ">", "<"]);
    assert!(unowned_builtin_predicates(&d, &p).is_empty());
    assert!(profile_decides_all_builtins(&d, &p));
}

/// A derivation citing no builtins at all reports nothing — the vacuous case, pinned so it
/// cannot drift into a false alarm.
#[test]
fn no_builtins_reports_nothing() {
    let p = profile(Box::new(UnboundTheory), Leaves::empty());
    let d = Derivation::new([], 0);
    assert!(unowned_builtin_predicates(&d, &p).is_empty());
}
