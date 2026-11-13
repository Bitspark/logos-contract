//! PROBE (#1371) — `PredicatePartitionViolation` is raised by **three** distinct
//! conditions, and a consumer branching on the code cannot tell them apart.
//!
//! This test pins what `check` reports **today** for each arm. It is deliberately
//! *framing-neutral*: it asserts the current conflation rather than a preferred fix, so
//! it is a valid regression anchor under either additive shape #1371 might take. When
//! the capability arm gets its own code, exactly one assertion here changes, and the
//! two that must NOT change are already spelled out.
//!
//! ## The three arms (`check/mod.rs`, and byte-identically in `check.go` / `check.ts`)
//!
//! ```text
//! !owned              "no theory owns the builtin predicate"        HOST CAPABILITY
//! also extensional    "builtin predicate is also extensional"       genuine §4.4 overlap
//! disowned            "theory owns predicate but returned NotMine"  INCONSISTENT THEORY
//! ```
//!
//! Only the first is a statement about the **verifier's binding set** rather than about
//! the account. It is the one #1371 moves: a sound account re-checked on a theory-less
//! host reports a structural-band code meaning "this account is malformed", which sends
//! a consumer's referee to investigate a producer that did nothing wrong.
//!
//! The other two are correctly structural and **must keep** the code — that is #1371's
//! own must-not-regress clause, pinned here as `arm2` and `arm3`.

use logos_contract::{
    check, CheckLimits, CheckProfile, Derivation, Evidence, GroundLiteral, LeafOutcome,
    LeafVerifier, MapProgram, Node, Outcome, PredicateSet, RejectionCode, Symbol, Theory,
    TheoryGround, Verdict,
};
use ontos_core::Value;

// ------------------------------- theories, one per arm -------------------------------

/// Arm 1: a host that binds **no** theory — `owns()` is false for everything.
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
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
}

/// Arms 2 and 4: a theory that owns the predicate and decides it holds.
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
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::holds()
    }
}

/// Arm 3: an **inconsistent** theory — `owns()` says yes, `decide_ground()` disowns.
struct DisowningTheory;
// test-double: adversarial(owns a predicate yet decides NotMine: the inconsistent arm)
impl Theory for DisowningTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        true
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
}

// ------------------------------------ leaves ------------------------------------

struct Leaves {
    extensional: PredicateSet,
}
impl Leaves {
    /// No extensional predicates — the ordinary case.
    fn empty() -> Self {
        Leaves {
            extensional: PredicateSet::new(),
        }
    }
    /// `pred` is extensional, so a builtin concluding it is a §4.4 partition overlap.
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

// ------------------------------------ harness ------------------------------------

/// A ground atom argument. The arms under test never look at the arguments — only the
/// predicate's ownership and partition membership — so an atom is enough and avoids
/// dragging numeric-tower construction into a probe about rejection codes.
fn atom_v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

/// A one-node derivation whose root is a `Builtin` concluding `pred(1, 1)`.
fn builtin_derivation(pred: &str) -> Derivation {
    Derivation::new(
        [Node::Builtin {
            conclusion: GroundLiteral::new(pred, [atom_v("a"), atom_v("a")]),
        }],
        0,
    )
}

fn run(theory: Box<dyn Theory>, leaves: Leaves, pred: &str) -> Outcome {
    let profile: CheckProfile<()> = CheckProfile {
        theory,
        leaves: Box::new(leaves),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let program = MapProgram::new();
    let deriv = builtin_derivation(pred);
    let claim = GroundLiteral::new(pred, [atom_v("a"), atom_v("a")]);
    check(&program, &claim, &deriv, &(), &profile)
}

fn reject_parts(outcome: &Outcome) -> (RejectionCode, String) {
    match &outcome.verdict {
        Verdict::Reject { code, detail } => (*code, detail.clone()),
        Verdict::Accept => panic!("expected a rejection, got Accept"),
    }
}

// ------------------------------------- the arms -------------------------------------

/// **Arm 1 — HOST CAPABILITY.** The account is sound; this host simply binds no theory
/// that owns the predicate. Today it is indistinguishable from a malformed account.
///
/// ⇒ This is the assertion #1371 changes. It is written to fail loudly rather than
/// silently when the capability arm gets its own code.
#[test]
fn arm1_unbound_theory_is_reported_as_a_structural_violation() {
    let (code, detail) = reject_parts(&run(Box::new(UnboundTheory), Leaves::empty(), "=:="));
    assert_eq!(
        code,
        RejectionCode::PredicatePartitionViolation,
        "arm 1 (no bound theory) — if this now reports its own code, #1371 has landed \
         and this probe should be updated to assert THAT code"
    );
    assert_eq!(detail, "no theory owns the builtin predicate");
}

/// **Arm 2 — genuine §4.4 overlap.** The theory owns it AND it is extensional. The
/// account really is malformed. #1371 must NOT change this.
#[test]
fn arm2_extensional_overlap_keeps_the_structural_code() {
    let (code, detail) = reject_parts(&run(Box::new(OwningTheory), Leaves::with("=:="), "=:="));
    assert_eq!(code, RejectionCode::PredicatePartitionViolation);
    assert_eq!(detail, "builtin predicate is also extensional");
}

/// **Arm 3 — inconsistent theory.** `owns()` said yes and `decide_ground()` disowned. A
/// verifier-side defect, correctly structural. #1371 must NOT change this either.
#[test]
fn arm3_inconsistent_theory_keeps_the_structural_code() {
    let (code, detail) = reject_parts(&run(Box::new(DisowningTheory), Leaves::empty(), "=:="));
    assert_eq!(code, RejectionCode::PredicatePartitionViolation);
    assert_eq!(detail, "theory owns predicate but returned NotMine");
}

/// **The conflation itself, stated as one assertion.** Three conditions, one code — so a
/// consumer branching on the code (which the structural band explicitly instructs:
/// *"Branch on these, not on `detail`"*) cannot separate "unverifiable here" from
/// "malformed account".
#[test]
fn the_three_arms_are_indistinguishable_by_code() {
    let a1 = reject_parts(&run(Box::new(UnboundTheory), Leaves::empty(), "=:="));
    let a2 = reject_parts(&run(Box::new(OwningTheory), Leaves::with("=:="), "=:="));
    let a3 = reject_parts(&run(Box::new(DisowningTheory), Leaves::empty(), "=:="));

    assert_eq!(a1.0, a2.0, "arm 1 and arm 2 share a code");
    assert_eq!(a2.0, a3.0, "arm 2 and arm 3 share a code");

    // ...while the DETAIL strings already separate them. That is precisely the gap:
    // the distinguishing information exists and lives in the one field the structural
    // band tells consumers not to branch on.
    assert_ne!(a1.1, a2.1);
    assert_ne!(a2.1, a3.1);
    assert_ne!(a1.1, a3.1);
}

/// **Positive control.** Without it, every assertion above would still pass if `check`
/// rejected *every* builtin for some unrelated reason — the arms would be trivially
/// equal and the probe would be measuring nothing.
#[test]
fn control_a_bound_consistent_theory_accepts() {
    let outcome = run(Box::new(OwningTheory), Leaves::empty(), "=:=");
    assert!(
        outcome.is_accept(),
        "control failed: a bound, consistent theory must ACCEPT — without this the \
         three arms could be equal for a reason that has nothing to do with #1371"
    );
}
