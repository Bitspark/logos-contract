//! PROBE (#1378) — `incoherent_builtin_atoms` gives arm 3 the attribution its rejection
//! code cannot carry.
//!
//! `check` rejects an `owns()`-yes / `decide_ground()`-disowns theory with the structural code
//! `PredicatePartitionViolation` (pinned as `arm3` in `partition_code_conflation_1371.rs`,
//! which this does **not** change). That code is correct — the account genuinely cannot be
//! verified by this profile — but it points a consumer at the **producer** for what is a
//! defect in the *verifier's own* theory binding.
//!
//! Per the #1382 ruling on the sibling arm, a new `RejectionCode` variant is v1-breaking in
//! all three cores, so the attribution is added as a **query** rather than as vocabulary.
//!
//! ## What these tests are for
//!
//! ```text
//! offending theory      -> names the atom        the query works at all
//! coherent theory       -> empty                 it does not fire on the healthy case
//! ARM-1 theory          -> empty                 ** it separates arm 3 from arm 1 **
//! repeated atom         -> one entry             dedup / determinism
//! no builtin cited      -> empty, THEORY IS BAD  ** the documented limit, executable **
//! ```
//!
//! The third and fifth are the load-bearing ones. Without the arm-1 control the query could
//! be firing on "any rejection" and still pass; without the fifth, the doc's warning that an
//! empty result does not certify coherence is prose that nothing holds to.

use logos_contract::{
    incoherent_builtin_atoms, CheckLimits, CheckProfile, Derivation, Evidence, GroundLiteral,
    LeafOutcome, LeafVerifier, Node, PredicateSet, Symbol, Theory, TheoryGround,
};
use ontos_core::Value;

// ------------------------------------- theories -------------------------------------

/// Arm 3: `owns()` says yes, `decide_ground()` disowns. The defect under test.
struct DisowningTheory;
// test-double: adversarial(owns a predicate yet decides NotMine: the defect under test)
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

/// A coherent theory: owns it and decides it.
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

/// Arm 1: a host binding no theory. `decide_ground` also disowns — which is exactly why a query
/// keyed on the disowning answer alone would conflate the two arms.
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

// -------------------------------------- harness --------------------------------------

struct Leaves {
    extensional: PredicateSet,
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

fn atom_v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

fn lit(pred: &str, arg: &str) -> GroundLiteral {
    GroundLiteral::new(pred, [atom_v(arg)])
}

fn profile(theory: Box<dyn Theory>) -> CheckProfile<()> {
    CheckProfile {
        theory,
        leaves: Box::new(Leaves {
            extensional: PredicateSet::new(),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn builtin_deriv(preds_args: &[(&str, &str)]) -> Derivation {
    let nodes: Vec<Node> = preds_args
        .iter()
        .map(|(p, a)| Node::Builtin {
            conclusion: lit(p, a),
        })
        .collect();
    Derivation::new(nodes, 0)
}

// --------------------------------------- tests ---------------------------------------

/// The query fires on the defect it is named for, and returns the **atom**, not the
/// predicate — incoherence is only observable per atom.
#[test]
fn names_the_atom_an_incoherent_theory_disowns() {
    let got = incoherent_builtin_atoms(
        &builtin_deriv(&[("=:=", "a")]),
        &profile(Box::new(DisowningTheory)),
    );
    assert_eq!(got, vec![lit("=:=", "a")]);
}

/// A coherent theory yields nothing. Without this the query could be returning every
/// builtin atom it sees and every other test here would still pass.
#[test]
fn a_coherent_theory_yields_nothing() {
    let got = incoherent_builtin_atoms(
        &builtin_deriv(&[("=:=", "a")]),
        &profile(Box::new(OwningTheory)),
    );
    assert!(
        got.is_empty(),
        "coherent theory reported as incoherent: {got:?}"
    );
}

/// ⭐ **THE DISCRIMINATING CONTROL.** Arm 1 also disowns, and `check` gives it the
/// **same** rejection code. If this query keyed on the outcome alone it would report arm 1
/// too — and then it would name a defect in a theory the host never bound, which is the
/// misattribution inverted rather than fixed.
#[test]
fn arm1_unbound_theory_is_not_reported_as_incoherent() {
    let got = incoherent_builtin_atoms(
        &builtin_deriv(&[("=:=", "a")]),
        &profile(Box::new(UnboundTheory)),
    );
    assert!(
        got.is_empty(),
        "arm 1 (no theory owns the predicate) is a HOST CAPABILITY refusal, not an \
         incoherent theory - the two share a rejection code and must not share this \
         query; got {got:?}"
    );
}

/// Deduplicated on first appearance, in node order — so the result is deterministic and a
/// repeated offending atom is reported (and decided) once.
#[test]
fn repeated_and_distinct_atoms_dedup_in_node_order() {
    let got = incoherent_builtin_atoms(
        &builtin_deriv(&[("=:=", "a"), ("<", "b"), ("=:=", "a")]),
        &profile(Box::new(DisowningTheory)),
    );
    assert_eq!(got, vec![lit("=:=", "a"), lit("<", "b")]);
}

/// ⛔ **THE DOCUMENTED LIMIT, MADE EXECUTABLE.** The theory here is the *same* provably
/// incoherent one as the first test, and the query returns empty — because this derivation
/// cites no `Builtin` node for it to disagree on.
///
/// So an empty result is **not** a coherence certificate: it is a PASS compatible with the
/// thing still failing (form 33). The docstring says so; this holds it to it, and will fail
/// if anyone ever "strengthens" the query into an oracle it cannot be.
#[test]
fn empty_result_does_not_certify_the_theory_coherent() {
    let deriv = Derivation::new(
        [Node::Leaf {
            conclusion: lit("edge", "a"),
            evidence: Evidence::default(),
        }],
        0,
    );
    let got = incoherent_builtin_atoms(&deriv, &profile(Box::new(DisowningTheory)));
    assert!(
        got.is_empty(),
        "expected empty: the query can only witness incoherence on atoms the derivation \
         cites, and this one cites no Builtin node"
    );
}
