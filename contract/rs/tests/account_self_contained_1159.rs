//! `Derivation::is_self_contained()` — §8.2's first portability arm (#1159, P4).
//!
//! The account-side mirror of the kernel seam's `CheckContext::is_trivial`. These tests pin
//! BOTH directions, because a predicate that is constant passes a one-armed test: an
//! all-positive account is self-contained, one carrying a `ClosedModelCert` is not, and the
//! two must actually DIFFER.

use logos_contract::{
    CertSizeDecl, ClosedModelCert, ClosureWitness, Derivation, GroundLiteral, Node, StratumPrefix,
    SupportWitness,
};

/// A structurally minimal cert. Never verified here — `is_self_contained` reads only
/// `closed_world`'s emptiness, so the cert's CONTENTS are deliberately irrelevant and a
/// valid one would test something this predicate does not do.
fn any_cert() -> ClosedModelCert {
    ClosedModelCert {
        scope: StratumPrefix::new(0, ["p".into()]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: Vec::new(),
        domains: Vec::new(),
        extensions: Vec::new(),
        supports: SupportWitness(Vec::new()),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 0,
            domain_values: 0,
            support_edges: 0,
            rule_groundings: 0,
            join_steps: 0,
            cert_bytes: 0,
        },
    }
}

fn one_node() -> Node {
    Node::Builtin {
        conclusion: GroundLiteral::new("p", []),
    }
}

#[test]
fn all_positive_account_is_self_contained() {
    let deriv = Derivation::new([one_node()], 0);
    assert!(
        deriv.is_self_contained(),
        "an all-positive account cites no closure, so it needs no context — §8.2's first arm"
    );
}

#[test]
fn certifying_account_is_not_self_contained() {
    let deriv = Derivation::with_closed_world([one_node()], 0, [any_cert()]);
    assert!(
        !deriv.is_self_contained(),
        "an account carrying a ClosedModelCert is a CERTIFYING check: it needs a bound cert \
         context, which is exactly what check/mod.rs's context-unbound gate reads"
    );
}

/// ⭐ The vacuity guard. Each test above passes on a predicate hard-coded to its own answer;
/// only the DIFFERENCE shows the predicate reads anything at all.
#[test]
fn the_predicate_is_not_constant() {
    let positive = Derivation::new([one_node()], 0);
    let certifying = Derivation::with_closed_world([one_node()], 0, [any_cert()]);
    assert_ne!(
        positive.is_self_contained(),
        certifying.is_self_contained(),
        "the two arms must DIFFER — a constant predicate satisfies both one-armed tests"
    );
}

/// The one thing the doc promises beyond the body: it tracks `closed_world` and nothing
/// else, so node count and shape must not move it.
#[test]
fn self_containment_tracks_closed_world_only_not_node_count() {
    let one = Derivation::new([one_node()], 0);
    let many = Derivation::new([one_node(), one_node(), one_node()], 0);
    assert!(one.is_self_contained() && many.is_self_contained());

    let certifying_many =
        Derivation::with_closed_world([one_node(), one_node(), one_node()], 0, [any_cert()]);
    assert!(!certifying_many.is_self_contained());
}
