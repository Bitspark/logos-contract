//! #2565: `Derivation::closed_world` is a [`CertStack`], a `Vec` whose storage clones SHARE.
//!
//! It must behave exactly as the `Vec` it replaced, with only cloning made cheap. Each row below
//! pins one half of that: clones share and are equal; a write copies a shared stack first, and
//! the other holder does not change; a write to an unshared stack copies nothing; `Debug`, every
//! iteration form and the wire bytes are those of the plain `Vec`.

use logos_contract::{
    encode_derivation_wire_v1, CertSizeDecl, CertStack, ClosedModelCert, ClosureWitness,
    Derivation, GroundLiteral, Node, StratumPrefix, SupportWitness,
};

/// A structurally minimal cert, told apart from its siblings by `program_hash`. Never verified:
/// these rows are about the container, not the certificate.
fn cert(tag: u8) -> ClosedModelCert {
    ClosedModelCert {
        scope: StratumPrefix::new(0, ["p".into()]),
        program_hash: [tag; 32],
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

fn node() -> Node {
    Node::Builtin {
        conclusion: GroundLiteral::new("p", []),
    }
}

#[test]
fn a_clone_shares_the_allocation_and_is_equal_2565() {
    let a = CertStack::new(vec![cert(1), cert(2)]);
    let b = a.clone();
    assert!(CertStack::ptr_eq(&a, &b), "a clone shares the storage");
    assert_eq!(a, b);
    // CONTROL: two stacks built separately are equal and NOT shared, so `ptr_eq` discriminates.
    let c = CertStack::new(vec![cert(1), cert(2)]);
    assert_eq!(a, c);
    assert!(!CertStack::ptr_eq(&a, &c));
}

#[test]
fn a_write_copies_a_shared_stack_and_the_other_holder_is_unchanged_2565() {
    let a = CertStack::new(vec![cert(1)]);
    let mut b = a.clone();
    b[0].program_hash = [9u8; 32];
    assert!(
        !CertStack::ptr_eq(&a, &b),
        "the write copied b's storage first"
    );
    assert_eq!(a[0].program_hash, [1u8; 32], "a is untouched");
    assert_eq!(b[0].program_hash, [9u8; 32]);

    let mut c = a.clone();
    c.push(cert(3));
    c.clear();
    assert_eq!(a.len(), 1, "push and clear on a clone leave a as it was");
}

#[test]
fn a_write_to_an_unshared_stack_copies_nothing_2565() {
    let mut a = CertStack::new(vec![cert(1)]);
    let before = a.as_ptr();
    a[0].program_hash = [9u8; 32];
    assert_eq!(a.as_ptr(), before, "no other holder, so no copy");
}

#[test]
fn it_reads_as_the_vec_it_replaced_2565() {
    let certs = vec![cert(1), cert(2)];
    let stack = CertStack::from(certs.clone());
    assert_eq!(
        format!("{stack:?}"),
        format!("{certs:?}"),
        "Debug prints the Vec, so a derivation prints as before"
    );
    assert_eq!(stack.len(), 2);
    let mut by_ref = 0;
    for _ in &stack {
        by_ref += 1;
    }
    assert_eq!(by_ref, 2);
    let mut owned = stack.clone();
    for c in &mut owned {
        c.program_hash = [7u8; 32];
    }
    assert!(owned.iter().all(|c| c.program_hash == [7u8; 32]));
    assert_eq!(stack.into_iter().collect::<Vec<_>>(), certs);
}

/// Sharing is an allocation detail: a derivation holding a SHARED stack encodes to exactly the
/// bytes of one holding its own deep copy.
#[test]
fn a_shared_stack_encodes_to_the_bytes_of_a_deep_copy_2565() {
    let shared = CertStack::new(vec![cert(1), cert(2)]);
    let holder = Derivation::with_shared_closed_world([node()], 0, shared.clone());
    let _other = Derivation::with_shared_closed_world([node()], 0, shared.clone());
    let deep = Derivation::with_closed_world([node()], 0, vec![cert(1), cert(2)]);
    assert!(CertStack::ptr_eq(&holder.closed_world, &shared));
    assert!(!CertStack::ptr_eq(&deep.closed_world, &shared));
    assert_eq!(holder, deep);
    assert_eq!(
        encode_derivation_wire_v1(&holder),
        encode_derivation_wire_v1(&deep)
    );
}
