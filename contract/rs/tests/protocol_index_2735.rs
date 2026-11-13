//! #2735: a protocol index is an INTEGER, not a host offset. It is held as `u64` on every build,
//! becomes an offset only through [`index_offset`] after a range check, and an index past its
//! collection reaches `check`, which refuses it by name. #2682's per-platform decode refusal
//! (`IndexBeyondPlatform`) is gone: on a 32-bit build, a root past `2^32 - 1` is still an integer
//! the decoder holds, and `check` refuses it as `root_out_of_range`, like any other root past the
//! nodes. The go twin is `contract/go/protocol_index_2735_test.go`.

use logos_contract::derivation_wire::INDEX_MAX;
use logos_contract::{
    check, decode_derivation_wire_v1, encode_derivation_wire_v1, index_offset, AlwaysAdmit, CertId,
    CheckLimits, CheckProfile, Derivation, Evidence, GroundLiteral, LeafOutcome, LeafVerifier,
    MapProgram, Node, Outcome, PredicateSet, RejectionCode, Symbol, Theory, TheoryGround, Verdict,
};
use ontos_core::Value;

/// In the contract's domain (`<= INDEX_MAX`), and past what a 32-bit `usize` holds.
const PAST_32: u64 = (1 << 32) + 5;

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
}

struct Leaves(PredicateSet);
// test-double: consumer(admits every leaf of its extensional set)
impl LeafVerifier<()> for Leaves {
    fn extensional(&self) -> &PredicateSet {
        &self.0
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn claim() -> GroundLiteral {
    GroundLiteral::new("p", [Value::atom(b"a".to_vec())])
}

/// One leaf proving the claim, rooted at `root`.
fn one_leaf(root: u64) -> Derivation {
    Derivation::new(
        [Node::Leaf {
            conclusion: claim(),
            evidence: Evidence::none(),
        }],
        root,
    )
}

fn verdict(d: &Derivation) -> Outcome {
    let profile = CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(Leaves(PredicateSet::from_iter(["p"]))),
        admit: Box::new(AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    check(&MapProgram::default(), &claim(), d, &(), &profile)
}

#[test]
fn the_offset_step_is_the_range_check_and_nothing_else_2735() {
    // CONTROL, checked at compile time: the probe is inside the contract's domain.
    const { assert!(PAST_32 <= INDEX_MAX) };
    assert_eq!(
        index_offset(2, 3),
        Some(2),
        "CONTROL: an in-range index is its offset"
    );
    for (i, n) in [(3, 3), (PAST_32, 3), (INDEX_MAX, 3), (0, 0)] {
        assert_eq!(
            index_offset(i, n),
            None,
            "index {i} is no offset into {n} elements"
        );
    }
    assert_eq!(
        CertId(1).offset(2),
        Some(1),
        "CONTROL: a cited cert that is carried"
    );
    assert_eq!(
        CertId(PAST_32).offset(2),
        None,
        "a cited cert past the carried ones"
    );
}

#[test]
fn a_root_past_a_32_bit_offset_is_held_whole_and_refused_by_check_2735() {
    assert!(
        verdict(&one_leaf(0)).is_accept(),
        "CONTROL: the same derivation rooted at its one node is accepted"
    );
    let d = one_leaf(PAST_32);
    assert_eq!(d.root, PAST_32, "the root is held as an integer");
    assert_eq!(d.root_offset(), None, "a root past the nodes has no offset");
    match verdict(&d).verdict {
        Verdict::Reject { code, .. } => assert_eq!(code, RejectionCode::RootOutOfRange),
        other => panic!("want root_out_of_range, got {other:?}"),
    }
}

/// The decoder reads the index as the integer it is, on every build: it round-trips intact, and the
/// refusal is `check`'s. Before #2735 a 32-bit build refused it at decode, by a per-platform code.
#[test]
fn a_root_past_a_32_bit_offset_decodes_intact_on_every_build_2735() {
    let d = one_leaf(PAST_32);
    let decoded = decode_derivation_wire_v1(&encode_derivation_wire_v1(&d))
        .expect("an in-domain index decodes on every build");
    assert_eq!(decoded.root, PAST_32);
    assert_eq!(decoded, d);
}
