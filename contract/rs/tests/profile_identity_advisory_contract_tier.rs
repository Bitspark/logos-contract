//! The CONTRACT-TIER reachability test for the unidentified-component advisory (#815).
//!
//! This file imports **`logos_contract` and nothing else**. That is the whole point: it is
//! the tier-level analogue of #800's consumer-path import test.
//!
//! ADR 0026 **G2** asks each exposed consumer to self-measure. The advisory originally lived
//! in `kernel`, so a consumer binding only `logos-contract` could not reach it — and could
//! not be given it, because `contract → kernel` is an **upward** edge the `arch` job rejects.
//! That was a reachability wall no release could lift, and it was found only when a real
//! consumer (thesmos, which binds `logos-contract`) tried to follow the instruction and had
//! to submit a source-level audit instead (#791).
//!
//! The kernel forms are now re-exports of these. **A test that imports the kernel cannot
//! detect a regression of the placement** — it would keep passing if the definition moved
//! back up a tier, because a re-export looks identical from above. Only a test that refuses
//! the kernel dependency can, which is why this file exists separately from
//! `kernel/rs/tests/profile_identity_advisory_vectors.rs` rather than replacing it.
//!
//! It replays the SAME `vectors/profile_identity_advisory.json` as the kernel arms, so
//! cross-tier agreement and tri-core agreement are one check rather than two.

use logos_contract::{
    unidentified_profile_slots, unidentified_profile_slots_allowing, AlwaysAdmit, CheckLimits,
    CheckProfile, ComponentIdentity, Evidence, GroundLiteral, LeafOutcome, LeafVerifier, NodeMeta,
    PredicateSet, ProfileSlot, RuleAdmissibility, RuleOutcome, Symbol, Theory, TheoryGround,
};
use serde_json::Value as Json;

struct VecTheory {
    identity: Option<ComponentIdentity>,
}
// test-double: consumer(an explicitly identified theory for the identity advisory)
impl Theory for VecTheory {
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
    fn identity(&self) -> ComponentIdentity {
        self.identity
            .clone()
            .unwrap_or_else(ComponentIdentity::unidentified)
    }
}

struct VecLeaves {
    ext: PredicateSet,
    identity: Option<ComponentIdentity>,
}
// test-double: consumer(an explicitly identified leaf verifier for the identity advisory)
impl LeafVerifier<()> for VecLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.ext
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Reject {
            code: "vector".into(),
        }
    }
    fn identity(&self) -> ComponentIdentity {
        self.identity
            .clone()
            .unwrap_or_else(ComponentIdentity::unidentified)
    }
}

struct AnonAdmit;
// test-double: adversarial(no identity: the anonymous reading the advisory flags)
impl RuleAdmissibility<()> for AnonAdmit {
    fn admissible(
        &self,
        _clause: &logos_contract::Clause,
        _meta: &NodeMeta,
        _ctx: &(),
    ) -> RuleOutcome {
        RuleOutcome::Admit
    }
}

fn repo_root() -> std::path::PathBuf {
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/profile_identity_advisory.json").exists() {
            return dir;
        }
        assert!(dir.pop(), "could not locate the advisory vector");
    }
}

fn identity_from(bindings: &Json, name: &str) -> Option<ComponentIdentity> {
    if name == "anonymous" {
        return None;
    }
    let b = &bindings[name];
    let hex = b["config_digest"].as_str().expect("config_digest");
    let mut digest = [0u8; 32];
    for (i, byte) in digest.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("hex");
    }
    Some(ComponentIdentity::new(
        b["id"].as_str().expect("id").as_bytes().to_vec(),
        b["version"].as_str().expect("version").as_bytes().to_vec(),
        digest,
    ))
}

#[test]
fn the_advisory_is_reachable_and_correct_from_contract_alone() {
    let raw = std::fs::read_to_string(repo_root().join("vectors/profile_identity_advisory.json"))
        .expect("read vector");
    let v: Json = serde_json::from_str(&raw).expect("parse vector");
    let bindings = &v["bindings"];

    let cases = v["cases"].as_array().expect("cases");
    assert!(!cases.is_empty(), "vector must carry cases");

    for case in cases {
        let name = case["name"].as_str().expect("name");

        let admit: Box<dyn RuleAdmissibility<()>> = match case["admit"].as_str().expect("admit") {
            "anonymous" => Box::new(AnonAdmit),
            "always_admit" => Box::new(AlwaysAdmit),
            other => panic!("case {name}: unknown admit binding {other}"),
        };

        let profile = CheckProfile {
            theory: Box::new(VecTheory {
                identity: identity_from(bindings, case["theory"].as_str().expect("theory")),
            }),
            leaves: Box::new(VecLeaves {
                ext: PredicateSet::default(),
                identity: identity_from(bindings, case["leaves"].as_str().expect("leaves")),
            }),
            admit,
            limits: CheckLimits::default(),
        };

        let allowance: Vec<ProfileSlot> = case["allow_unidentified"]
            .as_array()
            .map(|a| {
                a.iter()
                    .map(|s| match s.as_str().expect("slot") {
                        "theory" => ProfileSlot::Theory,
                        "leaves" => ProfileSlot::Leaves,
                        "admit" => ProfileSlot::Admit,
                        other => panic!("case {name}: unknown slot {other}"),
                    })
                    .collect()
            })
            .unwrap_or_default();

        let expected: Vec<&str> = case["unidentified_slots"]
            .as_array()
            .expect("unidentified_slots")
            .iter()
            .map(|s| s.as_str().expect("slot"))
            .collect();

        let actual: Vec<&str> = unidentified_profile_slots_allowing(&profile, &allowance)
            .into_iter()
            .map(ProfileSlot::name)
            .collect();

        // ORDERED — a set comparison would pass under reordering.
        assert_eq!(
            actual, expected,
            "case {name}: the contract-tier advisory must match the shared vector, in fold order"
        );

        if allowance.is_empty() {
            let plain: Vec<&str> = unidentified_profile_slots(&profile)
                .into_iter()
                .map(ProfileSlot::name)
                .collect();
            assert_eq!(
                plain, actual,
                "case {name}: the unallowed form must equal the empty allowance"
            );
        }
    }
}
