//! Rust replay of `vectors/identity_audit.json` (#767) — the identity-audit surface:
//! `ComponentIdentity::is_unidentified` and the `compound_identity_of` baseline fold,
//! which this vector uses to FREEZE the `CompoundTheory` identity byte layout tri-core.
//!
//! Every case builds REAL member theories (fixture types over the vector's invented
//! `mistfen` vocabulary, declared invented per ADR 0025 — a member named
//! `"unidentified"` is a theory that does NOT override `identity()`), constructs a live
//! [`CompoundTheory`], and asserts THREE independently-falsifiable facts per case:
//!
//! 1. the live `identity()` equals the HAND-AUTHORED pin (the layout freeze);
//! 2. `compound_identity_of` over the member identity triples equals the same pin
//!    (the public audit fn agrees with the pin, not merely with the live path);
//! 3. the distinguishability verdict — live identity vs the all-unidentified baseline
//!    of the same member count — equals the pinned verdict (the audit's acceptance:
//!    MOVES on substitution, does NOT move on an irrelevant member change).
//!
//! Plus the order pin: `identified_first` and `identified_second` must carry DIFFERENT
//! digests (member order is identity-bearing).

use logos_contract::{
    compound_identity_of, ComponentIdentity, CompoundTheory, GroundLiteral, Symbol, Theory,
    TheoryOutcome,
};
use serde_json::Value as Json;

/// A fixture member theory carrying an explicit identity (the vector's invented
/// `mistfen` components). Owns nothing — the audit is about identity, not routing.
struct PinnedTheory {
    identity: ComponentIdentity,
}
// test-double: consumer(an explicitly identified theory for the identity audit)
impl Theory for PinnedTheory {
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
    fn identity(&self) -> ComponentIdentity {
        self.identity.clone()
    }
}

/// A fixture member that does NOT override `identity()` — the defaulted
/// (unidentified) reading the audit exists to detect.
struct DefaultedTheory;
// test-double: adversarial(relies on the default identity: the unidentified reading the audit detects)
impl Theory for DefaultedTheory {
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

fn load() -> Json {
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/identity_audit.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/identity_audit.json");
    }
    let raw =
        std::fs::read_to_string(dir.join("vectors/identity_audit.json")).expect("read vector");
    serde_json::from_str(&raw).expect("parse vector")
}

fn hex32(s: &str) -> [u8; 32] {
    assert_eq!(s.len(), 64, "config_digest must be 64 hex chars");
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        out[i] = u8::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16).expect("hex byte");
    }
    out
}

fn identity_from(spec: &Json) -> ComponentIdentity {
    ComponentIdentity::new(
        spec["id"].as_str().expect("id").as_bytes().to_vec(),
        spec["version"]
            .as_str()
            .expect("version")
            .as_bytes()
            .to_vec(),
        hex32(spec["config_digest"].as_str().expect("config_digest")),
    )
}

#[test]
fn identity_audit_replay() {
    let file = load();
    let components = &file["components"];
    let wrapper = &file["compound_wrapper"];
    let cases = file["cases"].as_array().expect("cases");
    assert_eq!(cases.len(), 8, "the pin file carries exactly 8 cases");

    // The plain-component audit primitive, against the vector's triples.
    assert!(identity_from(&file["unidentified"]).is_unidentified());
    assert!(!identity_from(&components["brook"]).is_unidentified());
    assert!(!identity_from(&components["heron"]).is_unidentified());
    // A defaulted (non-overriding) live component reads as unidentified.
    assert!(DefaultedTheory.identity().is_unidentified());

    let mut config_by_name: Vec<(String, [u8; 32])> = Vec::new();
    for case in cases {
        let name = case["name"].as_str().expect("case.name");
        let members = case["members"].as_array().expect("case.members");
        let pinned = ComponentIdentity::new(
            wrapper["id"]
                .as_str()
                .expect("wrapper.id")
                .as_bytes()
                .to_vec(),
            wrapper["version"]
                .as_str()
                .expect("wrapper.version")
                .as_bytes()
                .to_vec(),
            hex32(case["config_digest"].as_str().expect("case.config_digest")),
        );

        // (1) LIVE: real member theories -> CompoundTheory -> identity().
        let live_members: Vec<Box<dyn Theory + Send + Sync>> = members
            .iter()
            .map(|m| {
                let key = m.as_str().expect("member name");
                if key == "unidentified" {
                    Box::new(DefaultedTheory) as Box<dyn Theory + Send + Sync>
                } else {
                    Box::new(PinnedTheory {
                        identity: identity_from(&components[key]),
                    }) as Box<dyn Theory + Send + Sync>
                }
            })
            .collect();
        let live = CompoundTheory::new(live_members).identity();
        assert_eq!(
            live, pinned,
            "case {name}: live identity vs hand-authored pin"
        );

        // (2) The public audit fn over the triples agrees with the same pin.
        let triples: Vec<ComponentIdentity> = members
            .iter()
            .map(|m| {
                let key = m.as_str().expect("member name");
                if key == "unidentified" {
                    ComponentIdentity::unidentified()
                } else {
                    identity_from(&components[key])
                }
            })
            .collect();
        assert_eq!(
            compound_identity_of(&triples),
            pinned,
            "case {name}: compound_identity_of vs hand-authored pin"
        );

        // (3) The audit verdict: live vs the all-unidentified baseline of the same n.
        let baseline =
            compound_identity_of(&vec![ComponentIdentity::unidentified(); members.len()]);
        let distinguishable = live != baseline;
        assert_eq!(
            distinguishable,
            case["distinguishable"]
                .as_bool()
                .expect("case.distinguishable"),
            "case {name}: distinguishability verdict"
        );

        config_by_name.push((name.to_string(), pinned.config_digest));
    }

    // Order is identity-bearing: the same member multiset in two orders pins two digests.
    let config_of = |wanted: &str| {
        config_by_name
            .iter()
            .find(|(n, _)| n == wanted)
            .unwrap_or_else(|| panic!("case {wanted} missing"))
            .1
    };
    assert_ne!(
        config_of("identified_first"),
        config_of("identified_second"),
        "member order must be identity-bearing"
    );
}
