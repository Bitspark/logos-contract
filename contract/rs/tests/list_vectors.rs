//! Rust replay of the cross-core THEORY-DECISION agreement vector `vectors/list.json`.
//!
//! The [`ListTheory`] `decide_ground` is asserted to reproduce the committed vector on every
//! ground atom (the A1 list relations `length/2`, `nth0/3`, `last/2` over the reified
//! `list` embedding). The SAME file is replayed by the Go binding
//! (`contract/go/list_vectors_test.go`) and the TS binding
//! (`contract/ts/test/list_vectors.test.ts`), so one oracle — the Rust `ListTheory::decide_ground`
//! — pins all three cores (the §7 dual-conformance / tri-core byte-parity law). A change to
//! the relations' judgments fails here AND in Go/TS, so the cores can never silently
//! diverge.
//!
//! Per `vectors/README.md`, the vector is *hand-authored from the spec*; this replay
//! re-derives every outcome through the REAL `ListTheory::decide_ground` — the committed file is
//! checked against the oracle, not trusted blind.

use logos_contract::completion::{Completion, TheoryDecision};
use logos_contract::{GroundLiteral, ListTheory, Symbol, Theory, TheoryGround};
use ontos_core::Value;
use serde_json::Value as Json;

// This source is in `contract/rs/tests/`, so `include_str!` (relative to the source file)
// reaches the repo root three levels up — same depth as the term/text/compound replays.
const VECTORS: &str = include_str!("../../../vectors/list.json");

/// Build the ontos `Value` an arg object denotes, matching the structural encoding in
/// `vectors/list.json` (and the Go/TS replays) EXACTLY:
///
/// * `{"atom": "<utf8>"}` → a bare `Atom` of those UTF-8 bytes;
/// * `{"int": N}`         → the frozen ontos-data `int` embedding (a `Tuple`);
/// * `{"list": [..]}`     → the ontos-data `list` embedding of the encoded children;
/// * `{"tuple": [..]}`    → a raw `Tuple` of the encoded children (cons cells / non-lists).
fn build_arg(arg: &Json) -> Value {
    let obj = arg
        .as_object()
        .unwrap_or_else(|| panic!("arg is not an object: {arg}"));
    if let Some(a) = obj.get("atom") {
        let s = a.as_str().expect("atom arg is a string");
        return Value::atom(s.as_bytes().to_vec());
    }
    if let Some(n) = obj.get("int") {
        let n = n
            .as_i64()
            .unwrap_or_else(|| panic!("int arg not an i64: {n}"));
        // Build the canonical int embedding via the frozen ontos-data single source — the
        // same byte form the search-side number/1 and the Shelf-B int payloads use.
        return ontos_data::encode_int(i128::from(n));
    }
    if let Some(children) = obj.get("list") {
        let children = children.as_array().expect("list arg is an array");
        let elems = children.iter().map(build_arg).collect::<Vec<_>>();
        return ontos_data::encode_list(&elems);
    }
    if let Some(children) = obj.get("tuple") {
        let children = children.as_array().expect("tuple arg is an array");
        let elems = children.iter().map(build_arg).collect::<Vec<_>>();
        return Value::tuple(elems);
    }
    panic!("unrecognized arg shape: {arg}");
}

/// Build the ground atom for one decision entry.
fn build_atom(entry: &Json) -> GroundLiteral {
    let pred = entry["pred"].as_str().expect("pred is a string");
    let args = entry["args"].as_array().expect("args is an array");
    let values = args.iter().map(build_arg).collect::<Vec<_>>();
    GroundLiteral::new(pred, values)
}

/// Assert the actual outcome matches the pinned `"holds" | {"fails": code}` outcome.
fn assert_outcome(name: &str, expected: &Json, got: &TheoryGround) {
    if let Some(s) = expected.as_str() {
        assert_eq!(s, "holds", "{name}: unknown string outcome {s:?}");
        assert!(
            *got == TheoryGround::holds(),
            "{name}: want Holds, got {got:?}"
        );
        return;
    }
    let code = expected["fails"].as_str().unwrap_or_else(|| {
        panic!("{name}: outcome is neither \"holds\" nor {{fails}}: {expected}")
    });
    match got {
        Completion::Completed(TheoryDecision::Fails { code: got_code }) => {
            assert_eq!(got_code, code, "{name}: fail-code mismatch");
        }
        other => panic!("{name}: want Fails{{{code}}}, got {other:?}"),
    }
}

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("vectors/list.json parses")
}

#[test]
fn replay_decision_vectors_match_the_oracle() {
    let json = vectors();
    let theory = ListTheory::new();
    let decisions = json["decisions"].as_array().expect("decisions array");
    assert!(!decisions.is_empty(), "no decision vectors loaded");
    for entry in decisions {
        let name = entry["name"].as_str().unwrap_or("<unnamed>");
        let atom = build_atom(entry);
        let got = theory.decide_ground(&atom);
        assert_outcome(name, &entry["outcome"], &got);
    }
}

#[test]
fn replay_owns_vector_matches_the_oracle() {
    let json = vectors();
    let theory = ListTheory::new();
    let owns = &json["owns"];
    for name in owns["owned"].as_array().expect("owned array") {
        let s = name.as_str().expect("owned name is a string");
        assert!(
            theory.owns(&Symbol::new(s.as_bytes().to_vec())),
            "owns({s:?}) = false, want true"
        );
    }
    for name in owns["not_owned"].as_array().expect("not_owned array") {
        let s = name.as_str().expect("not_owned name is a string");
        assert!(
            !theory.owns(&Symbol::new(s.as_bytes().to_vec())),
            "owns({s:?}) = true, want false"
        );
    }
}

#[test]
fn replay_identity_vector_matches_the_oracle() {
    let json = vectors();
    let id = ListTheory::new().identity();
    let want = &json["identity"];
    assert_eq!(
        id.id,
        want["id"].as_str().unwrap().as_bytes(),
        "identity id mismatch"
    );
    assert_eq!(
        id.version,
        want["version"].as_str().unwrap().as_bytes(),
        "identity version mismatch"
    );
    assert_eq!(
        id.config_digest, [0u8; 32],
        "identity config digest mismatch"
    );
}
