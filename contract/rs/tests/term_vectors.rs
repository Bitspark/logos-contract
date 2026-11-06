//! Rust replay of the cross-core THEORY-DECISION agreement vector `vectors/term.json`.
//!
//! The [`TermTheory`] `decide` is asserted to reproduce the committed vector on every
//! ground term atom (the A0 recognizers + standard-order comparisons). The SAME file is
//! replayed by the Go binding (`contract/go/term_vectors_test.go`) and the TS binding
//! (`contract/ts/test/term_vectors.test.ts`), so one oracle — the search-side builtins
//! (`builtin_atom`/`…`/`builtin_order_lt`/`…` in `core/rs/src/builtins.rs`, sharing the
//! contract's `compare_values` standard order) — pins all three cores (the §7
//! dual-conformance / tri-core byte-parity law). A change to the recognizers' or order's
//! judgments fails here AND in Go/TS, so search/check and the cores can never silently
//! diverge.
//!
//! Per `vectors/README.md`, the vector is *hand-authored from the spec*; this replay
//! re-derives every outcome through the REAL `TermTheory::decide` — the committed file is
//! checked against the oracle, not trusted blind.

use logos_contract::intval::BigInt;
use logos_contract::{GroundLiteral, Symbol, Term, TermTheory, Theory, TheoryOutcome};
use serde_json::Value as Json;

// This source is in `contract/rs/tests/`, so `include_str!` (relative to the source file)
// reaches the repo root three levels up — same depth as the text/compound replays.
const VECTORS: &str = include_str!("../../../vectors/term.json");

/// Build the ontos `Value` an arg object denotes, matching the structural encoding in
/// `vectors/term.json` (and the Go/TS replays) EXACTLY:
///
/// * `{"atom": "<utf8>"}`     → a bare `Atom` of those UTF-8 bytes;
/// * `{"int": N}`             → the frozen ontos-data `int` embedding (a `Tuple`);
/// * `{"decimal": "<d.ddd>"}` → the frozen ontos-data `decimal` embedding (#331);
/// * `{"tuple": [..]}`        → a raw `Tuple` of the encoded children.
fn build_arg(arg: &Json) -> Term {
    let obj = arg
        .as_object()
        .unwrap_or_else(|| panic!("arg is not an object: {arg}"));
    if let Some(a) = obj.get("atom") {
        let s = a.as_str().expect("atom arg is a string");
        return Term::atom(s.as_bytes().to_vec());
    }
    if let Some(n) = obj.get("int") {
        let n = n
            .as_i64()
            .unwrap_or_else(|| panic!("int arg not an i64: {n}"));
        return BigInt::from_i128(i128::from(n)).to_int_term();
    }
    if let Some(d) = obj.get("decimal") {
        let s = d.as_str().expect("decimal arg is a string");
        return logos_contract::BigDecimal::from_decimal_str(s)
            .unwrap_or_else(|| panic!("decimal {s:?} is not a decimal literal"))
            .to_decimal_term();
    }
    if let Some(children) = obj.get("tuple") {
        let children = children.as_array().expect("tuple arg is an array");
        return Term::tuple(children.iter().map(build_arg));
    }
    panic!("unrecognized arg shape: {arg}");
}

/// Build the ground atom for one decision entry.
fn build_atom(entry: &Json) -> GroundLiteral {
    let pred = entry["pred"].as_str().expect("pred is a string");
    let args = entry["args"].as_array().expect("args is an array");
    let values = args
        .iter()
        .map(|a| {
            build_arg(a)
                .erase_ground()
                .expect("a decision-vector arg must be ground")
        })
        .collect::<Vec<_>>();
    GroundLiteral::new(pred, values)
}

/// Assert the actual outcome matches the pinned `"holds" | {"fails": code}` outcome.
fn assert_outcome(name: &str, expected: &Json, got: &TheoryOutcome) {
    if let Some(s) = expected.as_str() {
        assert_eq!(s, "holds", "{name}: unknown string outcome {s:?}");
        assert!(
            matches!(got, TheoryOutcome::Holds),
            "{name}: want Holds, got {got:?}"
        );
        return;
    }
    let code = expected["fails"].as_str().unwrap_or_else(|| {
        panic!("{name}: outcome is neither \"holds\" nor {{fails}}: {expected}")
    });
    match got {
        TheoryOutcome::Fails { code: got_code } => {
            assert_eq!(got_code, code, "{name}: fail-code mismatch");
        }
        other => panic!("{name}: want Fails{{{code}}}, got {other:?}"),
    }
}

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("vectors/term.json parses")
}

#[test]
fn replay_decision_vectors_match_the_oracle() {
    let json = vectors();
    let theory = TermTheory::new();
    let decisions = json["decisions"].as_array().expect("decisions array");
    assert!(!decisions.is_empty(), "no decision vectors loaded");
    for entry in decisions {
        let name = entry["name"].as_str().unwrap_or("<unnamed>");
        let atom = build_atom(entry);
        let got = theory.decide(&atom);
        assert_outcome(name, &entry["outcome"], &got);
    }
}

#[test]
fn replay_owns_vector_matches_the_oracle() {
    let json = vectors();
    let theory = TermTheory::new();
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
    let id = TermTheory::new().identity();
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
