//! Rust replay of the cross-core Shelf-B prelude-loader vector `vectors/prelude.json`,
//! plus a load of the shipped on-disk bundle `prelude/sample@1.0.0.json`.
//!
//! Each vector case is a complete prelude manifest plus the PINNED `load_prelude` outcome.
//! This replay drives the REAL [`logos_contract::load_prelude`] over each manifest (the
//! committed file is checked against the loader, not trusted blind) and asserts the
//! `{ok | err}` outcome. The SAME `vectors/prelude.json` is the oracle a Go/TS loader mirror
//! replays — the recomputed `program_digest` is byte-identical across {rs,go,ts} (frozen
//! `ontos-codec` + syntactic `VarId`), so search/check/loader cannot silently diverge.
//!
//! The trust anchor is digest re-derivation, not the JSON parser: the `digest_mismatch` and
//! `tampered_clause_rejected_by_digest` cases pin that a wrong clause set (or a wrong pinned
//! digest) is *refused*, never silently admitted.

use logos_contract::{load_prelude, PreludeBundle, PreludeError};
use serde_json::Value as Json;

// This source is in `contract/rs/tests/`, so `include_str!` reaches the repo root three
// levels up — same depth as the term/text/compound replays.
const VECTORS: &str = include_str!("../../../vectors/prelude.json");
const SAMPLE_BUNDLE: &str = include_str!("../../../prelude/sample@1.0.0.json");

/// The error variant tag the vector pins (mirrors `PreludeError`).
fn err_variant(e: &PreludeError) -> &'static str {
    match e {
        PreludeError::Malformed(_) => "malformed",
        PreludeError::BadClause { .. } => "bad_clause",
        PreludeError::ClauseIdMismatch { .. } => "clause_id_mismatch",
        PreludeError::DuplicateClauseId(_) => "duplicate_clause_id",
        PreludeError::DigestMismatch { .. } => "digest_mismatch",
        PreludeError::Empty => "empty",
    }
}

fn assert_ok(name: &str, expected: &Json, got: &PreludeBundle) {
    assert_eq!(
        got.name,
        expected["name"].as_str().expect("ok.name"),
        "{name}: bundle name"
    );
    assert_eq!(
        got.version,
        expected["version"].as_str().expect("ok.version"),
        "{name}: bundle version"
    );
    assert_eq!(
        got.program_digest,
        expected["program_digest"]
            .as_str()
            .expect("ok.program_digest"),
        "{name}: recomputed program_digest"
    );
    let want_ids: Vec<&str> = expected["clause_ids"]
        .as_array()
        .expect("ok.clause_ids")
        .iter()
        .map(|v| v.as_str().expect("clause id is a string"))
        .collect();
    let got_ids: Vec<&str> = got.clauses.iter().map(|(id, _)| id.as_str()).collect();
    assert_eq!(got_ids, want_ids, "{name}: clause ids (in manifest order)");
}

#[test]
fn replay_loader_vectors_match_the_loader() {
    let json: Json = serde_json::from_str(VECTORS).expect("vectors/prelude.json parses");
    let cases = json["cases"].as_array().expect("cases array");
    assert!(!cases.is_empty(), "no loader vectors loaded");
    let mut saw_ok = false;
    let mut saw_err = false;
    for case in cases {
        let name = case["name"].as_str().unwrap_or("<unnamed>");
        // Re-serialize the embedded manifest to the JSON string `load_prelude` consumes.
        let manifest = serde_json::to_string(&case["manifest"]).expect("manifest re-serializes");
        let got = load_prelude(&manifest);
        let outcome = &case["outcome"];
        if let Some(ok) = outcome.get("ok") {
            saw_ok = true;
            match got {
                Ok(bundle) => assert_ok(name, ok, &bundle),
                Err(e) => panic!("{name}: expected ok, got err {e:?}"),
            }
        } else if let Some(err) = outcome.get("err") {
            saw_err = true;
            let want = err.as_str().expect("err is a string");
            match got {
                Ok(bundle) => panic!("{name}: expected err {want}, got ok {bundle:?}"),
                Err(e) => assert_eq!(err_variant(&e), want, "{name}: error variant"),
            }
        } else {
            panic!("{name}: outcome is neither ok nor err: {outcome}");
        }
    }
    assert!(
        saw_ok && saw_err,
        "vectors must cover both ok and err paths"
    );
}

#[test]
fn shipped_sample_bundle_loads_and_matches_vector() {
    // The on-disk `prelude/sample@1.0.0.json` must load with the same pins the vector commits.
    let bundle = load_prelude(SAMPLE_BUNDLE).expect("prelude/sample@1.0.0.json loads");
    assert_eq!(bundle.name, "sample");
    assert_eq!(bundle.version, "1.0.0");
    assert_eq!(
        bundle.program_digest,
        "cb22fbb4f7fcaf55de33742c2ad0328cc9f964bbb97b62ab508fced396fbb5a7"
    );
    assert_eq!(bundle.clauses.len(), 2);

    // The shipped bundle's pins must equal the `valid_sample_bundle_loads` vector case.
    let json: Json = serde_json::from_str(VECTORS).unwrap();
    let case = json["cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|c| c["name"] == "valid_sample_bundle_loads")
        .expect("valid_sample_bundle_loads case present");
    assert_ok("shipped sample bundle", &case["outcome"]["ok"], &bundle);
}
