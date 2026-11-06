//! #3057: the injective escape is `Symbol`'s canonical rendering, so it lives beside `Symbol` in
//! the contract tier (seat:caa's ruling on #2984, site 3). This replays
//! `vectors/identity_bytes.json`'s `escaped_name` section against `logos_contract::escaped_name`
//! directly. `kernel/rs/tests/identity_bytes_vectors.rs` replays the same rows through the kernel's
//! re-export. The same rows are replayed at the contract tier in go
//! (`contract/go/escaped_name_3057_test.go`) and ts (`contract/ts/test/escaped_name_3057.test.ts`).

use logos_contract::escaped_name;
use serde_json::Value as Json;
use std::collections::BTreeMap;

// This source is in `contract/rs/tests/`, so `include_str!` (relative to the source file)
// reaches the repo root in three steps.
const VECTORS: &str = include_str!("../../../vectors/identity_bytes.json");

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("row hex"))
        .collect()
}

/// Every row renders to exactly `rendered`, and a row naming `collides_with` renders differently
/// from that row, where a lossy render gave both U+FFFD.
#[test]
fn escaped_name_vector_at_the_contract_tier_3057() {
    let v: Json = serde_json::from_str(VECTORS).expect("identity_bytes.json parses");
    let cases = v["escaped_name"]["cases"]
        .as_array()
        .expect("escaped_name.cases");
    assert!(!cases.is_empty(), "[escaped_name] carries no rows");
    let mut rendered = BTreeMap::new();
    for c in cases {
        let name = c["name"].as_str().expect("name");
        let got = escaped_name(&unhex(c["bytes_hex"].as_str().expect("bytes_hex")));
        assert_eq!(
            got,
            c["rendered"].as_str().expect("rendered"),
            "[escaped_name/{name}] rendered differently"
        );
        rendered.insert(name, got);
    }
    for c in cases {
        if let Some(other) = c["collides_with"].as_str() {
            let name = c["name"].as_str().expect("name");
            assert_ne!(
                rendered[name], rendered[other],
                "[escaped_name/{name}] renders as {other} does"
            );
        }
    }
}
