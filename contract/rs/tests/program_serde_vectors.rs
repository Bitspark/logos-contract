//! Rust replay of the cross-core program-(de)serialization byte-pin vector
//! `vectors/program_serde.json` (logos-contract §10, issue #310).
//!
//! Each case rebuilds a `MapProgram` from the vector's `(id, head, body)` clause set
//! (authored in a deliberately NON-sorted insertion order), drives the REAL
//! [`program_to_value`]/[`program_from_value`], and asserts:
//!   * the `ontos-codec-v1` bytes of `program_to_value(p)` equal the pinned
//!     `program_bytes_hex` (the canonical, insertion-order-independent encoding), and
//!   * `program_from_value(program_to_value(p))` round-trips back to the same program.
//!
//! The SAME file is replayed by the Go binding (`contract/go/program_serde_vectors_test.go`)
//! and the TS binding (`contract/ts/test/program_serde_vectors.test.ts`), so one byte-pin
//! oracle pins all three cores: the frozen `ontos-codec`, the syntactic §2a `quote` tags,
//! and the canonical (sorted-by-id) clause order pin the SAME bytes across {rs,go,ts}. A
//! drift in any core's program encoding fails here AND in Go/TS.
//!
//! Per `vectors/README.md` the vector is hand-authored from the spec; this replay
//! re-derives the bytes through the real serializer — the committed file is checked
//! against the implementation, not trusted blind.

use logos_contract::intval::BigInt;
use logos_contract::{
    program_bytes, program_from_value, program_to_value, BodyLit, Clause, ClauseId,
    CompleteProgram, Goal, MapProgram, Program, Symbol, Term,
};
use serde_json::Value as Json;

// This source is in `contract/rs/tests/`, so `include_str!` reaches the repo root three
// levels up — same depth as the term/text/compound/prelude replays.
const VECTORS: &str = include_str!("../../../vectors/program_serde.json");

fn hex_to_bytes(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "hex must be even length: {s:?}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Build a `Term` from the vector arg notation (mirrors account.json / term.json):
/// `{atom:<hex>}` | `{atom_str:<utf8>}` | `{tuple:[term...]}` | `{int:N}` | `{var:<id>}`.
fn term_from_json(j: &Json) -> Term {
    let obj = j
        .as_object()
        .unwrap_or_else(|| panic!("term not an object: {j}"));
    if let Some(a) = obj.get("atom") {
        Term::atom(hex_to_bytes(a.as_str().unwrap()))
    } else if let Some(a) = obj.get("atom_str") {
        Term::atom(a.as_str().unwrap().as_bytes().to_vec())
    } else if let Some(n) = obj.get("int") {
        BigInt::from_i128(i128::from(n.as_i64().expect("int arg is an i64"))).to_int_term()
    } else if let Some(t) = obj.get("tuple") {
        Term::tuple(
            t.as_array()
                .unwrap()
                .iter()
                .map(term_from_json)
                .collect::<Vec<_>>(),
        )
    } else if let Some(v) = obj.get("var") {
        Term::var(v.as_str().unwrap())
    } else {
        panic!("unrecognized term shape: {j}");
    }
}

fn goal_from_json(j: &Json) -> Goal {
    let pred = Symbol::new(j["pred"].as_str().unwrap().as_bytes().to_vec());
    let args = j["args"]
        .as_array()
        .unwrap()
        .iter()
        .map(term_from_json)
        .collect::<Vec<_>>();
    Goal { pred, args }
}

/// A body literal: a bare goal (positive) or `{neg:<goal>}` (negated).
fn body_lit_from_json(j: &Json) -> BodyLit<Term> {
    if let Some(neg) = j.get("neg") {
        BodyLit::Neg(goal_from_json(neg))
    } else {
        BodyLit::Pos(goal_from_json(j))
    }
}

/// Rebuild a clause from its head + body json.
fn clause_from_json(c: &Json) -> Clause {
    let head = goal_from_json(&c["head"]);
    let body = c["body"]
        .as_array()
        .unwrap()
        .iter()
        .map(body_lit_from_json)
        .collect::<Vec<_>>();
    Clause::new(head, body)
}

/// Rebuild the program in the vector's INSERTION order (the canonical sort is the
/// serializer's job, exercised by the byte pin).
fn build_program(clauses: &[Json]) -> MapProgram {
    let mut p = MapProgram::new();
    for c in clauses {
        p.insert(
            ClauseId::new(c["id"].as_str().unwrap()),
            clause_from_json(c),
        );
    }
    p
}

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("vectors/program_serde.json parses")
}

#[test]
fn empty_program_bytes_match_the_pin() {
    let json = vectors();
    let want = json["empty_program"]["program_bytes_hex"].as_str().unwrap();
    assert_eq!(
        to_hex(&program_bytes(&MapProgram::new()).expect("serializes")),
        want,
        "empty program canonical bytes mismatch"
    );
}

#[test]
fn representative_program_bytes_match_the_pin_and_round_trip() {
    let json = vectors();
    let prog_j = &json["program"];
    let clauses = prog_j["clauses"].as_array().expect("clauses array");
    assert!(!clauses.is_empty(), "no program clauses loaded");
    let program = build_program(clauses);

    // 1. The canonical bytes match the pin (insertion-order-independent encoding).
    let want = prog_j["program_bytes_hex"].as_str().unwrap();
    assert_eq!(
        to_hex(&program_bytes(&program).expect("serializes")),
        want,
        "program canonical bytes mismatch"
    );

    // 2. Round-trip: program_from_value(program_to_value(p)) == p.
    let value = program_to_value(&program).expect("serializes");
    let back = program_from_value(&value).expect("round-trips");
    let mut ids_p: Vec<String> = Vec::new();
    program.for_each_clause(&mut |id, _| ids_p.push(id.as_str().to_string()));
    let mut ids_b: Vec<String> = Vec::new();
    back.for_each_clause(&mut |id, _| ids_b.push(id.as_str().to_string()));
    assert_eq!(ids_p, ids_b, "round-trip clause id set differs");
    program.for_each_clause(&mut |id, clause| {
        assert_eq!(
            back.clause(id),
            Some(clause),
            "round-trip clause {} differs",
            id.as_str()
        );
    });
}

#[test]
fn per_clause_bytes_match_the_pins() {
    // Cross-check each clause's account-codec bytes (the per-entry clause_value) against
    // the vector's clause_bytes_hex — so a divergence is localized to a clause.
    let json = vectors();
    for c in json["program"]["clauses"].as_array().unwrap() {
        let clause = clause_from_json(c);
        let want = c["clause_bytes_hex"].as_str().unwrap();
        assert_eq!(
            to_hex(&logos_contract::clause_bytes(&clause)),
            want,
            "clause_bytes mismatch for {}",
            c["id"].as_str().unwrap()
        );
    }
}

#[test]
fn map_program_iter_matches_canonical_clause_order() {
    // Drive the public ordered enumeration (`MapProgram::iter` / `len`) over the vector
    // program — built in a deliberately NON-sorted insertion order — and assert the (id)
    // order it yields equals the pinned `canonical_clause_order` (the same sorted-by-id
    // order the serializer emits and the Go/TS bindings reproduce). The cross-core proof
    // that the new iteration order is byte-identical tri-core (issue #368).
    let json = vectors();
    let prog_j = &json["program"];
    let clauses = prog_j["clauses"].as_array().unwrap();
    let program = build_program(clauses);
    let pinned: Vec<&str> = prog_j["canonical_clause_order"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();

    assert_eq!(program.len(), clauses.len(), "len mismatch");
    let iter_ids: Vec<&str> = program.iter().map(|(id, _)| id.as_str()).collect();
    assert_eq!(
        iter_ids, pinned,
        "MapProgram::iter order must equal the pinned canonical_clause_order"
    );
    // The clause paired with each id is the one `clause(id)` returns.
    for (id, clause) in program.iter() {
        assert_eq!(
            program.clause(id),
            Some(clause),
            "iter clause for {} differs",
            id.as_str()
        );
    }
}

#[test]
fn canonical_clause_order_is_sorted_by_id() {
    // The serializer emits entries sorted by clause-id bytes; assert the pinned
    // canonical_clause_order matches a defensive sort of the authored ids.
    let json = vectors();
    let prog_j = &json["program"];
    let mut authored: Vec<&str> = prog_j["clauses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| c["id"].as_str().unwrap())
        .collect();
    authored.sort_unstable();
    let pinned: Vec<&str> = prog_j["canonical_clause_order"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap())
        .collect();
    assert_eq!(
        authored, pinned,
        "canonical clause order must be sorted by id"
    );
}
