//! Rust replay of the cross-core agreement vector `vectors/compound.json`.
//!
//! [`CompoundTheory`] composed of `[ArithmeticTheory, TextTheory]` (in that order) is
//! asserted to reproduce the committed vector: the routed `decide` on every ground atom,
//! the `owns` union, AND the identity config-digest (a length-prefixed SHA-256 over the
//! ordered member identities). The SAME file is replayed by the Go binding
//! (`contract/go/compound_vectors_test.go`) and the TS binding
//! (`contract/ts/test/compound_vectors.test.ts`), so one oracle pins the compound's
//! routing + digest scheme across all three cores (the tri-core byte-parity law). The
//! identity digest in particular is the trust-critical artifact: a certifying kernel
//! derives a check-profile digest from a bound theory's identity, so a Rust and a Go
//! consumer that bind `Compound(Arithmetic, Text)` MUST compute the identical digest or
//! their certificates would not interoperate.

use logos_contract::intval::BigInt;
use logos_contract::{
    ArithmeticTheory, CompoundTheory, GroundLiteral, Symbol, TextTheory, Theory, TheoryOutcome,
};
use serde_json::Value as Json;

// This source is in `contract/rs/tests/`, so `include_str!` reaches the repo root three
// levels up — same depth as the arithmetic/text replays.
const VECTORS: &str = include_str!("../../../vectors/compound.json");

/// Build the ontos `Value` an arg object denotes, matching the structural encoding in
/// `vectors/compound.json` (and the Go/TS replays) EXACTLY — the same grammar as the
/// arithmetic/text replays:
///
/// * `{"int": N}`                 → the ontos-data `int` embedding of `N`;
/// * `{"text": "<s>"}`            → the ontos-data `utf8-text` embedding (a `Tuple`);
/// * `{"atom": "<utf8>"}`         → a bare `Atom` of those UTF-8 bytes;
/// * `{"op": "<op>", "args": []}` → an operator compound `Tuple(Atom(op), arg…)`;
/// * `{"tuple": [..]}`            → a raw `Tuple` of the encoded children.
fn build_arg(arg: &Json) -> logos_contract::Term {
    use logos_contract::Term;
    let obj = arg
        .as_object()
        .unwrap_or_else(|| panic!("arg is not an object: {arg}"));
    if let Some(n) = obj.get("int") {
        let n = n
            .as_i64()
            .unwrap_or_else(|| panic!("int arg not an i64: {n}"));
        return BigInt::from_i128(i128::from(n)).to_int_term();
    }
    if let Some(t) = obj.get("text") {
        let s = t.as_str().expect("text arg is a string");
        return Term::from_value(&ontos_data::encode_text(s));
    }
    if let Some(a) = obj.get("atom") {
        let s = a.as_str().expect("atom arg is a string");
        return Term::atom(s.as_bytes().to_vec());
    }
    if let Some(op) = obj.get("op") {
        let op = op.as_str().expect("op arg is a string");
        let args = obj
            .get("args")
            .and_then(Json::as_array)
            .expect("op arg has an args array");
        let mut children = Vec::with_capacity(args.len() + 1);
        children.push(Term::atom(op.as_bytes().to_vec()));
        children.extend(args.iter().map(build_arg));
        return Term::tuple(children);
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

/// Build the `CompoundTheory` the vector names, mapping each member string to its theory.
fn build_compound(members: &[Json]) -> CompoundTheory {
    let theories: Vec<Box<dyn Theory + Send + Sync>> = members
        .iter()
        .map(|m| match m.as_str().expect("member is a string") {
            "arithmetic" => Box::new(ArithmeticTheory::new()) as Box<dyn Theory + Send + Sync>,
            "text" => Box::new(TextTheory::new()) as Box<dyn Theory + Send + Sync>,
            other => panic!("unknown member theory {other:?}"),
        })
        .collect();
    CompoundTheory::new(theories)
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
    serde_json::from_str(VECTORS).expect("vectors/compound.json parses")
}

fn members(json: &Json) -> Vec<Json> {
    json["members"].as_array().expect("members array").clone()
}

#[test]
fn replay_decision_vectors_route_to_the_owning_member() {
    let json = vectors();
    let theory = build_compound(&members(&json));
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
fn replay_owns_vector_is_the_union() {
    let json = vectors();
    let theory = build_compound(&members(&json));
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
fn replay_identity_vector_matches_the_membership_digest() {
    let json = vectors();
    let id = build_compound(&members(&json)).identity();
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
    let got_hex: String = id
        .config_digest
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        got_hex,
        want["config_digest_hex"].as_str().unwrap(),
        "identity config_digest mismatch (the length-prefixed SHA-256 over the ordered \
         member identities must match the pinned hex byte-for-byte)"
    );
}
