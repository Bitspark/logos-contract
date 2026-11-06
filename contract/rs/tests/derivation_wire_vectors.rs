use logos_contract::{
    decode_derivation_wire_v1, encode_derivation_wire_v1, CertSizeDecl, ClauseId, ClosedModelCert,
    Derivation, Evidence, FiniteDomain, GroundLiteral, Node, NodeMeta, PredicateRef, Premise,
    ProjectSpec, RelationTable, StratumPrefix, Subst, SupportWitness, Symbol,
};
use ontos_core::Value;
use serde_json::Value as Json;

const VECTORS: &str = include_str!("../../../vectors/derivation_wire.json");

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

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

fn lit(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| atom(a)))
}

fn zero_hash() -> [u8; 32] {
    [0; 32]
}

fn closed_cert() -> ClosedModelCert {
    let pred = Symbol::new(b"sealed".to_vec());
    let row = lit("sealed", &["a"]);
    ClosedModelCert {
        scope: StratumPrefix::new(0, [pred.clone()]),
        program_hash: zero_hash(),
        profile_hash: zero_hash(),
        ctx_hash: zero_hash(),
        theory_config_hash: zero_hash(),
        edb_snapshot_hashes: Vec::new(),
        domains: vec![FiniteDomain::new("entity", [atom("a")])],
        extensions: vec![RelationTable::new(pred, 1, [row])],
        supports: SupportWitness::default(),
        closure: Default::default(),
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 1,
            support_edges: 0,
            rule_groundings: 0,
            join_steps: 0,
            cert_bytes: 0,
        },
    }
}

fn fixture(name: &str) -> Derivation {
    match name {
        "leaf" => Derivation::new(
            [Node::Leaf {
                conclusion: lit("edge", &["a", "b"]),
                evidence: Evidence::none(),
            }],
            0,
        ),
        "builtin" => Derivation::new(
            [Node::Builtin {
                conclusion: lit("=", &["a", "a"]),
            }],
            0,
        ),
        "rule" => Derivation::new(
            [
                Node::Leaf {
                    conclusion: lit("edge", &["a", "b"]),
                    evidence: Evidence::none(),
                },
                Node::Rule {
                    conclusion: lit("path", &["a", "b"]),
                    clause: ClauseId::new("path#edge"),
                    subst: Subst::new(),
                    premises: vec![Premise::pos(0)],
                    meta: NodeMeta::none(),
                },
            ],
            1,
        ),
        "closed_world_count" => Derivation::with_closed_world(
            [Node::Rule {
                conclusion: lit("has_count", &["a"]),
                clause: ClauseId::new("count#sealed"),
                subst: Subst::new(),
                premises: vec![Premise::Count {
                    pred: PredicateRef::new("sealed", 1),
                    filter: vec![(0, atom("a"))],
                    project: ProjectSpec::Rows,
                    k: ontos_data::encode_int(1),
                    cert: 0.into(),
                }],
                meta: NodeMeta::none(),
            }],
            0,
            [closed_cert()],
        ),
        // ADR 0030 D4: the twelve-element cert — the D10 witness at slot 11 AND a partial
        // sub-scope at slot 12. Byte-identical to the RED-first `malformed` entry of b1d3d5a7
        // (which every pre-0030 decoder refused by arity): the flip was the decoder, not the
        // fixture. A WIRE fixture only — the level-1 partial scope over a level-0 seal is not a
        // checkable cert (check() refuses `cert_partial_scope_invalid` on the level mismatch).
        "closed_world_count_partial" => {
            let mut cert = closed_cert();
            cert.decomposition_witness = Some([0xd1u8; 32]);
            cert.partial_scope = Some(StratumPrefix::new(1, [Symbol::new(b"sealed".to_vec())]));
            Derivation::with_closed_world(
                [Node::Rule {
                    conclusion: lit("has_count", &["a"]),
                    clause: ClauseId::new("count#sealed"),
                    subst: Subst::new(),
                    premises: vec![Premise::Count {
                        pred: PredicateRef::new("sealed", 1),
                        filter: vec![(0, atom("a"))],
                        project: ProjectSpec::Rows,
                        k: ontos_data::encode_int(1),
                        cert: 0.into(),
                    }],
                    meta: NodeMeta::none(),
                }],
                0,
                [cert],
            )
        }
        other => panic!("unknown derivation_wire fixture {other}"),
    }
}

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("vectors/derivation_wire.json parses")
}

#[test]
fn positive_derivation_wire_bytes_match_and_round_trip() {
    let json = vectors();
    for case in json["positive"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let want = case["wire_hex"].as_str().unwrap();
        let deriv = fixture(name);
        let bytes = encode_derivation_wire_v1(&deriv);
        assert_eq!(to_hex(&bytes), want, "wire bytes mismatch for {name}");
        let decoded = decode_derivation_wire_v1(&bytes).expect("decodes");
        assert_eq!(
            to_hex(&encode_derivation_wire_v1(&decoded)),
            want,
            "round-trip bytes mismatch for {name}"
        );
    }
}

#[test]
fn malformed_derivation_wire_vectors_reject() {
    let json = vectors();
    let malformed = json["malformed"].as_array().unwrap();
    assert!(!malformed.is_empty(), "the vector has malformed rows");
    for case in malformed {
        let name = case["name"].as_str().unwrap();
        let bytes = hex_to_bytes(case["wire_hex"].as_str().unwrap());
        let err = decode_derivation_wire_v1(&bytes)
            .expect_err(&format!("malformed case {name} unexpectedly decoded"));
        // #2630: the one decoder's refusal text, byte-identical in all three cores.
        let want = case["refusal"]
            .as_str()
            .unwrap_or_else(|| panic!("malformed case {name} states no refusal"));
        assert_eq!(
            err.to_string(),
            want,
            "malformed case {name}: the refusal text"
        );
    }
}

/// #2630 (`seat:caa`'s ruling on #2645): wires the decoder must ACCEPT. A root that indexes no
/// node passes through (check refuses it as root_out_of_range), and a subst in canonical order
/// decodes; each re-encodes byte for byte.
#[test]
fn decodes_derivation_wire_vectors_are_accepted_and_round_trip() {
    let json = vectors();
    let decodes = json["decodes"].as_array().expect("decodes rows");
    assert!(!decodes.is_empty(), "the vector has decodes rows");
    for case in decodes {
        let name = case["name"].as_str().unwrap();
        let wire = case["wire_hex"].as_str().unwrap();
        let decoded = decode_derivation_wire_v1(&hex_to_bytes(wire))
            .unwrap_or_else(|e| panic!("decodes case {name} was refused: {e}"));
        assert_eq!(
            decoded.root as u64,
            case["root"].as_u64().unwrap(),
            "{name}: root"
        );
        assert_eq!(
            decoded.nodes.len() as u64,
            case["nodes"].as_u64().unwrap(),
            "{name}: node count"
        );
        assert_eq!(
            to_hex(&encode_derivation_wire_v1(&decoded)),
            wire,
            "{name}: re-encodes byte for byte"
        );
    }
}

// ============== decode refuses non-canonical cert collections (issue #839) ==============
// The wire encoding promises sorted+deduped cert collections; the decoder CHECKS that
// promise instead of assuming it (rs/go previously admitted the bytes verbatim - a
// defeated binary search downstream - while ts silently re-sorted them - a repaired
// producer bug and a tri-core verdict divergence on identical bytes). Proof-carrying
// data is rejected, never fixed up: each case encodes a struct-literal cert violating
// one collection's invariant and asserts decode refuses it.

fn cert_derivation(cert: ClosedModelCert) -> Derivation {
    Derivation::with_closed_world(
        [Node::Rule {
            conclusion: lit("has_count", &["a"]),
            clause: ClauseId::new("count#sealed"),
            subst: Subst::new(),
            premises: vec![Premise::Count {
                pred: PredicateRef::new("sealed", 1),
                filter: vec![(0, atom("a"))],
                project: ProjectSpec::Rows,
                k: ontos_data::encode_int(1),
                cert: 0.into(),
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    )
}

#[test]
fn decode_refuses_unsorted_domain_values() {
    let mut cert = closed_cert();
    cert.domains = vec![FiniteDomain {
        type_tag: Symbol::new(b"entity".to_vec()),
        values: vec![atom("b"), atom("a")], // unsorted on the wire
    }];
    let bytes = encode_derivation_wire_v1(&cert_derivation(cert));
    let err = decode_derivation_wire_v1(&bytes).expect_err("unsorted domain must not decode");
    assert!(
        err.to_string().contains("closed_world.cert.domain.values"),
        "error must name the collection, got: {err}"
    );
}

#[test]
fn decode_refuses_duplicated_domain_values() {
    let mut cert = closed_cert();
    cert.domains = vec![FiniteDomain {
        type_tag: Symbol::new(b"entity".to_vec()),
        values: vec![atom("a"), atom("a")], // sorted but not deduped
    }];
    let bytes = encode_derivation_wire_v1(&cert_derivation(cert));
    decode_derivation_wire_v1(&bytes).expect_err("duplicated domain values must not decode");
}

#[test]
fn decode_refuses_unsorted_scope_predicates() {
    let mut cert = closed_cert();
    cert.scope = StratumPrefix {
        level: 0,
        predicates: vec![Symbol::new(b"sealed".to_vec()), Symbol::new(b"al".to_vec())],
    };
    let bytes = encode_derivation_wire_v1(&cert_derivation(cert));
    let err = decode_derivation_wire_v1(&bytes).expect_err("unsorted scope must not decode");
    assert!(
        err.to_string()
            .contains("closed_world.cert.scope.predicates"),
        "error must name the collection, got: {err}"
    );
}

#[test]
fn decode_refuses_unsorted_extension_rows() {
    let mut cert = closed_cert();
    cert.extensions = vec![RelationTable {
        pred: Symbol::new(b"sealed".to_vec()),
        arity: 1,
        rows: vec![lit("sealed", &["b"]), lit("sealed", &["a"])],
    }];
    let bytes = encode_derivation_wire_v1(&cert_derivation(cert));
    let err = decode_derivation_wire_v1(&bytes).expect_err("unsorted rows must not decode");
    assert!(
        err.to_string().contains("closed_world.cert.extension.rows"),
        "error must name the collection, got: {err}"
    );
}

/// The canonical fixture still round-trips - the decode checks reject only genuinely
/// non-canonical collections, never well-formed certs.
#[test]
fn decode_still_accepts_canonical_cert() {
    let deriv = cert_derivation(closed_cert());
    let bytes = encode_derivation_wire_v1(&deriv);
    let back = decode_derivation_wire_v1(&bytes).expect("canonical cert decodes");
    assert_eq!(deriv, back);
}
