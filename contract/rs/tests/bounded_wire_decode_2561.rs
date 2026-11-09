//! #2561 (`seat:caa`'s ruling): `decode_derivation_wire_v1_bounded` holds a derivation wire's
//! certificates to the caller's `CheckLimits` BEFORE decoding. The wires are the real producer
//! derivations of `vectors/cert_encoded_bytes.json` (#2524), which go and ts decode in their twins.

use logos_contract::{
    cert_bytes_slack, cert_wire_spans, decode_derivation_wire_v1,
    decode_derivation_wire_v1_bounded, BoundedWireError, CertWireError, CheckLimits,
    DERIVATION_WIRE_V1_CERT_PATH,
};

const VECTOR: &str = include_str!("../../../vectors/cert_encoded_bytes.json");

#[cfg(target_pointer_width = "64")]
#[test]
fn invalid_proof_configuration_precedes_wire_inspection() {
    let certificate = wire("permit_one_certificate");
    for (field, _) in CheckLimits::default().budgets() {
        let mut limits = CheckLimits::default();
        let (_, value) = limits
            .budgets_mut()
            .into_iter()
            .find(|(name, _)| *name == field)
            .expect("a declared budget");
        *value = 1usize << 53;
        for frame in [&[][..], certificate.as_slice()] {
            let error = decode_derivation_wire_v1_bounded(frame, &limits)
                .expect_err("an invalid configuration cannot decode a proof");
            let BoundedWireError::InvalidLimits(invalid) = error else {
                panic!("invalid {field} was reported as {error}");
            };
            assert_eq!(invalid.field, field);
            assert_eq!(invalid.count, 1u64 << 53);
        }
    }
}

#[test]
fn portable_certificate_caps_accept_a_real_frame_when_the_host_can_represent_them() {
    let frame = wire("permit_one_certificate");
    for count in [u64::from(u32::MAX), 1u64 << 32, (1u64 << 53) - 1] {
        if let Ok(max_bytes) = usize::try_from(count) {
            decode_derivation_wire_v1_bounded(&frame, &limits(max_bytes))
                .expect("a small certificate fits this portable byte allowance");
        }
    }
}

/// A named case's derivation wire.
fn wire(name: &str) -> Vec<u8> {
    let v: serde_json::Value = serde_json::from_str(VECTOR).expect("the vector parses");
    let case = v["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|c| c["name"] == name)
        .unwrap_or_else(|| panic!("no case {name}"));
    let hex = case["derivation_wire"].as_str().expect("a wire");
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

fn limits(max_cert_bytes: usize) -> CheckLimits {
    CheckLimits {
        max_cert_bytes,
        ..CheckLimits::default()
    }
}

#[test]
fn a_certificate_over_the_callers_budget_is_refused_before_decoding_2561() {
    for name in ["permit_one_certificate", "stacked_two_certificates"] {
        let bytes = wire(name);
        let spans = cert_wire_spans(&bytes, &DERIVATION_WIRE_V1_CERT_PATH).expect("the walk");
        assert!(!spans.is_empty(), "{name}: the wire carries certificates");
        let largest = *spans.iter().max().expect("a span");
        let at = largest - cert_bytes_slack() as usize;
        // CONTROL: at max_cert_bytes + slack the bytes decode, to what the unbounded decoder reads.
        assert_eq!(
            decode_derivation_wire_v1_bounded(&bytes, &limits(at)),
            decode_derivation_wire_v1(&bytes).map_err(BoundedWireError::Decode),
            "{name}: read at max + slack"
        );
        match decode_derivation_wire_v1_bounded(&bytes, &limits(at - 1)) {
            Err(BoundedWireError::OverBudget { span, .. }) => assert_eq!(span, largest, "{name}"),
            other => {
                panic!("{name}: one byte past max + slack is refused undecoded, got {other:?}")
            }
        }
    }
}

#[test]
fn bytes_the_walk_cannot_read_are_refused_and_a_positive_wire_needs_no_budget_2561() {
    let bytes = wire("permit_one_certificate");
    assert_eq!(
        decode_derivation_wire_v1_bounded(&bytes[..bytes.len() / 2], &CheckLimits::default()),
        Err(BoundedWireError::Unreadable(CertWireError::Truncated))
    );
    let mut trailing = bytes.clone();
    trailing.push(0x00);
    assert_eq!(
        decode_derivation_wire_v1_bounded(&trailing, &CheckLimits::default()),
        Err(BoundedWireError::Unreadable(CertWireError::TrailingBytes))
    );
    // A readable, within-budget value that is not a derivation wire is the decoder's refusal.
    let not_a_wire = [0x01, 0x02, 0x00, 0x01, b'x', 0x01, 0x00];
    assert!(matches!(
        decode_derivation_wire_v1_bounded(&not_a_wire, &CheckLimits::default()),
        Err(BoundedWireError::Decode(_))
    ));
    // A codec capacity stop is the codec's own error, never the shape refusal (#2734 3c).
    let mut nested = Vec::new();
    for _ in 0..2000 {
        nested.extend_from_slice(&[0x01, 0x01]);
    }
    nested.extend_from_slice(&[0x00, 0x00]);
    match decode_derivation_wire_v1_bounded(&nested, &CheckLimits::default()) {
        Err(BoundedWireError::Stopped(stop)) => assert_eq!(stop.code(), "limit_exceeded"),
        other => panic!("a value past the codec's decode depth stops the codec, got {other:?}"),
    }
    // The refusal names are the hosts' (#2528).
    let e = decode_derivation_wire_v1_bounded(&bytes, &limits(0)).expect_err("over budget");
    assert!(e.to_string().starts_with("cert_wire_over_budget"), "{e}");
}
