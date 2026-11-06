//! #2630 (`seat:caa`'s ruling on its checkpoint): an arity refusal names EVERY arity the reading
//! accepts, and a reading that accepts ONE keeps the exact text it always had, so no existing
//! refusal string moves when `DecodeError::Arity` starts carrying a set.

use logos_contract::derivation_wire::{arity_refusal, DecodeError};

#[test]
fn a_singleton_renders_the_text_arity_refusals_always_had() {
    // The pre-#2630 rendering, verbatim: `decode {ctx}: expected arity {expected}, got {got}`.
    for (ctx, one, got) in [
        ("subst.entry", 2, 3),
        ("node.rule", 6, 1),
        ("derivation wire v1", 2, 0),
    ] {
        assert_eq!(
            arity_refusal(ctx, &[one], got),
            format!("decode {ctx}: expected arity {one}, got {got}")
        );
    }
    let err = DecodeError::Arity {
        ctx: "node.leaf",
        accepted: &[3],
        got: 2,
    };
    assert_eq!(err.to_string(), "decode node.leaf: expected arity 3, got 2");
}

#[test]
fn a_set_renders_every_accepted_arity() {
    assert_eq!(
        arity_refusal("closed_world.cert", &[10, 11, 12], 13),
        "decode closed_world.cert: 13 elements, expected 10, 11 or 12"
    );
    assert_eq!(
        arity_refusal("derivation", &[2, 3], 4),
        "decode derivation: 4 elements, expected 2 or 3"
    );
}
