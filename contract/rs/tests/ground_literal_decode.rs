//! #1914 — the public strict inverse of the ground-literal account representation,
//! exercised ONLY through the public contract surface: no derivation is fabricated and no
//! private decoder is copied. Positive cases round-trip; refusals name the class.

use logos_contract::{
    ground_literal_as_value, ground_literal_from_value_v1, quote, DecodeError, GroundLiteral,
    Symbol, Term,
};
use ontos_core::Value;

fn lit(pred: &[u8], args: Vec<Value>) -> GroundLiteral {
    GroundLiteral::new(Symbol::new(pred.to_vec()), args)
}

fn round_trip(l: &GroundLiteral) {
    let v = ground_literal_as_value(l);
    let back = ground_literal_from_value_v1(&v).expect("a valid encoding decodes");
    assert_eq!(&back, l);
    assert_eq!(
        ground_literal_as_value(&back),
        v,
        "re-encoding is byte-stable"
    );
}

#[test]
fn positive_cases_round_trip() {
    round_trip(&lit(b"p", vec![]));
    round_trip(&lit(
        b"pred with bytes \x00\xff",
        vec![Value::atom(b"a".to_vec())],
    ));
    round_trip(&lit(
        b"q",
        vec![Value::atom(Vec::new()), Value::atom(vec![0, 255, 7])],
    ));
    round_trip(&lit(
        b"nested",
        vec![Value::tuple([
            Value::atom(b"a".to_vec()),
            Value::tuple([
                Value::atom(b"b".to_vec()),
                Value::tuple(Vec::<Value>::new()),
            ]),
        ])],
    ));
}

/// An atom whose bytes spell a variable name is DATA: `quote` marks it as an atom, so it
/// survives the round trip as the atom `X`, never as a variable.
#[test]
fn data_that_looks_like_a_variable_is_preserved() {
    let l = lit(
        b"looks",
        vec![Value::atom(b"X".to_vec()), Value::atom(b"_".to_vec())],
    );
    round_trip(&l);
}

#[test]
fn refusals_name_the_class() {
    // missing predicate: the empty tuple
    assert!(matches!(
        ground_literal_from_value_v1(&Value::tuple(Vec::<Value>::new())),
        Err(DecodeError::Arity { .. })
    ));
    // non-atom predicate
    let bad_pred = Value::tuple([Value::tuple(Vec::<Value>::new())]);
    assert!(matches!(
        ground_literal_from_value_v1(&bad_pred),
        Err(DecodeError::Shape { .. })
    ));
    // an argument outside the image of quote: the RAW Ontos compound reading
    let raw = Value::tuple([Value::atom(b"p".to_vec()), Value::atom(b"a".to_vec())]);
    assert!(matches!(
        ground_literal_from_value_v1(&raw),
        Err(DecodeError::NotQuoted { .. })
    ));
    // a quoted VARIABLE: in the image of quote, but not ground
    let with_var = Value::tuple([Value::atom(b"p".to_vec()), quote(&Term::var("X"))]);
    assert!(matches!(
        ground_literal_from_value_v1(&with_var),
        Err(DecodeError::NotQuoted { .. })
    ));
    // a quoted tuple hiding a variable
    let nested_var = Value::tuple([
        Value::atom(b"p".to_vec()),
        quote(&Term::tuple([Term::atom(b"a".to_vec()), Term::var("Y")])),
    ]);
    assert!(matches!(
        ground_literal_from_value_v1(&nested_var),
        Err(DecodeError::NotQuoted { .. })
    ));
    // not a tuple at all
    assert!(matches!(
        ground_literal_from_value_v1(&Value::atom(b"p".to_vec())),
        Err(DecodeError::Shape { .. })
    ));
}
