//! #2233: `load_prelude` refuses a lone UTF-16 surrogate escape, which go's `encoding/json` and a
//! permissive ts parse would silently turn into U+FFFD, merging two distinct authored names. The
//! same witnesses are pinned in contract/go and contract/ts.
//!
//! The raw-bytes witness (PJ2, bytes that are not UTF-8) has no rs form: `load_prelude` takes a
//! `&str`, so such a document cannot reach it. The caller's UTF-8 decode is where rs refuses it.

use logos_contract::{load_prelude, PreludeBundle, PreludeError, Term};

/// `p(X,Y) :- q(X), r(Y)` with the two variable names spliced in as raw JSON string contents.
fn clause(x: &str, y: &str) -> String {
    format!(
        r#"{{"head":{{"pred":"p","args":[{{"var":"{x}"}},{{"var":"{y}"}}]}},"body":[{{"pred":"q","args":[{{"var":"{x}"}}]}},{{"pred":"r","args":[{{"var":"{y}"}}]}}]}}"#
    )
}

/// Load a one-clause bundle, pinning the digest the loader recomputes, so only a refusal BEFORE
/// the digest check can fail it.
fn load(clause_json: &str) -> Result<PreludeBundle, PreludeError> {
    let doc = format!(
        r#"{{"name":"t","version":"0.0.0","program_digest":"DIGEST","clauses":[{{"clause":{clause_json}}}]}}"#
    );
    match load_prelude(&doc) {
        Err(PreludeError::DigestMismatch { recomputed, .. }) => {
            load_prelude(&doc.replace("DIGEST", &recomputed))
        }
        other => other,
    }
}

#[test]
fn a_lone_surrogate_escape_is_refused_2233() {
    for (name, x, y) in [
        ("PJ1 lone surrogate escapes", r"\ud800", r"\udc00"),
        (
            "a high surrogate followed by a non-surrogate escape",
            r"\ud800\u0041",
            "Y",
        ),
        ("a lone low surrogate", "X", r"\udfff"),
    ] {
        match load(&clause(x, y)) {
            Err(PreludeError::Malformed(_)) => {}
            other => panic!("{name}: got {other:?}, want Malformed"),
        }
    }
}

#[test]
fn well_formed_names_still_load_distinct_2233() {
    for (name, x, y) in [
        ("PJ0 control", "X", "Y"),
        (
            "a surrogate PAIR each (U+1F600, U+1F601)",
            r"\ud83d\ude00",
            r"\ud83d\ude01",
        ),
    ] {
        let bundle = load(&clause(x, y)).unwrap_or_else(|e| panic!("{name}: refused: {e:?}"));
        let head = &bundle.clauses[0].1.head;
        match head.args.as_slice() {
            [Term::Var(a), Term::Var(b)] => assert_ne!(a, b, "{name}: the head variables merged"),
            other => panic!("{name}: unexpected head {other:?}"),
        }
    }
}
