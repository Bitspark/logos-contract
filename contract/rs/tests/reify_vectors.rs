//! Rust replay of `vectors/reify.json` (#3102): §2a's `reify` decision, pinned as a shared fact.
//!
//! Before #3102 go's `Reify` accepted a quoted variable whose name is not UTF-8
//! (`Tuple[Atom(0x02), Atom(0xFF)]` reified to a variable), while rs and ts refused it. The three
//! cores decode one untrusted input, so their agreement is replayed from one hand-authored file
//! (the same file `contract/go/reify_vectors_test.go` and `contract/ts/test/reify_vectors.test.ts`
//! replay) rather than claimed in a comment.

use logos_contract::{quote, reify, Term, VarId};
use ontos_core::Value;
use serde_json::Value as Json;

const VECTORS: &str = include_str!("../../../vectors/reify.json");

fn hex_to_bytes(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "hex must be even length: {s:?}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The rows of one section, refusing an empty one: a replay over no rows proves nothing.
fn section<'a>(file: &'a Json, key: &str) -> &'a [Json] {
    let rows = file[key]
        .as_array()
        .unwrap_or_else(|| panic!("section {key:?} is not an array"));
    assert!(!rows.is_empty(), "section {key:?} is empty");
    rows
}

/// A row's value bytes, and what `reify` makes of the decoded value.
fn reified(row: &Json) -> (String, Vec<u8>, Option<Term>) {
    let name = row["name"].as_str().expect("a row has a name").to_owned();
    let raw = hex_to_bytes(row["value_hex"].as_str().expect("a row has value_hex"));
    let value = ontos_codec::decode(&raw)
        .unwrap_or_else(|e| panic!("{name}: the value does not decode: {e:?}"));
    let term = reify(&value);
    (name, raw, term)
}

/// The term a row describes: `{"var": name}`, `{"atom_hex": bytes}` or `{"tuple": [terms]}`.
fn described(name: &str, desc: &Json) -> Term {
    let obj = desc
        .as_object()
        .filter(|o| o.len() == 1)
        .unwrap_or_else(|| panic!("{name}: a term is an object with one key, got {desc}"));
    let (kind, body) = obj.iter().next().expect("one key");
    match kind.as_str() {
        "var" => Term::Var(VarId::new(body.as_str().expect("var is a string"))),
        "atom_hex" => Term::atom(hex_to_bytes(body.as_str().expect("atom_hex is a string"))),
        "tuple" => Term::tuple(
            body.as_array()
                .expect("tuple is an array")
                .iter()
                .map(|kid| described(name, kid)),
        ),
        other => panic!("{name}: unknown term kind {other:?}"),
    }
}

#[test]
fn reify_vectors_3102() {
    let file: Json = serde_json::from_str(VECTORS).expect("vectors/reify.json parses");
    for key in file.as_object().expect("the file is an object").keys() {
        assert!(
            matches!(
                key.as_str(),
                "spec" | "note" | "refused" | "reifies" | "var_names"
            ),
            "vectors/reify.json carries a section {key:?} this replay has no reader for"
        );
    }

    let mut failures = Vec::new();
    for row in section(&file, "refused") {
        let (name, _, term) = reified(row);
        if let Some(term) = term {
            failures.push(format!(
                "refused/{name}: reify ACCEPTED it as {term:?}; the value is outside quote's image"
            ));
        }
    }
    for row in section(&file, "reifies") {
        let (name, raw, term) = reified(row);
        let Some(got) = term else {
            failures.push(format!(
                "reifies/{name}: reify refused a value in quote's image"
            ));
            continue;
        };
        let want = described(&name, &row["term"]);
        if got != want {
            failures.push(format!("reifies/{name}: reify gave {got:?}, want {want:?}"));
        }
        let again = ontos_codec::encode(&quote(&got));
        if again != raw {
            failures.push(format!(
                "reifies/{name}: quote re-encodes to {again:02x?}, want {raw:02x?}"
            ));
        }
    }
    replay_var_names_3115(&file, &mut failures);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `var_names` (#3115): a `String` holds exactly the UTF-8 byte strings, so rs can build a row's name
/// iff the row is `in_domain`. Where it can, `VarId::new` accepts it (the domain holds by type) and
/// the name round-trips, with quote writing exactly `name_hex`. Where it cannot, the replay records
/// that `from_utf8` refuses the bytes: capability by type, the row's "unrepresentable".
fn replay_var_names_3115(file: &Json, failures: &mut Vec<String>) {
    for row in section(file, "var_names") {
        let name = row["name"].as_str().expect("a row has a name");
        let bytes = hex_to_bytes(row["name_hex"].as_str().expect("a row has name_hex"));
        let in_domain = row["in_domain"].as_bool().expect("a row has in_domain");
        match String::from_utf8(bytes.clone()) {
            Err(_) if !in_domain => {} // unrepresentable in rs, as the row says
            Err(_) => failures.push(format!(
                "var_names/{name}: in_domain, but no String holds the bytes"
            )),
            Ok(_) if !in_domain => failures.push(format!(
                "var_names/{name}: the row says out of domain, but the bytes are UTF-8"
            )),
            Ok(text) => {
                let v = Term::Var(VarId::new(text));
                let quoted = quote(&v);
                if reify(&quoted).as_ref() != Some(&v) {
                    failures.push(format!("var_names/{name}: reify(quote(v)) != v"));
                }
                let want = Value::tuple([Value::atom([0x02]), Value::atom(bytes)]);
                if ontos_codec::encode(&quoted) != ontos_codec::encode(&want) {
                    failures.push(format!(
                        "var_names/{name}: quote does not write exactly name_hex"
                    ));
                }
            }
        }
    }
}

/// #3115's round-trip property in rs, over generated strings: every `String` is a name (by type),
/// so every one quotes and reifies back to itself. A small LCG keeps the test dependency-free.
#[test]
fn every_string_name_round_trips_3115() {
    let alphabet = [
        'a',
        'Z',
        '0',
        '\0',
        '\u{7f}',
        'é',
        '\u{fffd}',
        '\u{d7ff}',
        '\u{e000}',
        '😀',
        '\u{10ffff}',
    ];
    let mut seed: u32 = 3115;
    let mut next = || {
        seed = seed.wrapping_mul(1_103_515_245).wrapping_add(12_345);
        (seed >> 8) as usize
    };
    for _ in 0..2000 {
        let len = next() % 7;
        let name: String = (0..len)
            .map(|_| alphabet[next() % alphabet.len()])
            .collect();
        let v = Term::Var(VarId::new(name.clone()));
        assert_eq!(reify(&quote(&v)), Some(v), "{name:?}: reify(quote(v)) != v");
    }
}
