//! Rust replay of `vectors/exact_answer_set.json` (#3022, research 0028 rows 1, 3, 4, 5 and 6):
//! the completeness gate's G4 compares the emitted answers with the sealed rows STRUCTURALLY.
//! #3023 (research 0028 A16): G4 is the contract's `check_answer_set`, so the replay runs it here,
//! through the contract entry point, and asserts its structured result: which kind of mismatch, and
//! the literal the normative precedence names. Replayed identically by go
//! (`contract/go/exact_answer_set_vectors_test.go`) and ts
//! (`contract/ts/test/exact_answer_set_vectors.test.ts`).
//!
//! Denominator first: the file must carry exactly the named cases, so a case added to the file and
//! not replayed, or dropped from it, reds here rather than silently thinning the replay.

use logos_contract::{check_answer_set, AnswerSetMismatch, Goal, GroundLiteral, Term};
use serde_json::Value;

const VECTORS: &str = include_str!("../../../vectors/exact_answer_set.json");

const CASE_NAMES: &[&str] = &[
    "control_the_sealed_set_emitted_accepts",
    "row1_one_spelling_emitted_of_two_sealed_rows_is_refused",
    "row1_both_sealed_rows_emitted_accepts",
    "row3_a_flat_ground_goal_has_no_cons_instance_accepts_the_empty_set",
    "row3_the_cons_row_emitted_for_a_flat_ground_goal_is_refused",
    "row4_an_open_cons_pattern_matches_its_cons_row_accepts",
    "row5_an_open_flat_pattern_has_no_cons_instance_accepts_the_empty_set",
    "row6_a_repeated_variable_does_not_join_two_spellings_accepts_the_empty_set",
    "precedence_an_extra_is_reported_before_a_missing_row",
    "precedence_the_first_extra_is_in_claim_order",
    "precedence_the_first_missing_row_is_in_key_order",
];

fn term(v: &Value) -> Term {
    if let Some(name) = v.get("var").and_then(Value::as_str) {
        Term::var(name)
    } else if let Some(s) = v.get("atom_str").and_then(Value::as_str) {
        Term::Atom(s.as_bytes().to_vec())
    } else if let Some(children) = v.get("tuple").and_then(Value::as_array) {
        Term::Tuple(children.iter().map(term).collect())
    } else {
        panic!("unknown term form: {v}")
    }
}

fn goal(v: &Value) -> Goal {
    let pred = v["pred"].as_str().expect("goal.pred");
    let args = v["args"].as_array().expect("goal.args");
    Goal::new(pred, args.iter().map(term))
}

fn ground(v: &Value) -> GroundLiteral {
    goal(v)
        .as_ground()
        .expect("a sealed row or an emitted claim is ground")
}

fn literals(v: &Value) -> Vec<GroundLiteral> {
    v.as_array()
        .expect("a literal list")
        .iter()
        .map(ground)
        .collect()
}

#[test]
fn every_exact_answer_set_case_replays_3022() {
    let doc: Value = serde_json::from_str(VECTORS).expect("exact_answer_set.json parses");
    let cases = doc["cases"].as_array().expect("cases");
    let names: Vec<&str> = cases
        .iter()
        .map(|c| c["name"].as_str().expect("case.name"))
        .collect();
    assert_eq!(
        names, CASE_NAMES,
        "the file's cases are exactly the replayed ones"
    );

    for case in cases {
        let name = case["name"].as_str().expect("case.name");
        let verdict = check_answer_set(
            &goal(&case["goal"]),
            &literals(&case["sealed"]),
            &literals(&case["emitted"]),
        );
        match &case["outcome"] {
            Value::String(s) if s == "accept" => {
                assert_eq!(verdict, Ok(()), "{name}: expected accept");
            }
            outcome => {
                assert_eq!(
                    outcome["reject"].as_str(),
                    Some("completeness_set_mismatch"),
                    "{name}: the only G4 refusal is completeness_set_mismatch"
                );
                let m = &outcome["mismatch"];
                let want = match (m.get("extra"), m.get("missing")) {
                    (Some(lit), None) => AnswerSetMismatch::Extra(ground(lit)),
                    (None, Some(lit)) => AnswerSetMismatch::Missing(ground(lit)),
                    (Some(_), Some(_)) | (None, None) => {
                        panic!("{name}: a mismatch names exactly one of extra or missing: {m}")
                    }
                };
                assert_eq!(verdict, Err(want), "{name}: the normative mismatch");
            }
        }
    }
}
