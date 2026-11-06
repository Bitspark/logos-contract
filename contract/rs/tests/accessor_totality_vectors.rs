//! Rust replay of `vectors/accessor_totality.json` — the `BodyLit` accessor family's behaviour
//! around the `Count` variant.
//!
//! Every case carries ONE outcome, the same in every core: the file is an `interface` section
//! (`vectors/CORPUS-CLASSES.md`). It keyed outcomes per core until #2733, because the partial
//! `inner()` accessor failed differently on a `Count` (rs trapped, go/ts returned the empty goal,
//! #728). That accessor was deleted tri-core (#2733, `seat:caa`'s D1), and the total `as_inner()`
//! is the only one left.

use logos_contract::{BodyLit, CountLit, Goal, PredicateRef, ProjectSpec, Symbol, Term};
use serde_json::Value as Json;

fn load() -> Json {
    // Walk up from the crate dir to the repo root holding the vector file.
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/accessor_totality.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/accessor_totality.json");
    }
    let raw =
        std::fs::read_to_string(dir.join("vectors/accessor_totality.json")).expect("read vector");
    serde_json::from_str(&raw).expect("parse vector")
}

fn fixture_goal(fixture: &Json) -> Goal {
    let pred = fixture["goal"]["pred"].as_str().expect("goal.pred");
    let atom = fixture["goal"]["args"][0]["atom_str"]
        .as_str()
        .expect("goal.args[0].atom_str");
    Goal::new(
        Symbol::new(pred.as_bytes().to_vec()),
        [Term::atom(atom.as_bytes().to_vec())],
    )
}

fn build(variant: &str, fixture: &Json) -> BodyLit<Term> {
    match variant {
        "pos" => BodyLit::Pos(fixture_goal(fixture)),
        "neg" => BodyLit::Neg(fixture_goal(fixture)),
        "count" => {
            let c = &fixture["count"];
            assert_eq!(c["project"].as_str(), Some("rows"), "fixture project");
            assert_eq!(
                c["filter"].as_array().map(|f| f.len()),
                Some(0),
                "fixture filter"
            );
            BodyLit::Count(CountLit {
                pred: PredicateRef::new(
                    Symbol::new(c["pred"].as_str().expect("count.pred").as_bytes().to_vec()),
                    c["arity"].as_u64().expect("count.arity") as u32,
                ),
                filter: Vec::new(),
                project: ProjectSpec::Rows,
                count: Term::var(c["count_var"].as_str().expect("count.count_var")),
            })
        }
        other => panic!("unknown variant {other}"),
    }
}

/// Classify a returned goal against the closed outcome vocabulary.
fn classify(goal: &Goal, expected_goal: &Goal) -> &'static str {
    if goal == expected_goal {
        "goal"
    } else {
        "other"
    }
}

fn observe_as_inner(bl: &BodyLit<Term>, expected_goal: &Goal) -> &'static str {
    match bl.as_inner() {
        None => "none",
        Some(goal) => classify(goal, expected_goal),
    }
}

/// The file is an `interface` section: ONE outcome per case, never keyed by core. A per-core
/// key here would re-open the door #2733 closed, where a difference is written down as a
/// "documented" one and then reads as conformance.
#[test]
fn every_case_has_one_outcome_for_every_core_2733() {
    let file = load();
    let cases = file["cases"].as_array().expect("cases");
    assert!(!cases.is_empty(), "the pin file carries cases");
    for case in cases {
        let name = case["name"].as_str().expect("case.name");
        assert!(
            case["outcome"].is_string(),
            "case {name}: the outcome must be one value for every core, got {}",
            case["outcome"]
        );
    }
}

#[test]
fn accessor_totality_replay() {
    let file = load();
    let fixture = &file["fixture"];
    let expected_goal = fixture_goal(fixture);
    let cases = file["cases"].as_array().expect("cases");
    assert_eq!(cases.len(), 3, "the pin file carries exactly 3 cases");

    for case in cases {
        let name = case["name"].as_str().expect("case.name");
        let expected = case["outcome"]
            .as_str()
            .unwrap_or_else(|| panic!("case {name} has no single outcome"));
        let bl = build(case["variant"].as_str().expect("case.variant"), fixture);
        let observed = match case["accessor"].as_str().expect("case.accessor") {
            "as_inner" => observe_as_inner(&bl, &expected_goal),
            other => panic!("unknown accessor {other}"),
        };
        assert_eq!(observed, expected, "case {name}: observed vs pinned");
    }
}
