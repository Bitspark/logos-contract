//! Replay the shared AST fixture notation through the public typed checker.
//! This decoder is test-only and makes no production ingress/resource promise.

use logos_contract::typed::{self, Declaration, Expr, Limits, Outcome, Policy, Statement};
use serde_json::Value;
use std::collections::BTreeSet;

fn corpus() -> Value {
    serde_json::from_str(include_str!("../../../vectors/typed_check.json")).unwrap()
}

fn text(value: &Value) -> String {
    value.as_str().expect("fixture string").to_owned()
}

fn strings(value: &Value) -> Vec<String> {
    value
        .as_array()
        .expect("fixture string list")
        .iter()
        .map(text)
        .collect()
}

fn expression(value: &Value) -> Expr {
    let fields = value.as_array().expect("fixture expression array");
    let tag = fields[0].as_str().expect("fixture constructor tag");
    let child = |index| Box::new(expression(&fields[index]));
    let arity = match tag {
        "sort" | "var" | "const" | "fst" | "snd" | "succ" => 1,
        "pi" | "lam" | "app" | "sigma" | "refl" => 2,
        "pair" | "id" => 3,
        "nat-elim" | "bool-elim" => 4,
        "transport" => 6,
        "nat" | "zero" | "bool" | "false" | "true" => 0,
        _ => panic!("unknown fixture constructor {tag}"),
    };
    assert_eq!(fields.len(), arity + 1, "fixture arity for {tag}");
    match tag {
        "sort" => Expr::Sort(u32::try_from(fields[1].as_u64().unwrap()).unwrap()),
        "var" => Expr::Var(u32::try_from(fields[1].as_u64().unwrap()).unwrap()),
        "const" => Expr::Const(text(&fields[1])),
        "pi" => Expr::Pi {
            domain: child(1),
            body: child(2),
        },
        "lam" => Expr::Lam {
            domain: child(1),
            body: child(2),
        },
        "app" => Expr::App {
            fun: child(1),
            arg: child(2),
        },
        "sigma" => Expr::Sigma {
            domain: child(1),
            body: child(2),
        },
        "pair" => Expr::Pair {
            sigma: child(1),
            first: child(2),
            second: child(3),
        },
        "fst" => Expr::Fst(child(1)),
        "snd" => Expr::Snd(child(1)),
        "nat" => Expr::Nat,
        "zero" => Expr::Zero,
        "succ" => Expr::Succ(child(1)),
        "nat-elim" => Expr::NatElim {
            motive: child(1),
            zero: child(2),
            step: child(3),
            scrutinee: child(4),
        },
        "bool" => Expr::Bool,
        "false" => Expr::False,
        "true" => Expr::True,
        "bool-elim" => Expr::BoolElim {
            motive: child(1),
            on_false: child(2),
            on_true: child(3),
            scrutinee: child(4),
        },
        "id" => Expr::Eq {
            ty: child(1),
            lhs: child(2),
            rhs: child(3),
        },
        "refl" => Expr::Refl {
            ty: child(1),
            value: child(2),
        },
        "transport" => Expr::Transport {
            ty: child(1),
            from: child(2),
            to: child(3),
            equality: child(4),
            motive: child(5),
            value: child(6),
        },
        _ => unreachable!(),
    }
}

fn declaration(value: &Value) -> Declaration {
    let name = text(&value["symbol"]);
    let ty = expression(&value["type"]);
    match value["kind"].as_str().unwrap() {
        "assume" => Declaration::Assume {
            name,
            ty,
            dependencies: strings(&value["dependencies"]),
        },
        "define" => Declaration::Define {
            name,
            ty,
            value: expression(&value["value"]),
        },
        other => panic!("fixture declaration {other}"),
    }
}

fn statement(corpus: &Value, case: &Value) -> Statement {
    let request = &case["statement"];
    let set = request["declarations"].as_str().unwrap();
    Statement {
        foundation: request["foundation"]
            .as_str()
            .unwrap_or(corpus["foundation"].as_str().unwrap())
            .into(),
        declarations: corpus["declaration_sets"][set]
            .as_array()
            .unwrap()
            .iter()
            .map(declaration)
            .collect(),
        context: request["context"]
            .as_array()
            .unwrap()
            .iter()
            .map(expression)
            .collect(),
        expected: expression(&request["expected"]),
    }
}

fn policy(corpus: &Value, case: &Value) -> Policy {
    let policy = &case["policy"];
    Policy {
        foundation: policy["foundation"]
            .as_str()
            .unwrap_or(corpus["foundation"].as_str().unwrap())
            .into(),
        checker: policy["checker"].as_str().unwrap_or(typed::CHECKER).into(),
        dependencies: strings(&policy["dependencies"]),
    }
}

fn limits(case: &Value) -> Limits {
    let mut limits = Limits::default();
    if let Some(overrides) = case["limits"].as_object() {
        for (name, value) in overrides {
            let value = u32::try_from(value.as_u64().unwrap()).unwrap();
            match name.as_str() {
                "input_nodes" => limits.input_nodes = value,
                "input_depth" => limits.input_depth = value,
                "collection_entries" => limits.collection_entries = value,
                "name_bytes" => limits.name_bytes = value,
                "work" => limits.work = value,
                "depth" => limits.depth = value,
                _ => panic!("unknown fixture limit {name}"),
            }
        }
    }
    limits
}

fn assert_outcome(case: &Value, outcome: &Outcome) {
    let id = case["id"].as_str().unwrap();
    assert_eq!(
        outcome.status(),
        case["expect"]["status"].as_str().unwrap(),
        "{id}: {outcome:?}"
    );
    assert_eq!(
        outcome.code(),
        case["expect"]["code"].as_str(),
        "{id}: {outcome:?}"
    );
    if let Outcome::Accepted(accepted) = outcome {
        let expected: BTreeSet<_> = strings(&case["expect"]["dependencies"])
            .into_iter()
            .collect();
        assert_eq!(accepted.dependencies(), &expected, "{id}");
    }
}

fn each_budget_raised(limits: Limits) -> [Limits; 6] {
    [
        Limits {
            input_nodes: limits.input_nodes.saturating_add(1),
            ..limits
        },
        Limits {
            input_depth: limits.input_depth.saturating_add(1),
            ..limits
        },
        Limits {
            collection_entries: limits.collection_entries.saturating_add(1),
            ..limits
        },
        Limits {
            name_bytes: limits.name_bytes.saturating_add(1),
            ..limits
        },
        Limits {
            work: limits.work.saturating_add(1),
            ..limits
        },
        Limits {
            depth: limits.depth.saturating_add(1),
            ..limits
        },
    ]
}

#[test]
fn shared_typed_check_vectors() {
    let corpus = corpus();
    assert_eq!(corpus["schema"], "logos/typed-check-fixtures/v1");
    for case in corpus["cases"].as_array().unwrap() {
        let statement = statement(&corpus, case);
        let candidate = expression(&case["candidate"]);
        let policy = policy(&corpus, case);
        let limits = limits(case);
        let outcome = typed::check(&statement, &candidate, &policy, limits);
        assert_outcome(case, &outcome);
        if let Outcome::Accepted(baseline) = outcome {
            assert_eq!(baseline.statement(), &statement);
            assert_eq!(baseline.candidate(), &candidate);
            assert_eq!(baseline.policy(), &policy);
            for raised in each_budget_raised(limits) {
                let outcome = typed::check(&statement, &candidate, &policy, raised);
                assert_outcome(case, &outcome);
                let Outcome::Accepted(accepted) = outcome else {
                    unreachable!("assert_outcome requires acceptance");
                };
                assert_eq!(accepted.statement(), baseline.statement());
                assert_eq!(accepted.candidate(), baseline.candidate());
                assert_eq!(accepted.policy(), baseline.policy());
                assert_eq!(accepted.dependencies(), baseline.dependencies());
                assert_eq!(accepted.used_constants(), baseline.used_constants());
            }
        }
    }
}

#[test]
fn checked_page_result_is_reused_by_definition_and_both_nested_projections() {
    let corpus = corpus();
    let cases = corpus["cases"].as_array().unwrap();
    let symbolic = cases
        .iter()
        .find(|case| case["id"] == "page-symbolic-theorem")
        .unwrap();
    let mut input = statement(&corpus, symbolic);
    input.declarations.retain(|declaration| match declaration {
        Declaration::Define { name, .. } => name != "page.proof",
        Declaration::Assume { .. } => true,
    });
    let proof = expression(&symbolic["candidate"]);
    let accepted = match typed::check(&input, &proof, &policy(&corpus, symbolic), limits(symbolic))
    {
        Outcome::Accepted(accepted) => accepted,
        other => panic!("Page theorem was not checked: {other:?}"),
    };
    let mut declarations = input.declarations;
    declarations.push(Declaration::Define {
        name: "page.proof".into(),
        ty: accepted.statement().expected.clone(),
        value: accepted.candidate().clone(),
    });
    for id in [
        "page-person-application",
        "page-nested-application-consumes-both-projections",
        "page-nesting-cannot-substitute-membership-for-representation",
    ] {
        let case = cases.iter().find(|case| case["id"] == id).unwrap();
        let mut request = statement(&corpus, case);
        request.declarations = declarations.clone();
        let outcome = typed::check(
            &request,
            &expression(&case["candidate"]),
            &policy(&corpus, case),
            limits(case),
        );
        assert_outcome(case, &outcome);
    }
}
