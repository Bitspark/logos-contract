use logos_contract::typed::{self, Declaration, Expr, Limits, Outcome, Phase, Policy, Statement};
use std::collections::BTreeSet;

fn boxed(expression: Expr) -> Box<Expr> {
    Box::new(expression)
}

fn statement(expected: Expr) -> Statement {
    Statement {
        foundation: typed::FOUNDATION.into(),
        declarations: Vec::new(),
        context: Vec::new(),
        expected,
    }
}

fn policy(dependencies: &[&str]) -> Policy {
    Policy {
        foundation: typed::FOUNDATION.into(),
        checker: typed::CHECKER.into(),
        dependencies: dependencies.iter().map(|name| (*name).into()).collect(),
    }
}

fn assume(name: &str, ty: Expr, dependency: &str) -> Declaration {
    Declaration::Assume {
        name: name.into(),
        ty,
        dependencies: vec![dependency.into()],
    }
}

fn accepted(outcome: Outcome) -> typed::Accepted {
    match outcome {
        Outcome::Accepted(accepted) => *accepted,
        other => panic!("expected acceptance, got {other:?}"),
    }
}

#[test]
fn accepted_statement_is_an_owned_exact_request_and_keeps_policy() {
    let mut input = statement(Expr::Nat);
    let mut proof = Expr::Zero;
    let mut policy = policy(&[]);
    let report = accepted(typed::check(&input, &proof, &policy, Limits::default()));
    input.expected = Expr::Bool;
    proof = Expr::True;
    policy.checker = "different implementation".into();
    assert_eq!(report.statement().expected, Expr::Nat);
    assert_eq!(report.candidate(), &Expr::Zero);
    assert_eq!(report.policy().checker, typed::CHECKER);
    assert_ne!(report.candidate(), &proof);
    assert_ne!(report.statement(), &input);
    assert_ne!(report.policy(), &policy);
    assert_eq!(report.foundation(), typed::FOUNDATION);
    assert_eq!(report.checker(), typed::CHECKER);
    assert!(report.steps() > 0);
}

#[test]
fn expected_expression_is_retained_even_when_conversion_eliminates_a_definition() {
    let mut input = statement(Expr::Const("Alias".into()));
    input.declarations.push(Declaration::Define {
        name: "Alias".into(),
        ty: Expr::Sort(0),
        value: Expr::Nat,
    });
    let report = accepted(typed::check(
        &input,
        &Expr::Zero,
        &policy(&[]),
        Limits::default(),
    ));
    assert_eq!(report.statement().expected, Expr::Const("Alias".into()));
    assert!(report.used_constants().contains("Alias"));
}

#[test]
fn erased_argument_dependencies_are_retained_and_unused_entries_are_excluded() {
    let mut input = statement(Expr::Nat);
    input.declarations = vec![
        assume("supplied", Expr::Nat, "procedure/value"),
        assume("unrelated", Expr::Bool, "unrelated/assumption"),
    ];
    let proof = Expr::App {
        fun: boxed(Expr::Lam {
            domain: boxed(Expr::Nat),
            body: boxed(Expr::Zero),
        }),
        arg: boxed(Expr::Const("supplied".into())),
    };
    let report = accepted(typed::check(
        &input,
        &proof,
        &policy(&["procedure/value", "unused/allowance"]),
        Limits::default(),
    ));
    assert_eq!(
        report.dependencies(),
        &BTreeSet::from(["procedure/value".into()])
    );
    assert!(!report.used_constants().contains("unrelated"));
    let narrowed = typed::check(&input, &proof, &policy(&[]), Limits::default());
    assert_eq!(narrowed.status(), "unsupported");
    assert_eq!(narrowed.code(), Some("unadmitted-dependency"));
    assert_eq!(narrowed.location().unwrap().phase, Phase::Policy);
}

#[test]
fn malformed_unused_declaration_still_prevents_admission() {
    let mut input = statement(Expr::Nat);
    input.declarations.push(Declaration::Define {
        name: "broken".into(),
        ty: Expr::Nat,
        value: Expr::True,
    });
    let outcome = typed::check(&input, &Expr::Zero, &policy(&[]), Limits::default());
    assert_eq!(outcome.code(), Some("type-mismatch"));
    assert_eq!(outcome.location().unwrap().phase, Phase::Declaration);
    assert_eq!(outcome.location().unwrap().index, Some(0));
}

#[test]
fn contexts_and_expected_types_are_checked_separately_from_candidate_failure() {
    let mut input = statement(Expr::Nat);
    input.context.push(Expr::Var(0));
    let context = typed::check(&input, &Expr::Zero, &policy(&[]), Limits::default());
    assert_eq!(context.code(), Some("escaped-variable"));
    assert_eq!(context.location().unwrap().phase, Phase::Context);
    assert_eq!(context.location().unwrap().index, Some(0));

    input.context.clear();
    input.expected = Expr::Zero;
    let expected = typed::check(&input, &Expr::Zero, &policy(&[]), Limits::default());
    assert_eq!(expected.code(), Some("expected-universe"));
    assert_eq!(expected.location().unwrap().phase, Phase::Expected);

    input.expected = Expr::Bool;
    let candidate = typed::check(&input, &Expr::Zero, &policy(&[]), Limits::default());
    assert_eq!(candidate.code(), Some("type-mismatch"));
    assert_eq!(candidate.location().unwrap().phase, Phase::Candidate);
}

#[test]
fn limits_are_incomplete_and_the_same_allowance_pays_for_the_snapshot() {
    let input = statement(Expr::Nat);
    let policy = policy(&[]);
    let baseline = accepted(typed::check(
        &input,
        &Expr::Zero,
        &policy,
        Limits::default(),
    ));
    let limits = Limits {
        work: (baseline.steps() - 1) as u32,
        ..Limits::default()
    };
    let tight = typed::check(&input, &Expr::Zero, &policy, limits);
    assert_eq!(tight.status(), "incomplete");
    assert_eq!(tight.code(), Some("work"));
    let no_depth = typed::check(
        &input,
        &Expr::Zero,
        &policy,
        Limits {
            input_depth: 0,
            ..Limits::default()
        },
    );
    assert_eq!(no_depth.code(), Some("input-depth"));
    let mut overdeep = Expr::Zero;
    for _ in 0..typed::MAX_INPUT_DEPTH {
        overdeep = Expr::Succ(boxed(overdeep));
    }
    let capped = typed::check(
        &input,
        &overdeep,
        &policy,
        Limits {
            input_depth: u32::MAX,
            ..Limits::default()
        },
    );
    assert_eq!(capped.code(), Some("input-depth"));
}

#[test]
fn a_previous_proof_is_reused_by_checked_definition_not_an_acceptance_flag() {
    let identity_type = Expr::Pi {
        domain: boxed(Expr::Nat),
        body: boxed(Expr::Nat),
    };
    let identity = Expr::Lam {
        domain: boxed(Expr::Nat),
        body: boxed(Expr::Var(0)),
    };
    let report = accepted(typed::check(
        &statement(identity_type),
        &identity,
        &policy(&[]),
        Limits::default(),
    ));
    let mut reuse = statement(Expr::Nat);
    reuse.declarations.push(Declaration::Define {
        name: "identity".into(),
        ty: report.statement().expected.clone(),
        value: report.candidate().clone(),
    });
    let application = Expr::App {
        fun: boxed(Expr::Const("identity".into())),
        arg: boxed(Expr::Zero),
    };
    accepted(typed::check(
        &reuse,
        &application,
        &policy(&[]),
        Limits::default(),
    ));
    if let Declaration::Define { value, .. } = &mut reuse.declarations[0] {
        *value = Expr::True;
    }
    assert_eq!(
        typed::check(&reuse, &application, &policy(&[]), Limits::default()).code(),
        Some("type-mismatch")
    );
}

#[test]
fn identity_bytes_are_charged_before_snapshot_and_duplicate_entries_are_counted() {
    let mut input = statement(Expr::Nat);
    let long_name = "x".repeat(2_048);
    input
        .declarations
        .push(assume(&long_name, Expr::Nat, "premise"));
    let outcome = typed::check(
        &input,
        &Expr::Zero,
        &policy(&[]),
        Limits {
            name_bytes: 2_048,
            work: 1_000,
            ..Limits::default()
        },
    );
    assert_eq!(outcome.code(), Some("work"));
    assert_eq!(outcome.location().unwrap().phase, Phase::Preflight);

    let mut input = statement(Expr::Nat);
    input.declarations.push(Declaration::Assume {
        name: "value".into(),
        ty: Expr::Nat,
        dependencies: vec!["premise".into(), "premise".into()],
    });
    let candidate = Expr::Const("value".into());
    let policy = policy(&["premise", "premise"]);
    let report = accepted(typed::check(&input, &candidate, &policy, Limits::default()));
    assert_eq!(report.dependencies(), &BTreeSet::from(["premise".into()]));
    let outcome = typed::check(
        &input,
        &candidate,
        &policy,
        Limits {
            collection_entries: 4,
            ..Limits::default()
        },
    );
    assert_eq!(outcome.code(), Some("collection-entries"));
}
