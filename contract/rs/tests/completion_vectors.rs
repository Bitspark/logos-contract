//! Rust replay of `vectors/completion_algebra.json`, the completion algebra's `not`/`and`/`or`
//! (research 0031 row 15, #3164). The same file is replayed by Go
//! (`contract/go/completion/completion_vectors_test.go`) and TypeScript
//! (`contract/ts/test/completion_vectors.test.ts`).
//!
//! The vector is hand-authored from research 0031's advice (the strong-Kleene tables, the scoped
//! absorption rule and the closure implication table) and from seat:caa's ruling on #3179 (a fault
//! carries no scope and ranks above a limit). Each case is checked twice: the written operand
//! order must give `expect` exactly, and every reordering of every `and`/`or` node's operands must
//! give an outcome of the same class, so a verdict never depends on evaluation order. A case with
//! `construct` names a kind and scope the checked constructor must refuse; Rust cannot form the
//! hand-built value its `expr` holds, so only the refusal is checked here.
//!
//! The replay is also run against three deliberately wrong algebras, and must reject each: one that
//! never absorbs (`F ∧ U = U`), one that absorbs a request-scope stop, and one that ranks a fault
//! with a limit. Those are the broken counterparts design/0004 §7.7 asks for, kept in the tree so
//! the negative witness cannot rot.

use logos_contract::completion::{
    self, CauseScope, Completion, Decision, FalseCode, GroundOutcome, NonCompletion,
    NonCompletionKind,
};
use serde_json::Value as Json;

const VECTORS: &str = include_str!("../../../vectors/completion_algebra.json");

type Outcome = GroundOutcome<String>;

/// The three combinators under test, so the replay can run a mutant as well as the real ones.
struct Algebra {
    not: fn(Outcome) -> Outcome,
    and: fn(Outcome, Outcome) -> Outcome,
    or: fn(Outcome, Outcome) -> Outcome,
}

const REAL: Algebra = Algebra {
    not: completion::not::<String>,
    and: completion::and::<String>,
    or: completion::or::<String>,
};

// ---- the vocabulary, each list guarded by an exhaustive match ----

fn scopes() -> Vec<CauseScope> {
    use CauseScope::*;
    let all = vec![
        Literal,
        Branch,
        Enumeration,
        Dependency,
        TheorySnapshot,
        Request,
    ];
    // A new scope fails to compile here, which is the prompt to list it above.
    for s in &all {
        match s {
            Literal | Branch | Enumeration | Dependency | TheorySnapshot | Request => {}
        }
    }
    all
}

fn kinds() -> Vec<NonCompletionKind> {
    use NonCompletionKind::*;
    let all = vec![
        Capacity,
        WorkCap,
        Instantiation,
        HostRefusal,
        ReplyUnreadable,
        InconsistentTheory,
        MalformedOutcome,
    ];
    for k in &all {
        match k {
            Capacity | WorkCap | Instantiation | HostRefusal | ReplyUnreadable
            | InconsistentTheory | MalformedOutcome => {}
        }
    }
    all
}

fn false_codes() -> Vec<FalseCode> {
    let all = vec![FalseCode::Unsatisfied];
    for c in &all {
        match c {
            FalseCode::Unsatisfied => {}
        }
    }
    all
}

fn scope(tag: &str) -> CauseScope {
    scopes()
        .into_iter()
        .find(|s| s.tag() == tag)
        .unwrap_or_else(|| panic!("unknown scope {tag:?}"))
}

fn kind(tag: &str) -> NonCompletionKind {
    kinds()
        .into_iter()
        .find(|k| k.tag() == tag)
        .unwrap_or_else(|| panic!("unknown kind {tag:?}"))
}

fn false_code(tag: &str) -> FalseCode {
    false_codes()
        .into_iter()
        .find(|c| c.tag() == tag)
        .unwrap_or_else(|| panic!("unknown false code {tag:?}"))
}

fn text<'a>(j: &'a Json, field: &str) -> &'a str {
    j[field]
        .as_str()
        .unwrap_or_else(|| panic!("{field} is not a string in {j}"))
}

/// A kind and an optional scope, through the checked constructor.
fn cause(j: &Json) -> Result<NonCompletion, completion::IllegalCause> {
    let s = j
        .get("scope")
        .map(|s| scope(s.as_str().expect("scope is a string")));
    NonCompletion::from_parts(kind(text(j, "kind")), s)
}

fn leaf(j: &Json) -> Outcome {
    match text(j, "arm") {
        "holds" => Completion::Completed(Decision::Holds),
        "fails" => Completion::Completed(Decision::Fails {
            code: false_code(text(j, "false_code")),
        }),
        "not_completed" => Completion::NotCompleted(
            cause(j).unwrap_or_else(|e| panic!("a vector leaf must be constructible: {e}")),
        ),
        "limit_exceeded" => Completion::LimitExceeded(text(j, "limit").to_string()),
        other => panic!("unknown arm {other:?}"),
    }
}

/// The outcome's class: the part of the result that must not depend on operand order.
fn class(o: &Outcome) -> &'static str {
    match o {
        Completion::Completed(Decision::Holds) => "holds",
        Completion::Completed(Decision::Fails { .. }) => "fails",
        Completion::NotCompleted(c) => match c.scope() {
            None => "fault",
            Some(s) if s.is_absorbable() => "absorbable",
            Some(_) => "dominant",
        },
        Completion::LimitExceeded(_) => "dominant",
    }
}

fn args(e: &Json) -> &Vec<Json> {
    e["args"]
        .as_array()
        .unwrap_or_else(|| panic!("args is not an array in {e}"))
}

fn fold(alg: &Algebra, op: &str, operands: Vec<Outcome>) -> Outcome {
    let combine = match op {
        "and" => alg.and,
        "or" => alg.or,
        other => panic!("{other:?} does not fold"),
    };
    let mut iter = operands.into_iter();
    let first = iter.next().expect("a fold has at least one operand");
    iter.fold(first, combine)
}

/// The expression in its written order.
fn eval(alg: &Algebra, e: &Json) -> Outcome {
    if e.get("arm").is_some() {
        return leaf(e);
    }
    let op = text(e, "op");
    let operands: Vec<Outcome> = args(e).iter().map(|a| eval(alg, a)).collect();
    if op == "not" {
        assert_eq!(operands.len(), 1, "not takes one operand: {e}");
        return (alg.not)(operands.into_iter().next().unwrap());
    }
    fold(alg, op, operands)
}

fn permutations(n: usize) -> Vec<Vec<usize>> {
    if n == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for rest in permutations(n - 1) {
        for at in 0..=rest.len() {
            let mut p = rest.clone();
            p.insert(at, n - 1);
            out.push(p);
        }
    }
    out
}

/// The expression under every reordering of every `and`/`or` node's operands.
fn eval_every_order(alg: &Algebra, e: &Json) -> Vec<Outcome> {
    if e.get("arm").is_some() {
        return vec![leaf(e)];
    }
    let op = text(e, "op");
    let children: Vec<Vec<Outcome>> = args(e).iter().map(|a| eval_every_order(alg, a)).collect();
    if op == "not" {
        return children[0].iter().cloned().map(alg.not).collect();
    }
    let mut out = Vec::new();
    for order in permutations(children.len()) {
        // every combination of the children's own orderings, taken in this order
        let mut combos: Vec<Vec<Outcome>> = vec![vec![]];
        for &i in &order {
            let mut next = Vec::new();
            for combo in &combos {
                for o in &children[i] {
                    let mut c = combo.clone();
                    c.push(o.clone());
                    next.push(c);
                }
            }
            combos = next;
        }
        out.extend(combos.into_iter().map(|c| fold(alg, op, c)));
    }
    out
}

fn cases() -> Vec<Json> {
    let v: Json = serde_json::from_str(VECTORS).expect("vectors/completion_algebra.json parses");
    v["cases"].as_array().expect("cases is an array").clone()
}

/// Every failing case's name and why, for one algebra.
fn replay(alg: &Algebra) -> Vec<String> {
    let mut failures = Vec::new();
    for case in cases() {
        // Every failure carries the case's `why`, so the reader sees what the case pins.
        let name = format!("{} ({})", text(&case, "name"), text(&case, "why"));
        if let Some(construct) = case.get("construct") {
            // Rust cannot hand-build the illegal value; the checked constructor must refuse it.
            assert_eq!(
                case["refused"],
                Json::Bool(true),
                "{name}: refused must be true"
            );
            if let Ok(c) = cause(construct) {
                failures.push(format!("{name}: the constructor built {c:?}"));
            }
            continue;
        }
        let expect = leaf(&case["expect"]);
        let got = eval(alg, &case["expr"]);
        if got != expect {
            failures.push(format!(
                "{name}: written order gave {got:?}, expected {expect:?}"
            ));
            continue;
        }
        for o in eval_every_order(alg, &case["expr"]) {
            if class(&o) != class(&expect) {
                failures.push(format!(
                    "{name}: a reordering gave {o:?}, class {} instead of {}",
                    class(&o),
                    class(&expect)
                ));
                break;
            }
        }
    }
    failures
}

#[test]
fn completion_vectors_replay() {
    let n = cases().len();
    assert!(n >= 55, "expected the full vector, loaded {n} cases");
    let failures = replay(&REAL);
    assert!(
        failures.is_empty(),
        "{} of {n} cases fail:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn completion_vocabulary_matches_the_vector() {
    let v: Json = serde_json::from_str(VECTORS).unwrap();
    let voc = &v["vocabulary"];
    let names = |field: &str| -> Vec<String> {
        voc[field]
            .as_array()
            .unwrap_or_else(|| panic!("vocabulary.{field}"))
            .iter()
            .map(|t| t.as_str().unwrap().to_string())
            .collect()
    };
    let tags = |v: Vec<&'static str>| -> Vec<String> { v.into_iter().map(String::from).collect() };
    assert_eq!(
        names("scopes"),
        tags(scopes().iter().map(|s| s.tag()).collect())
    );
    assert_eq!(
        names("kinds"),
        tags(kinds().iter().map(|k| k.tag()).collect())
    );
    assert_eq!(
        names("false_codes"),
        tags(false_codes().iter().map(|c| c.tag()).collect())
    );
    assert_eq!(
        names("absorbable_scopes"),
        tags(
            scopes()
                .into_iter()
                .filter(|s| s.is_absorbable())
                .map(|s| s.tag())
                .collect()
        )
    );
    // The three groups, read from what the checked constructor accepts.
    let accepts =
        |k: NonCompletionKind, s: Option<CauseScope>| NonCompletion::from_parts(k, s).is_ok();
    let group = |f: &dyn Fn(NonCompletionKind) -> bool| -> Vec<String> {
        tags(
            kinds()
                .into_iter()
                .filter(|k| f(*k))
                .map(|k| k.tag())
                .collect(),
        )
    };
    assert_eq!(
        names("scoped_stops"),
        group(&|k| accepts(k, Some(CauseScope::Literal)))
    );
    assert_eq!(
        names("request_stops"),
        group(&|k| accepts(k, Some(CauseScope::Request)) && !accepts(k, Some(CauseScope::Literal)))
    );
    assert_eq!(names("faults"), group(&|k| accepts(k, None)));
    assert_eq!(names("faults"), group(&|k| k.is_fault()));
}

// ---- the broken counterparts ----

fn mutant_higher(a: Outcome, b: Outcome, rank: fn(&Outcome) -> u8) -> Outcome {
    if rank(&b) > rank(&a) {
        b
    } else {
        a
    }
}

/// The position of an outcome's class in `order`, under a class reading `read`.
fn rank_in(o: &Outcome, read: fn(&Outcome) -> &'static str, order: [&str; 5]) -> u8 {
    order
        .iter()
        .position(|c| *c == read(o))
        .expect("every class is ranked") as u8
}

/// Never absorbs: an undecided operand outranks a decided one in `and` and in `or`.
fn never_absorbs_and(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            class,
            ["holds", "fails", "absorbable", "dominant", "fault"],
        )
    })
}

fn never_absorbs_or(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            class,
            ["fails", "holds", "absorbable", "dominant", "fault"],
        )
    })
}

/// Absorbs every scope: a stop is absorbable wherever it reaches.
fn every_scope(o: &Outcome) -> &'static str {
    match o {
        Completion::NotCompleted(c) if c.scope().is_some() => "absorbable",
        other => class(other),
    }
}

fn absorbs_all_and(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            every_scope,
            ["holds", "absorbable", "fails", "dominant", "fault"],
        )
    })
}

fn absorbs_all_or(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            every_scope,
            ["fails", "absorbable", "holds", "dominant", "fault"],
        )
    })
}

/// Drops the fault class: a fault ranks with a limit, as before seat:caa's ruling on #3179.
fn fault_as_dominant(o: &Outcome) -> &'static str {
    match class(o) {
        "fault" => "dominant",
        other => other,
    }
}

fn no_fault_class_and(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            fault_as_dominant,
            ["holds", "absorbable", "fails", "dominant", "fault"],
        )
    })
}

fn no_fault_class_or(a: Outcome, b: Outcome) -> Outcome {
    mutant_higher(a, b, |o| {
        rank_in(
            o,
            fault_as_dominant,
            ["fails", "absorbable", "holds", "dominant", "fault"],
        )
    })
}

const NEVER_ABSORBS: Algebra = Algebra {
    not: completion::not::<String>,
    and: never_absorbs_and,
    or: never_absorbs_or,
};

const ABSORBS_REQUEST_SCOPE: Algebra = Algebra {
    not: completion::not::<String>,
    and: absorbs_all_and,
    or: absorbs_all_or,
};

const NO_FAULT_CLASS: Algebra = Algebra {
    not: completion::not::<String>,
    and: no_fault_class_and,
    or: no_fault_class_or,
};

fn assert_rejected(alg: &Algebra, mutant: &str, must_fail: &str) {
    let failures = replay(alg);
    assert!(
        failures
            .iter()
            .any(|f| f.starts_with(&format!("{must_fail} ("))),
        "the vector must reject the {mutant} mutant at {must_fail}; it failed only:\n{}",
        failures.join("\n")
    );
}

#[test]
fn completion_vectors_reject_an_algebra_that_never_absorbs() {
    assert_rejected(
        &NEVER_ABSORBS,
        "never-absorbs",
        "and_fails_absorbs_literal_undecided",
    );
    assert_rejected(
        &NEVER_ABSORBS,
        "never-absorbs",
        "or_holds_absorbs_literal_undecided",
    );
}

#[test]
fn completion_vectors_reject_an_algebra_that_absorbs_a_request_stop() {
    assert_rejected(
        &ABSORBS_REQUEST_SCOPE,
        "absorbs-request-scope",
        "and_fails_keeps_request_undecided",
    );
    assert_rejected(
        &ABSORBS_REQUEST_SCOPE,
        "absorbs-request-scope",
        "or_holds_keeps_request_undecided",
    );
}

#[test]
fn completion_vectors_reject_an_algebra_that_ranks_a_fault_with_a_limit() {
    assert_rejected(
        &NO_FAULT_CLASS,
        "no-fault-class",
        "and_limit_then_fault_reports_fault",
    );
    assert_rejected(
        &NO_FAULT_CLASS,
        "no-fault-class",
        "and_fault_then_limit_reports_fault",
    );
}
