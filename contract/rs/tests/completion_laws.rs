//! The completion algebra's laws, checked over EVERY ground outcome its vocabulary can form
//! (research 0031 row 15, #3164; seat:caa's ruling on #3179).
//!
//! The carrier is finite: `Holds`, `Fails` with each code, every legal stop (the scoped stops at
//! each scope, the request-wide stops), every fault, and `LimitExceeded` with two limit names. So
//! each law below is checked over every pair or triple, not over a random sample: for this
//! implementation it is a proof by enumeration. The Go
//! (`contract/go/completion/completion_laws_test.go`) and TypeScript
//! (`contract/ts/test/completion_laws.test.ts`) twins check the same laws.
//!
//! The Kleene tables and the legal kind/scope pairs are written out independently of the
//! implementation, from research 0031's advice §3 and the #3179 ruling.

use logos_contract::completion::{
    self, CauseScope, Completion, Decision, FalseCode, GroundOutcome, NonCompletion,
    NonCompletionKind,
};

type Outcome = GroundOutcome<&'static str>;

const SCOPES: [CauseScope; 6] = [
    CauseScope::Literal,
    CauseScope::Branch,
    CauseScope::Enumeration,
    CauseScope::Dependency,
    CauseScope::TheorySnapshot,
    CauseScope::Request,
];

const KINDS: [NonCompletionKind; 7] = [
    NonCompletionKind::Capacity,
    NonCompletionKind::WorkCap,
    NonCompletionKind::Instantiation,
    NonCompletionKind::HostRefusal,
    NonCompletionKind::ReplyUnreadable,
    NonCompletionKind::InconsistentTheory,
    NonCompletionKind::MalformedOutcome,
];

/// The legal pairs, from the ruling: a scoped stop at any scope, a request stop at request scope,
/// a fault with no scope. Written as a table, independently of `from_parts`.
fn legal(kind: NonCompletionKind, scope: Option<CauseScope>) -> bool {
    use NonCompletionKind::*;
    match kind {
        Capacity | WorkCap | Instantiation => scope.is_some(),
        HostRefusal | ReplyUnreadable => scope == Some(CauseScope::Request),
        InconsistentTheory | MalformedOutcome => scope.is_none(),
    }
}

fn every_pair() -> Vec<(NonCompletionKind, Option<CauseScope>)> {
    let mut all = Vec::new();
    for k in KINDS {
        all.push((k, None));
        for s in SCOPES {
            all.push((k, Some(s)));
        }
    }
    all
}

fn carrier() -> Vec<Outcome> {
    let mut all = vec![
        Completion::Completed(Decision::Holds),
        Completion::Completed(Decision::Fails {
            code: FalseCode::Unsatisfied,
        }),
        Completion::LimitExceeded("limit_a"),
        Completion::LimitExceeded("limit_b"),
    ];
    for (k, s) in every_pair() {
        if let Ok(c) = NonCompletion::from_parts(k, s) {
            all.push(Completion::NotCompleted(c));
        }
    }
    all
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Truth {
    True,
    False,
    Undecided,
}

fn truth(o: &Outcome) -> Truth {
    match o {
        Completion::Completed(Decision::Holds) => Truth::True,
        Completion::Completed(Decision::Fails { .. }) => Truth::False,
        Completion::NotCompleted(_) | Completion::LimitExceeded(_) => Truth::Undecided,
    }
}

/// 0 decided or absorbable, 1 a dominant stop or a limit, 2 a fault.
fn tier(o: &Outcome) -> u8 {
    match o {
        Completion::Completed(_) => 0,
        Completion::LimitExceeded(_) => 1,
        Completion::NotCompleted(c) => match c.scope() {
            None => 2,
            Some(s) if s.is_absorbable() => 0,
            Some(_) => 1,
        },
    }
}

fn class(o: &Outcome) -> (Truth, u8) {
    (truth(o), tier(o))
}

// The strong-Kleene tables (advice §3), independent of the implementation.
fn k_not(a: Truth) -> Truth {
    match a {
        Truth::True => Truth::False,
        Truth::False => Truth::True,
        Truth::Undecided => Truth::Undecided,
    }
}

fn k_and(a: Truth, b: Truth) -> Truth {
    if a == Truth::False || b == Truth::False {
        Truth::False
    } else if a == Truth::Undecided || b == Truth::Undecided {
        Truth::Undecided
    } else {
        Truth::True
    }
}

fn k_or(a: Truth, b: Truth) -> Truth {
    if a == Truth::True || b == Truth::True {
        Truth::True
    } else if a == Truth::Undecided || b == Truth::Undecided {
        Truth::Undecided
    } else {
        Truth::False
    }
}

use completion::{and, not, or};

type Op = fn(Outcome, Outcome) -> Outcome;

fn ops() -> [(&'static str, Op); 2] {
    [("and", and::<&'static str>), ("or", or::<&'static str>)]
}

#[test]
fn the_constructor_builds_exactly_the_legal_pairs() {
    for (k, s) in every_pair() {
        match NonCompletion::from_parts(k, s) {
            Ok(c) => {
                assert!(legal(k, s), "{k:?} at {s:?} was built");
                assert_eq!((c.kind(), c.scope()), (k, s));
            }
            Err(e) => {
                assert!(!legal(k, s), "{k:?} at {s:?} was refused");
                assert_eq!((e.kind, e.scope), (k, s));
            }
        }
    }
    // The named constructors build the same values.
    use CauseScope::*;
    for s in SCOPES {
        assert_eq!(NonCompletion::capacity(s).scope(), Some(s));
        assert_eq!(NonCompletion::work_cap(s).scope(), Some(s));
        assert_eq!(NonCompletion::instantiation(s).scope(), Some(s));
    }
    assert_eq!(NonCompletion::host_refusal().scope(), Some(Request));
    assert_eq!(NonCompletion::reply_unreadable().scope(), Some(Request));
    assert_eq!(NonCompletion::inconsistent_theory().scope(), None);
    assert_eq!(NonCompletion::malformed_outcome().scope(), None);
    for k in KINDS {
        assert_eq!(
            k.is_fault(),
            legal(k, None),
            "{k:?}: a fault is exactly a kind with no scope"
        );
    }
}

#[test]
fn carrier_is_the_whole_vocabulary() {
    // 2 decisions + 2 limits + 3 scoped stops x 6 scopes + 2 request stops + 2 faults
    assert_eq!(carrier().len(), 26);
}

#[test]
fn negation_is_strong_kleene_and_an_involution() {
    for a in carrier() {
        assert_eq!(truth(&not(a)), k_not(truth(&a)), "not {a:?}");
        // Exact, except that negation cannot recover a Fails code: not(not(Fails)) is Fails
        // with the code negation gives.
        let back = match a {
            Completion::Completed(Decision::Fails { .. }) => {
                Completion::Completed(Decision::Fails {
                    code: FalseCode::Unsatisfied,
                })
            }
            other => other,
        };
        assert_eq!(not(not(a)), back, "not not {a:?}");
        if truth(&a) == Truth::Undecided {
            assert_eq!(not(a), a, "not keeps an undecided outcome unchanged: {a:?}");
        }
    }
}

#[test]
fn idempotence() {
    for a in carrier() {
        assert_eq!(and(a, a), a, "{a:?} and itself");
        assert_eq!(or(a, a), a, "{a:?} or itself");
    }
}

#[test]
fn commutativity_of_the_class_and_exactly_when_classes_differ() {
    for a in carrier() {
        for b in carrier() {
            for (name, f) in ops() {
                let (ab, ba) = (f(a, b), f(b, a));
                assert_eq!(class(&ab), class(&ba), "{a:?} {name} {b:?}");
                if class(&a) != class(&b) {
                    assert_eq!(ab, ba, "{a:?} {name} {b:?}: one operand outranks the other");
                }
            }
        }
    }
}

#[test]
fn associativity_is_exact() {
    let all = carrier();
    for a in &all {
        for b in &all {
            for c in &all {
                assert_eq!(
                    and(and(*a, *b), *c),
                    and(*a, and(*b, *c)),
                    "and {a:?} {b:?} {c:?}"
                );
                assert_eq!(
                    or(or(*a, *b), *c),
                    or(*a, or(*b, *c)),
                    "or {a:?} {b:?} {c:?}"
                );
            }
        }
    }
}

#[test]
fn de_morgan_is_exact() {
    for a in carrier() {
        for b in carrier() {
            assert_eq!(not(and(a, b)), or(not(a), not(b)), "not({a:?} and {b:?})");
            assert_eq!(not(or(a, b)), and(not(a), not(b)), "not({a:?} or {b:?})");
        }
    }
}

#[test]
fn without_a_dominant_operand_the_truth_is_strong_kleene() {
    for a in carrier().into_iter().filter(|o| tier(o) == 0) {
        for b in carrier().into_iter().filter(|o| tier(o) == 0) {
            assert_eq!(
                truth(&and(a, b)),
                k_and(truth(&a), truth(&b)),
                "{a:?} and {b:?}"
            );
            assert_eq!(
                truth(&or(a, b)),
                k_or(truth(&a), truth(&b)),
                "{a:?} or {b:?}"
            );
            // lattice absorption, on the truth value
            assert_eq!(
                truth(&and(a, or(a, b))),
                truth(&a),
                "{a:?} and ({a:?} or {b:?})"
            );
            assert_eq!(
                truth(&or(a, and(a, b))),
                truth(&a),
                "{a:?} or ({a:?} and {b:?})"
            );
        }
    }
}

/// A dominant stop, a limit or a fault is never absorbed; a fault outranks the other two; and the
/// leftmost of the top tier is reported.
#[test]
fn the_highest_tier_is_never_absorbed_and_the_leftmost_is_reported() {
    for a in carrier() {
        for b in carrier() {
            let top = tier(&a).max(tier(&b));
            if top == 0 {
                continue;
            }
            let leftmost = if tier(&a) == top { a } else { b };
            assert_eq!(and(a, b), leftmost, "{a:?} and {b:?}");
            assert_eq!(or(a, b), leftmost, "{a:?} or {b:?}");
        }
    }
}

/// The absorption criterion (advice §3): a decided result must not rely on how an undecided
/// operand would resolve. Replacing an absorbable undecided operand by `Holds` or by `Fails` must
/// leave a decided result's truth unchanged.
#[test]
fn a_decided_result_does_not_depend_on_an_undecided_operand() {
    let decided = [
        Completion::Completed(Decision::Holds),
        Completion::Completed(Decision::Fails {
            code: FalseCode::Unsatisfied,
        }),
    ];
    for a in carrier() {
        for b in carrier() {
            for (name, f) in ops() {
                let r = f(a, b);
                if truth(&r) == Truth::Undecided {
                    continue;
                }
                for d in decided {
                    if truth(&a) == Truth::Undecided {
                        assert_eq!(
                            truth(&f(d, b)),
                            truth(&r),
                            "{a:?} {name} {b:?}, {a:?} as {d:?}"
                        );
                    }
                    if truth(&b) == Truth::Undecided {
                        assert_eq!(
                            truth(&f(a, d)),
                            truth(&r),
                            "{a:?} {name} {b:?}, {b:?} as {d:?}"
                        );
                    }
                }
            }
        }
    }
}
