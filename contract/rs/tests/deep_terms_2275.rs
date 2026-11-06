//! #2275 layer 3: every walk over a `Term` is bounded on the native stack. A surface list
//! `[a, b, ...]` nests one level per element, so an ordinary long list used to overflow the stack in
//! the derived `Clone`, `==`, `Hash` and `Drop`, and in every recursive walk.
//!
//! Each test builds a list [`DEPTH`] levels deep with a loop (building it cannot recurse) and runs
//! one walk over it on the test harness's default thread stack. At this depth a walk that recursed
//! once per level would overflow many times over, so a pass means the walk is bounded.
//!
//! No test turns a deep term into an `ontos::Value`: `Value`'s own derives still recurse, which is
//! Bitspark/ontos#340, and a deep `Value` would abort on drop whatever logos does.

use logos_contract::{Subst, Term, VarId, TERM_RECURSION_BUDGET};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Far past any native stack at one frame per level, and far past [`TERM_RECURSION_BUDGET`].
const DEPTH: usize = 200_000;

fn atom(s: &str) -> Term {
    Term::atom(s.as_bytes().to_vec())
}

/// `[e, e, ...]`, `len` elements, built from the tail up: one cons cell per element.
fn list_of(len: usize, element: impl Fn(usize) -> Term) -> Term {
    let mut list = atom("[]");
    for i in (0..len).rev() {
        list = Term::tuple([atom("."), element(i), list]);
    }
    list
}

fn hash_of(term: &Term) -> u64 {
    let mut hasher = DefaultHasher::new();
    term.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn a_deep_list_is_deeper_than_the_budget() {
    // The premise, checked rather than assumed.
    let list = list_of(DEPTH, |_| atom("a"));
    assert!(!list.depth_le(DEPTH));
    assert!(list.depth_le(DEPTH + 1));
    const { assert!(DEPTH > TERM_RECURSION_BUDGET * 1000) };
}

#[test]
fn clone_eq_hash_and_drop_are_bounded() {
    let list = list_of(DEPTH, |_| atom("a"));
    let copy = list.clone();
    assert_eq!(list, copy);
    assert_eq!(hash_of(&list), hash_of(&copy));
    // A difference at the very bottom is found, and hashes differently.
    let other = list_of(
        DEPTH,
        |i| if i + 1 == DEPTH { atom("b") } else { atom("a") },
    );
    assert_ne!(list, other);
    assert_ne!(hash_of(&list), hash_of(&other));
    // All three drop here, each through the iterative `Drop`.
}

#[test]
fn a_shallow_term_hashes_and_compares_as_the_derive_did() {
    // Behaviour preserved below the budget, where the plain recursion still runs.
    let a = Term::tuple([atom("f"), Term::var("X"), atom("b")]);
    let b = Term::tuple([atom("f"), Term::var("X"), atom("b")]);
    assert_eq!(a, b);
    assert_eq!(hash_of(&a), hash_of(&b));
    assert_ne!(a, Term::tuple([atom("f"), Term::var("Y"), atom("b")]));
}

#[test]
fn the_variable_walk_is_bounded_and_ordered() {
    let list = list_of(DEPTH, |i| {
        if i % 50_000 == 0 {
            Term::var(format!("V{i}"))
        } else {
            atom("a")
        }
    });
    assert!(!list.is_ground());
    let mut seen: Vec<VarId> = Vec::new();
    list.for_each_var(|v| seen.push(v.clone()));
    let names: Vec<&str> = seen.iter().map(|v| v.as_str()).collect();
    assert_eq!(names, ["V0", "V50000", "V100000", "V150000"]);
    assert!(list_of(DEPTH, |_| atom("a")).is_ground());
}

#[test]
fn fold_and_substitute_are_bounded() {
    let list = list_of(DEPTH, |_| Term::var("X"));
    // `fold`: count the leaves without building anything deep.
    let leaves = list
        .fold(
            |_| Some(1usize),
            |children: Vec<usize>| children.into_iter().sum(),
        )
        .expect("no leaf aborts");
    // Per cell: the `.` atom and the element; plus the final `[]`.
    assert_eq!(leaves, 2 * DEPTH + 1);
    // `substitute` rebuilds the whole list.
    let mut subst = Subst::new();
    subst.insert(VarId::new("X"), atom("a"));
    let ground = list.substitute(&subst);
    assert!(ground.is_ground());
    assert_eq!(ground, list_of(DEPTH, |_| atom("a")));
}
