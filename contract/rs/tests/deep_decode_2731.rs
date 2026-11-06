//! #2731 (`seat:caa`'s ruling: remove the restriction, keep the promise): the derivation decoder
//! imposes no depth policy. It used to refuse any quoted value deeper than 256 VALUE levels
//! (#253's fixed guard, about 128 TERM levels), because its readers recursed once per level. Go and
//! ts decode those derivations and every core's `check` accepts them at its default
//! `max_term_depth` of 256, so the guard made the spec's tri-core acceptance promise false.
//!
//! The readers the guard protected, `reify` and `erase_ground`, now recurse only within
//! [`TERM_RECURSION_BUDGET`] and continue on a heap stack (#2275 layer 3). Each test here decodes a
//! term [`LEVELS`] deep through a public door of the decoder, on the test harness's default thread
//! stack, where one native frame per level would overflow many times over. A pass means the door is
//! bounded.
//!
//! Unlike `deep_terms_2275.rs`, these tests must build deep `ontos::Value`s, because the decoder
//! reads and yields them. `Value`'s own derived `Drop` still recurses once per level
//! (Bitspark/ontos#340), so every deep `Value` here is leaked with `ManuallyDrop`. What is compared
//! is the decoded TERM, whose walks are logos's and bounded.

use logos_contract::derivation_wire::{ground_literal_from_value_v1, subst_from_value};
use logos_contract::{quote, Term, VarId, TERM_RECURSION_BUDGET};
use ontos_core::Value;
use std::mem::ManuallyDrop;

/// Far past any native stack at one frame per level, and far past [`TERM_RECURSION_BUDGET`].
const LEVELS: usize = 100_000;

fn atom(s: &str) -> Term {
    Term::atom(s.as_bytes().to_vec())
}

/// `s(s(...s(z)...))`, [`LEVELS`] deep (the atom counts as one level), built from the leaf up.
fn chain() -> Term {
    let mut term = atom("z");
    for _ in 1..LEVELS {
        term = Term::tuple([atom("s"), term]);
    }
    term
}

#[test]
fn the_chain_is_deeper_than_the_budget() {
    // The premise, checked rather than assumed.
    let term = chain();
    assert!(!term.depth_le(LEVELS - 1));
    assert!(term.depth_le(LEVELS));
    const { assert!(LEVELS > TERM_RECURSION_BUDGET * 1000) };
}

#[test]
fn a_deep_ground_argument_decodes_without_a_frame_per_level() {
    let term = chain();
    // The account representation of `edge(<term>)`: `Tuple[Atom(pred), quote(arg)]`.
    let value = ManuallyDrop::new(Value::tuple([Value::atom(*b"edge"), quote(&term)]));
    let literal = ManuallyDrop::new(
        ground_literal_from_value_v1(&value).expect("a deep ground argument decodes"),
    );
    assert_eq!(literal.pred.bytes(), b"edge");
    assert_eq!(literal.args.len(), 1);
    assert_eq!(Term::from_value(&literal.args[0]), term);
}

#[test]
fn a_deep_subst_term_decodes_without_a_frame_per_level() {
    // A subst term may hold variables; one sits at the very bottom, under every level.
    let mut term = Term::var("Y");
    for _ in 1..LEVELS {
        term = Term::tuple([atom("s"), term]);
    }
    let value = ManuallyDrop::new(Value::tuple([Value::tuple([
        Value::atom(*b"X"),
        quote(&term),
    ])]));
    let subst = subst_from_value(&value).expect("a deep subst term decodes");
    assert_eq!(subst.get(&VarId::new("X")), Some(&term));
}
