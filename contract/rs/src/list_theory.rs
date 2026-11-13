//! `contract::list_theory` — the standard checkable `ListTheory` over the **reified**
//! `list` embedding (ADR 0016, Shelf A1). **[STABLE-v1 Theory impl.]**
//!
//! The Rust home of the A1 **list relations** over the ontos/data flat `list` embedding
//! `Tuple[Atom("list"), e0, …, e_{n-1}]` (spec §5.5) — the native, constant/linear-time,
//! *checkable* complement to the Shelf-B cons-cell `lists@1.1.0` prelude. It owns a
//! focused, clearly-checkable set of predicates and decides each by **destructuring the
//! `list(…)` embedding directly** (no search, no trail, no recursion over a clause set):
//!
//! - `length/2` — `length(list(e0..e_{n-1}), int(n))`: the reified list's length, counted
//!   against the frozen ontos/data `int` embedding (mirroring [`TermTheory`]'s
//!   `number/1` int handling via [`ontos_data::read_int`] / [`ontos_data::encode_int`]).
//! - `nth0/3` — `nth0(int(i), list(e0..), e_i)`: 0-indexed element access (Prolog /
//!   SWI argument order: index, list, element).
//! - `last/2` — `last(list(e0..e_{n-1}), e_{n-1})`: the last element of a non-empty list.
//!
//! `is_list/1` is ALREADY a [`TermTheory`] recognizer (over the FROZEN cons form) — this
//! theory does **not** duplicate it.
//!
//! # Why this is the A1 fast-path complement, not a duplicate (ADR 0016)
//!
//! The Shelf-B `lists@1.1.0` prelude (#284) ships `length/2`, `nth0/3`, `last/2` as
//! ordinary account `Rule` clauses over **cons cells** (`[H|T]` = `Tuple[Atom("."), H,
//! T]`); the existing `check` verifies them with zero new trusted code. This theory is the
//! native A1 reading over the **`list(…)` embedding** instead — the SAME relations, a
//! DIFFERENT representation. The two share predicate *names* but own structurally
//! disjoint argument shapes, so a profile binds exactly one of them per predicate (the
//! §4.4 builtin partition forbids a theory-owned name from also being a rule head). The
//! differential test (`conformance/rs/tests/list_theory_differential.rs`) pins the
//! "proven-identical meaning"
//! tie-break (ADR 0016 #1): on the shared ground domain the native decision AGREES with
//! the Shelf-B clause form.
//!
//! # Dual-conformance (§7)
//!
//! When the bound theory owns a predicate, the engine emits a `Builtin` account node for
//! a ground goal of that predicate, and `check` re-decides it with this same `decide_ground`.
//! `check` re-decides a `Builtin` node on its own spelling, exactly (#2232; every site is
//! structural since #3022), so a `Builtin` node concluding a `list(…)` relation is one
//! `check()` re-accepts — the dual-conformance law.
//!
//! # Judgments
//!
//! `owns(pred)`: by NAME only (any arity) — `length`, `nth0`, `last`.
//! `decide_ground(atom)` on a ground atom: a non-UTF-8 predicate → `Fails{list_unknown_predicate}`
//! (defensive); an owned name at the wrong arity → `Fails{list_bad_arity}`; the relation
//! true → `Holds`; the relation false (a non-`list` argument, an out-of-range index, a
//! count/element mismatch, an empty list for `last`) → `Fails{list_does_not_hold}`.

use ontos_core::Value;

use crate::{ComponentIdentity, GroundLiteral, Symbol, Theory, TheoryGround};

/// The predicate names this theory owns. Owned by NAME only (any arity); a wrong arity is
/// then a `list_bad_arity` failure, exactly as [`TermTheory`](crate::term_theory) handles
/// its recognizers / comparisons.
const LIST_PREDICATES: &[&[u8]] = &[b"length", b"nth0", b"last"];

/// The predicate set this theory owns — the three reified-list relations (`length`, `nth0`, `last`) — the SAME set its `owns` recognizes by name.
///
/// Exposed for the #1406 guard family: an engine path with no builtin evaluation must be
/// able to ask "does this program carry a literal I cannot decide?" without a `Theory`
/// handle, which `EngineProvider::prepare` does not receive. Mirrors
/// [`arithmetic_predicate_set`](crate::arithmetic::arithmetic_predicate_set), which was the
/// only such set exposed until the silent zero was measured on THIS theory too.
pub fn list_predicate_set() -> crate::PredicateSet {
    LIST_PREDICATES
        .iter()
        .map(|bytes| crate::Symbol::new(bytes.to_vec()))
        .collect()
}

/// Whether `pred` names an owned list relation (`length nth0 last`).
fn owns_name(pred: &Symbol) -> bool {
    LIST_PREDICATES.contains(&pred.bytes())
}

/// The config-pinned §5 [`Theory`] that owns the A1 list relations (`length nth0 last`)
/// over the ontos/data `list` embedding and decides a GROUND atom by a direct structural
/// match against `list(…)` (constant/linear, no search, no trail). Pure / total /
/// deterministic / config-free — a faithful mirror of the Go/TS bindings.
#[derive(Clone, Copy, Debug, Default)]
pub struct ListTheory;

impl ListTheory {
    /// The standard list theory (no configuration).
    pub fn new() -> Self {
        ListTheory
    }
}

impl Theory for ListTheory {
    /// Opt in to the #1023 probe clone. `ListTheory` is a stateless `Copy` unit, so an
    /// independent copy is the value itself — the probe runs under a theory byte-identical to
    /// the one the provider advertises, which is what keeps the check-profile digest equal.
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, crate::spi::CopyIncapacity> {
        Ok(Box::new(*self))
    }

    fn owns(&self, pred: &Symbol) -> bool {
        owns_name(pred)
    }

    /// `logos-core/list-theory@1.0.0`, no config. The `logos-core/` namespace is a STABLE
    /// IDENTITY, not a path (ADR 0014/0016): it is byte-frozen in `vectors/list.json` and
    /// stays this string regardless of the theory's physical home — mirroring
    /// [`TermTheory`](crate::term_theory)'s identity.
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/list-theory".to_vec(),
            b"1.0.0".to_vec(),
            [0u8; 32],
        )
    }

    /// #3142: every decision completes. `length`, `nth0` and `last` destructure the `list(..)`
    /// embedding directly, with no cap, so a `Fails` here is always a decided false.
    fn completion(&self, _pred: &Symbol) -> crate::spi::DecisionCompletion {
        crate::spi::DecisionCompletion::StopsAreTyped
    }

    fn decide_ground(&self, atom: &GroundLiteral) -> TheoryGround {
        // Not one of ours: a routing safety net (`check` routes by `owns`, so this is
        // unreachable on a correctly-routed call — but stay total).
        if !owns_name(&atom.pred) {
            return TheoryGround::disowned();
        }
        let name = match std::str::from_utf8(atom.pred.bytes()) {
            Ok(name) => name,
            // A non-UTF-8 predicate cannot be a registered list relation.
            Err(_) => return TheoryGround::fails("list_unknown_predicate"),
        };
        match name {
            "length" => decide_length(&atom.args),
            "nth0" => decide_nth0(&atom.args),
            "last" => decide_last(&atom.args),
            // Owned name routed here but not handled above — unreachable (the name set is
            // exactly the match arms above), but stay total.
            _ => TheoryGround::fails("list_does_not_hold"),
        }
    }
}

/// Read the elements of a GROUND `list` embedding `Tuple[Atom("list"), e0, …]`, or `None`
/// if the value is not a canonical list embedding. Thin wrapper over the frozen
/// [`ontos_data::read_list`] — the SAME recognizer the producer's `reify_lists` emits
/// through, so producer and checker agree by construction.
fn list_elements(value: &Value) -> Option<Vec<Value>> {
    ontos_data::read_list(value).ok()
}

/// A `Holds` shorthand for a passing relation.
fn holds() -> TheoryGround {
    TheoryGround::holds()
}

/// A `Fails{list_does_not_hold}` shorthand: the arguments are well-formed shape-wise but
/// the relation is false (non-`list` argument, out-of-range index, count/element
/// mismatch, or an empty list for `last`).
fn does_not_hold() -> TheoryGround {
    TheoryGround::fails("list_does_not_hold")
}

/// A `Fails{list_bad_arity}` shorthand: an owned name at an arity with no such relation.
fn bad_arity() -> TheoryGround {
    TheoryGround::fails("list_bad_arity")
}

/// `length(list(e0..e_{n-1}), int(n))`: arity must be 2; then `arg0` must be a `list`
/// embedding of `n` elements AND `arg1` must be the canonical `int` embedding of that same
/// `n`. A non-`list` `arg0`, a non-`int` `arg1`, or a count mismatch is `list_does_not_hold`.
fn decide_length(args: &[Value]) -> TheoryGround {
    if args.len() != 2 {
        return bad_arity();
    }
    let Some(elems) = list_elements(&args[0]) else {
        return does_not_hold();
    };
    // The list's length is always a small non-negative count; build the canonical `int`
    // embedding and compare structurally — so `arg1` must be the SAME canonical int the
    // Shelf-B `length` clauses (`is/2` over the `int` embedding) accumulate. A non-int or a
    // wrong-int `arg1` simply fails to equal it.
    let want = ontos_data::encode_int(elems.len() as i128);
    if args[1] == want {
        holds()
    } else {
        does_not_hold()
    }
}

/// `nth0(int(i), list(e0..e_{n-1}), e_i)`: arity must be 3; then `arg0` must be a
/// non-negative `int` index `i`, `arg1` a `list` embedding, `i` in range `0 ≤ i < n`, and
/// `arg2` structurally equal to the `i`-th element. A non-`int` index, a non-`list`,
/// an out-of-range index, or an element mismatch is `list_does_not_hold`. (Prolog / SWI
/// argument order: index, list, element.)
fn decide_nth0(args: &[Value]) -> TheoryGround {
    if args.len() != 3 {
        return bad_arity();
    }
    // Index must be the canonical `int` embedding. A non-int / negative / out-of-range
    // index is simply a false relation (the element does not exist at that position).
    let Ok(index) = ontos_data::read_int(&args[0]) else {
        return does_not_hold();
    };
    let Some(elems) = list_elements(&args[1]) else {
        return does_not_hold();
    };
    if index < 0 {
        return does_not_hold();
    }
    // index >= 0 here; compare against the (usize) length. A huge index that overflows
    // usize is trivially out of range.
    let Ok(idx) = usize::try_from(index) else {
        return does_not_hold();
    };
    match elems.get(idx) {
        Some(elem) if *elem == args[2] => holds(),
        _ => does_not_hold(),
    }
}

/// `last(list(e0..e_{n-1}), e_{n-1})`: arity must be 2; then `arg0` must be a NON-EMPTY
/// `list` embedding and `arg1` structurally equal to its last element. A non-`list`, an
/// empty list, or a mismatch is `list_does_not_hold`.
fn decide_last(args: &[Value]) -> TheoryGround {
    if args.len() != 2 {
        return bad_arity();
    }
    let Some(elems) = list_elements(&args[0]) else {
        return does_not_hold();
    };
    match elems.last() {
        Some(last) if *last == args[1] => holds(),
        _ => does_not_hold(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::completion::{Completion, TheoryDecision};

    fn atomv(s: &str) -> Value {
        Value::atom(s.as_bytes().to_vec())
    }
    fn listv(elems: &[Value]) -> Value {
        ontos_data::encode_list(elems)
    }
    fn intv(n: i128) -> Value {
        ontos_data::encode_int(n)
    }
    fn lit(pred: &str, args: Vec<Value>) -> GroundLiteral {
        GroundLiteral::new(pred, args)
    }

    fn holds(t: &ListTheory, pred: &str, args: Vec<Value>) {
        assert_eq!(
            t.decide_ground(&lit(pred, args)),
            TheoryGround::holds(),
            "{pred} should Hold"
        );
    }
    fn fails(t: &ListTheory, pred: &str, args: Vec<Value>, code: &str) {
        let outcome = t.decide_ground(&lit(pred, args));
        let Completion::Completed(TheoryDecision::Fails { code: got }) = &outcome else {
            panic!("{pred}: want Fails{{{code}}}, got {outcome:?}");
        };
        assert_eq!(got, code, "{pred} fail-code");
    }

    #[test]
    fn owns_only_the_three_relations() {
        let t = ListTheory::new();
        for name in ["length", "nth0", "last"] {
            assert!(
                t.owns(&Symbol::new(name.as_bytes().to_vec())),
                "owns {name}"
            );
        }
        for name in [
            "is_list", "member", "reverse", "append", "nth1", "msort", "is",
        ] {
            assert!(
                !t.owns(&Symbol::new(name.as_bytes().to_vec())),
                "must NOT own {name}"
            );
        }
    }

    #[test]
    fn identity_is_logos_core_list_theory() {
        let id = ListTheory::new().identity();
        assert_eq!(id.id, b"logos-core/list-theory");
        assert_eq!(id.version, b"1.0.0");
        assert_eq!(id.config_digest, [0u8; 32]);
    }

    #[test]
    fn length_decides_against_the_int_embedding() {
        let t = ListTheory::new();
        // length(list(), int(0))
        holds(&t, "length", vec![listv(&[]), intv(0)]);
        // length(list(a, b), int(2))
        holds(
            &t,
            "length",
            vec![listv(&[atomv("a"), atomv("b")]), intv(2)],
        );
        // wrong count fails
        fails(
            &t,
            "length",
            vec![listv(&[atomv("a"), atomv("b")]), intv(3)],
            "list_does_not_hold",
        );
        // a non-list arg0 fails
        fails(
            &t,
            "length",
            vec![atomv("not_a_list"), intv(0)],
            "list_does_not_hold",
        );
        // a cons-form arg0 is NOT the reified embedding -> fails (this theory is over list())
        let cons = Value::tuple([atomv("."), atomv("a"), atomv("[]")]);
        fails(&t, "length", vec![cons, intv(1)], "list_does_not_hold");
        // a non-int count fails
        fails(
            &t,
            "length",
            vec![listv(&[atomv("a")]), atomv("1")],
            "list_does_not_hold",
        );
        // bad arity
        fails(&t, "length", vec![listv(&[])], "list_bad_arity");
    }

    #[test]
    fn nth0_in_and_out_of_range() {
        let t = ListTheory::new();
        let l = || listv(&[atomv("a"), atomv("b"), atomv("c")]);
        holds(&t, "nth0", vec![intv(0), l(), atomv("a")]);
        holds(&t, "nth0", vec![intv(2), l(), atomv("c")]);
        // wrong element at a valid index
        fails(
            &t,
            "nth0",
            vec![intv(1), l(), atomv("a")],
            "list_does_not_hold",
        );
        // out of range
        fails(
            &t,
            "nth0",
            vec![intv(3), l(), atomv("a")],
            "list_does_not_hold",
        );
        // negative index
        fails(
            &t,
            "nth0",
            vec![intv(-1), l(), atomv("a")],
            "list_does_not_hold",
        );
        // non-int index
        fails(
            &t,
            "nth0",
            vec![atomv("0"), l(), atomv("a")],
            "list_does_not_hold",
        );
        // non-list
        fails(
            &t,
            "nth0",
            vec![intv(0), atomv("x"), atomv("a")],
            "list_does_not_hold",
        );
        // bad arity
        fails(&t, "nth0", vec![intv(0), l()], "list_bad_arity");
    }

    #[test]
    fn last_singleton_multi_and_empty() {
        let t = ListTheory::new();
        holds(&t, "last", vec![listv(&[atomv("x")]), atomv("x")]);
        holds(
            &t,
            "last",
            vec![listv(&[atomv("a"), atomv("b"), atomv("c")]), atomv("c")],
        );
        // empty list has no last element
        fails(
            &t,
            "last",
            vec![listv(&[]), atomv("a")],
            "list_does_not_hold",
        );
        // wrong element
        fails(
            &t,
            "last",
            vec![listv(&[atomv("a"), atomv("b")]), atomv("a")],
            "list_does_not_hold",
        );
        // non-list
        fails(
            &t,
            "last",
            vec![atomv("x"), atomv("x")],
            "list_does_not_hold",
        );
        // bad arity
        fails(
            &t,
            "last",
            vec![listv(&[atomv("a")]), atomv("a"), atomv("b")],
            "list_bad_arity",
        );
    }

    #[test]
    fn nested_list_elements_compare_structurally() {
        let t = ListTheory::new();
        // length(list(list(a), b), int(2)) — the elements may themselves be embeddings.
        let nested = listv(&[listv(&[atomv("a")]), atomv("b")]);
        holds(&t, "length", vec![nested.clone(), intv(2)]);
        // nth0(int(0), list(list(a), b), list(a))
        holds(
            &t,
            "nth0",
            vec![intv(0), nested.clone(), listv(&[atomv("a")])],
        );
        // last(list(list(a), b), b)
        holds(&t, "last", vec![nested, atomv("b")]);
    }

    #[test]
    fn not_mine_routing_safety_net() {
        let t = ListTheory::new();
        assert_eq!(
            t.decide_ground(&lit("member", vec![atomv("a")])),
            TheoryGround::disowned()
        );
    }
}
