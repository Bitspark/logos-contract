//! `contract::term_theory` — the standard checkable term-algebra `Theory` (ADR 0016,
//! Shelf A0). **[STABLE-v1 Theory impl.]**
//!
//! The Rust home of the A0 **term recognizers** (`atom/1`, `atomic/1`, `compound/1`,
//! `is_list/1`, `number/1`) and the **standard-order** comparisons (`==/2`, `\==/2`,
//! `@</2`, `@>/2`, `@=</2`, `@>=/2`), placed in the contract tier beside the Theory SPI
//! per ADR 0014 / ADR 0016 (Shelf A0: pure, total, deterministic functions of a *resolved
//! ground* term — they introspect term structure, **not** the trail, so they are
//! byte-identical tri-core and non-derivable from a smaller clause set). Their *meaning*
//! is therefore a shared, certifiable artifact rather than a search-only Rust builtin.
//!
//! The search-side builtins (`logos_core::builtins::{builtin_atom, …, builtin_order_lt,
//! …}`) stay in `core` as the fast path over `Term`/`Subst`; this `decide_ground` reproduces
//! them byte-for-byte over the SAME structure — the §7 dual-conformance law, pinned by
//! `vectors/term.json` and mirrored tri-core (`contract/{go,ts}`). To guarantee that, the
//! standard order itself ([`compare_values`]) lives HERE and is the single source `core`'s
//! `@<` family imports (the allowed `core → contract` edge), exactly as
//! [`arithmetic::apply_operator`](crate::arithmetic::apply_operator) is shared.
//!
//! # The standard order of terms (documented + total)
//!
//! Ground terms are an `ontos::Value = Atom(Bytes) | Tuple(Value*)` — there is **no
//! `Var`** in a ground atom (a `Var` is logos's sole non-ground addition). The full
//! standard order over *all* terms is `Var < Atom < Tuple`; restricted to the ground
//! terms a `decide_ground` ever sees it is just
//!
//! ```text
//! Atom  <  Tuple
//! ```
//!
//! with ties broken structurally: two `Atom`s by their raw bytes (lexicographic,
//! shorter-is-prefix-first), two `Tuple`s first by **arity** (length) then element-wise.
//! The order is *total* and consistent with structural equality
//! (`compare_values(a, b) == Equal ⟺ a == b`), so `@<`/`@>` are antisymmetric and
//! `@=<`/`@>=` are reflexive.
//!
//! **Number rank note.** ISO Prolog ranks `Var < Number < Atom < Compound`. logos has no
//! distinct `Number` term: an integer is the `ontos-data` `int` *embedding*
//! `Tuple(Atom("int"), Atom(payload))`, i.e. structurally a `Tuple`. So a number sorts
//! with the **compound** rank, **not** before atoms — this is the natural specialization
//! of the standard order onto logos's three-constructor term world and is exactly what
//! the search-side `core::builtins::compare_terms` computes, so search and check agree.
//! (The `number/1` recognizer below still distinguishes a number from a bare atom — it is
//! the int embedding's *shape*, an A1 reading, while the order is purely A0 structural.)
//!
//! # Judgments
//!
//! `owns(pred)`: by NAME only (any arity) — the five recognizers, the six comparisons,
//! univ, and (since `1.1.0`, #1611) unification and the control constants.
//! `decide_ground(atom)` on a ground atom: a non-UTF-8 predicate → `Fails{term_unknown_predicate}`
//! (defensive); an owned name at the wrong arity (a recognizer not at arity 1, a
//! comparison not at arity 2, a control constant not at arity 0) → `Fails{term_bad_arity}`;
//! the relation true → `Holds`; the relation false → `Fails{term_does_not_hold}`.
//!
//! # Unification and the control constants (`1.1.0`, #1611 — `seat:caa`'s ruling)
//!
//! `=`/2, `\=`/2, `true`/0, `fail`/0 and `false`/0 are registered by the search-side
//! Stage-A registry and served by sldnf, but sldnf consults the registry only behind
//! `theory.owns(pred)`, and the checker's `Builtin` arm accepts a node only if a bound theory
//! owns its predicate — so until a theory owned them, `X = a` in a rule body yielded a
//! SILENT empty answer and no `Builtin` node could ever certify. The account grammar
//! (`Rule | Builtin | Leaf`, ADR 0001) leaves no engine-native form, so the ruling puts them
//! HERE with ground semantics: on ground terms syntactic unification coincides with structural
//! equality, so `t = u` holds iff `compare_values(t, u) == Equal` and `t \= u` holds iff they
//! differ; `true` holds; `fail` and `false` never hold. A non-ground atom cannot reach
//! `decide_ground` (it takes a `GroundLiteral`), so there is no NotMine arm for an unbound `=`.

use std::cmp::Ordering;

use ontos_core::Value;

use crate::decval::BigDecimal;
use crate::intval::BigInt;
use crate::{ComponentIdentity, GroundLiteral, Symbol, Term, Theory, TheoryGround};

/// The list-cons functor `.`/2 (`[H|T]` = `Tuple[Atom("."), H, T]`) and nil `[]`.
const CONS_FUNCTOR: &[u8] = b".";
const NIL_ATOM: &[u8] = b"[]";

/// The arity-1 recognizers this theory owns. Owned by NAME only.
const RECOGNIZER_PREDICATES: &[&[u8]] = &[b"atom", b"atomic", b"compound", b"is_list", b"number"];

/// The arity-2 standard-order comparisons this theory owns. Owned by NAME only.
const COMPARISON_PREDICATES: &[&[u8]] = &[b"==", b"\\==", b"@<", b"@>", b"@=<", b"@>="];

/// The arity-2 unification relations this theory owns since `1.1.0` (#1611): `=` holds iff
/// the two GROUND terms are structurally equal (syntactic unification of ground terms IS
/// structural equality), `\=` iff they differ. Owned by NAME only.
const UNIFICATION_PREDICATES: &[&[u8]] = &[b"=", b"\\="];

/// The arity-0 control constants this theory owns since `1.1.0` (#1611): `true` holds,
/// `fail` and `false` never do. Owned by NAME only.
const CONTROL_PREDICATES: &[&[u8]] = &[b"true", b"fail", b"false"];

/// The predicate set this theory owns — the UNION of its recognizers and its comparisons,
/// the same two constants its `owns` consults.
///
/// ⚠ **Two constants, not one**, which is why this cannot be derived by the caller: a guard
/// that reached for `RECOGNIZER_PREDICATES` alone would silently under-detect every
/// comparison literal. Exposed for the #1406 guard family; see
/// [`arithmetic_predicate_set`](crate::arithmetic::arithmetic_predicate_set).
pub fn term_predicate_set() -> crate::PredicateSet {
    RECOGNIZER_PREDICATES
        .iter()
        .chain(COMPARISON_PREDICATES.iter())
        .chain(UNIFICATION_PREDICATES.iter())
        .chain(CONTROL_PREDICATES.iter())
        .map(|bytes| crate::Symbol::new(bytes.to_vec()))
        .collect()
}

/// The arity-2 structural decomposition primitive `=..` (univ): relates a term to
/// the cons-list `[Functor | Args]` of its principal functor and arguments (#658).
/// The reference companion to the search-side `core::builtins` univ builtin.
const UNIV_PREDICATE: &[u8] = b"=..";

/// Whether `pred` names an owned term recognizer (`atom atomic compound is_list number`).
fn owns_recognizer(pred: &Symbol) -> bool {
    RECOGNIZER_PREDICATES.contains(&pred.bytes())
}

/// Whether `pred` names an owned standard-order comparison (`== \== @< @> @=< @>=`).
fn owns_comparison(pred: &Symbol) -> bool {
    COMPARISON_PREDICATES.contains(&pred.bytes())
}

/// Whether `pred` names the structural decomposition primitive `=..` (univ).
fn owns_univ(pred: &Symbol) -> bool {
    pred.bytes() == UNIV_PREDICATE
}

/// Whether `pred` names an owned unification relation (`=` `\=`, #1611).
fn owns_unification(pred: &Symbol) -> bool {
    UNIFICATION_PREDICATES.contains(&pred.bytes())
}

/// Whether `pred` names an owned control constant (`true fail false`, #1611).
fn owns_control(pred: &Symbol) -> bool {
    CONTROL_PREDICATES.contains(&pred.bytes())
}

/// Whether `pred` names any owned term relation.
fn owns_name(pred: &Symbol) -> bool {
    owns_recognizer(pred)
        || owns_comparison(pred)
        || owns_univ(pred)
        || owns_unification(pred)
        || owns_control(pred)
}

/// Compare two GROUND terms by the **standard order of terms** — a total order
/// consistent with structural equality (`compare_values(a, b) == Equal ⟺ a == b`).
///
/// Ground terms are ranked `Atom < Tuple`; within a rank, `Atom`s order by their raw
/// bytes and `Tuple`s first by arity then element-wise (lexicographic over the
/// children). This is the ground restriction of the full `Var < Atom < Tuple` order;
/// `core::builtins::compare_terms` is the search-side mirror over `Term` (which adds the
/// `Var` rank for the non-ground case), so a ground `@<` goal decides identically in
/// search and check (the dual-conformance law).
pub fn compare_values(a: &Value, b: &Value) -> Ordering {
    // #2275 layer 3: an explicit stack of pairs, not one native frame per nesting level. Pairs
    // are taken depth-first, left to right, so the first difference found is the recursion's.
    let mut work: Vec<(&Value, &Value)> = vec![(a, b)];
    while let Some(pair) = work.pop() {
        match pair {
            (Value::Atom(x), Value::Atom(y)) => match x.bytes().cmp(y.bytes()) {
                Ordering::Equal => {}
                non_eq @ (Ordering::Less | Ordering::Greater) => return non_eq,
            },
            (Value::Tuple(xs), Value::Tuple(ys)) => {
                let (xs, ys) = (xs.items(), ys.items());
                match xs.len().cmp(&ys.len()) {
                    Ordering::Equal => work.extend(xs.iter().zip(ys).rev()),
                    arity @ (Ordering::Less | Ordering::Greater) => return arity,
                }
            }
            // Different kinds: Atom (rank 0) before Tuple (rank 1).
            (Value::Atom(_), Value::Tuple(_)) => return Ordering::Less,
            (Value::Tuple(_), Value::Atom(_)) => return Ordering::Greater,
        }
    }
    Ordering::Equal
}

/// Is the ground value the nil atom `[]`?
fn is_nil(value: &Value) -> bool {
    matches!(value, Value::Atom(atom) if atom.bytes() == NIL_ATOM)
}

/// Match a `[H|T]` cons cell over a GROUND value, returning `(head, tail)`. A cons cell
/// is a 3-element tuple headed by the `.` atom. Mirrors `core::builtins::as_cons`.
fn as_cons(value: &Value) -> Option<(&Value, &Value)> {
    let Value::Tuple(tuple) = value else {
        return None;
    };
    let items = tuple.items();
    match items {
        [Value::Atom(a), h, t] if a.bytes() == CONS_FUNCTOR => Some((h, t)),
        _ => None,
    }
}

/// Whether a GROUND value is a *proper* list (a `[]`-terminated chain of `.`/2 cons
/// cells). A ground value can never be a partial list (no `Var`), so only the
/// improper-tail case fails here — mirroring `core::builtins::proper_list_elements`'s
/// success condition over a ground spine.
fn is_proper_list(value: &Value) -> bool {
    let mut current = value;
    loop {
        if is_nil(current) {
            return true;
        }
        match as_cons(current) {
            Some((_head, tail)) => current = tail,
            None => return false,
        }
    }
}

/// The config-pinned §5 [`Theory`] that owns the A0 term recognizers (`atom atomic
/// compound is_list number`) and the standard-order comparisons (`== \== @< @> @=< @>=`)
/// and decides a GROUND term atom by a constant-time structural match (no search, no
/// trail). Pure / total / deterministic / config-free — a faithful mirror of the Go/TS
/// bindings and of the search-side builtins.
#[derive(Clone, Copy, Debug, Default)]
pub struct TermTheory;

impl TermTheory {
    /// The standard term theory (no configuration).
    pub fn new() -> Self {
        TermTheory
    }
}

impl Theory for TermTheory {
    /// Opt in to the #1023 probe clone. `TermTheory` is a stateless `Copy` unit, so an
    /// independent copy is the value itself — the probe runs under a theory byte-identical to
    /// the one the provider advertises, which is what keeps the check-profile digest equal.
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, crate::spi::CopyIncapacity> {
        Ok(Box::new(*self))
    }

    fn owns(&self, pred: &Symbol) -> bool {
        owns_name(pred)
    }

    /// `logos-core/term-theory@1.1.0`, no config. The `logos-core/` namespace is a
    /// STABLE IDENTITY, not a path (ADR 0014/0016): it is byte-frozen in
    /// `vectors/term.json` and stays this string regardless of the theory's physical
    /// home. `1.0.0` → `1.1.0` with #1611: the owned set grew by `=` `\=` `true` `fail`
    /// `false`, and a profile digest folding this identity moves with it — byte-identical
    /// in rs, go and ts.
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/term-theory".to_vec(),
            b"1.1.0".to_vec(),
            [0u8; 32],
        )
    }

    /// #3142: every decision completes. The recognizers, univ, and the standard order (an
    /// explicit-stack walk since #2275) have no cap, so a `Fails` here is always a decided false.
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
            // A non-UTF-8 predicate cannot be a registered term relation.
            Err(_) => return TheoryGround::fails("term_unknown_predicate"),
        };
        match name {
            // A0 recognizers (arity 1).
            "atom" => decide_recognizer(&atom.args, |v| matches!(v, Value::Atom(_))),
            // In the ground term world the only atomic terms are `Atom`s (no `Var`, and a
            // number is the `int` Tuple embedding), so `atomic` coincides with `atom`.
            "atomic" => decide_recognizer(&atom.args, |v| matches!(v, Value::Atom(_))),
            "compound" => decide_recognizer(&atom.args, |v| matches!(v, Value::Tuple(_))),
            "is_list" => decide_recognizer(&atom.args, is_proper_list),
            "number" => decide_recognizer(&atom.args, is_number),
            // A0 standard-order comparisons (arity 2).
            "==" => decide_comparison(&atom.args, |o| o == Ordering::Equal),
            "\\==" => decide_comparison(&atom.args, |o| o != Ordering::Equal),
            "@<" => decide_comparison(&atom.args, |o| o == Ordering::Less),
            "@>" => decide_comparison(&atom.args, |o| o == Ordering::Greater),
            "@=<" => decide_comparison(&atom.args, |o| o != Ordering::Greater),
            "@>=" => decide_comparison(&atom.args, |o| o != Ordering::Less),
            // A0 structural decomposition (arity 2): univ.
            "=.." => decide_univ(&atom.args),
            // Unification over GROUND terms (arity 2, #1611): syntactic unification of two
            // ground terms is structural equality, which is exactly the standard order's
            // `Equal`.
            "=" => decide_comparison(&atom.args, |o| o == Ordering::Equal),
            "\\=" => decide_comparison(&atom.args, |o| o != Ordering::Equal),
            // Control constants (arity 0, #1611).
            "true" => decide_control(&atom.args, true),
            "fail" | "false" => decide_control(&atom.args, false),
            // Owned name routed here but not handled above — unreachable (the name set is
            // exactly the match arms above), but stay total.
            _ => TheoryGround::fails("term_does_not_hold"),
        }
    }
}

/// Whether a GROUND value is a number — a canonical exact-integer `int` embedding OR a
/// canonical exact-decimal `decimal` embedding (#331). Unlike `atom`, a number-shaped
/// *bare atom* (`"3.14"` or `Atom("42")`) does NOT count — only the genuine embeddings do.
/// Shares `BigInt::from_int_term`/`BigDecimal::from_decimal_term` with the search-side
/// `core::builtins::builtin_number`, so the two agree byte-for-byte.
fn is_number(value: &Value) -> bool {
    let term = Term::from_value(value);
    BigInt::from_int_term(&term).is_some() || BigDecimal::from_decimal_term(&term).is_some()
}

/// Decide an arity-1 recognizer: arity must be 1; then `test(arg0)`. A non-1 arity has no
/// such relation (`term_bad_arity`); a false test is `term_does_not_hold`.
fn decide_recognizer(args: &[Value], test: impl Fn(&Value) -> bool) -> TheoryGround {
    if args.len() != 1 {
        return TheoryGround::fails("term_bad_arity");
    }
    if test(&args[0]) {
        TheoryGround::holds()
    } else {
        TheoryGround::fails("term_does_not_hold")
    }
}

/// Decide an arity-2 standard-order comparison: arity must be 2; then accept iff
/// `accept(compare_values(arg0, arg1))`. A non-2 arity has no such relation
/// (`term_bad_arity`); a false comparison is `term_does_not_hold`.
fn decide_comparison(args: &[Value], accept: impl Fn(Ordering) -> bool) -> TheoryGround {
    if args.len() != 2 {
        return TheoryGround::fails("term_bad_arity");
    }
    if accept(compare_values(&args[0], &args[1])) {
        TheoryGround::holds()
    } else {
        TheoryGround::fails("term_does_not_hold")
    }
}

/// Decide an arity-0 control constant (#1611): arity must be 0 (`term_bad_arity`
/// otherwise); then `true` holds and `fail`/`false` are `term_does_not_hold`.
fn decide_control(args: &[Value], holds: bool) -> TheoryGround {
    if !args.is_empty() {
        return TheoryGround::fails("term_bad_arity");
    }
    if holds {
        TheoryGround::holds()
    } else {
        TheoryGround::fails("term_does_not_hold")
    }
}

/// Build the cons-list `[e0, e1, … en]` as a ground `Value` — the frozen `.`/2 cons form
/// (`Tuple[Atom("."), head, tail]`, `[]`-terminated). Mirrors the search-side
/// `core::builtins::list_from_elements`.
fn value_cons_list(elements: &[Value]) -> Value {
    let mut acc = Value::atom(NIL_ATOM.to_vec());
    for e in elements.iter().rev() {
        acc = Value::tuple([Value::atom(CONS_FUNCTOR.to_vec()), e.clone(), acc]);
    }
    acc
}

/// The univ image of a ground term: the `[Functor | Args]` cons-list a `T =.. L` relation
/// holds for. A labeled compound `Tuple[Atom(f), a1 … an]` ⇒ `[f, a1, … an]`; a bare
/// `Atom(a)` ⇒ `[a]` (arity-0). An empty tuple or a non-`Atom`-headed tuple is outside the
/// labeled-compound image and has no univ list (`None`). Mirrors the search-side builtin.
fn univ_list_of(value: &Value) -> Option<Value> {
    match value {
        Value::Atom(_) => Some(value_cons_list(std::slice::from_ref(value))),
        Value::Tuple(tuple) => match tuple.items() {
            [head @ Value::Atom(_), rest @ ..] => {
                let mut elements = Vec::with_capacity(rest.len() + 1);
                elements.push(head.clone());
                elements.extend(rest.iter().cloned());
                Some(value_cons_list(&elements))
            }
            // Empty tuple or non-atom head: not a labeled compound.
            _ => None,
        },
    }
}

/// Decide the arity-2 univ relation `T =.. L`: arity must be 2; then `Holds` iff `L` equals
/// the univ image of `T` (`compare_values == Equal ⟺ structural equality`). A `T` that is
/// not a labeled compound / atom ⇒ `univ_not_callable`; a mismatched `L` ⇒ `univ_mismatch`.
/// Pure / total / deterministic over the ground args, like every term-theory decision.
fn decide_univ(args: &[Value]) -> TheoryGround {
    if args.len() != 2 {
        return TheoryGround::fails("term_bad_arity");
    }
    match univ_list_of(&args[0]) {
        Some(expected) if compare_values(&args[1], &expected) == Ordering::Equal => {
            TheoryGround::holds()
        }
        Some(_) => TheoryGround::fails("univ_mismatch"),
        None => TheoryGround::fails("univ_not_callable"),
    }
}

#[cfg(test)]
mod univ_tests {
    use super::*;
    use crate::completion::{Completion, TheoryDecision};
    use crate::GroundLiteral;
    use ontos_core::Value;

    fn a(s: &[u8]) -> Value {
        Value::atom(s.to_vec())
    }

    #[test]
    fn univ_decomposes_labeled_compound() {
        let theory = TermTheory::new();
        let t = Value::tuple([a(b"f"), a(b"a"), a(b"b")]);
        let list = value_cons_list(&[a(b"f"), a(b"a"), a(b"b")]);
        assert_eq!(
            theory.decide_ground(&GroundLiteral::new("=..", [t.clone(), list])),
            TheoryGround::holds()
        );
        // A wrong functor in the list rejects.
        let wrong = value_cons_list(&[a(b"g"), a(b"a"), a(b"b")]);
        assert!(matches!(
            theory.decide_ground(&GroundLiteral::new("=..", [t, wrong])),
            Completion::Completed(TheoryDecision::Fails { .. })
        ));
    }

    #[test]
    fn univ_atom_is_arity_zero_singleton() {
        let theory = TermTheory::new();
        let list = value_cons_list(&[a(b"x")]);
        assert_eq!(
            theory.decide_ground(&GroundLiteral::new("=..", [a(b"x"), list])),
            TheoryGround::holds()
        );
    }

    #[test]
    fn univ_wrong_arity_fails() {
        let theory = TermTheory::new();
        assert!(matches!(
            theory.decide_ground(&GroundLiteral::new("=..", [a(b"x")])),
            Completion::Completed(TheoryDecision::Fails { .. })
        ));
    }
}
