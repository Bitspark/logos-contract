//! `contract::text` — the standard checkable byte-string `Theory` (ADR 0016, Shelf A).
//! **[STABLE-v1 Theory impl.]**
//!
//! The Rust home of the text relations `contains/2`, `starts_with/2`, `ends_with/2`,
//! placed in the contract tier beside the Theory SPI per ADR 0014 / ADR 0016 (Shelf A:
//! a pure, total, deterministic function of ground args, non-derivable). So their
//! *meaning* is a shared, certifiable artifact rather than a search-only Rust builtin.
//! The search-side builtins (`logos_core::builtins::{builtin_contains, builtin_starts_with,
//! builtin_ends_with}`) stay in `core` as the A1 fast path; this `decide_ground` reproduces them
//! byte-for-byte over the SAME raw `Atom` bytes — the §7 dual-conformance law, pinned by
//! `vectors/text.json` and mirrored tri-core (`contract/{go,ts}`).
//!
//! # Judgments
//!
//! `owns(pred)`: by NAME only (any arity) — `contains starts_with ends_with`. There is no
//! nested expression grammar (unlike arithmetic operators), so nothing else to exclude.
//! `decide_ground(atom)` on a ground atom: a non-UTF-8 predicate → `Fails{text_unknown_predicate}`
//! (defensive); an owned name at arity ≠ 2 → `Fails{text_bad_arity}`; both args bare
//! `Atom`s with the byte test true → `Holds`; a false test or a non-`Atom` arg (a compound,
//! or the `utf8-text` *embedding*, which is a `Tuple`) → `Fails{text_does_not_hold}`.
//!
//! Operands are **raw `Atom` bytes** — exactly what the search builtins read via
//! `atom_bytes`, **not** the `utf8-text` embedding (a `Tuple`, which therefore does not
//! hold). An empty needle / prefix / suffix holds (every byte-slice contains/starts
//! with/ends with the empty slice).

use crate::{ComponentIdentity, GroundLiteral, Symbol, Term, Theory, TheoryGround};

/// The byte-string relation names this theory owns. Owned by NAME only.
const TEXT_PREDICATES: &[&[u8]] = &[b"contains", b"starts_with", b"ends_with"];

/// The predicate set this theory owns — the three text relations (`contains`, `starts_with`, `ends_with`) — the SAME set its `owns` recognizes by name.
///
/// Exposed for the #1406 guard family: an engine path with no builtin evaluation must be
/// able to ask "does this program carry a literal I cannot decide?" without a `Theory`
/// handle, which `EngineProvider::prepare` does not receive. Mirrors
/// [`arithmetic_predicate_set`](crate::arithmetic::arithmetic_predicate_set), which was the
/// only such set exposed until the silent zero was measured on THIS theory too.
pub fn text_predicate_set() -> crate::PredicateSet {
    TEXT_PREDICATES
        .iter()
        .map(|bytes| crate::Symbol::new(bytes.to_vec()))
        .collect()
}

/// Whether `pred` names an owned text relation.
fn owns_name(pred: &Symbol) -> bool {
    TEXT_PREDICATES.contains(&pred.bytes())
}

/// The bytes of a bare `Atom`, or `None` for any non-atom term (a compound `Tuple` —
/// including the `utf8-text` embedding — or, defensively, a variable, which a ground atom
/// never carries). Mirrors the search-side `atom_bytes` accessor exactly.
fn atom_bytes(term: &Term) -> Option<&[u8]> {
    match term {
        Term::Atom(bytes) => Some(bytes),
        Term::Tuple(_) | Term::Var(_) => None,
    }
}

/// Whether `haystack` contains `needle` as a contiguous byte subslice. An empty needle is
/// contained in everything (matching `str::contains("")`). Byte-for-byte identical to
/// `logos_core::builtins::contains_subslice` — the search/check shared semantics.
fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    if needle.len() > haystack.len() {
        return false;
    }
    haystack
        .windows(needle.len())
        .any(|window| window == needle)
}

/// The standard checkable byte-string [`Theory`] over `contains/2`, `starts_with/2`,
/// `ends_with/2`. Pure / total / deterministic / config-free — a faithful mirror of the
/// search-side builtins and of the Go/TS bindings.
#[derive(Clone, Copy, Debug, Default)]
pub struct TextTheory;

impl TextTheory {
    /// The standard text theory (no configuration).
    pub fn new() -> Self {
        TextTheory
    }
}

impl Theory for TextTheory {
    /// Opt in to the #1023 probe clone. `TextTheory` is a stateless `Copy` unit, so an
    /// independent copy is the value itself — the probe runs under a theory byte-identical to
    /// the one the provider advertises, which is what keeps the check-profile digest equal.
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, crate::spi::CopyIncapacity> {
        Ok(Box::new(*self))
    }

    fn owns(&self, pred: &Symbol) -> bool {
        owns_name(pred)
    }

    /// `logos-core/text-theory@1.0.0`, no config. The `logos-core/` namespace is a
    /// STABLE IDENTITY, not a path (ADR 0014/0016): it is byte-frozen in
    /// `vectors/text.json` and stays this string regardless of the theory's physical home.
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/text-theory".to_vec(),
            b"1.0.0".to_vec(),
            [0u8; 32],
        )
    }

    /// #3142: every decision completes. `contains`, `starts_with` and `ends_with` compare two ground
    /// atoms byte by byte, with no cap, so a `Fails` here is always a decided false.
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
            // A non-UTF-8 predicate cannot be a registered text relation.
            Err(_) => return TheoryGround::fails("text_unknown_predicate"),
        };
        let args: Vec<Term> = atom.args.iter().map(Term::from_value).collect();
        match name {
            "contains" => decide_relation(&args, contains_subslice),
            "starts_with" => decide_relation(&args, |text, prefix| text.starts_with(prefix)),
            "ends_with" => decide_relation(&args, |text, suffix| text.ends_with(suffix)),
            // Owned name routed here but not handled above — unreachable (the name set is
            // exactly the match arms above), but stay total.
            _ => TheoryGround::fails("text_does_not_hold"),
        }
    }
}

/// Decide a binary byte-string relation: arity must be 2; both args must be bare `Atom`s;
/// then `test(arg0_bytes, arg1_bytes)`. Mirrors the search-side builtins
/// (`builtin_contains` et al.): a non-atom arg or a false test is `text_does_not_hold`;
/// a non-2 arity has no such relation (`text_bad_arity`).
fn decide_relation(args: &[Term], test: impl Fn(&[u8], &[u8]) -> bool) -> TheoryGround {
    if args.len() != 2 {
        return TheoryGround::fails("text_bad_arity");
    }
    match (atom_bytes(&args[0]), atom_bytes(&args[1])) {
        (Some(lhs), Some(rhs)) if test(lhs, rhs) => TheoryGround::holds(),
        _ => TheoryGround::fails("text_does_not_hold"),
    }
}
