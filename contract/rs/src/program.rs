//! §2 Program — clauses as data, not engine. **[FIRM]**
//!
//! A `Clause` is `head :- body₀, …, bodyₙ` (an empty body is a rule-fact). A
//! consumer's whole policy *is* a `Program` — data — so swapping the engine never
//! touches the policy. `check` validates only the clauses a derivation cites: the
//! single-method lookup [`Program::clause`] is all the checker requires.

use crate::literal::{Goal, Literal, Symbol};
use crate::term::{Subst, Term};
use std::collections::BTreeMap;

/// An opaque clause handle. **For v1 its only contract is *stable + lookup-able*.**
/// It is deliberately **not** yet a canonical hash (§9: hashing a clause needs the
/// `quote`/`reify` byte form *and* a `VarId` alpha-normalization policy, neither
/// fixed in v1). A consumer that already has a canonical hash (e.g. arche) may use
/// it here — "stable + lookup-able" is a strict generalization.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClauseId(String);

impl ClauseId {
    pub fn new(handle: impl Into<String>) -> Self {
        ClauseId(handle.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<S: Into<String>> From<S> for ClauseId {
    fn from(s: S) -> Self {
        ClauseId(s.into())
    }
}

/// An **arity-sensitive** reference to the sealed relation a certifiable aggregate
/// counts over (ADR 0023, the #581 sharpening). A counted relation is matched by name
/// **and** arity — `obs/3` and `obs/2` are *different* relations, so the count premise
/// pins both. A `pred`/`arity` that names no sealed table, or a wrong arity, is rejected
/// (`count_attr_out_of_range`) rather than silently counting a different-arity table.
///
/// Replaces the bare [`Symbol`] the early ADR-0023 draft carried in `CountLit`/
/// `Premise::Count`; threading the arity here is the one expert sharpening shared by all
/// three cores before the go/ts mirror, so a wrong-arity count can never slip past name
/// agreement alone.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PredicateRef {
    /// The counted relation's predicate symbol.
    pub pred: Symbol,
    /// The counted relation's arity (number of arguments). A sealed table is matched
    /// only when BOTH its predicate and its arity equal this ref.
    pub arity: u32,
}

impl PredicateRef {
    /// An arity-sensitive predicate reference.
    pub fn new(pred: impl Into<Symbol>, arity: u32) -> Self {
        PredicateRef {
            pred: pred.into(),
            arity,
        }
    }
}

/// What a certifiable aggregate folds over a sealed relation's matching rows
/// (ADR 0023 Phase 0 + the `min`/`max`/`sum` follow-on, #587). One enum, one
/// `Premise::Count` carrier (a count is just the `Rows` fold) — not a separate premise:
///
/// - [`ProjectSpec::Rows`] ⇒ `count` — count the rows matching the filter.
/// - [`ProjectSpec::Distinct`] ⇒ `count_distinct` — count the **distinct** values of
///   one projected attribute (column `attr`) across the matching rows, deduped by the
///   canonical codec key and **excluding `null()`** (SQL-style; ADR 0023 Phase 0).
/// - [`ProjectSpec::Sum`] / [`ProjectSpec::Min`] / [`ProjectSpec::Max`] ⇒ `sum`/`min`/`max`
///   — fold the **integer** column `attr` over matching rows with the existing
///   `ArithmeticTheory` exact operators over [`BigInt`](crate::intval::BigInt) (#587). v1
///   is **integer-only** over a **sealed numeric (int) column**; a non-int column is
///   ill-typed (`count_attr_out_of_range`). **Set semantics** over the proven-exact deduped
///   rows. `sum` of no matching rows is `0`; `min`/`max` of no matching rows is **undefined**
///   and `REJECT`ed (`agg_empty_undefined`) — no infinities, no sentinels.
///
/// `attr` is a 0-based argument index into the folded predicate; out of range is
/// `count_attr_out_of_range`. The result slot `k`/`count` carries the canonical ontos `int`
/// embedding of the folded value (the same slot `count` binds), so `sum`/`min`/`max` reuse
/// the count premise verbatim — the searcher proposes the folded value; the gate re-derives it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProjectSpec {
    /// `count`: count rows matching the filter (no projection).
    Rows,
    /// `count_distinct`: count distinct values of attribute `attr` over matching rows.
    Distinct { attr: u32 },
    /// `sum`: the exact integer sum of column `attr` over matching rows (empty ⇒ `0`).
    Sum { attr: u32 },
    /// `min`: the exact integer minimum of column `attr` over matching rows (empty ⇒ REJECT).
    Min { attr: u32 },
    /// `max`: the exact integer maximum of column `attr` over matching rows (empty ⇒ REJECT).
    Max { attr: u32 },
}

impl ProjectSpec {
    /// The 0-based projected/folded column index, if this spec reads a column
    /// ([`Distinct`](ProjectSpec::Distinct)/[`Sum`](ProjectSpec::Sum)/[`Min`](ProjectSpec::Min)/[`Max`](ProjectSpec::Max));
    /// `None` for [`Rows`](ProjectSpec::Rows). Out-of-range is `count_attr_out_of_range`.
    pub fn attr(&self) -> Option<u32> {
        match self {
            ProjectSpec::Rows => None,
            ProjectSpec::Distinct { attr }
            | ProjectSpec::Sum { attr }
            | ProjectSpec::Min { attr }
            | ProjectSpec::Max { attr } => Some(*attr),
        }
    }
}

/// A certifiable **count** / **count-distinct** body literal (ADR 0023). It is NOT a
/// derivation node: like a negated literal, it is discharged as a checked
/// side-condition against a sealed [`ClosedModelCert`](crate::cert::ClosedModelCert)
/// by [`verify_count_premise`](crate::check) — the searcher proposes the cardinality,
/// the gate re-derives it over a relation it has independently proven exact.
///
/// Generic over the argument type so the same shape expresses a clause body literal
/// (`T = Term`, with variables in `filter`/`count`) and a grounded one
/// (`T = Term`, all ground — see [`CountLit::substitute`]).
///
/// `count` is the **result slot**: the claimed cardinality `k`, bound exactly as
/// `is/2` binds an arithmetic result — a head variable `N` in
/// `eligible(O) :- candidate(O), count_distinct(perspective(O,_,V), V, N).` is checked,
/// not searched, by recomputing the count over the proven-exact relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountLit<T> {
    /// The sealed relation whose rows are counted — matched by name **and** arity
    /// (ADR 0023, #581: a wrong-arity table is never silently counted).
    pub pred: PredicateRef,
    /// The ground/bound-position filter: each `(position, term)` requires the row's
    /// argument at `position` to equal the (grounded) `term`. Positions not listed are
    /// free. An empty filter counts every row of `pred`. (Kept in caller order; the
    /// checker treats it positionally, not as a set.)
    pub filter: Vec<(u32, T)>,
    /// `Rows` ⇒ count rows; `Distinct { attr }` ⇒ count-distinct of column `attr`.
    pub project: ProjectSpec,
    /// The result slot — the claimed cardinality `k`, as a term that binds a head var.
    pub count: T,
}

/// A body literal with **polarity** — `Pos` for a positive subgoal `p(t…)`, `Neg`
/// for a negated subgoal `\+ p(t…)` (ADR 0007), or `Count` for a certifiable
/// aggregate (ADR 0023). The enum is generic over the argument type so the same
/// shape expresses a clause body literal (`T = Term`) and a grounded one
/// (`T = Term`, all ground — see [`BodyLit::substitute`]).
///
/// **Additive (ADR 0007 / ADR 0023).** Today's account is exactly an all-[`BodyLit::Pos`]
/// body. The account codec ([`crate::account`]) reads a `Pos(g)` **byte-identically
/// to the bare `goal_as_term(g)`** (no wrapper), so existing positive clause ids
/// are unchanged; `Neg(g)` and `Count(_)` each get a distinct tagged reading, so a
/// body with no `Count` literal encodes byte-identically to today.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodyLit<T> {
    /// A positive body literal `p(t…)`.
    Pos(Literal<T>),
    /// A negated body literal `\+ p(t…)` — discharged by a closed-model certificate
    /// (ADR 0007), never by a derivation node.
    Neg(Literal<T>),
    /// A certifiable `count` / `count_distinct` literal (ADR 0023) — discharged by a
    /// closed-model certificate, never by a derivation node.
    Count(CountLit<T>),
}

impl<T> BodyLit<T> {
    /// The underlying literal of a `Pos`/`Neg` body literal, or `None` for a
    /// [`BodyLit::Count`]: TOTAL, mirroring
    /// [`BodyLit::as_count`] from the other side (#728, the same additive shape as
    /// [`BodyLit::is_pos`] in #722). Prefer this wherever the body may carry a `Count`
    /// (any clause decoded from bytes — #727 established a `Count` round-trips the
    /// clause codec): the absent case lands in the caller's control flow identically in
    /// every core, instead of hitting a per-core failure mode.
    pub fn as_inner(&self) -> Option<&Literal<T>> {
        match self {
            BodyLit::Pos(l) | BodyLit::Neg(l) => Some(l),
            BodyLit::Count(_) => None,
        }
    }

    /// True iff this is a [`BodyLit::Pos`].
    ///
    /// Prefer this over `!is_neg() && !is_count()` when gating on positive-only bodies. A
    /// consumer that admits by ruling out the known non-positive variants is writing a
    /// BLACKLIST: every variant added here later is admitted by default, silently, in every
    /// consumer that has not been updated. `is_pos` is total over the enum — it stays
    /// correct for variants that do not exist yet — so a positive-Horn gate (arche
    /// PROTOCOL 3.10a) can be expressed as the whitelist it actually is. That matters most
    /// where the clause is attacker-supplied, since the default must be deny.
    ///
    /// (A `match` in this crate is already exhaustive and gets a compile error on a new
    /// variant; a downstream boolean gate does not. This method is what gives the
    /// cross-language cores the same property.)
    pub fn is_pos(&self) -> bool {
        matches!(self, BodyLit::Pos(_))
    }

    /// True iff this is a [`BodyLit::Neg`].
    ///
    /// ⚠ **Not a building block for a positive-Horn gate.** `!is_neg() && !is_count()` is a
    /// BLACKLIST: it admits every variant added to this enum later, silently, in every
    /// consumer that has not been updated. Use [`BodyLit::is_pos`], which is total over the
    /// enum and stays correct for variants that do not exist yet — the reasoning is there.
    pub fn is_neg(&self) -> bool {
        matches!(self, BodyLit::Neg(_))
    }

    /// True iff this is a [`BodyLit::Count`].
    ///
    /// ⚠ **Not a building block for a positive-Horn gate** — see [`BodyLit::is_neg`] and use
    /// [`BodyLit::is_pos`].
    pub fn is_count(&self) -> bool {
        matches!(self, BodyLit::Count(_))
    }

    /// The predicate [`Symbol`] this body literal is over — the underlying literal's
    /// predicate for `Pos`/`Neg`, or the counted relation's predicate for
    /// [`BodyLit::Count`]. Total over all variants.
    pub fn pred(&self) -> &crate::literal::Symbol {
        match self {
            BodyLit::Pos(l) | BodyLit::Neg(l) => &l.pred,
            BodyLit::Count(c) => &c.pred.pred,
        }
    }

    /// The [`CountLit`] of a [`BodyLit::Count`], else `None`.
    pub fn as_count(&self) -> Option<&CountLit<T>> {
        match self {
            BodyLit::Count(c) => Some(c),
            BodyLit::Pos(_) | BodyLit::Neg(_) => None,
        }
    }

    // ── first-class binding & dependency modes (research-doc 0009) ──────────────────
    //
    // The analyzer's range-restriction (safety) and dependency-graph passes must know, per
    // body form, WHICH variables it binds, WHICH must already be bound, and WHAT dependency
    // edge it contributes. Historically each pass `match`ed on the variant (and reached for
    // [`inner`](Self::inner), which is invalid for `Count`). These three total methods make
    // those modes FIRST-CLASS metadata of the form itself: a new body form declares its
    // binding and dependency semantics here, once, and every pass reads them uniformly —
    // closing the "analyzer accumulates ad-hoc knowledge of each new body form" gap.

    /// The argument terms whose variables this literal **binds** (range-restriction outputs):
    /// a positive atom binds all its arguments; a negation binds nothing (a side condition); a
    /// `count` binds only its result term. The safety pass collects bound variables from THIS.
    pub fn binding_terms(&self) -> Vec<&T> {
        match self {
            BodyLit::Pos(l) => l.args.iter().collect(),
            BodyLit::Neg(_) => Vec::new(),
            BodyLit::Count(c) => vec![&c.count],
        }
    }

    /// The argument terms whose variables must ALREADY be positively bound for this literal to
    /// be safe (range-restriction inputs): a positive atom requires nothing (it binds); a
    /// negation requires all its arguments bound (no variable solely under `\+`); a `count`
    /// requires its filter/group variables bound (its result is exempt — that is what it binds).
    pub fn required_terms(&self) -> Vec<&T> {
        match self {
            BodyLit::Pos(_) => Vec::new(),
            BodyLit::Neg(l) => l.args.iter().collect(),
            BodyLit::Count(c) => c.filter.iter().map(|(_, t)| t).collect(),
        }
    }

    /// The dependency edge this literal contributes to the predicate graph: the predicate it
    /// reads, and whether that edge is **non-monotone** (a negation or an aggregate — both read a
    /// sealed, strictly-lower stratum, so the stratifier treats them identically). `hasNegation`
    /// (a per-stratum closed-world obligation) stays a `Neg`-only query via [`is_neg`](Self::is_neg):
    /// an aggregate adds a non-monotone edge but no closed-world obligation.
    pub fn dependency(&self) -> (&crate::literal::Symbol, bool) {
        match self {
            BodyLit::Pos(l) => (&l.pred, false),
            BodyLit::Neg(l) => (&l.pred, true),
            BodyLit::Count(c) => (&c.pred.pred, true),
        }
    }
}

impl CountLit<Term> {
    /// Apply a grounding substitution to the filter terms and the count slot,
    /// preserving the predicate and projection (which are structural, not substituted).
    pub fn substitute(&self, subst: &Subst) -> CountLit<Term> {
        CountLit {
            pred: self.pred.clone(),
            filter: self
                .filter
                .iter()
                .map(|(pos, t)| (*pos, t.substitute(subst)))
                .collect(),
            project: self.project,
            count: self.count.substitute(subst),
        }
    }
}

impl BodyLit<Term> {
    /// Apply a grounding substitution to the underlying literal, **preserving
    /// polarity** (§3 Rule obligation; the polarity is structural, not substituted).
    pub fn substitute(&self, subst: &Subst) -> BodyLit<Term> {
        match self {
            BodyLit::Pos(l) => BodyLit::Pos(l.substitute(subst)),
            BodyLit::Neg(l) => BodyLit::Neg(l.substitute(subst)),
            BodyLit::Count(c) => BodyLit::Count(c.substitute(subst)),
        }
    }
}

/// A bare [`Literal`] lifts to a **positive** body literal — so every existing
/// caller passing `Goal`s (`Clause::new(h, [Goal, …])`) keeps compiling, with each
/// goal read as `Pos` (the all-positive body of today's account).
impl<T> From<Literal<T>> for BodyLit<T> {
    fn from(l: Literal<T>) -> Self {
        BodyLit::Pos(l)
    }
}

/// `head :- body₀, …, bodyₙ`. The head is a [`Goal`]; each body literal is a
/// polarity-tagged [`BodyLit`] (positive or negated). They contain variables —
/// that is what makes a clause a *rule* rather than a ground fact. An empty `body`
/// is a rule-fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub head: Goal,
    pub body: Vec<BodyLit<Term>>,
}

impl Clause {
    /// `head :- b₀, …, bₙ`. Accepts anything that lifts into a [`BodyLit`] — in
    /// particular a sequence of [`Goal`]s (each read as [`BodyLit::Pos`]), so every
    /// existing positive-body call site is unchanged.
    pub fn new<I>(head: Goal, body: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<BodyLit<Term>>,
    {
        Clause {
            head,
            body: body.into_iter().map(Into::into).collect(),
        }
    }

    /// A rule-fact: a clause with an empty body.
    pub fn fact(head: Goal) -> Self {
        Clause {
            head,
            body: Vec::new(),
        }
    }

    /// `head :- pos₀, …, \+ neg₀, …` — a clause with explicit positive and negated
    /// body literals (ADR 0007). Positive literals are appended first, then the
    /// negated ones, so the body order is `[pos…, neg…]`.
    pub fn with_neg<P, N>(head: Goal, pos: P, neg: N) -> Self
    where
        P: IntoIterator<Item = Goal>,
        N: IntoIterator<Item = Goal>,
    {
        let mut body: Vec<BodyLit<Term>> = pos.into_iter().map(BodyLit::Pos).collect();
        body.extend(neg.into_iter().map(BodyLit::Neg));
        Clause { head, body }
    }
}

/// The only capability `check` requires of a program: look a cited clause up by id
/// (§2 "local checking"). Whole-program predicate-partition hygiene (§4.4) is a
/// consumer / program-loading responsibility, not a per-`check` obligation.
///
/// **ADR 0007 closure soundness (additive).** Certifying a negated premise `\+ r(a)`
/// requires the checker to enumerate **every** clause defining a sealed predicate —
/// the support witness's cited clauses are attacker-chosen and cannot be trusted to
/// be complete (a non-cited defining clause could hide a derivable head). So the
/// trait gains [`Program::for_each_clause`], a **trusted** whole-program iteration.
/// It is **DEFAULTED to a no-op** (additive — no existing impl breaks): a program
/// that does not override it exposes an *empty* clause set, which is **fail-closed**
/// — the closure check then finds no defining clauses and (if any predicate the
/// scope seals has no enumerated clause yet a `\+` cites it) the cert is rejected,
/// never wrongly accepted. A consumer that wants certifiable negation MUST override
/// it to enumerate its real clause set (as [`MapProgram`] does).
pub trait Program {
    fn clause(&self, id: &ClauseId) -> Option<&Clause>;

    /// Iterate **every** clause of the program, calling `f` with each `(id, clause)`.
    /// The closure check (ADR 0007) drives over this to find all clauses defining a
    /// sealed predicate. **Defaulted to a no-op** (empty enumeration) — additive and
    /// fail-closed; certifiable negation requires a real override.
    fn for_each_clause(&self, _f: &mut dyn FnMut(&ClauseId, &Clause)) {}
}

/// A straightforward in-memory `Program` (a `ClauseId → Clause` map). Provided for
/// tests, fixtures, and simple consumers; an engine may back `Program` by a store.
#[derive(Clone, Debug, Default)]
pub struct MapProgram {
    clauses: BTreeMap<ClauseId, Clause>,
}

impl MapProgram {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, id: impl Into<ClauseId>, clause: Clause) -> Self {
        self.clauses.insert(id.into(), clause);
        self
    }

    pub fn insert(&mut self, id: impl Into<ClauseId>, clause: Clause) {
        self.clauses.insert(id.into(), clause);
    }

    /// The number of clauses in the program.
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Whether the program has no clauses.
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Iterate `(id, clause)` pairs in **canonical order — ascending by the clause-id's
    /// UTF-8 bytes** (lexicographic). The backing `BTreeMap<ClauseId>` already yields its
    /// keys in `ClauseId` order, which is byte-lexicographic on the id string, so this is
    /// the same total order the program (de)serialization ([`crate::program_serde`]) sorts
    /// entries by and the same order Go's `MapProgram.Iter` and TS's `MapProgram.iter`
    /// reproduce — the enumeration is **deterministic and byte-identical across
    /// `{rs,go,ts}`** (a cross-core divergence here would break parity for a consumer that
    /// assembles a request straight from the program). Clause ids are unique (map keys),
    /// so the order is total and unambiguous.
    pub fn iter(&self) -> impl Iterator<Item = (&ClauseId, &Clause)> {
        self.clauses.iter()
    }
}

impl Program for MapProgram {
    fn clause(&self, id: &ClauseId) -> Option<&Clause> {
        self.clauses.get(id)
    }

    /// Iterate the backing map in `ClauseId` order (deterministic) — the trusted
    /// whole-program enumeration the ADR-0007 closure check needs.
    fn for_each_clause(&self, f: &mut dyn FnMut(&ClauseId, &Clause)) {
        for (id, clause) in &self.clauses {
            f(id, clause);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Goal;

    fn fact(pred: &str) -> Clause {
        Clause::fact(Goal::new(pred, []))
    }

    /// EXHAUSTIVENESS FORCER (#830). Adding a `BodyLit` variant fails to **compile** here,
    /// and that compile stop is what brings the author to the corpus below.
    ///
    /// The `match` has no `_` arm, deliberately. Do not add one: a catch-all restores exactly
    /// the silent-vacuity this function exists to remove.
    ///
    /// **Honest bound, stated so nobody reads more into it:** this forces a compile error at
    /// the right place; it is *not* a proof that a sample was added.
    ///
    /// ✅ CLOSED (#997). That residue — "an author who adds an arm here and no sample below
    /// still gets a vacuous pass" — is now caught by [`corpus_covers_every_declared_variant`],
    /// which parses this file and compares the DECLARED variant count against the corpus size.
    /// The compile stop still does the useful work of bringing the author here; it is simply no
    /// longer the only thing standing between a new variant and a vacuous pass.
    fn variant_name(bl: &BodyLit<Term>) -> &'static str {
        match bl {
            BodyLit::Pos(_) => "pos",
            BodyLit::Neg(_) => "neg",
            BodyLit::Count(_) => "count",
        }
    }

    /// One `BodyLit` per variant, LABELLED THROUGH [`variant_name`] rather than by a string
    /// literal — so the corpus and the forcer cannot drift apart.
    ///
    /// ⚠ The doc here used to read *"the partition test below fails until you do"*. **That was
    /// false**: every guard below iterates this list, so a variant added without touching it
    /// left all of them passing **vacuously** — including
    /// `is_pos_is_not_the_negated_complement`, whose own message is *"the blacklist formulation
    /// admits a variant it was never told about"*. A guard that cannot see the thing it warns
    /// about is the defect it warns about (#830 audit, 2026-08-14).
    fn body_lit_variants() -> Vec<(&'static str, BodyLit<Term>)> {
        let samples = vec![
            BodyLit::Pos(Goal::new("p", [])),
            BodyLit::Neg(Goal::new("p", [])),
            BodyLit::Count(CountLit {
                pred: crate::PredicateRef::new("q", 1),
                filter: vec![],
                project: ProjectSpec::Rows,
                count: Term::var("N"),
            }),
        ];
        samples
            .into_iter()
            .map(|bl| (variant_name(&bl), bl))
            .collect()
    }

    /// The `BodyLit` variant names declared in this file's own source, in declaration order.
    ///
    /// WHY PARSE THE SOURCE. Closing #991's residue requires ENUMERATING the variants, and no
    /// stable Rust mechanism enumerates a data-carrying enum: `match` exhaustiveness forces you
    /// to *handle* every variant, never to *iterate* them; `std::mem::variant_count` is nightly;
    /// and a derive such as `strum::EnumIter` cannot construct variants that carry payloads. So
    /// the enumeration has to come from outside the language. (The go half of #996 does the same
    /// thing with `go/ast`, for the same reason — go cannot force at all.)
    ///
    /// Hand-rolled rather than `syn`: a `syn` dev-dependency puts this crate inside the wasm
    /// guest's dependency cone (measured twice by caa, #991 and #994), and the sanctioned
    /// remedy there has its own failure mode — a CANCELLED `wasm-compile` defeats the
    /// attestation. A guard whose *setup* is flakier than the defect it catches is a bad trade.
    ///
    /// The brittleness this buys is paid for by failing LOUDLY on zero variants rather than
    /// passing vacuously — the one outcome a parser-backed guard must never have.
    fn declared_body_lit_variants() -> Vec<String> {
        let src = include_str!("program.rs");
        let header = src
            .find("pub enum BodyLit<T> {")
            .expect("BodyLit's declaration moved or was renamed — this guard cannot run blind");
        let body = &src[header + "pub enum BodyLit<T> {".len()..];

        let mut names = Vec::new();
        let mut depth = 0usize;
        for raw in body.lines() {
            let line = raw.trim();
            if depth == 0 && line.starts_with('}') {
                break;
            }
            let opens = line.matches('{').count();
            let closes = line.matches('}').count();
            let at_top = depth == 0;
            depth = depth + opens - closes.min(depth + opens);

            if !at_top || line.is_empty() || line.starts_with("//") || line.starts_with("#[") {
                continue;
            }
            // A variant is `Ident(..)`, `Ident { .. }`, or a bare `Ident,`.
            let ident: String = line
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            let rest = line[ident.len()..].trim_start();
            let looks_like_variant = !ident.is_empty()
                && ident.starts_with(|c: char| c.is_ascii_uppercase())
                && (rest.starts_with('(') || rest.starts_with('{') || rest.starts_with(','));
            if looks_like_variant {
                names.push(ident);
            }
        }
        names
    }

    /// CLOSES #991's ENUMERATION RESIDUE (#997) — the last unforced step in the chain.
    ///
    /// #991 gave this corpus a compile-time forcer and stated its own honest bound: *"an author
    /// who adds an arm here and no sample below still gets a vacuous pass on the new variant."*
    /// That is exactly this test's subject. `variant_name`'s arm-less `match` stops the author at
    /// the forcer; nothing made them continue to the corpus. Now the declared variant count does.
    ///
    /// Both numbers and both name lists are in the failure message: a verdict without its
    /// denominator is not auditable, and it was a printed denominator — not a better assertion —
    /// that caught the equivalent gap in go and ts (#996).
    ///
    /// HONEST BOUND: this proves the corpus has one sample per DECLARED variant. It does not
    /// prove each sample is well-FORMED — `variant_corpus_has_no_duplicates` and the behavioural
    /// guards cover the rest, and because #991 labels samples through `variant_name(&bl)`, a
    /// sample cannot lie about which variant it is.
    #[test]
    fn corpus_covers_every_declared_variant() {
        let declared = declared_body_lit_variants();
        assert!(
            !declared.is_empty(),
            "parsed program.rs and found ZERO BodyLit variants — this guard would pass \
             VACUOUSLY, so it fails instead. The declaration shape changed; fix this parser \
             rather than deleting the test."
        );

        let corpus = body_lit_variants();
        let corpus_labels: Vec<&str> = corpus.iter().map(|(n, _)| *n).collect();
        assert_eq!(
            corpus.len(),
            declared.len(),
            "BodyLit corpus is INCOMPLETE: {} variant(s) declared {:?} but body_lit_variants() \
             has {} sample(s) {:?} — every guard in this module iterates that corpus, so the \
             missing variant passes them ALL vacuously. Add a sample.",
            declared.len(),
            declared,
            corpus.len(),
            corpus_labels
        );
    }

    /// The corpus must carry a DISTINCT variant per sample.
    ///
    /// This is the half the compile stop cannot cover. It does not prove the corpus is
    /// complete (nothing here can enumerate the variants), but it does refuse the cheapest
    /// wrong way to satisfy the forcer: adding a `variant_name` arm and then a duplicate
    /// sample, which would grow the list while leaving the new variant untested.
    #[test]
    fn variant_corpus_has_no_duplicates() {
        let corpus = body_lit_variants();
        let mut labels: Vec<&'static str> = corpus.iter().map(|(name, _)| *name).collect();
        let total = labels.len();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(
            labels.len(),
            total,
            "the BodyLit corpus has {total} samples but only {} distinct variants — a duplicate \
             sample satisfies the exhaustiveness forcer without testing the new variant",
            labels.len()
        );
    }

    #[test]
    fn is_pos_holds_only_for_pos() {
        for (name, bl) in body_lit_variants() {
            assert_eq!(bl.is_pos(), name == "pos", "is_pos() wrong for {name}");
        }
    }

    /// EXACTLY ONE of `is_pos`/`is_neg`/`is_count` must hold for every variant.
    ///
    /// "At least one" fails when a variant is added with no predicate — the case where a
    /// downstream whitelist (`is_pos`) silently stops matching a body it should classify.
    /// "At most one" fails if two ever overlap, which would make a whitelist and a
    /// blacklist disagree about the same literal.
    #[test]
    fn polarity_predicates_partition() {
        for (name, bl) in body_lit_variants() {
            let n = [bl.is_pos(), bl.is_neg(), bl.is_count()]
                .iter()
                .filter(|h| **h)
                .count();
            assert_eq!(
                n, 1,
                "variant {name}: {n} of {{is_pos, is_neg, is_count}} hold, want exactly 1 — \
                 a variant with no predicate is admitted by default in any consumer that \
                 gates by ruling out the others"
            );
        }
    }

    /// Pins why `is_pos` is not a convenience alias for the negated complement: the two
    /// agree TODAY, and a variant added without a predicate makes them diverge. Consumers
    /// gating on positive-Horn bodies (arche PROTOCOL 3.10a) must use the whitelist.
    #[test]
    fn is_pos_is_not_the_negated_complement() {
        for (name, bl) in body_lit_variants() {
            let whitelist = bl.is_pos();
            let blacklist = !bl.is_neg() && !bl.is_count();
            assert_eq!(
                whitelist, blacklist,
                "variant {name}: is_pos()={whitelist} but !is_neg()&&!is_count()={blacklist} \
                 — the blacklist formulation admits a variant it was never told about"
            );
        }
    }

    #[test]
    fn len_and_is_empty() {
        let mut p = MapProgram::new();
        assert!(p.is_empty());
        assert_eq!(p.len(), 0);
        p.insert(ClauseId::new("a"), fact("a"));
        p.insert(ClauseId::new("b"), fact("b"));
        assert!(!p.is_empty());
        assert_eq!(p.len(), 2);
        // Re-inserting the same id replaces, never grows.
        p.insert(ClauseId::new("a"), fact("a2"));
        assert_eq!(p.len(), 2);
    }

    /// Iterate a known multi-clause program built in NON-sorted insertion order and assert
    /// the iteration is in canonical clause-id byte order, with the matching count.
    #[test]
    fn iter_is_canonical_clause_id_order() {
        // Insert in a deliberately scrambled order; iteration must come back sorted.
        let mut p = MapProgram::new();
        p.insert(ClauseId::new("m"), fact("m"));
        p.insert(ClauseId::new("z"), fact("z"));
        p.insert(ClauseId::new("a"), fact("a"));
        p.insert(ClauseId::new("aa"), fact("aa"));
        p.insert(ClauseId::new("A"), fact("A")); // uppercase 'A' (0x41) sorts before 'a' (0x61)

        let ids: Vec<&str> = p.iter().map(|(id, _)| id.as_str()).collect();
        // Byte-lexicographic: 'A'(0x41) < 'a'(0x61) < "aa" < 'm' < 'z'.
        assert_eq!(ids, vec!["A", "a", "aa", "m", "z"]);
        assert_eq!(p.len(), 5);

        // iter yields the SAME order as for_each_clause (the closure-check enumeration).
        let mut fe_ids: Vec<String> = Vec::new();
        p.for_each_clause(&mut |id, _| fe_ids.push(id.as_str().to_string()));
        assert_eq!(fe_ids, ids);

        // The clause paired with each id is the right one.
        for (id, clause) in p.iter() {
            assert_eq!(Some(clause), p.clause(id));
        }
    }

    /// The first-class binding & dependency mode descriptors (research-doc 0009): each total over
    /// Pos/Neg/Count. Pins the contract the analyzer's safety + dependency passes now rely on
    /// uniformly (and the go/ts BodyLit mirror in their own program tests).
    #[test]
    fn bodylit_first_class_modes() {
        let (x, y, z, g, n) = (
            Term::var("X"),
            Term::var("Y"),
            Term::var("Z"),
            Term::var("G"),
            Term::var("N"),
        );

        let pos = BodyLit::Pos(Goal::new("p", [x.clone(), y.clone()]));
        let neg = BodyLit::Neg(Goal::new("q", [z.clone()]));
        let count = BodyLit::Count(CountLit {
            pred: PredicateRef::new("obs", 3),
            filter: vec![(0, g.clone())],
            project: ProjectSpec::Rows,
            count: n.clone(),
        });

        // binding_terms: a positive atom binds all its args; a negation binds nothing; a count
        // binds only its result.
        assert_eq!(pos.binding_terms(), vec![&x, &y]);
        assert!(neg.binding_terms().is_empty());
        assert_eq!(count.binding_terms(), vec![&n]);

        // required_terms: a positive atom requires nothing; a negation requires all its args; a
        // count requires its filter/group vars (the result is exempt).
        assert!(pos.required_terms().is_empty());
        assert_eq!(neg.required_terms(), vec![&z]);
        assert_eq!(count.required_terms(), vec![&g]);

        // dependency: (read predicate, non-monotone?). A positive atom is monotone; a negation and
        // an aggregate are non-monotone (both read a sealed, strictly-lower stratum).
        assert_eq!(pos.dependency().0.bytes(), b"p");
        assert!(!pos.dependency().1);
        assert_eq!(neg.dependency().0.bytes(), b"q");
        assert!(neg.dependency().1);
        assert_eq!(count.dependency().0.bytes(), b"obs");
        assert!(count.dependency().1);
    }
}
