//! The engine-facing seam — **[PROPOSED]** (ADR 0002).
//!
//! This module is the *search-side* counterpart to the FIRM proof account and the
//! STABLE-v1 checker SPI: it is the seam an **evaluator** binds, where the contract
//! ends and an engine implementation begins. Per ADR 0002 these shapes are
//! **recommended, not frozen** — they may change without the additive-only
//! discipline that governs `logos-checker-spi v1`. They live in the contract crate
//! (rather than `logos-core`) only so the generic scheduler in `logos-core`
//! (`logos_core::drive`) can depend on the *trait* and never on an `impl`,
//! satisfying the V3 layering fix of ADR 0004: the seam points **down**, the
//! fixpoint loop sits above it, and no engine crate is in the dependency graph of
//! either.
//!
//! ## What is ported, and what is re-grounded
//!
//! The shape is ported from the plexis unified bottom-up kernel (`svc/log/engine/
//! common` `bottom_up.rs` + `operator.rs`). Two deliberate simplifications:
//!
//! 1. **Synchronous.** plexis made [`BottomUpEngine`] `async` *only* because
//!    clause's seed/round steps write through an async `LogStore::apply_batch` so a
//!    websocket store client could drive wire I/O. That is an engine-and-store
//!    concern; the *scheduler contract* — walk strata, drive rounds to a delta-empty
//!    fixpoint — is synchronous. Keeping it `fn` (not `async fn`) avoids pulling an
//!    async runtime into the contract layer and keeps the trait trivially
//!    object-safe-adjacent and generic-usable. An engine that needs async store I/O
//!    owns its own runtime inside its method bodies.
//! 2. **Engine-internal vocabulary erased.** plexis's [`PhysicalOperator`] threaded a
//!    concrete `OperatorInput<H: HostLookupAccess>` carrying compiled rules,
//!    relation-access choices, scratch buffers, and a wgpu witness — all engine
//!    internals that do not exist at the contract layer. Here the operator is
//!    generic over an associated `Input`/`Output`, so the *cost-driven decline →
//!    fallback* dialect is captured without naming any engine's row model.
//!
//! ## The seam traits
//!
//! - [`LeafSource`] — the producer-side fact seam: where the evaluator gets the
//!   ground `Leaf` candidates for a goal. The static dual is the blanket
//!   `impl LeafSource for Vec<GroundLiteral>`; a store (arche's signed-fact ledger,
//!   `logos-store`'s indexed table) plugs its own impl in. The search-side dual of
//!   the checker's [`LeafVerifier`](crate::spi::LeafVerifier).
//! - [`BuiltinSolver`] — the producer-side seam for *binding* theory builtins
//!   (`?- X is 2 + 3`): the search-side dual of the checker's
//!   [`Theory`](crate::spi::Theory). `logos-core` supplies the standard arithmetic
//!   impl over its `BuiltinRegistry`.
//! - [`BottomUpEngine`] — the ~4-method round/stratum interface a seminaive engine
//!   exposes so the shared scheduler can drive it to a least fixpoint. The engine
//!   owns everything that requires knowing what a "row" is (seeding deltas, swapping
//!   rounds, sealing facts); the scheduler owns only the loop.
//! - [`PhysicalOperator`] — a per-unit-of-work evaluator with a cost-driven
//!   selection dialect: [`estimated_cost`](PhysicalOperator::estimated_cost) returns
//!   `None` to *decline* (the catalog falls back to another operator) or `Some(cost)`
//!   to *accept* (lower cost wins). [`OperatorSelectionPolicy`] resolves the winner
//!   when several operators accept.

use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use ontos_core::Value;

use crate::completion::{Completion, NonCompletion};
use crate::derivation::{Derivation, Evidence, Node, NodeMeta, Premise};
use crate::literal::{Goal, GroundLiteral};
use crate::program::ClauseId;
use crate::term::Subst;

// ===========================================================================
// List reification (cons ↔ `list`) — the additive, opt-in account-emit mode (#159)
// ===========================================================================
//
// The logos surface lowers list syntax to Prolog-style **cons cells**: `[]` is the
// nil atom `Atom("[]")`, and `[H|T]` is `Tuple[Atom("."), H, T]` (see the core parser
// `parse_list`). The ontos/data L2 profile (`ontos-data`) instead carries a sequence
// as the *flat* `list` embedding `Tuple[Atom("list"), e0, …, e_{n-1}]` (spec §5.5).
//
// These are two SPELLINGS, and since #3022 (research 0028; `seat:caa`'s ruling) only one is
// certified. Every certified literal claim is EXACT: a derivation's nodes conclude exactly the
// facts the engine derived, in the cons spelling the clauses produce, and `check` compares them
// structurally. Reifying cons → `list` lets a consumer that speaks the ontos/data `list`
// profile SEE answers in its shape, and that is presentation: the display spelling travels
// BESIDE the exact certified fact ([`PresentedFact`]), never in place of it. So the reifying
// builder mode ([`DerivationBuilder::with_list_reification`]) no longer rewrites a node's
// conclusion; it answers [`DerivationBuilder::present`] with the reified spelling.
//
// Why a respelled node conclusion is not certified: #277's account equality (cons and `list`
// spellings as one term) is not a congruence, because the list normal form never rewrites a
// cons TAIL, so a label-tolerant `check` concluded `r([a|list(b)])` from `p([b]). r([a|X]) :-
// p(X).`, a claim true in neither the exact model nor the list quotient. The normalizer is the
// FIRM term-algebra primitive [`canonicalize_lists`](crate::term::canonicalize_lists).

/// Reify every **ground proper cons-list** anywhere inside `value` into the ontos/data
/// flat `list` embedding — the PRESENTATION spelling (#3022), a thin re-export of the FIRM
/// [`canonicalize_lists`](crate::term::canonicalize_lists) primitive. A value that is not a
/// proper list (an improper `.(a, b)`, a bare `[]` atom, an existing `list(…)` tuple, an
/// ordinary compound) keeps its shape — only its children are reified. Idempotent. `check`
/// never applies it: a reified value is a display spelling, never a certified term. See
/// [`canonicalize_lists`](crate::term::canonicalize_lists) for the bijection / no-conflation
/// argument and edge-case handling.
pub fn reify_lists(value: &Value) -> Value {
    crate::term::canonicalize_lists(value)
}

/// Reify (cons → `list`) every argument of a ground literal, leaving its predicate
/// untouched: the display spelling the reifying [`DerivationBuilder`] mode presents.
fn reify_conclusion(conclusion: GroundLiteral) -> GroundLiteral {
    GroundLiteral {
        pred: conclusion.pred,
        args: conclusion.args.iter().map(reify_lists).collect(),
    }
}

/// A certified fact and the spelling a producer PRESENTS it in (#3022, step 2). `fact` is what
/// the derivation proves and `check` certifies, exactly; `display` is presentation metadata
/// carried BESIDE it, never certified in place of it. Built by [`DerivationBuilder::present`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PresentedFact {
    /// The exact certified fact.
    pub fact: GroundLiteral,
    /// Its display spelling: `fact` with every proper cons list reified to `list(…)` under the
    /// list-reifying builder mode, else `fact` itself. Never checked.
    pub display: GroundLiteral,
}

// ===========================================================================
// Fact + builtin search seams
// ===========================================================================

/// A source of extensional ground facts — the search-side seam for `Leaf`
/// candidates. A static program uses a `Vec<GroundLiteral>` (the blanket impl
/// below); arche plugs its signed-fact store here (indexed lookup over the ledger
/// projection) so the *same* engine drives both. This is the search-side dual of
/// the checker's [`LeafVerifier`](crate::spi::LeafVerifier): `candidates` proposes
/// facts to try; `check`'s `LeafVerifier` later re-validates each one independently.
pub trait LeafSource {
    /// Ground facts that could satisfy `goal` (the engine unifies each, keeping
    /// matches). Order is the source's; the engine preserves it, so enumeration
    /// order stays stable.
    fn candidates(&self, goal: &Goal) -> Vec<GroundLiteral>;

    /// **REQUIRED: hand back an independent copy of this source, or DECLARE why not (#1023;
    /// required since #2722 item 1).**
    ///
    /// The search-side counterpart of [`Theory::boxed_clone`](crate::spi::Theory::boxed_clone):
    /// composition rebinds a provider's search over a slice by copying its source, so a source
    /// that cannot copy makes that provider unable to be rebound. Defaulted to `None` until #2722,
    /// which made "cannot copy" and "never considered" indistinguishable. A source that does not
    /// copy writes `logos_contract::cannot_copy!(LeafSource, "<why>");` inside its impl.
    fn boxed_clone(&self) -> Result<Box<dyn LeafSource + Send + Sync>, crate::spi::CopyIncapacity>;
}

/// The obvious static source: an in-memory fact table. Returns the same-predicate
/// facts (only those can unify); arche supplies its own indexed impl instead.
impl LeafSource for Vec<GroundLiteral> {
    /// Opt in to the #1023 probe clone: an in-memory fact table copies by value.
    fn boxed_clone(&self) -> Result<Box<dyn LeafSource + Send + Sync>, crate::spi::CopyIncapacity> {
        Ok(Box::new(self.clone()))
    }

    fn candidates(&self, goal: &Goal) -> Vec<GroundLiteral> {
        self.iter()
            .filter(|fact| fact.pred == goal.pred)
            .cloned()
            .collect()
    }
}

/// The **search-side** seam for theory-owned (builtin) predicates that may *bind*
/// variables — e.g. `is/2`, which evaluates its right operand and binds its left.
///
/// This is strictly the producer's counterpart to the checker's
/// [`Theory`](crate::spi::Theory): a `Theory` only *decides* an already-**ground**
/// atom (`Holds`/`Fails`), which the engine uses directly for a ground builtin goal
/// (a comparison, `5 is 2 + 3`). But `?- X is 2 + 3` arrives with `X` unbound — the
/// engine must *solve* it (bind `X = 5`) before any ground atom exists. A
/// `BuiltinSolver` performs that search: given the (partially-instantiated) goal and
/// the current bindings, it returns the extension substitutions under which the goal
/// holds.
///
/// **The dual-conformance contract (§7) of an implementor.** Each returned `Subst`,
/// deep-applied to the goal, MUST yield a **ground** atom that the paired
/// [`Theory::decide`](crate::spi::Theory::decide) also accepts (`Holds`). The engine
/// relies on this: after binding via the solver it forms the now-ground conclusion
/// and re-checks it with `Theory::decide` before emitting the `Builtin` node, so a
/// `Builtin` the engine produces is exactly one [`check`](crate::check::check)
/// re-accepts. A solver whose bindings disagree with the theory would simply have its
/// proposed solution dropped (the engine's `decide` gate fails it), never emit an
/// unsound node.
///
/// `logos-core` provides the standard implementation over its arithmetic registry
/// (`impl BuiltinSolver for logos_core::builtins::BuiltinRegistry`), paired with
/// `logos_core::builtins::ArithmeticTheory` as the `Theory`.
///
/// **A solver reports whether it finished (#3162, research 0031 row 2).** An empty answer list
/// means the goal cannot be satisfied only when the report's terminal is
/// `Completed(Exhausted)`. A solver that stopped (a host refusal, an unreadable reply, a goal
/// it cannot bind) says so with `NotCompleted(cause)`, and a caller reads that as a refusal,
/// never as "no".
pub trait BuiltinSolver {
    /// Whether this solver answers `goal`'s predicate at its arity. A search routes a
    /// theory-owned goal the solver owns through [`solve`](Self::solve), ground or not, and a
    /// goal it does not own to the theory alone (seat:caa's D2 ruling on #3162, the v1 interim
    /// until the checker's theory reports three values, #3165). It is derived from the same
    /// declaration that routes `solve`, never from a second list, and it claims only what the
    /// paired theory owns (solver-owned within theory-owned), so every answer has a gate.
    fn owns(&self, goal: &Goal) -> bool;

    /// The extension substitutions under which the (theory-owned) `goal` holds, given the
    /// current `subst`, and whether they are all of them. Each answer, deep-applied, must
    /// ground the goal to a `Theory::decide`-accepted atom. A stop names the decider that stopped
    /// ([`SolverReport::stopped`]).
    fn solve(&self, goal: &Goal, subst: &Subst) -> SolverReport;
}

/// A [`BuiltinSolver`]'s answer to one goal (#3392, `seat:caa`'s corrected Q1): the extension
/// substitutions under which the goal holds, and whether they are all of them.
///
/// A stop carries the DECIDER that stopped, stamped by the code that stopped: the stopped arm
/// cannot be built without it, and nothing reads a stop without it. So no caller re-derives which
/// member of a composite solver decided a goal (the routing query `seat:caa`'s Q1 on #3343
/// rejects), and the attribution cannot disagree with the solve that produced it. A composite
/// solver forwards its member's report unchanged, stamp included.
///
/// The answers read as a [`SearchReport`]'s do (research 0031 row 2): answers then an exhausted
/// terminal are exactly these; answers then a stop hold, but more may exist; no answers then a
/// stop decide neither existence nor absence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverReport {
    answers: Vec<Subst>,
    stop: Option<(crate::spi::ComponentIdentity, NonCompletion)>,
}

impl SolverReport {
    /// Every answer there is.
    pub fn exhausted(answers: Vec<Subst>) -> Self {
        SolverReport {
            answers,
            stop: None,
        }
    }

    /// `answers` hold, and `decider` stopped (`stop`) before the solver established there are no
    /// others.
    pub fn stopped(
        answers: Vec<Subst>,
        decider: crate::spi::ComponentIdentity,
        stop: NonCompletion,
    ) -> Self {
        SolverReport {
            answers,
            stop: Some((decider, stop)),
        }
    }

    /// The answers.
    pub fn answers(&self) -> &[Subst] {
        &self.answers
    }

    /// The answers, taken.
    pub fn into_answers(self) -> Vec<Subst> {
        self.answers
    }

    /// The decider that stopped and why, if the solver did not exhaust its alternatives.
    pub fn stop(&self) -> Option<(&crate::spi::ComponentIdentity, NonCompletion)> {
        self.stop.as_ref().map(|(decider, stop)| (decider, *stop))
    }
}

/// The search's alternatives were exhausted: the answers reported are all there are.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Exhausted;

/// The caller-limit vocabulary of a producer no caller's limit reaches. It has no values, so a
/// [`SearchReport`] over it can never claim `LimitExceeded`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NoCallerLimit {}

/// A search's answers, and whether they are all of them (research 0031 row 2). The two are
/// independent (research 0031, the search observations table):
///
/// - answers, then `Completed(Exhausted)`: exactly these answers;
/// - no answers, then `Completed(Exhausted)`: absence;
/// - answers, then `NotCompleted(cause)`: these answers hold, but more may exist;
/// - no answers, then `NotCompleted(cause)`: neither existence nor absence.
///
/// An engine's `Exhausted` is still an untrusted claim when it reaches certification; it is
/// never a closed-world certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchReport<A, L = NoCallerLimit> {
    pub answers: Vec<A>,
    pub terminal: Completion<Exhausted, L>,
}

impl<A, L> SearchReport<A, L> {
    /// Every answer there is.
    pub fn exhausted(answers: Vec<A>) -> Self {
        SearchReport {
            answers,
            terminal: Completion::Completed(Exhausted),
        }
    }

    /// `answers` hold, and the search stopped before it established there are no others.
    pub fn stopped(answers: Vec<A>, cause: NonCompletion) -> Self {
        SearchReport {
            answers,
            terminal: Completion::NotCompleted(cause),
        }
    }

    /// Why the search stopped, if it did not exhaust its alternatives. A caller limit (`L`) is
    /// not a non-completion and is `None` here; a report over [`NoCallerLimit`] cannot carry one.
    pub fn stop(&self) -> Option<NonCompletion> {
        match &self.terminal {
            Completion::NotCompleted(cause) => Some(*cause),
            Completion::Completed(Exhausted) | Completion::LimitExceeded(_) => None,
        }
    }
}

// ===========================================================================
// Derivation builder (producer-side)
// ===========================================================================

/// Accumulates derivation nodes in dependency order — every premise is pushed before
/// the node that cites it, so each premise index is `<` the citing node's index
/// (`check`'s acyclic-premise-order obligation). Interns by conclusion so a fact
/// proved twice is a single `Leaf` referenced twice (a DAG, not a tree — keeps the
/// node count down).
///
/// **[PROPOSED]** (ADR 0002) — the producer-side counterpart an evaluator uses to
/// emit a [`Derivation`] `check()` accepts (the §7 dual-conformance law). Shared so
/// every engine (the top-down sldnf evaluator, the seminaive negation engine) builds
/// derivations through one primitive rather than cloning it. The general
/// [`rule`](DerivationBuilder::rule) takes `Vec<Premise>` so a `Neg` premise (ADR
/// 0007) is expressible; the positive-only [`rule_pos`](DerivationBuilder::rule_pos)
/// convenience lifts a `Vec<usize>` of node indices to `Premise::Pos`.
///
/// ## The single account-emit seam (#159)
///
/// Because *both* engines funnel every node conclusion through this builder, it is the
/// one place a producer decides how an answer is PRESENTED — notably **list reification**
/// (cons → the ontos/data `list` embedding). Every mode interns conclusions **verbatim**,
/// exactly as derived: a certified claim is exact (#3022). The mode only chooses the display
/// spelling [`present`](DerivationBuilder::present) returns beside the exact fact: the fact
/// itself by default ([`new`](DerivationBuilder::new) / [`Default`]), its [`reify_lists`]
/// spelling under [`with_list_reification`](DerivationBuilder::with_list_reification).
#[derive(Default)]
pub struct DerivationBuilder {
    nodes: Vec<Node>,
    /// The interning index (#1754): each interned (normalized) conclusion's hash → the position
    /// in `nodes` of the latest node filed under it. `nodes` stays the canonical insertion-ordered
    /// store and is what `finish` hands out; the map only answers [`intern`](Self::intern) in
    /// O(1) instead of a scan over every node already interned, which made building a derivation
    /// of `n` nodes O(n²) — 346 ms of a 862 ms `solve_all` on a 256-deep chain (65 792 nodes).
    ///
    /// #2185: keyed by the hash, not the conclusion. A conclusion key cloned every conclusion
    /// into the map a second time, and emitting runs once per answer.
    index: HashMap<u64, usize>,
    /// `chain[i]` is the node filed before node `i` under the same hash, so a hash collision is
    /// resolved by comparing conclusions along the chain.
    chain: Vec<Option<usize>>,
    /// The per-builder hash key for conclusions.
    hasher: RandomState,
    /// When `true`, [`present`](Self::present) displays a fact through [`reify_lists`]
    /// (cons → `list`). Conclusions are interned verbatim either way (#3022).
    reify_lists: bool,
}

impl DerivationBuilder {
    /// A fresh, empty builder in the **default** (verbatim, frozen-identity) emission
    /// mode — conclusions are interned exactly as supplied. This is the byte-preserving
    /// default every existing caller gets.
    pub fn new() -> Self {
        Self::default()
    }

    /// A fresh, empty builder in the **list-reifying** PRESENTATION mode (#159, #3022): its
    /// nodes conclude exactly what is derived, as every builder's do, and
    /// [`present`](Self::present) displays a fact with its proper cons lists reified to the
    /// ontos/data `list` embedding, beside the exact fact.
    pub fn with_list_reification() -> Self {
        Self {
            reify_lists: true,
            ..Self::default()
        }
    }

    /// The exact `fact` and the spelling this builder's mode presents it in (#3022): the
    /// reified spelling under [`with_list_reification`](Self::with_list_reification), the fact
    /// itself otherwise. The one place the display decision lives; the certified claim is
    /// always `fact`.
    pub fn present(&self, fact: GroundLiteral) -> PresentedFact {
        let display = if self.reify_lists {
            reify_conclusion(fact.clone())
        } else {
            fact.clone()
        };
        PresentedFact { fact, display }
    }

    /// Index of an existing node concluding `conclusion` (the interning probe), or, when there is
    /// none, the conclusion's hash to file the new node under.
    fn intern(&self, conclusion: &GroundLiteral) -> Result<usize, u64> {
        let hash = self.hasher.hash_one(conclusion);
        let mut at = self.index.get(&hash).copied();
        while let Some(i) = at {
            if self.nodes[i].conclusion() == conclusion {
                return Ok(i);
            }
            at = self.chain[i];
        }
        Err(hash)
    }

    /// Append `node` — whose conclusion is already normalized and known to be absent — and
    /// file it in the index under `hash`, the one [`intern`](Self::intern) returned. The ONE push
    /// site, so the map and the chain cannot drift from the `Vec`.
    fn push(&mut self, node: Node, hash: u64) -> usize {
        let pos = self.nodes.len();
        self.chain.push(self.index.insert(hash, pos));
        self.nodes.push(node);
        pos
    }

    /// Intern a `Leaf` concluding `conclusion` with **no** evidence (the trusted-axiom
    /// form), returning its node index.
    pub fn leaf(&mut self, conclusion: GroundLiteral) -> usize {
        self.leaf_with_evidence(conclusion, Evidence::none())
    }

    /// Intern a `Leaf` concluding `conclusion` carrying `evidence` (an attestation a
    /// [`LeafVerifier`](crate::spi::LeafVerifier) interprets — arche-style), returning
    /// its node index. The `none`-evidence dual is [`leaf`](DerivationBuilder::leaf).
    pub fn leaf_with_evidence(&mut self, conclusion: GroundLiteral, evidence: Evidence) -> usize {
        let hash = match self.intern(&conclusion) {
            Ok(i) => return i,
            Err(hash) => hash,
        };
        self.push(
            Node::Leaf {
                conclusion,
                evidence,
            },
            hash,
        )
    }

    /// Intern a `Builtin` concluding `conclusion` (a theory-decided atom), returning
    /// its node index.
    pub fn builtin(&mut self, conclusion: GroundLiteral) -> usize {
        let hash = match self.intern(&conclusion) {
            Ok(i) => return i,
            Err(hash) => hash,
        };
        self.push(Node::Builtin { conclusion }, hash)
    }

    /// Intern a `Rule` node — the **general** form, accepting an explicit
    /// `Vec<Premise>` so both positive ([`Premise::Pos`]) and negated
    /// ([`Premise::Neg`], ADR 0007) premises are expressible (the seminaive negation
    /// engine needs `Neg`). Returns its node index.
    pub fn rule(
        &mut self,
        conclusion: GroundLiteral,
        clause: ClauseId,
        subst: Subst,
        premises: Vec<Premise>,
    ) -> usize {
        let hash = match self.intern(&conclusion) {
            Ok(i) => return i,
            Err(hash) => hash,
        };
        self.push(
            Node::Rule {
                conclusion,
                clause,
                subst,
                premises,
                meta: NodeMeta::none(),
            },
            hash,
        )
    }

    /// Intern a `Rule` whose premises are all **positive**: each node index in
    /// `premises` lifts to a [`Premise::Pos`], then delegates to
    /// [`rule`](DerivationBuilder::rule). The convenience an all-positive (SLD)
    /// evaluator uses.
    pub fn rule_pos(
        &mut self,
        conclusion: GroundLiteral,
        clause: ClauseId,
        subst: Subst,
        premises: Vec<usize>,
    ) -> usize {
        self.rule(
            conclusion,
            clause,
            subst,
            // A builder's node index is a host offset; the account holds the protocol integer.
            premises
                .into_iter()
                .map(|p| Premise::pos(p as u64))
                .collect(),
        )
    }

    /// Finish, producing the [`Derivation`] rooted at node index `root`.
    pub fn finish(self, root: usize) -> Derivation {
        Derivation::new(self.nodes, root as u64)
    }
}

// ===========================================================================
// Resource limits + truncation
// ===========================================================================

/// Why a fixpoint evaluation stopped before reaching its least model.
///
/// **[PROPOSED]** (ADR 0002). Minimal on purpose — the scheduler only
/// needs the wall-clock and cancellation reasons it can itself detect; richer
/// per-engine causes (max-goals, max-depth, max-solutions) are surfaced by the
/// engine through [`RoundOutcome::Truncated`] and travel opaquely.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TruncationReason {
    /// The caller's guest live-allocation budget, distinct from a deployment capacity.
    MemoryBytes,
    /// The RUN-WIDE fixpoint round budget ([`ResourceLimits::max_rounds`], #1605) tripped:
    /// the scheduler had executed that many rounds across strata in stratification order
    /// and refused the next one — sealing the current stratum and evaluating NO higher
    /// stratum (the soundness rule under negation: a higher stratum must never negate over a
    /// partial relation). The partial is the k-th iterate of the immediate-consequence
    /// operator within the truncating stratum, a LOWER BOUND on the least model. Also the
    /// reason an engine returns when it treats a configured per-stratum ceiling as a hard
    /// error. (The scheduler's *own* soft [`SchedulerOptions::max_rounds`] cap is **not** a
    /// truncation — it ends the stratum cleanly with `truncated: None`.)
    MaxRounds,
    /// A wall-clock budget (`ResourceLimits::max_wall_ms`) was exceeded, or the
    /// configured budget was itself invalid (negative / non-finite).
    MaxWallMs,
    /// The external cancellation flag (`ResourceLimits::cancelled`) was set.
    Cancelled,
    /// An engine-detected limit not modeled above (e.g. max-goals, max-solutions).
    /// Engines pass a short stable token so the host can classify it.
    Engine(&'static str),
    /// A host CAPACITY ran out before the least model (#3448 increment 2b, `seat:caa`'s ruling):
    /// the scheduler polled [`CapacityResource`]'s probe at a round or stratum check and stopped.
    /// It is NOT a budget, so nothing a caller raises recovers it, and it never reads as one
    /// (research 0031 row 4 separates a capacity from a caller limit).
    CapacityExhausted(CapacityResource),
}

/// A host capacity a search can run out of (#3448 increment 2, `seat:caa`'s rulings): the ONE
/// resource vocabulary of a cooperative stop (`capacity_exhausted(<resource>)`, answers kept) and
/// of a trap (`capability_unavailable(host, wasm, <resource>)`, none). It lives here, the lowest
/// tier, because the parties that detect a capacity sit below the kernel: the probes in
/// `logos-core`, the engines' reports and the scheduler. The kernel re-exports it.
///
/// A closed vocabulary (research 0025): each resource's capability name is defined once, by
/// [`capability`](Self::capability)'s exhaustive match, so a new resource reds every site that
/// interprets it until it is placed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CapacityResource {
    /// The search's call stack (#2269, #2292).
    CallStack,
    /// The guest's linear memory (#3448).
    Memory,
}

impl CapacityResource {
    /// Every resource, in a fixed order. When one run reports more than one, it names the first
    /// in this order, so the report is deterministic for a given program and limits.
    pub const ALL: [CapacityResource; 2] = [CapacityResource::CallStack, CapacityResource::Memory];

    /// The capability name, shared with `capability_unavailable`. The only place it is written.
    pub const fn capability(self) -> &'static str {
        match self {
            CapacityResource::CallStack => "call_stack",
            CapacityResource::Memory => "memory",
        }
    }

    /// The inverse of [`capability`](Self::capability); `None` for a capability no capacity names.
    pub fn from_capability(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|r| r.capability() == name)
    }
}

/// Caller-supplied bounds the scheduler and engine poll during evaluation.
///
/// **[PROPOSED]** (ADR 0002). Cloneable and cheap; the cancellation
/// flag is shared (`Arc<AtomicBool>`) so a caller on another thread can request a
/// stop. `Default` is "no limits".
#[derive(Clone, Default)]
pub struct ResourceLimits {
    /// Wall-clock budget in milliseconds, measured from a caller-supplied
    /// [`Instant`]. `None` means unbounded. A negative or non-finite value is
    /// treated as an immediate [`TruncationReason::MaxWallMs`].
    pub max_wall_ms: Option<f64>,
    /// External cancellation flag. When `Some(flag)` and the flag reads `true`, the
    /// scheduler stops with [`TruncationReason::Cancelled`].
    pub cancelled: Option<Arc<AtomicBool>>,
    /// The bottom-up WORK budget (#1605): the maximum number of fixpoint rounds the
    /// scheduler may execute in this run, counted across strata in stratification order.
    /// `None` means unbounded. Rounds rather than firings because a round is the unit the
    /// seam already names ([`RoundOutcome`]) and the partial after `k` rounds is the `k`-th
    /// iterate of the immediate-consequence operator — canonical, order-independent, and
    /// therefore tri-core by construction; a firing count depends on a firing order no
    /// engine pins. On the trip the scheduler reports [`TruncationReason::MaxRounds`].
    pub max_rounds: Option<usize>,
}

impl ResourceLimits {
    /// A limit set with no bounds (same as [`Default`], but explicit at call sites).
    pub fn unbounded() -> Self {
        Self::default()
    }

    /// A limit set bounded only by a wall-clock budget in milliseconds.
    pub fn with_wall_ms(max_wall_ms: f64) -> Self {
        Self {
            max_rounds: None,
            max_wall_ms: Some(max_wall_ms),
            cancelled: None,
        }
    }

    /// A limit set carrying an external cancellation flag.
    pub fn with_cancel(flag: Arc<AtomicBool>) -> Self {
        Self {
            max_wall_ms: None,
            cancelled: Some(flag),
            max_rounds: None,
        }
    }

    /// Whether either limit has tripped as of `started`. Returns the first
    /// triggering [`TruncationReason`], or `None` if the evaluation may continue.
    ///
    /// The order is cancellation first (cheapest, and the most urgent), then the
    /// wall-clock budget. A non-finite or negative `max_wall_ms` is reported as
    /// [`TruncationReason::MaxWallMs`] immediately (fail-loud over silently
    /// admitting an unbounded run from a malformed budget).
    pub fn reason(&self, started: MonoClock) -> Option<TruncationReason> {
        if self
            .cancelled
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            return Some(TruncationReason::Cancelled);
        }
        let max_wall_ms = self.max_wall_ms?;
        if !max_wall_ms.is_finite() || max_wall_ms < 0.0 {
            return Some(TruncationReason::MaxWallMs);
        }
        if started.elapsed_ms() > max_wall_ms {
            Some(TruncationReason::MaxWallMs)
        } else {
            None
        }
    }
}

/// A monotonic run clock for the engines' wall-clock budget. On native targets it wraps
/// [`Instant`].
///
/// On `wasm32-unknown-unknown` `Instant::now()` PANICS ("time not implemented on this
/// platform"), so the clock there reads a HOST clock the embedding installs with
/// [`install_host_clock`] (#2238): the wasm guest installs its `logos_host::now_ms` import, so
/// a wall-clock budget is real inside the sandbox and an engine can stop ITSELF at it, keeping
/// what it found. Until a clock is installed — any other wasm32 embedder, or a guest predating
/// #2238 — it is the old zero-cost no-op whose elapsed time is always `0`, so it changes
/// nothing for them.
#[derive(Clone, Copy, Debug)]
pub struct MonoClock {
    #[cfg(not(target_arch = "wasm32"))]
    started: Instant,
    /// The installed host clock's reading at [`start`](Self::start), in milliseconds.
    /// Meaningful only while a host clock is installed.
    #[cfg(target_arch = "wasm32")]
    started_ms: f64,
}

/// The host clock a wasm32 embedding installed ([`install_host_clock`]): monotonic
/// milliseconds from an origin of the host's choosing. Unset = no clock.
#[cfg(target_arch = "wasm32")]
static HOST_CLOCK: std::sync::OnceLock<fn() -> f64> = std::sync::OnceLock::new();

/// Install the host clock [`MonoClock`] reads on `wasm32` (#2238): `now_ms` returns monotonic
/// milliseconds from any fixed origin. The first installation wins and later calls are
/// ignored, so an embedding may call this at every entry point. A no-op on native targets,
/// where [`MonoClock`] wraps [`Instant`]. The clock is TRUSTED: it only ever bounds work, and a
/// host that lies about time can at worst stop a search early or late, never admit a claim.
#[inline]
pub fn install_host_clock(now_ms: fn() -> f64) {
    #[cfg(target_arch = "wasm32")]
    {
        let _ = HOST_CLOCK.set(now_ms);
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = now_ms;
    }
}

impl MonoClock {
    /// Start the clock at "now". On wasm without an installed host clock, a no-op.
    #[inline]
    pub fn start() -> Self {
        Self {
            #[cfg(not(target_arch = "wasm32"))]
            started: Instant::now(),
            #[cfg(target_arch = "wasm32")]
            started_ms: HOST_CLOCK.get().map_or(0.0, |now| now()),
        }
    }

    /// Milliseconds elapsed since [`start`](Self::start). On wasm it reads the installed host
    /// clock, and is `0.0` when none is installed (no clock).
    #[inline]
    pub fn elapsed_ms(&self) -> f64 {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.started.elapsed().as_secs_f64() * 1000.0
        }
        #[cfg(target_arch = "wasm32")]
        {
            HOST_CLOCK
                .get()
                .map_or(0.0, |now| (now() - self.started_ms).max(0.0))
        }
    }

    /// Whether [`elapsed_ms`](Self::elapsed_ms) measures anything (#2234): always natively, and
    /// on wasm only once a host clock is installed. Without one every reading is a constant
    /// `0.0`, so a caller that records a timing checks this first rather than recording a zero
    /// it never measured (design 0006: a timer whose producer did not run is absent, not `0`).
    #[inline]
    pub fn measures() -> bool {
        #[cfg(not(target_arch = "wasm32"))]
        {
            true
        }
        #[cfg(target_arch = "wasm32")]
        {
            HOST_CLOCK.get().is_some()
        }
    }

    /// A clock started at an explicit instant (native only), so a test can simulate elapsed
    /// wall-clock time. Hidden from the public API — it exists only for the engines' wall-clock
    /// tests (cross-crate, so it cannot be `#[cfg(test)]`).
    #[cfg(not(target_arch = "wasm32"))]
    #[doc(hidden)]
    pub fn from_instant(started: Instant) -> Self {
        Self { started }
    }
}

// ===========================================================================
// BottomUpEngine seam
// ===========================================================================

/// Result of [`BottomUpEngine::begin_stratum`].
///
/// The scheduler reads `initial_delta_size` only to short-circuit an empty stratum
/// (when `allow_empty_stratum` is on, the default): `0` means "nothing staged, skip
/// the round loop". It is an informational gate, not a precise tuple count — an
/// engine whose bootstrap always stages work can return any positive value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StratumSeed {
    /// Facts the engine staged in its delta after this stratum's bootstrap. `0`
    /// (with `allow_empty_stratum`) tells the scheduler to skip `execute_round`
    /// entirely and seal the stratum with `rounds = 0`.
    pub initial_delta_size: usize,
}

impl StratumSeed {
    /// Seed reporting `n` staged facts.
    pub fn of(initial_delta_size: usize) -> Self {
        Self { initial_delta_size }
    }

    /// The empty seed — no work staged for this stratum.
    pub fn empty() -> Self {
        Self {
            initial_delta_size: 0,
        }
    }
}

/// Result of one [`BottomUpEngine::execute_round`] call.
///
/// `Progressed { new_delta_size: 0 }` is the **fixpoint signal**: the round derived
/// nothing new, so the scheduler breaks the round loop and seals the stratum.
/// `Truncated` aborts the current stratum and (under the default scheduler config)
/// the whole evaluation — the engine has already rolled back its working state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundOutcome {
    /// The round staged `new_delta_size` new facts. `0` signals fixpoint for the
    /// current stratum. The scheduler uses this only for fixpoint detection; it
    /// neither aggregates nor reports the count.
    Progressed {
        /// New facts staged this round. `0` ⇒ stratum fixpoint.
        new_delta_size: usize,
    },
    /// A resource limit or cancellation tripped mid-round. The engine has already
    /// cleaned up; the scheduler seals the stratum and returns the reason.
    Truncated {
        /// The terminating reason.
        reason: TruncationReason,
    },
}

impl RoundOutcome {
    /// The fixpoint sentinel — `Progressed { new_delta_size: 0 }`.
    pub fn fixpoint() -> Self {
        RoundOutcome::Progressed { new_delta_size: 0 }
    }

    /// Whether this outcome is the stratum-fixpoint signal.
    pub fn is_fixpoint(&self) -> bool {
        matches!(self, RoundOutcome::Progressed { new_delta_size: 0 })
    }
}

/// Per-stratum summary handed back to the engine after the scheduler finishes (or
/// aborts) the round loop. Engines seal stats, record elapsed counters, or finalize
/// per-stratum bookkeeping from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StratumSummary {
    /// Rounds the scheduler executed in this stratum. A no-work fixpoint returns
    /// `0`; a truncated stratum returns the round at which truncation fired.
    pub rounds: usize,
    /// `None` on a clean fixpoint (including the scheduler's soft `max_rounds` cap);
    /// `Some(reason)` if a round returned [`RoundOutcome::Truncated`].
    pub truncated: Option<TruncationReason>,
}

/// The seminaive-engine seam the shared scheduler drives.
///
/// **[PROPOSED]** (ADR 0002). The scheduler calls, per stratum:
///
/// 1. [`begin_stratum`](BottomUpEngine::begin_stratum) — seed the initial delta
///    (base facts / `Known` rows / warm-start cascade).
/// 2. [`execute_round`](BottomUpEngine::execute_round) repeatedly — once per round,
///    from `0`, until one returns the fixpoint sentinel
///    ([`RoundOutcome::fixpoint`]), a [`RoundOutcome::Truncated`], or the scheduler's
///    soft `max_rounds` cap trips.
/// 3. [`end_stratum`](BottomUpEngine::end_stratum) — record stats and seal the
///    stratum's facts.
///
/// The scheduler iterates strata `0..stratum_count()` in order and stops early on
/// any truncation. It never inspects what a "row" is — that vocabulary lives
/// entirely inside the engine's method bodies.
///
/// The methods take `&mut self`; the trait carries no other bound, so it is usable
/// both as a generic bound (the shape `logos_core::drive` needs) and — being
/// free of generic methods — as a `dyn BottomUpEngine` trait object.
pub trait BottomUpEngine {
    /// Total stratum count for this evaluation. `0` means "nothing to do" — the
    /// scheduler returns immediately without calling any other method.
    fn stratum_count(&self) -> usize;

    /// Set up `stratum`: seed the initial delta, run warm-start decisions, start
    /// per-stratum timers. The returned [`StratumSeed`] tells the scheduler whether
    /// the stratum has any work.
    fn begin_stratum(&mut self, stratum: usize) -> StratumSeed;

    /// One round of body evaluation for `stratum` (rounds count from `0`). The
    /// engine schedules its recursive variants by delta atom, runs them, swaps
    /// rounds, and returns the new delta size so the scheduler can detect fixpoint.
    /// It receives the scheduler's `limits` and `started` so it can short-circuit a
    /// long round on a wall-clock or cancellation trip without round-tripping the
    /// scheduler.
    fn execute_round(
        &mut self,
        stratum: usize,
        round: usize,
        limits: &ResourceLimits,
        started: MonoClock,
    ) -> RoundOutcome;

    /// Called exactly once after the stratum's round loop terminates (fixpoint,
    /// truncation, or soft cap). Engines record stratum-level stats and seal the
    /// stratum's facts here.
    fn end_stratum(&mut self, stratum: usize, summary: StratumSummary);
}

// ===========================================================================
// PhysicalOperator seam
// ===========================================================================

/// Stable identifier per operator implementation, for stats / tracing / diagnostics.
/// The `&'static str` payload shows up in debug output; equality is by content.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OperatorId(pub &'static str);

impl OperatorId {
    /// The underlying name.
    pub fn name(&self) -> &'static str {
        self.0
    }
}

/// Projected per-unit evaluation cost. **Lower is better.** `u64` (not `f64`) so
/// there is no `NaN` and ordering is total. A real estimator (keyed on
/// cardinalities, selectivity, witness shape) is engine work; operators may ship
/// placeholder constants that merely preserve a "specialized wins when both accept"
/// ordering.
pub type Cost = u64;

/// Policy resolving which operator wins when more than one accepts a unit of work.
///
/// **[PROPOSED]** (ADR 0002). Held on the catalog-driven engine and
/// switchable at runtime. [`pick`](OperatorSelectionPolicy::pick) operates on a
/// slice of `(OperatorId, Option<Cost>)` candidates — the engine's catalog walk —
/// so the policy never needs to know how the engine stores its operators.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum OperatorSelectionPolicy {
    /// Pick the lowest `Some(cost)`. Ties break by candidate-list (catalog) order.
    /// The default.
    #[default]
    LowestCost,
    /// Pick the first candidate whose cost is `Some` — catalog priority order,
    /// ignoring magnitude. Reproduces a pre-cost "first acceptor wins" engine.
    PriorityOrder,
    /// Pick the named operator iff it accepted. If it declined (or is absent),
    /// [`pick`](OperatorSelectionPolicy::pick) returns `None` and the engine skips
    /// the unit — a diagnostic that must show as "skipped" rather than silently
    /// falling back.
    ForceOperator(OperatorId),
}

impl OperatorSelectionPolicy {
    /// Pick a winning candidate index from `(OperatorId, Option<Cost>)` pairs, or
    /// `None` when no candidate is eligible under the policy. A `None` cost means
    /// that operator declined the unit.
    pub fn pick(&self, candidates: &[(OperatorId, Option<Cost>)]) -> Option<usize> {
        match self {
            Self::LowestCost => {
                let mut best: Option<(usize, Cost)> = None;
                for (idx, (_id, cost)) in candidates.iter().enumerate() {
                    if let Some(c) = *cost {
                        match best {
                            None => best = Some((idx, c)),
                            Some((_, bc)) if c < bc => best = Some((idx, c)),
                            _ => {}
                        }
                    }
                }
                best.map(|(i, _)| i)
            }
            Self::PriorityOrder => candidates.iter().position(|(_id, cost)| cost.is_some()),
            Self::ForceOperator(target) => candidates
                .iter()
                .position(|(id, cost)| id == target && cost.is_some()),
        }
    }
}

/// A per-unit physical evaluator with a cost-driven *decline → fallback* dialect.
///
/// **[PROPOSED]** (ADR 0002). An engine keeps a small priority-ordered
/// catalog of operators; for each unit of work it probes every operator's
/// [`estimated_cost`](PhysicalOperator::estimated_cost), then asks an
/// [`OperatorSelectionPolicy`] which one runs. The associated `Input` / `Output`
/// types keep the trait honest at the contract layer — the engine names its own row
/// model without the contract ever depending on it.
///
/// - [`estimated_cost`](PhysicalOperator::estimated_cost) returns `None` to
///   **decline** this unit (the catalog falls back to another operator) or
///   `Some(cost)` to **accept** with a projected cost (lower wins).
/// - [`run`](PhysicalOperator::run) executes the selected unit; `None` ⇒
///   accepted-but-could-not-run, and the catalog re-picks the next acceptor.
///
/// Both `estimated_cost` and `run` borrow the input (`&Self::Input`), so the catalog
/// can probe every operator and — crucially — re-run a *different* operator on the
/// same unit when the chosen one returns `None`.
pub trait PhysicalOperator {
    /// The engine's per-unit input (compiled rule + accesses + scratch in a real
    /// engine; whatever the engine needs).
    type Input;
    /// What a successful run produces (head emissions / a row count / an emit
    /// summary in a real engine).
    type Output;

    /// Stable identifier for stats / tracing.
    fn id(&self) -> OperatorId;

    /// Project a cost for this unit, or **decline** it. `None` ⇒ "not mine, fall
    /// back"; `Some(c)` ⇒ "I accept with projected cost `c`" (lower is better).
    /// Takes `&self` and `&input` so the catalog walk can probe without committing.
    fn estimated_cost(&self, input: &Self::Input) -> Option<Cost>;

    /// Run a unit this operator was selected for.
    ///
    /// - `Some(output)` is a **clean run**. The output may legitimately be empty
    ///   (a join that matched nothing) — that is a real result, not a failure.
    /// - `None` means the operator accepted at
    ///   [`estimated_cost`](PhysicalOperator::estimated_cost) but could **not** in
    ///   fact run this unit. The catalog **drops it and re-picks** the next
    ///   acceptor; a never-declining universal operator guarantees one remains.
    ///
    /// `None` must never be conflated with an empty `Some(output)`: collapsing
    /// "couldn't run" into "ran and derived nothing" is silent and, for a
    /// certifying engine, unsound. `run` borrows `&Self::Input` (rather than
    /// consuming it) precisely so the catalog can hand the same unit to a fallback
    /// operator after a `None`.
    fn run(&self, input: &Self::Input) -> Option<Self::Output>;
}

#[cfg(test)]
mod tests {
    use super::*;

    // -------- list reification (cons ↔ `list`) #159 --------

    fn atomv(s: &str) -> Value {
        Value::atom(s.as_bytes().to_vec())
    }
    fn consv(head: Value, tail: Value) -> Value {
        Value::tuple([atomv("."), head, tail])
    }
    fn nilv() -> Value {
        atomv("[]")
    }
    /// A cons list `[e0, e1, …]` (proper, ending in `[]`).
    fn cons_list(elems: &[Value]) -> Value {
        let mut acc = nilv();
        for e in elems.iter().rev() {
            acc = consv(e.clone(), acc);
        }
        acc
    }

    #[test]
    fn reify_empty_cons_list_stays_a_bare_nil_atom() {
        // A standalone `[]` is an atom, not a cons cell — it is NOT reified to `list()`.
        assert_eq!(reify_lists(&nilv()), nilv());
        assert_ne!(reify_lists(&nilv()), ontos_data::encode_list(&[]));
    }

    #[test]
    fn reify_singleton_and_multi_proper_lists() {
        // [a] -> list(a)
        assert_eq!(
            reify_lists(&cons_list(&[atomv("a")])),
            ontos_data::encode_list(&[atomv("a")])
        );
        // [a, b, c] -> list(a, b, c)
        assert_eq!(
            reify_lists(&cons_list(&[atomv("a"), atomv("b"), atomv("c")])),
            ontos_data::encode_list(&[atomv("a"), atomv("b"), atomv("c")])
        );
    }

    #[test]
    fn reify_nested_list_elements() {
        // [[a], b] -> list(list(a), b)
        let inner = cons_list(&[atomv("a")]);
        let outer = cons_list(&[inner, atomv("b")]);
        assert_eq!(
            reify_lists(&outer),
            ontos_data::encode_list(&[ontos_data::encode_list(&[atomv("a")]), atomv("b")])
        );
    }

    #[test]
    fn reify_improper_list_is_left_as_cons() {
        // [a | b] = .(a, b) with b a non-`[]` atom -> NOT a proper list, stays cons.
        let improper = consv(atomv("a"), atomv("b"));
        assert_eq!(reify_lists(&improper), improper);
        // [a, b | c] -> still improper, stays cons (children reified, structure kept).
        let improper2 = consv(atomv("a"), consv(atomv("b"), atomv("c")));
        assert_eq!(reify_lists(&improper2), improper2);
    }

    #[test]
    fn reify_list_embedding_passes_through_idempotently() {
        // An existing list(...) is headed by `list`, not `.`, so it is untouched; and
        // reify is idempotent.
        let already = ontos_data::encode_list(&[atomv("a"), atomv("b")]);
        assert_eq!(reify_lists(&already), already.clone());
        assert_eq!(reify_lists(&reify_lists(&cons_list(&[atomv("a")]))), {
            ontos_data::encode_list(&[atomv("a")])
        });
    }

    #[test]
    fn reify_ordinary_compound_only_reifies_its_children() {
        // f([a], x) -> f(list(a), x). The `f` compound itself is not a cons cell.
        let t = Value::tuple([atomv("f"), cons_list(&[atomv("a")]), atomv("x")]);
        let expected = Value::tuple([
            atomv("f"),
            ontos_data::encode_list(&[atomv("a")]),
            atomv("x"),
        ]);
        assert_eq!(reify_lists(&t), expected);
    }

    #[test]
    fn reify_list_inside_a_list_element() {
        // [f([b])] -> list(f(list(b)))
        let elem = Value::tuple([atomv("f"), cons_list(&[atomv("b")])]);
        let lst = cons_list(&[elem]);
        let expected = ontos_data::encode_list(&[Value::tuple([
            atomv("f"),
            ontos_data::encode_list(&[atomv("b")]),
        ])]);
        assert_eq!(reify_lists(&lst), expected);
    }

    // -------- DerivationBuilder interning index #1754 --------

    /// #1754: interning is answered by a map beside the node vector, not a scan over it. The
    /// map must agree with the vector at every push site — a site that appends without
    /// filing would make a later duplicate a SECOND node — so every kind is exercised, in
    /// interleaved order, each re-interned to its FIRST position, with a fresh conclusion
    /// still appended at the end. The key filed is the exact conclusion in every mode: a cons
    /// list and its `list` form are two nodes even under `with_list_reification` (#3022).
    /// Measured on the builder alone (chain-shaped, n distinct nodes): the scan built
    /// 32 768 nodes in 63.9 s, the map in 178 ms — quadratic against linear.
    #[test]
    fn intern_index_agrees_with_the_node_vector_across_every_push_site() {
        let mut b = DerivationBuilder::new();
        let a = GroundLiteral::new("a", [atomv("1")]);
        let r = GroundLiteral::new("r", [atomv("1")]);
        let c = GroundLiteral::new("c", [atomv("1")]);
        let ia = b.leaf(a.clone());
        let ir = b.rule_pos(r.clone(), ClauseId::new("k"), Subst::new(), vec![ia]);
        let ic = b.builtin(c.clone());
        assert_eq!((ia, ir, ic), (0, 1, 2));
        // Every kind re-interns to its first position, whichever push method asks.
        assert_eq!(b.leaf(a.clone()), 0);
        assert_eq!(
            b.builtin(a.clone()),
            0,
            "same conclusion, other kind: the FIRST node"
        );
        assert_eq!(
            b.rule_pos(r.clone(), ClauseId::new("k2"), Subst::new(), vec![]),
            1
        );
        assert_eq!(b.leaf(c.clone()), 2);
        assert_eq!(b.builtin(c.clone()), 2);
        // A fresh conclusion still appends.
        let d = GroundLiteral::new("d", [atomv("1")]);
        assert_eq!(b.leaf(d.clone()), 3);
        let out = b.finish(3);
        assert_eq!(out.nodes.len(), 4, "no duplicate node was appended");
        assert_eq!(
            out.nodes
                .iter()
                .map(|n| n.conclusion().clone())
                .collect::<Vec<_>>(),
            vec![a, r, c, d]
        );

        // The key filed is the EXACT conclusion, in every mode (#3022).
        let mut b = DerivationBuilder::with_list_reification();
        let cons = GroundLiteral::new("p", [cons_list(&[atomv("x")])]);
        let listed = GroundLiteral::new("p", [reify_lists(&cons_list(&[atomv("x")]))]);
        let i = b.leaf(cons);
        let j = b.leaf(listed);
        assert_ne!(i, j, "cons and its `list` form are two exact facts");
        assert_eq!(b.finish(j).nodes.len(), 2);
    }

    // -------- DerivationBuilder emission modes #159 --------

    #[test]
    fn default_builder_emits_conclusions_verbatim() {
        // The DEFAULT path must not touch a cons list — the frozen identity.
        let mut b = DerivationBuilder::new();
        let concl = GroundLiteral::new("p", [cons_list(&[atomv("a"), atomv("b")])]);
        let i = b.leaf(concl.clone());
        let d = b.finish(i);
        assert_eq!(
            d.nodes[i].conclusion(),
            &concl,
            "default = verbatim, frozen"
        );
    }

    #[test]
    fn default_via_default_trait_also_verbatim() {
        let mut b = DerivationBuilder::default();
        let concl = GroundLiteral::new("p", [cons_list(&[atomv("a")])]);
        let i = b.builtin(concl.clone());
        let d = b.finish(i);
        assert_eq!(d.nodes[i].conclusion(), &concl);
    }

    #[test]
    fn reifying_builder_keeps_the_exact_conclusion_and_presents_the_list_spelling() {
        // #3022: the node concludes exactly what was derived; the reified spelling is the
        // display, carried beside it.
        let mut b = DerivationBuilder::with_list_reification();
        let concl = GroundLiteral::new("p", [cons_list(&[atomv("a"), atomv("b")])]);
        let i = b.leaf(concl.clone());
        let presented = b.present(concl.clone());
        let d = b.finish(i);
        assert_eq!(
            d.nodes[i].conclusion(),
            &concl,
            "the certified fact is exact"
        );
        let expected =
            GroundLiteral::new("p", [ontos_data::encode_list(&[atomv("a"), atomv("b")])]);
        assert_eq!(presented.fact, concl);
        assert_eq!(
            presented.display, expected,
            "the display is the `list` spelling"
        );
    }

    #[test]
    fn default_builder_presents_the_fact_as_itself() {
        let b = DerivationBuilder::new();
        let concl = GroundLiteral::new("p", [cons_list(&[atomv("a")])]);
        let presented = b.present(concl.clone());
        assert_eq!(presented.fact, concl);
        assert_eq!(presented.display, concl);
    }

    #[test]
    fn reifying_builder_interns_cons_and_list_forms_apart() {
        // #3022: a cons-form and a list-form conclusion are two exact facts, so they are two
        // nodes in every mode.
        let mut b = DerivationBuilder::with_list_reification();
        let cons_form = GroundLiteral::new("p", [cons_list(&[atomv("a")])]);
        let list_form = GroundLiteral::new("p", [ontos_data::encode_list(&[atomv("a")])]);
        let i = b.leaf(cons_form);
        let j = b.leaf(list_form);
        assert_ne!(i, j, "two exact facts, two nodes");
    }

    // -------- ResourceLimits / TruncationReason --------

    #[test]
    fn default_limits_never_trip() {
        assert_eq!(ResourceLimits::default().reason(MonoClock::start()), None);
        assert_eq!(ResourceLimits::unbounded().reason(MonoClock::start()), None);
    }

    #[test]
    fn cancelled_flag_trips_cancelled() {
        let flag = Arc::new(AtomicBool::new(true));
        let limits = ResourceLimits::with_cancel(flag);
        assert_eq!(
            limits.reason(MonoClock::start()),
            Some(TruncationReason::Cancelled)
        );
    }

    #[test]
    fn unset_cancel_flag_does_not_trip() {
        let flag = Arc::new(AtomicBool::new(false));
        let limits = ResourceLimits::with_cancel(flag.clone());
        assert_eq!(limits.reason(MonoClock::start()), None);
        flag.store(true, Ordering::Relaxed);
        assert_eq!(
            limits.reason(MonoClock::start()),
            Some(TruncationReason::Cancelled)
        );
    }

    #[test]
    fn negative_or_nan_wall_budget_trips_immediately() {
        assert_eq!(
            ResourceLimits::with_wall_ms(-1.0).reason(MonoClock::start()),
            Some(TruncationReason::MaxWallMs)
        );
        assert_eq!(
            ResourceLimits::with_wall_ms(f64::NAN).reason(MonoClock::start()),
            Some(TruncationReason::MaxWallMs)
        );
        assert_eq!(
            ResourceLimits::with_wall_ms(f64::INFINITY).reason(MonoClock::start()),
            Some(TruncationReason::MaxWallMs)
        );
    }

    #[test]
    fn exceeded_wall_budget_trips() {
        // A zero budget measured from a point in the past is already exceeded.
        let started =
            MonoClock::from_instant(Instant::now() - std::time::Duration::from_millis(50));
        assert_eq!(
            ResourceLimits::with_wall_ms(1.0).reason(started),
            Some(TruncationReason::MaxWallMs)
        );
    }

    #[test]
    fn generous_wall_budget_does_not_trip() {
        assert_eq!(
            ResourceLimits::with_wall_ms(1_000_000.0).reason(MonoClock::start()),
            None
        );
    }

    #[test]
    fn cancel_takes_priority_over_wall() {
        let flag = Arc::new(AtomicBool::new(true));
        let limits = ResourceLimits {
            max_wall_ms: Some(-1.0),
            cancelled: Some(flag),
            max_rounds: None,
        };
        // Cancellation is checked first.
        assert_eq!(
            limits.reason(MonoClock::start()),
            Some(TruncationReason::Cancelled)
        );
    }

    // -------- StratumSeed / RoundOutcome / StratumSummary --------

    #[test]
    fn stratum_seed_constructors() {
        assert_eq!(StratumSeed::empty().initial_delta_size, 0);
        assert_eq!(StratumSeed::of(7).initial_delta_size, 7);
    }

    #[test]
    fn round_outcome_fixpoint_helpers() {
        assert!(RoundOutcome::fixpoint().is_fixpoint());
        assert!(RoundOutcome::Progressed { new_delta_size: 0 }.is_fixpoint());
        assert!(!RoundOutcome::Progressed { new_delta_size: 3 }.is_fixpoint());
        assert!(!RoundOutcome::Truncated {
            reason: TruncationReason::MaxRounds
        }
        .is_fixpoint());
    }

    #[test]
    fn stratum_summary_carries_rounds_and_truncation() {
        let s = StratumSummary {
            rounds: 7,
            truncated: Some(TruncationReason::MaxWallMs),
        };
        assert_eq!(s.rounds, 7);
        assert_eq!(s.truncated, Some(TruncationReason::MaxWallMs));
    }

    // -------- BottomUpEngine is generic-usable AND object-safe --------

    /// A trivial engine: two strata, three rounds each. Records observed
    /// `(stratum, round)` pairs.
    struct FixedEngine {
        rounds_per_stratum: usize,
        observed: Vec<(usize, usize)>,
    }

    // test-double: synthetic(a trivial two-stratum engine for generic and object-safety checks)
    impl BottomUpEngine for FixedEngine {
        fn stratum_count(&self) -> usize {
            2
        }
        fn begin_stratum(&mut self, _stratum: usize) -> StratumSeed {
            StratumSeed::of(1)
        }
        fn execute_round(
            &mut self,
            stratum: usize,
            round: usize,
            _limits: &ResourceLimits,
            _started: MonoClock,
        ) -> RoundOutcome {
            self.observed.push((stratum, round));
            if round + 1 >= self.rounds_per_stratum {
                RoundOutcome::fixpoint()
            } else {
                RoundOutcome::Progressed { new_delta_size: 1 }
            }
        }
        fn end_stratum(&mut self, _stratum: usize, _summary: StratumSummary) {}
    }

    #[test]
    fn engine_usable_as_generic_bound() {
        fn count<E: BottomUpEngine>(e: &E) -> usize {
            e.stratum_count()
        }
        let e = FixedEngine {
            rounds_per_stratum: 3,
            observed: Vec::new(),
        };
        assert_eq!(count(&e), 2);
    }

    #[test]
    fn engine_is_object_safe() {
        // If `BottomUpEngine` ever grew a generic method or a `Self`-by-value
        // method this coercion would stop compiling.
        let mut e = FixedEngine {
            rounds_per_stratum: 3,
            observed: Vec::new(),
        };
        let dynref: &mut dyn BottomUpEngine = &mut e;
        assert_eq!(dynref.stratum_count(), 2);
        let seed = dynref.begin_stratum(0);
        assert_eq!(seed.initial_delta_size, 1);
        let outcome = dynref.execute_round(0, 0, &ResourceLimits::default(), MonoClock::start());
        assert_eq!(outcome, RoundOutcome::Progressed { new_delta_size: 1 });
    }

    // -------- OperatorSelectionPolicy --------

    #[test]
    fn default_policy_is_lowest_cost() {
        assert_eq!(
            OperatorSelectionPolicy::default(),
            OperatorSelectionPolicy::LowestCost
        );
    }

    #[test]
    fn lowest_cost_picks_lowest() {
        let cands = [
            (OperatorId("a"), Some(1000)),
            (OperatorId("b"), Some(100)),
            (OperatorId("c"), Some(500)),
        ];
        assert_eq!(OperatorSelectionPolicy::LowestCost.pick(&cands), Some(1));
    }

    #[test]
    fn lowest_cost_ties_break_by_order() {
        let cands = [
            (OperatorId("a"), Some(100)),
            (OperatorId("b"), Some(100)),
            (OperatorId("c"), Some(100)),
        ];
        assert_eq!(OperatorSelectionPolicy::LowestCost.pick(&cands), Some(0));
    }

    #[test]
    fn lowest_cost_skips_decliners() {
        let cands = [
            (OperatorId("a"), None),
            (OperatorId("b"), Some(500)),
            (OperatorId("c"), None),
        ];
        assert_eq!(OperatorSelectionPolicy::LowestCost.pick(&cands), Some(1));
    }

    #[test]
    fn priority_order_picks_first_acceptor() {
        let cands = [
            (OperatorId("a"), None),
            (OperatorId("b"), Some(1000)),
            (OperatorId("c"), Some(100)),
        ];
        // First Some wins, not lowest cost.
        assert_eq!(OperatorSelectionPolicy::PriorityOrder.pick(&cands), Some(1));
    }

    #[test]
    fn force_operator_picks_named_acceptor() {
        let cands = [
            (OperatorId("wgpu"), Some(100)),
            (OperatorId("cpu"), Some(1000)),
        ];
        let p = OperatorSelectionPolicy::ForceOperator(OperatorId("cpu"));
        assert_eq!(p.pick(&cands), Some(1));
    }

    #[test]
    fn force_operator_none_when_named_declined_or_absent() {
        let declined = [(OperatorId("wgpu"), Some(100)), (OperatorId("cpu"), None)];
        let absent = [(OperatorId("wgpu"), Some(100))];
        let p = OperatorSelectionPolicy::ForceOperator(OperatorId("cpu"));
        assert_eq!(p.pick(&declined), None);
        assert_eq!(p.pick(&absent), None);
    }

    #[test]
    fn no_acceptor_and_empty_return_none() {
        let none_accept = [(OperatorId("a"), None), (OperatorId("b"), None)];
        let empty: [(OperatorId, Option<Cost>); 0] = [];
        for p in [
            OperatorSelectionPolicy::LowestCost,
            OperatorSelectionPolicy::PriorityOrder,
            OperatorSelectionPolicy::ForceOperator(OperatorId("a")),
        ] {
            assert_eq!(p.pick(&none_accept), None, "policy {p:?}");
            assert_eq!(p.pick(&empty), None, "policy {p:?}");
        }
    }

    // -------- PhysicalOperator is implementable + generic-usable --------

    /// A no-op operator over `usize` units that declines everything below a
    /// threshold (exercises the decline → fallback dialect).
    struct ThresholdOperator {
        threshold: usize,
    }

    // test-double: synthetic(a usize operator that declines below a threshold)
    impl PhysicalOperator for ThresholdOperator {
        type Input = usize;
        type Output = usize;

        fn id(&self) -> OperatorId {
            OperatorId("threshold")
        }
        fn estimated_cost(&self, input: &usize) -> Option<Cost> {
            if *input >= self.threshold {
                Some(*input as Cost)
            } else {
                None // decline → fallback
            }
        }
        fn run(&self, input: &usize) -> Option<usize> {
            Some(input * 2)
        }
    }

    #[test]
    fn operator_decline_and_accept() {
        let op = ThresholdOperator { threshold: 10 };
        assert_eq!(op.id(), OperatorId("threshold"));
        assert_eq!(op.estimated_cost(&5), None);
        assert_eq!(op.estimated_cost(&42), Some(42));
        assert_eq!(op.run(&21), Some(42));
    }

    #[test]
    fn operator_usable_as_generic_bound() {
        fn id_of<O: PhysicalOperator>(op: &O) -> OperatorId {
            op.id()
        }
        let op = ThresholdOperator { threshold: 1 };
        assert_eq!(id_of(&op), OperatorId("threshold"));
    }

    #[test]
    fn operator_id_is_copy_eq_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let a = OperatorId("x");
        let b = OperatorId("x");
        let c = OperatorId("y");
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(a.name(), "x");
        let mut ha = DefaultHasher::new();
        a.hash(&mut ha);
        let mut hb = DefaultHasher::new();
        b.hash(&mut hb);
        assert_eq!(ha.finish(), hb.finish());
    }
}
