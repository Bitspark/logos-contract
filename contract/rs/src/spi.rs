//! The checker-facing extension points — `Theory` (§5), `RuleAdmissibility` (§5a),
//! `LeafVerifier` (§6). **[STABLE v1]** (`logos-checker-spi v1`).
//!
//! These are the seams through which everything consumer-specific enters; the core
//! `check` stays consumer-agnostic and merely routes to them.

use crate::cert::{sort_dedup_by_ground_key, Hash};
use crate::completion::{Completion, NonCompletion, TheoryDecision};
use crate::derivation::{Evidence, NodeMeta};
use crate::engine::NoCallerLimit;
use crate::literal::{GroundLiteral, Symbol};
use crate::program::Clause;
use ontos_core::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

/// Domain separator for the canonical EDB-table snapshot hash (ADR 0007 §3.6), so an
/// EDB-snapshot digest can never collide with a clause id or any other hash.
pub const EDB_PREFIX: &[u8] = b"logos/account/edb-snapshot/v1\n";

/// The canonical snapshot hash of one extensional predicate's table, read as a SET —
/// `SHA-256(EDB_PREFIX ‖ pred-bytes ‖ ontos-codec(Tuple[rows…]))`, with the rows sorted by
/// [`ground_key`](crate::cert::ground_key) and a repeated row ignored (#2279): order and
/// multiplicity never change the hash. This is the value a [`LeafVerifier::edb_snapshot`]
/// returns for `pred` over its trusted EDB, and the value [`check`](crate::check) recomputes
/// over a cert's sealed extension table to bind that table to the live EDB (the
/// `cert_edb_mismatch` obligation). The sealed table is itself a set
/// ([`RelationTable::new`](crate::cert::RelationTable::new) dedups by the same key), so a
/// snapshot provider need not deduplicate its rows first.
pub fn edb_table_hash(pred: &Symbol, rows: &[GroundLiteral]) -> Hash {
    let mut sorted: Vec<&GroundLiteral> = rows.iter().collect();
    sort_dedup_by_ground_key(&mut sorted);
    // Reuse each row's labeled-compound value `Tuple[Atom(pred), args…]` (matching
    // ground_key's reading) so the canonical bytes are stable + cross-language.
    let row_values: Vec<Value> = sorted
        .iter()
        .map(|g| {
            let mut items = Vec::with_capacity(g.args.len() + 1);
            items.push(Value::atom(g.pred.bytes().to_vec()));
            items.extend(g.args.iter().cloned());
            Value::tuple(items)
        })
        .collect();
    let mut hasher = Sha256::new();
    hasher.update(EDB_PREFIX);
    hasher.update(pred.bytes());
    hasher.update(ontos_codec::encode(&Value::tuple(row_values)));
    hasher.finalize().into()
}

/// The inherent identity of a bound check component — an `(id, version,
/// config_digest)` triple a certificate's meaning depends on: "this derivation was
/// checked under THIS theory / leaves / admit." **[STABLE v1 — additive]**
///
/// Returned by the Checker-SPI components' [`Theory::identity`] /
/// [`LeafVerifier::identity`] / [`RuleAdmissibility::identity`] so a consumer above the
/// firewall (the certifying kernel) can DERIVE the check-profile digest from the *live*
/// profile it actually ran — rather than trusting a separately-supplied digest. That is
/// what makes a stamped certificate provably attest its verification path.
///
/// **Firewall-respecting (the contract carries only the raw triple).** This type holds
/// no digest scheme, no wire encoding, no negotiation policy — just the identity bytes.
/// The kernel maps it to its own negotiation binding and computes the digest; the
/// contract never learns how. Seam-free by construction (depends on nothing below).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ComponentIdentity {
    /// Component id bytes, e.g. `b"logos-core/arithmetic-theory"`.
    pub id: Vec<u8>,
    /// Version bytes, e.g. `b"1.0.0"`.
    pub version: Vec<u8>,
    /// A 32-byte config pin (all-zero = unconfigured / not config-bearing).
    pub config_digest: [u8; 32],
}

impl ComponentIdentity {
    /// An identity over explicit `(id, version, config_digest)`.
    pub fn new(
        id: impl Into<Vec<u8>>,
        version: impl Into<Vec<u8>>,
        config_digest: [u8; 32],
    ) -> Self {
        ComponentIdentity {
            id: id.into(),
            version: version.into(),
            config_digest,
        }
    }

    /// The placeholder a component that has NOT overridden `identity()` reports: a
    /// sentinel id, empty version, zero config digest. A profile of unidentified
    /// components still derives a *stable* digest — it simply does not distinguish
    /// them, so real attestation requires a component to override `identity()`.
    pub fn unidentified() -> Self {
        ComponentIdentity {
            id: b"unidentified".to_vec(),
            version: Vec::new(),
            config_digest: [0u8; 32],
        }
    }

    /// True iff this is the [`unidentified`](Self::unidentified) placeholder — the
    /// identity-audit primitive for a PLAIN component (#767, a **supported v1
    /// surface**, additive per ADR 0003): a component whose reported identity is
    /// unidentified contributes only a constant to any derived profile digest, so the
    /// digest attests nothing about it. For a [`CompoundTheory`], whose identity is a
    /// real-looking *computed* digest even over all-unidentified members, compare
    /// against [`compound_identity_of`] instead — this method alone cannot see through
    /// the composition, and the members are deliberately not enumerable (#708).
    pub fn is_unidentified(&self) -> bool {
        *self == Self::unidentified()
    }
}

/// The verdict of a [`Theory`] on a ground atom (§5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryOutcome {
    Holds,
    /// The atom is owned by this theory but does not hold; `code` is a host-band
    /// sub-code surfaced under `builtin_failed`.
    Fails {
        code: String,
    },
    /// Not this theory's predicate (a routing safety net; `check` routes by
    /// [`Theory::owns`], so a correctly-routed call never returns this).
    NotMine,
}

/// The mapping [`Theory::decide_ground`]'s default applies to a v1 answer (#3126): `Holds` and
/// `Fails` are the decision, and `NotMine` is the named `inconsistent_theory` fault. A wrapper
/// whose own answers come from `decide` (a host builtin) uses it for them, and forwards the rest.
pub fn ground_from_legacy(outcome: TheoryOutcome) -> Completion<TheoryDecision, NoCallerLimit> {
    match outcome {
        TheoryOutcome::Holds => Completion::Completed(TheoryDecision::Holds),
        TheoryOutcome::Fails { code } => Completion::Completed(TheoryDecision::Fails { code }),
        TheoryOutcome::NotMine => Completion::NotCompleted(NonCompletion::inconsistent_theory()),
    }
}

/// **The one legacy adapter (#3126):** the v1 [`TheoryOutcome`] of a
/// [`decide_ground`](Theory::decide_ground) answer, for a theory that overrides `decide_ground`
/// and derives its `decide` from it.
///
/// A not-completed answer becomes `NotMine`, never `Fails`: v1 has no "not decided" arm, and
/// every reader refuses an owned atom's `NotMine` by name, so a legacy reader fails CLOSED. It is
/// the wrong category (a stop reported as a routing fault) but never a wrong answer, and ADR 0036
/// D8's v2 deletes it with `decide` (seat:caa on #3126).
pub fn legacy_outcome(ground: Completion<TheoryDecision, NoCallerLimit>) -> TheoryOutcome {
    match ground {
        Completion::Completed(TheoryDecision::Holds) => TheoryOutcome::Holds,
        Completion::Completed(TheoryDecision::Fails { code }) => TheoryOutcome::Fails { code },
        Completion::LimitExceeded(never) => match never {},
        Completion::NotCompleted(_) => TheoryOutcome::NotMine,
    }
}

/// A DECLARED refusal to copy (#2722 item 1, ADR 0003's amendment): what
/// [`Theory::boxed_clone`] and [`LeafSource::boxed_clone`](crate::engine::LeafSource::boxed_clone)
/// return instead of a copy.
///
/// It replaces the defaulted `None` those methods returned until #2722. A default answered for
/// every implementor that never considered the question, so "cannot copy" and "never asked" read
/// the same, and nothing downstream could say why a provider could not sit an exam or be rebound.
/// The reason is mandatory ([`cannot_copy!`](crate::cannot_copy) refuses an empty one at compile
/// time), and callers carry it to where a refusal is reported.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyIncapacity {
    reason: std::borrow::Cow<'static, str>,
}

impl CopyIncapacity {
    /// An implementor's declared reason for not copying.
    pub fn declared(reason: impl Into<std::borrow::Cow<'static, str>>) -> Self {
        CopyIncapacity {
            reason: reason.into(),
        }
    }

    /// The reason, in the implementor's words.
    pub fn reason(&self) -> &str {
        &self.reason
    }

    /// The same refusal, located inside a composite: a compound declines as a whole when member
    /// `index` declines, and says which one.
    pub fn in_member(self, index: usize) -> Self {
        CopyIncapacity::declared(format!("member {index}: {}", self.reason))
    }
}

impl std::fmt::Display for CopyIncapacity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cannot copy: {}", self.reason)
    }
}

impl std::error::Error for CopyIncapacity {}

/// Whether a decider's `Fails` on a predicate it owns is always a decided false (#3142; research
/// 0031 row 13, `seat:caa`'s rulings on #3124 item 2, on #3142, and on #3189 Q3/Q4).
///
/// A decider that stops before it decides can surface the stop as [`TheoryOutcome::Fails`], a
/// decided false, and a closure check reads that false as knowledge: a sealed table can miss a
/// derivable row and still pass as exhaustive. #3313 landed the typed outcome channel,
/// [`Theory::decide_ground`], on which a stop is `NotCompleted` and never `Fails`. So the guard's
/// scope is the deciders whose stops still surface as `Fails`: the certifying kernel refuses, at
/// admission, every seal whose clauses reach a decider that does not declare [`StopsAreTyped`].
/// Host builtins stay in scope until a host declares its own decider's completion (#3506), and so
/// does any decider on the v1 `decide` alone.
///
/// **It retires at v2:** ADR 0036 D8 makes `decide_ground` required and deletes `decide`, and this
/// declaration goes with them.
///
/// The declaration is TYPED and made by the decider about itself, never a predicate list kept
/// elsewhere. Silence is not the safe answer (research 0025): a decider that declares nothing
/// reads [`Undeclared`], which admission treats exactly as [`MayNotComplete`] (fail closed,
/// `seat:caa` on #3142), and the census names it.
///
/// [`StopsAreTyped`]: DecisionCompletion::StopsAreTyped
/// [`MayNotComplete`]: DecisionCompletion::MayNotComplete
/// [`Undeclared`]: DecisionCompletion::Undeclared
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecisionCompletion {
    /// Every non-decision on the predicate reaches readers as [`Theory::decide_ground`]'s typed
    /// `NotCompleted`, so a `Fails` is always a decided false. A decider that never stops satisfies
    /// it trivially; one that stops satisfies it when every stop is typed (arithmetic's work cap,
    /// #3313). Named for the claim the guard needs, never "completes": a decider here may stop.
    StopsAreTyped,
    /// A decision may stop without deciding and still answer `Fails`: a capacity, a bounded-work
    /// cap, a host refusal or an unreadable reply.
    MayNotComplete {
        /// The deciding component, as it attests itself (the refusal's `component`).
        decider: ComponentIdentity,
        /// Why a decision may not complete, in the decider's words.
        cause: std::borrow::Cow<'static, str>,
    },
    /// The decider declared nothing ([`Theory::completion`]'s default). Admission reads it as
    /// `MayNotComplete`; the variant exists so the census can name the deciders that never
    /// considered the question.
    Undeclared {
        /// The deciding component, as it attests itself.
        decider: ComponentIdentity,
    },
}

impl DecisionCompletion {
    /// `decider`'s declaration that its decisions may not complete, for `cause`.
    pub fn may_not_complete(
        decider: ComponentIdentity,
        cause: impl Into<std::borrow::Cow<'static, str>>,
    ) -> Self {
        DecisionCompletion::MayNotComplete {
            decider,
            cause: cause.into(),
        }
    }

    /// Whether admission may rest a certified claim on this decider: only a declared
    /// [`StopsAreTyped`](DecisionCompletion::StopsAreTyped). Exhaustive on purpose, so a new arm is
    /// a compile error here rather than a silent admission.
    pub fn stops_are_typed(&self) -> bool {
        match self {
            DecisionCompletion::StopsAreTyped => true,
            DecisionCompletion::MayNotComplete { .. } | DecisionCompletion::Undeclared { .. } => {
                false
            }
        }
    }

    /// The deciding component a refusal names; `None` for a decider whose stops are typed.
    pub fn decider(&self) -> Option<&ComponentIdentity> {
        match self {
            DecisionCompletion::StopsAreTyped => None,
            DecisionCompletion::MayNotComplete { decider, .. }
            | DecisionCompletion::Undeclared { decider } => Some(decider),
        }
    }

    /// The stable tag the census and a refusal name the declaration by.
    pub fn tag(&self) -> &'static str {
        match self {
            DecisionCompletion::StopsAreTyped => "stops_are_typed",
            DecisionCompletion::MayNotComplete { .. } => "may_not_complete",
            DecisionCompletion::Undeclared { .. } => "undeclared",
        }
    }
}

impl std::fmt::Display for DecisionCompletion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = |d: &ComponentIdentity| crate::literal::escaped_name(&d.id);
        match self {
            DecisionCompletion::StopsAreTyped => f.write_str("stops are typed"),
            DecisionCompletion::MayNotComplete { decider, cause } => {
                write!(f, "{} may not complete: {cause}", name(decider))
            }
            DecisionCompletion::Undeclared { decider } => write!(
                f,
                "{} declares nothing, so it is read as may not complete",
                name(decider)
            ),
        }
    }
}

/// §5 Theory SPI — builtins / decidable atoms.
///
/// **Purity is load-bearing (§5).** A verdict MUST be a pure, total, deterministic
/// function of the ground arguments alone, reproducible from configuration, with
/// no I/O, clock, or ledger access — a *parameterized fact*, re-derivable by
/// anyone.
///
/// **Rust realization of "config-pinned" (§5).** The spec writes `type Config` +
/// `decide(atom, cfg)`. To keep [`check`](crate::check::check)'s signature stable
/// via a `Box<dyn Theory>` (object-safe — see §4's `CheckProfile`), the config is
/// held *inside* the implementing value (closed over at construction) rather than
/// threaded as an associated type. `decide` therefore takes only the atom; the
/// theory is still config-pinned and pure by construction. This realizes the
/// spec's *intent* (a stable check signature over a config-pinned pure relation);
/// it adjusts the trait's literal Rust syntax, not its semantics.
///
/// spi-role: consumer. A consumer implements this extension point in its own domain; a test
/// double of it may declare `consumer(<what it models>)` (#2720, scripts/test_doubles_inventory.py).
pub trait Theory {
    /// Does this theory own (decide) the given predicate? (§4 obligation 3 routes
    /// `Builtin` nodes by this; exactly one theory must own each builtin predicate.)
    fn owns(&self, pred: &Symbol) -> bool;

    /// Decide an owned ground atom. Pure / total / deterministic / config-pinned.
    ///
    /// The v1 form, kept for external readers: logos's own readers call
    /// [`decide_ground`](Self::decide_ground), which can also say "not decided".
    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome;

    /// **Decide an owned ground atom, or say it was NOT DECIDED (#3126; seat:caa's rulings of
    /// 2026-09-27).** A decider that stops before it establishes a fact (a work cap, a capacity)
    /// returns `NotCompleted(cause)`, never a false: under negation or in the closure check a
    /// stop read as `Fails` becomes a false positive (research 0031).
    ///
    /// **Additive (ADR 0003), defaulted from [`decide`](Self::decide):** `Holds` and `Fails` map
    /// to the decision, and `NotMine` to the named `inconsistent_theory` fault, so a theory that
    /// never stops needs no change. A theory that can stop overrides it, and its `decide` then
    /// answers the stopped case with `NotMine`, never `Fails`, so a legacy reader fails CLOSED.
    /// A composite theory FORWARDS it to its members rather than taking the default, which would
    /// read a member's `NotMine` as a fault.
    ///
    /// Every logos reader calls this, never `decide`: `check`'s builtin verification, the
    /// closure's literal truth, and the search registry's ground decision. `check` refuses a
    /// certificate whose builtin was not decided, in every position. ADR 0036 D8's checker SPI v2
    /// makes this method required and deletes `decide`.
    fn decide_ground(&self, atom: &GroundLiteral) -> Completion<TheoryDecision, NoCallerLimit> {
        ground_from_legacy(self.decide(atom))
    }

    /// **REQUIRED: hand back an independent copy of this theory, or DECLARE why not (#1023;
    /// required since #2722 item 1).**
    ///
    /// A conformance gate that wants to examine a provider on a program of the GATE's choosing has
    /// to rebuild that provider's context — and a context carries its theory. It cannot supply its
    /// own: the theory is part of the **pinned check-profile identity** (see
    /// [`guarantee`](../seam/guarantee) in the kernel — theory/leaves/admit identity, order-sensitive
    /// on the wire), so substituting one produces a DIFFERENT digest and therefore a verdict about a
    /// configuration nobody can request. The digest exists precisely to forbid that swap.
    ///
    /// **A declared break of ADR 0003's additive-only promise** (its #2722 amendment). This was
    /// defaulted to `None` until #2722, and a default answered for every implementor that never
    /// considered the question: research 0023 §3's "a default that answers dishonestly". It is now
    /// required. Declining is still a real answer, as a [`CopyIncapacity`] naming why: a theory
    /// that cannot copy itself makes its provider unable to sit a probe, and a provider that
    /// cannot sit a probe cannot be minted. An implementor that does not copy writes
    /// `logos_contract::cannot_copy!(Theory, "<why>");` inside its impl.
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, CopyIncapacity>;

    /// The [`ComponentIdentity`] this theory attests under. The certifying kernel
    /// derives the stamped check-profile digest from this (across theory/leaves/admit),
    /// so a certificate records the verification path it passed. **Additive (ADR
    /// 0003):** defaults to [`ComponentIdentity::unidentified`] — existing impls are
    /// unaffected; a real attestation overrides it.
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::unidentified()
    }

    /// Whether every stop this theory can make on the OWNED predicate `pred` reaches readers typed,
    /// so its `Fails` is always a decided false (#3142; [`DecisionCompletion::StopsAreTyped`]).
    ///
    /// **Additive (ADR 0003), and the default fails closed:** a theory that does not override
    /// this reads [`DecisionCompletion::Undeclared`], which admission treats as "may not
    /// complete", so a certified closure never rests on a decider that never declared
    /// (`seat:caa` on #3142). The predicate argument lets a composite route the question to the
    /// member that owns `pred`; a single theory answers for all it owns. On a predicate the
    /// theory does not own the answer is not meaningful, and a composite returns `Undeclared`.
    fn completion(&self, pred: &Symbol) -> DecisionCompletion {
        let _ = pred;
        DecisionCompletion::Undeclared {
            decider: self.identity(),
        }
    }
}

/// Domain separator for the [`CompoundTheory`] identity config-digest, so a compound's
/// config digest can never collide with another hash band.
const COMPOUND_THEORY_PREFIX: &[u8] = b"logos-core/compound-theory/v1\n";

/// A [`Theory`] that delegates to an ORDERED list of member theories, routing each
/// predicate to the first member that [`owns`](Theory::owns) it. This is how a consumer
/// binds MORE THAN ONE standard theory (e.g. arithmetic + text) behind the single
/// `Box<dyn Theory>` a [`CheckProfile`](crate::check::CheckProfile) holds — and, because
/// the engine emits a `Builtin` node only for a predicate its bound theory owns
/// ([dual-conformance][crate::check]), binding a compound is exactly what makes a
/// standard theory's relations reachable in search AND checkable.
///
/// **Partition discipline (§4.4).** `check` requires exactly one theory to own each
/// builtin predicate. The members a compound holds MUST own DISJOINT predicate sets; if
/// two members claim the same predicate, `decide` routes it to the FIRST owner
/// (deterministic, but a mis-binding) — keep the member predicate sets disjoint, as the
/// standard theories (arithmetic vs text) are by construction.
///
/// **Identity.** `logos-core/compound-theory@1.0.0` with a config digest that commits to
/// the ORDERED member identities (a length-prefixed SHA-256 over each member's `(id,
/// version, config_digest)`), so a profile binding a compound derives a stable digest
/// that distinguishes the exact membership and order.
///
/// **`Send + Sync` members.** The boxed members are `Send + Sync` so a compound is
/// itself `Send + Sync` — required by the kernel provider seam, which holds the search
/// theory across threads (the standard theories are zero-config unit structs, so this
/// costs nothing).
pub struct CompoundTheory {
    theories: Vec<Box<dyn Theory + Send + Sync>>,
}

impl CompoundTheory {
    /// A compound over `theories`, routed in order. The members SHOULD own disjoint
    /// predicate sets (the §4.4 builtin partition extends to the composition).
    pub fn new(theories: Vec<Box<dyn Theory + Send + Sync>>) -> Self {
        CompoundTheory { theories }
    }
}

impl Theory for CompoundTheory {
    /// Opt in to the #1023 probe clone — **the recursive case, and the only non-trivial one.**
    ///
    /// `CompoundTheory` is not `Clone` precisely because its members are `Box<dyn Theory>`; that
    /// makes it look like the counter-example to this whole affordance and it is the opposite —
    /// it is the case the affordance is FOR. If every member can copy itself, the compound can.
    ///
    /// **Declines as a whole if ANY member declines**, deliberately: a partial copy would be a
    /// DIFFERENT theory list, and theory order/content is identity-bearing on the wire
    /// (`theory_list_order_is_identity_bearing`), so a "best effort" copy would produce a
    /// mismatched check-profile digest — exactly the silent swap the digest exists to forbid.
    /// The refusal names the member that declined (#2722 item 1).
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, CopyIncapacity> {
        let mut copied: Vec<Box<dyn Theory + Send + Sync>> =
            Vec::with_capacity(self.theories.len());
        for (index, t) in self.theories.iter().enumerate() {
            copied.push(t.boxed_clone().map_err(|e| e.in_member(index))?);
        }
        Ok(Box::new(CompoundTheory { theories: copied }))
    }

    fn owns(&self, pred: &Symbol) -> bool {
        self.theories.iter().any(|t| t.owns(pred))
    }

    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome {
        // Route to the FIRST member that owns the predicate (members own disjoint sets,
        // so "first" is "the" owner). No member owns it → NotMine — a routing safety net;
        // `check` routes by `owns`, so a correctly-routed call always finds an owner.
        for theory in &self.theories {
            if theory.owns(&atom.pred) {
                return theory.decide(atom);
            }
        }
        TheoryOutcome::NotMine
    }

    /// Forwarded to the owning member (#3126), never the default: the default would read a
    /// member's `NotMine` (the answer a stopping member gives its legacy `decide`) as a fault
    /// instead of the member's own non-completion.
    fn decide_ground(&self, atom: &GroundLiteral) -> Completion<TheoryDecision, NoCallerLimit> {
        for theory in &self.theories {
            if theory.owns(&atom.pred) {
                return theory.decide_ground(atom);
            }
        }
        Completion::NotCompleted(NonCompletion::inconsistent_theory())
    }

    fn identity(&self) -> ComponentIdentity {
        let member_identities: Vec<ComponentIdentity> =
            self.theories.iter().map(|t| t.identity()).collect();
        compound_identity_of(&member_identities)
    }

    /// #3142: the declaration of the member that DECIDES `pred`, routed exactly as
    /// [`decide`](Theory::decide) routes (the first owner). A predicate no member owns has no
    /// decider here, so it reads `Undeclared` (fail closed), never a borrowed `StopsAreTyped`.
    fn completion(&self, pred: &Symbol) -> DecisionCompletion {
        match self.theories.iter().find(|theory| theory.owns(pred)) {
            Some(theory) => theory.completion(pred),
            None => DecisionCompletion::Undeclared {
                decider: self.identity(),
            },
        }
    }
}

/// The [`ComponentIdentity`] a [`CompoundTheory`] over members with exactly these
/// identities reports — the length-prefixed SHA-256 fold `CompoundTheory::identity`
/// itself delegates to, so the audit baseline and the live identity share ONE code
/// path and cannot drift.
///
/// **Supported v1 surface (#767, additive per ADR 0003).** This is the
/// identity-audit primitive for a COMPOUND: a compound's `identity()` is a computed
/// digest that reads as evidence even when every member is unidentified, and its
/// members are deliberately not enumerable (the #708 hazard). The audit therefore
/// never inspects members — the party that CONSTRUCTED the compound knows its member
/// count, and compares:
///
/// ```
/// # use logos_contract::{compound_identity_of, ComponentIdentity};
/// # let live_identity = compound_identity_of(&[ComponentIdentity::unidentified()]);
/// # let n = 1;
/// let baseline = compound_identity_of(&vec![ComponentIdentity::unidentified(); n]);
/// let distinguishable = live_identity != baseline;
/// ```
///
/// Equality with the baseline means no member contributes anything distinguishable —
/// the digest computes but attests nothing. Member ORDER and COUNT are identity-
/// bearing (the fold commits to both), so the baseline must be built for the same
/// `n` the live compound was constructed with.
///
/// **Inequality proves at least ONE member is distinguishable — not that all are.**
/// A compound with one identified member among unidentified ones reads
/// distinguishable while the others contribute constants (the vector's
/// `identified_first` case pins exactly this). A constructor who needs "every member
/// attested" has a stronger check available from the same helper: compare the live
/// identity against `compound_identity_of` over the member identities they INTENDED
/// to bind — equality there proves exact membership, in order. (The
/// `identity_audit_vectors` replays exercise that comparison for every case.)
pub fn compound_identity_of(member_identities: &[ComponentIdentity]) -> ComponentIdentity {
    let mut hasher = Sha256::new();
    hasher.update(COMPOUND_THEORY_PREFIX);
    for id in member_identities {
        hasher.update((id.id.len() as u64).to_be_bytes());
        hasher.update(&id.id);
        hasher.update((id.version.len() as u64).to_be_bytes());
        hasher.update(&id.version);
        hasher.update(id.config_digest);
    }
    let config_digest: [u8; 32] = hasher.finalize().into();
    ComponentIdentity::new(
        b"logos-core/compound-theory".to_vec(),
        b"1.0.0".to_vec(),
        config_digest,
    )
}

/// The consumer-facing **standard gate `Theory`** — a [`CompoundTheory`] over the four
/// standard checkable theories, in the SAME order the wasm guest binds them
/// (`app/wasm/rs/src/lib.rs` `standard_theory()`): [`ArithmeticTheory`](crate::arithmetic::ArithmeticTheory)
/// · [`TextTheory`](crate::text::TextTheory) · [`TermTheory`](crate::term_theory::TermTheory)
/// · [`ListTheory`](crate::list_theory::ListTheory).
///
/// **This is the helper a CHECK-side consumer binds into its [`CheckProfile`](crate::check::CheckProfile)
/// to certify a search that uses the guest's builtins.** A consumer that hand-assembles a
/// `CompoundTheory` member-by-member must keep it byte-identical to the guest's
/// `standard_theory()` (same members, same order) AND derive its advertised
/// `CheckProfileDigest` from the same components — getting either wrong silently fails to
/// certify a perfectly-formed `Builtin` node (issue #574). Binding `standard_theory()`
/// removes that footgun: it owns EXACTLY the predicate set the guest evaluates in search
/// (`is =:= =\= < > >= =< · contains starts_with ends_with · atom atomic compound is_list
/// number == \== @< @> @=< @>= =.. = \= true fail false · length nth0 last`), so every `Builtin` node the guest can
/// emit routes to an owner under `check`, and its [`identity`](Theory::identity) is the
/// stable [`CompoundTheory`] digest the kernel's `DeriveCheckProfileDigest` folds in.
///
/// The members own DISJOINT predicate sets (§4.4), so the partition discipline holds and a
/// program using none of these builtins is byte-identical to the empty-theory path (the
/// theory is never consulted). A SYNC-GUARD test pins this helper's owned set EQUAL to the
/// guest's so the two cannot silently diverge.
pub fn standard_theory() -> CompoundTheory {
    CompoundTheory::new(vec![
        Box::new(crate::arithmetic::ArithmeticTheory::new()),
        Box::new(crate::text::TextTheory::new()),
        Box::new(crate::term_theory::TermTheory::new()),
        Box::new(crate::list_theory::ListTheory::new()),
    ])
}

/// The verdict of a [`LeafVerifier`] (§6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeafOutcome {
    Admit,
    /// `code` is a host-band sub-code surfaced under `leaf_rejected`.
    Reject {
        code: String,
    },
}

/// §6 Leaf SPI — attestation / extensional admission, generic over the
/// verification context `C`.
///
/// Leaf verification is **fully delegated** here (v1 decision, §6): the kernel
/// verifies no signatures itself — a signature is an arche-style evidence
/// mechanism, not a universal property of an extensional leaf. `verify` MUST be
/// total and deterministic over `(atom, evidence, ctx)`; `ctx` is an immutable
/// snapshot (no I/O, clock, mutable state, or unbounded search) — §6 / G14.
///
/// spi-role: consumer. A consumer implements this extension point in its own domain; a test
/// double of it may declare `consumer(<what it models>)` (#2720, scripts/test_doubles_inventory.py).
pub trait LeafVerifier<C> {
    /// Declares the extensional (sealed/leaf) predicate set (§4.2). A `Leaf` may
    /// conclude **only** a predicate in this set.
    fn extensional(&self) -> &PredicateSet;

    fn verify(&self, atom: &GroundLiteral, evidence: &Evidence, ctx: &C) -> LeafOutcome;

    /// The canonical [`edb_table_hash`] of `pred`'s **complete** extensional table in
    /// this verifier's trusted EDB-of-record, or `None` if the verifier does not
    /// attest a snapshot for `pred` (ADR 0007 §3.6).
    ///
    /// **Additive — defaults to `None` (fail-closed).** A certifying check binds a
    /// cert's sealed extension table for an extensional predicate `p` to the live EDB
    /// by requiring `edb_table_hash(p, cert.table(p).rows) == leaves.edb_snapshot(p)`.
    /// When this returns `None`, the cert cannot bind `p` to a live snapshot, so a
    /// cert sealing an extensional `p` is **rejected** (`cert_edb_mismatch`) rather
    /// than trusted on the prover's word. A consumer that wants certifiable negation
    /// over extensional inputs MUST override this to return the real snapshot hash.
    fn edb_snapshot(&self, _pred: &Symbol, _ctx: &C) -> Option<Hash> {
        None
    }

    /// The [`ComponentIdentity`] this leaf verifier attests under (see
    /// [`Theory::identity`]). **Additive (ADR 0003):** defaults to
    /// [`ComponentIdentity::unidentified`].
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::unidentified()
    }
}

/// The verdict of a [`RuleAdmissibility`] check (§5a).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleOutcome {
    Admit,
    /// `code` is a host-band sub-code surfaced under `rule_inadmissible`
    /// (e.g. `"placement_mismatch"`).
    Reject {
        code: String,
    },
}

/// §5a RuleAdmissibility SPI — validates a `Rule` node's *metadata* after the core
/// has validated its *logical shape*. Generic over the context `C`.
///
/// `NodeMeta` stays opaque to core; only this verifier interprets it. Most
/// consumers bind the no-op [`AlwaysAdmit`] — a plain engine or any consumer whose
/// clauses are fixed/bootstrap needs nothing here. MUST be total and deterministic
/// over `(clause, meta, ctx)`; `ctx` is an immutable snapshot (§5a / G14).
///
/// spi-role: consumer. A consumer implements this extension point in its own domain; a test
/// double of it may declare `consumer(<what it models>)` (#2720, scripts/test_doubles_inventory.py).
pub trait RuleAdmissibility<C> {
    fn admissible(&self, clause: &Clause, meta: &NodeMeta, ctx: &C) -> RuleOutcome;

    /// The [`ComponentIdentity`] this admissibility policy attests under (see
    /// [`Theory::identity`]). **Additive (ADR 0003):** defaults to
    /// [`ComponentIdentity::unidentified`].
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::unidentified()
    }
}

/// The no-op `RuleAdmissibility`: admits every rule node. The default for any
/// consumer without provenance-bound clauses (§5a) — costs non-arche consumers
/// nothing.
#[derive(Clone, Copy, Debug, Default)]
pub struct AlwaysAdmit;

impl<C> RuleAdmissibility<C> for AlwaysAdmit {
    fn admissible(&self, _clause: &Clause, _meta: &NodeMeta, _ctx: &C) -> RuleOutcome {
        RuleOutcome::Admit
    }

    /// `core/always-admit@1.0.0`, no config — the no-op admit has a stable canonical
    /// identity so a profile that uses it derives a meaningful admit binding (rather
    /// than the `unidentified` placeholder).
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(b"core/always-admit".to_vec(), b"1.0.0".to_vec(), [0u8; 32])
    }
}

/// A set of predicate [`Symbol`]s — the extensional predicates a [`LeafVerifier`]
/// declares (§4.2).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PredicateSet(BTreeSet<Symbol>);

impl PredicateSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn contains(&self, pred: &Symbol) -> bool {
        self.0.contains(pred)
    }

    pub fn insert(&mut self, pred: impl Into<Symbol>) {
        self.0.insert(pred.into());
    }

    /// Iterate the member predicates in `BTreeSet` order (sorted by `Symbol`
    /// bytes). Additive accessor — used by the negotiation wire encoding (§3) to
    /// read a [`PredicateSet`] as a sorted `Tuple` of member symbols.
    pub fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.0.iter()
    }
}

impl<S: Into<Symbol>> FromIterator<S> for PredicateSet {
    fn from_iter<I: IntoIterator<Item = S>>(iter: I) -> Self {
        PredicateSet(iter.into_iter().map(Into::into).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unidentified_is_stable() {
        // The placeholder is a fixed value, so two unidentified components derive the
        // same identity (a stable digest, just not a distinguishing one).
        let a = ComponentIdentity::unidentified();
        let b = ComponentIdentity::unidentified();
        assert_eq!(a, b);
        assert_eq!(a.id, b"unidentified");
        assert!(a.version.is_empty());
        assert_eq!(a.config_digest, [0u8; 32]);
    }

    #[test]
    fn default_trait_identity_is_unidentified() {
        // A component that does not override `identity()` reports the placeholder.
        struct BareTheory;
        // test-double: adversarial(relies on the default identity: the placeholder under test)
        impl Theory for BareTheory {
            crate::cannot_copy!(
                Theory,
                "a test double: declines to copy, as the defaulted method did before #2722"
            );
            fn owns(&self, _pred: &Symbol) -> bool {
                false
            }
            fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
                TheoryOutcome::NotMine
            }
        }
        assert_eq!(BareTheory.identity(), ComponentIdentity::unidentified());
    }

    #[test]
    fn overridden_identity_round_trips() {
        // A component that DOES override `identity()` reports exactly its triple.
        struct LtTheory;
        // test-double: consumer(a less-than theory with an explicit identity)
        impl Theory for LtTheory {
            crate::cannot_copy!(
                Theory,
                "a test double: declines to copy, as the defaulted method did before #2722"
            );
            fn owns(&self, _pred: &Symbol) -> bool {
                true
            }
            fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
                TheoryOutcome::Holds
            }
            fn identity(&self) -> ComponentIdentity {
                ComponentIdentity::new(b"demo/lt".to_vec(), b"1.2.0".to_vec(), [7u8; 32])
            }
        }
        let id = LtTheory.identity();
        assert_eq!(id.id, b"demo/lt");
        assert_eq!(id.version, b"1.2.0");
        assert_eq!(id.config_digest, [7u8; 32]);
        assert_ne!(id, ComponentIdentity::unidentified());
    }

    #[test]
    fn compound_routes_to_the_owning_member_and_has_a_membership_digest() {
        use crate::arithmetic::ArithmeticTheory;
        use crate::text::TextTheory;

        let compound = CompoundTheory::new(vec![
            Box::new(ArithmeticTheory::new()),
            Box::new(TextTheory::new()),
        ]);

        // owns the UNION of both members' predicates, and nothing else.
        assert!(compound.owns(&Symbol::new(b"is".to_vec())));
        assert!(compound.owns(&Symbol::new(b"contains".to_vec())));
        assert!(compound.owns(&Symbol::new(b"starts_with".to_vec())));
        assert!(!compound.owns(&Symbol::new(b"concat".to_vec())));

        // decide routes each predicate to the member that owns it: a true text goal
        // holds, a false one fails with the text sub-code (not an arithmetic one).
        let hit = GroundLiteral::new(
            Symbol::new(b"contains".to_vec()),
            [
                Value::atom(b"hello world".to_vec()),
                Value::atom(b"world".to_vec()),
            ],
        );
        assert_eq!(compound.decide(&hit), TheoryOutcome::Holds);
        let miss = GroundLiteral::new(
            Symbol::new(b"contains".to_vec()),
            [Value::atom(b"abc".to_vec()), Value::atom(b"z".to_vec())],
        );
        assert_eq!(
            compound.decide(&miss),
            TheoryOutcome::Fails {
                code: "text_does_not_hold".into()
            }
        );
        // and an arithmetic goal still routes to the arithmetic member: two non-int
        // atoms make `=:=` not hold, with the arithmetic sub-code (not a text one).
        assert_eq!(
            compound.decide(&GroundLiteral::new(
                Symbol::new(b"=:=".to_vec()),
                [Value::atom(b"x".to_vec()), Value::atom(b"y".to_vec())],
            )),
            TheoryOutcome::Fails {
                code: "arith_does_not_hold".into()
            }
        );

        // identity: the compound id + a digest that commits to membership AND order.
        let id = compound.identity();
        assert_eq!(id.id, b"logos-core/compound-theory");
        assert_eq!(id.version, b"1.0.0");
        assert_ne!(id.config_digest, [0u8; 32]);
        let swapped = CompoundTheory::new(vec![
            Box::new(TextTheory::new()),
            Box::new(ArithmeticTheory::new()),
        ]);
        assert_ne!(id.config_digest, swapped.identity().config_digest);
        // deterministic: the same membership/order digests identically.
        let again = CompoundTheory::new(vec![
            Box::new(ArithmeticTheory::new()),
            Box::new(TextTheory::new()),
        ]);
        assert_eq!(id.config_digest, again.identity().config_digest);
    }

    #[test]
    fn always_admit_has_a_canonical_identity() {
        // The no-op admit reports a real, stable identity (not the placeholder), so a
        // profile that uses it derives a meaningful admit binding.
        let id = RuleAdmissibility::<()>::identity(&AlwaysAdmit);
        assert_eq!(id.id, b"core/always-admit");
        assert_eq!(id.version, b"1.0.0");
        assert_ne!(id, ComponentIdentity::unidentified());
    }
}
