//! §3 Derivation — the shared DTO, the heart. **[FIRM]**
//!
//! A finite DAG of nodes; each node concludes a **ground** literal; premises
//! reference earlier nodes (acyclic). The node set is **closed and positive** —
//! `Rule | Builtin | Leaf` — with no negation/cut/findall/aggregation (§3.1): that
//! is the single decision making the contract checkable by a verifier *and*
//! producible by a solver, rather than "arche with holes".

use crate::cert::{CertId, ClosedModelCert, NonMemberProof};
use crate::literal::GroundLiteral;
use crate::program::{ClauseId, PredicateRef, ProjectSpec};
use crate::term::Subst;
use ontos_core::Value;

/// Provenance / placement metadata attached to a `Rule` node. **Opaque to the
/// core** — only a [`RuleAdmissibility`](crate::spi::RuleAdmissibility) verifier
/// interprets it (it carries, e.g., arche's `RuleProvenance`: signer, projection
/// binding, space). Modelled as an optional ontos value so a consumer can pack
/// arbitrary structured data the kernel never inspects. The inner value is private
/// so opacity-to-core is enforced by the type, not merely by convention: the
/// kernel cannot read it, only thread it to the verifier.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NodeMeta(Option<Value>);

impl NodeMeta {
    /// Empty metadata (the common case for non-provenance-bound rules).
    pub fn none() -> Self {
        NodeMeta(None)
    }

    /// Pack a consumer value as rule metadata.
    pub fn new(value: Value) -> Self {
        NodeMeta(Some(value))
    }

    /// The packed value, for a consumer's `RuleAdmissibility` to interpret.
    pub fn value(&self) -> Option<&Value> {
        self.0.as_ref()
    }
}

/// Attestation / admission evidence attached to a `Leaf` node. **Opaque to the
/// core** — only a [`LeafVerifier`](crate::spi::LeafVerifier) interprets it (it
/// carries, e.g., arche's `{signer, signature, admission, space}`). The inner
/// value is private for the same opacity reason as [`NodeMeta`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Evidence(Option<Value>);

impl Evidence {
    /// No evidence (e.g. a trusted axiom leaf).
    pub fn none() -> Self {
        Evidence(None)
    }

    /// Pack consumer evidence for a `LeafVerifier` to interpret.
    pub fn new(value: Value) -> Self {
        Evidence(Some(value))
    }

    /// The packed value, for a consumer's `LeafVerifier` to interpret.
    pub fn value(&self) -> Option<&Value> {
        self.0.as_ref()
    }
}

/// A grounded count filter (ADR 0023): each `(position, value)` requires the counted
/// row's argument at `position` to equal `value`. A row matches iff **every** entry
/// holds; an empty filter matches every row. Positions are 0-based argument indices.
/// The checker treats it positionally (not as a set) — a position out of the counted
/// predicate's arity is `count_attr_out_of_range`.
pub type GroundFilter = Vec<(u32, Value)>;

/// A `Rule` premise — one per clause body literal, with polarity (ADR 0007 / ADR 0023).
///
/// - [`Premise::Pos`] discharges a positive body literal by an earlier derivation
///   node (the same backward edge today's account carried as a bare `usize`).
/// - [`Premise::Neg`] discharges a **negated** body literal `\+ r(a)` as a checked
///   side-condition (NOT a node): the negated atom `r(a)` must be absent from a
///   cited, already-verified [`ClosedModelCert`]. This is what makes absence sound
///   rather than an upper bound — the cert proves the sealed relation is *exact*.
/// - [`Premise::Count`] discharges a `count`/`count_distinct` body literal (ADR 0023)
///   as a checked side-condition (NOT a node): the checker re-derives the cardinality
///   over the same proven-exact sealed relation and accepts only if it equals the
///   claimed `k`. The searcher proposes `k`; the gate re-checks it (dual-conformance).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Premise {
    /// A positive body literal, discharged by node index `node` (`< this node`).
    Pos { node: u64 },
    /// A negated body literal `\+ atom`, discharged by absence from `closed_world[cert]`.
    Neg {
        /// The grounded negated atom that must be absent from the sealed relation.
        atom: GroundLiteral,
        /// Index into [`Derivation::closed_world`] of the certificate to consult.
        cert: CertId,
        /// How non-membership is witnessed (a direct table lookup in v1).
        nonmember: NonMemberProof,
    },
    /// A certifiable `count` / `count_distinct` body literal (ADR 0023), discharged by
    /// recomputing the cardinality over `closed_world[cert].table(pred)`.
    Count {
        /// The sealed relation being counted — matched by name **and** arity (ADR 0023,
        /// #581: a wrong-arity table is `count_attr_out_of_range`, never silently counted).
        pred: PredicateRef,
        /// The ground bound-position filter selecting the counted rows (see
        /// [`GroundFilter`]).
        filter: GroundFilter,
        /// `Rows` ⇒ count matching rows; `Distinct { attr }` ⇒ count-distinct of
        /// column `attr` over matching rows (deduped by canonical key, `null()` excluded).
        project: ProjectSpec,
        /// The **claimed** cardinality, embedded as the canonical ontos/data `int`
        /// ground value (so it can bind a head variable exactly as `is/2` binds an
        /// arithmetic result). The checker recomputes `n` and requires `n == k`.
        k: Value,
        /// Index into [`Derivation::closed_world`] of the certificate to consult.
        cert: CertId,
    },
}

impl Premise {
    /// A positive premise referencing node index `n`.
    pub fn pos(n: u64) -> Premise {
        Premise::Pos { node: n }
    }
}

/// The one conversion from a protocol index to a host offset (#2735). An index is an INTEGER in
/// the contract's domain (`<=` [`INDEX_MAX`](crate::derivation_wire::INDEX_MAX)), not an offset: the offset exists
/// only when the index names an element of a collection of `len` elements. `None` otherwise,
/// including an index past what this build's `usize` holds, which then names no element either.
pub fn index_offset(index: u64, len: usize) -> Option<usize> {
    usize::try_from(index).ok().filter(|&i| i < len)
}

/// A bare node index lifts to a [`Premise::Pos`] — so existing all-positive premise
/// lists (`premises: vec![0, 2]` / `[0, 2].into()`) keep constructing unchanged.
impl From<u64> for Premise {
    fn from(node: u64) -> Self {
        Premise::Pos { node }
    }
}

/// A derivation node. Every kind concludes a [`GroundLiteral`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    /// Intensional step: instantiate a cited clause.
    Rule {
        conclusion: GroundLiteral,
        clause: ClauseId,
        /// Grounding substitution applied to the clause.
        subst: Subst,
        /// One [`Premise`] per body literal, in body order; each `Pos` index `< this
        /// node's index`. A `Neg` premise is a checked side-condition (ADR 0007).
        premises: Vec<Premise>,
        /// Opaque to core (provenance / projection binding / …).
        meta: NodeMeta,
    },
    /// A theory/builtin atom, decided by the [`Theory`](crate::spi::Theory) SPI
    /// (§5), not by clauses. Carries **no** `TheoryId` — dispatch is by predicate
    /// ownership (§3, §4 obligation 3).
    Builtin { conclusion: GroundLiteral },
    /// An extensional leaf, admitted by the [`LeafVerifier`](crate::spi::LeafVerifier)
    /// SPI (§6), not derived.
    Leaf {
        conclusion: GroundLiteral,
        evidence: Evidence,
    },
}

impl Node {
    /// The ground literal this node concludes (every kind has one).
    pub fn conclusion(&self) -> &GroundLiteral {
        match self {
            Node::Rule { conclusion, .. }
            | Node::Builtin { conclusion, .. }
            | Node::Leaf { conclusion, .. } => conclusion,
        }
    }
}

/// A finite DAG of nodes with a distinguished `root` (an index into `nodes`), plus
/// the [`ClosedModelCert`]s the derivation's `Neg` premises cite. This is
/// arche-core's `Proof { nodes, root }`, generalized so the two non-structural node
/// kinds delegate to extension points and a negated premise discharges against a
/// sealed certificate.
///
/// **Additive (ADR 0007).** `closed_world` defaults to empty
/// ([`Derivation::new`]); an all-`Pos`, empty-`closed_world` derivation is exactly
/// today's account, and `check` over it behaves byte-identically — the certificate
/// machinery is only consulted when a `Neg` premise (and hence a non-empty
/// `closed_world`) is present.
///
/// # This type IS the **account**
///
/// `Account` is not a separate type and never has been — it is the name the v2 design and
/// ADR 0003 give to *this* artifact:
///
/// - ADR 0003's layer table: **"A. Account / proof artifact"** → `Derivation`
///   (`Rule|Theory|Leaf`), **FIRM / invariant** per ADR 0001.
/// - `docs/spec/logos-contract.md`: *"the account grammar — the `Derivation` node set"*.
/// - v2 §0 glossary: *"**Account** — a derivation in the core evidence language (§8.3)"*.
///
/// So a plan item written `Account::foo()` is a method on `Derivation` — e.g. v2 §8.2's
/// `Account::is_self_contained()` ships as [`Derivation::is_self_contained`].
///
/// ⚠ Stated because a **declaration-shaped** search (`struct|enum|type Account`) returns
/// zero and reads as *"unbuilt"*. Two agents concluded exactly that on 2026-08-29; the
/// mapping was already in the three documents above and neither looked, because a
/// code-shaped question invites a code-shaped search. **This note cannot make that query
/// succeed** — only a public alias could, and adding a public name to FIRM layer A is
/// outside ADR 0003's additive permission (ADR 0003 says so explicitly) and is not a
/// documentation change. What it does is make a plain search for `account` state the
/// identity outright instead of only alluding to it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub nodes: Vec<Node>,
    pub root: u64,
    /// The closed-model certificates this derivation CARRIES, indexed by [`CertId`]: every
    /// certificate its `Neg` and `Count` premises cite, at the index they cite it by. The in-tree
    /// producer carries the prefix up to the highest cited certificate, and none when nothing is
    /// cited (#2533), so a carried certificate is not by itself a dependency: read the citations.
    ///
    /// #2565: a [`CertStack`], whose storage the answers of one solve SHARE. It reads and writes
    /// as the `Vec` it replaces; only cloning got cheap.
    pub closed_world: CertStack,
}

/// The closed-model certificates a [`Derivation`] carries, indexed by [`CertId`]: a `Vec` whose
/// storage is SHARED between clones (#2565).
///
/// Every answer of one solve that cites the same prefix of the stack holds the same allocation, so
/// cloning a derivation (the provider, the gate and the kernel's doors each do, per answer) copies
/// a pointer, not the certificates. Before this each answer owned a deep copy, and N answers of a
/// negation over a closure held N copies of the closure: the run's whole resident memory.
///
/// It behaves as the `Vec` it replaces. Reads deref to it (`len`, `iter`, indexing, `for c in &s`),
/// and a write copies first when the storage is shared (`Arc::make_mut`), so mutating one
/// derivation's stack never changes another's. Equality, `Debug` and every wire encoding read the
/// certificates, so no byte and no comparison moves: sharing is an allocation detail, not part of
/// the account.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CertStack(std::sync::Arc<Vec<ClosedModelCert>>);

impl CertStack {
    /// A stack over `certs`, sharable by cloning.
    pub fn new(certs: Vec<ClosedModelCert>) -> Self {
        CertStack(std::sync::Arc::new(certs))
    }

    /// Whether `a` and `b` share ONE allocation, not merely equal certificates.
    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        std::sync::Arc::ptr_eq(&a.0, &b.0)
    }
}

impl std::fmt::Debug for CertStack {
    /// The `Vec`'s own `Debug`, so a derivation prints as it did before the storage was shared.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::ops::Deref for CertStack {
    type Target = Vec<ClosedModelCert>;
    fn deref(&self) -> &Vec<ClosedModelCert> {
        &self.0
    }
}

impl std::ops::DerefMut for CertStack {
    /// Copy-on-write: a stack shared with another derivation is copied before it is changed.
    fn deref_mut(&mut self) -> &mut Vec<ClosedModelCert> {
        std::sync::Arc::make_mut(&mut self.0)
    }
}

impl From<Vec<ClosedModelCert>> for CertStack {
    fn from(certs: Vec<ClosedModelCert>) -> Self {
        CertStack::new(certs)
    }
}

/// Equal to a `Vec` holding the same certificates, in either order of comparison, as the `Vec`
/// field it replaced was.
impl PartialEq<Vec<ClosedModelCert>> for CertStack {
    fn eq(&self, other: &Vec<ClosedModelCert>) -> bool {
        *self.0 == *other
    }
}

impl PartialEq<CertStack> for Vec<ClosedModelCert> {
    fn eq(&self, other: &CertStack) -> bool {
        *self == *other.0
    }
}

impl FromIterator<ClosedModelCert> for CertStack {
    fn from_iter<I: IntoIterator<Item = ClosedModelCert>>(iter: I) -> Self {
        CertStack::new(iter.into_iter().collect())
    }
}

impl IntoIterator for CertStack {
    type Item = ClosedModelCert;
    type IntoIter = std::vec::IntoIter<ClosedModelCert>;
    fn into_iter(self) -> Self::IntoIter {
        std::sync::Arc::unwrap_or_clone(self.0).into_iter()
    }
}

impl<'a> IntoIterator for &'a CertStack {
    type Item = &'a ClosedModelCert;
    type IntoIter = std::slice::Iter<'a, ClosedModelCert>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut CertStack {
    type Item = &'a mut ClosedModelCert;
    type IntoIter = std::slice::IterMut<'a, ClosedModelCert>;
    fn into_iter(self) -> Self::IntoIter {
        std::ops::DerefMut::deref_mut(self).iter_mut()
    }
}

impl Derivation {
    /// The root as an offset into `nodes`, or `None` when the index names no node (#2735).
    pub fn root_offset(&self) -> Option<usize> {
        index_offset(self.root, self.nodes.len())
    }

    /// A derivation with **no** closed-model certificates (the all-positive case).
    /// Every existing call site is unchanged — `closed_world` defaults to empty.
    pub fn new(nodes: impl IntoIterator<Item = Node>, root: u64) -> Self {
        Derivation {
            nodes: nodes.into_iter().collect(),
            root,
            closed_world: CertStack::default(),
        }
    }

    /// A derivation that carries the closed-model certificates its `Neg` premises
    /// cite (ADR 0007).
    pub fn with_closed_world(
        nodes: impl IntoIterator<Item = Node>,
        root: u64,
        closed_world: impl IntoIterator<Item = ClosedModelCert>,
    ) -> Self {
        Derivation {
            nodes: nodes.into_iter().collect(),
            root,
            closed_world: closed_world.into_iter().collect(),
        }
    }

    /// [`with_closed_world`](Self::with_closed_world) over a stack the caller already holds
    /// (#2565): the derivation SHARES `closed_world`, it does not copy it.
    pub fn with_shared_closed_world(
        nodes: impl IntoIterator<Item = Node>,
        root: u64,
        closed_world: CertStack,
    ) -> Self {
        Derivation {
            nodes: nodes.into_iter().collect(),
            root,
            closed_world,
        }
    }

    /// Whether this account can be checked against a **trivial** context — no closure
    /// certificates to resolve against.
    ///
    /// §8.2 of the v2 design: *"an account is portable iff it is either fully
    /// self-contained or carries authenticated …"*. This is the **first arm**, and it is
    /// the account-side mirror of the kernel seam's `CheckContext::is_trivial`
    /// (named in prose, not linked: `contract` is the bottom tier and does not depend on
    /// `kernel` — ADR 0004).
    ///
    /// The polarity this reads is already load-bearing in [`check`](crate::check::check):
    /// a non-empty `closed_world` is a *certifying* check that needs a bound cert
    /// context, and for an all-positive derivation the context is never consulted.
    ///
    /// ⚠ **Deliberately HALF of its mirror, and that asymmetry is the point.**
    /// `CheckContext::is_trivial` is two-half — `base_commitments.is_empty() &&
    /// certificates.is_empty()`. This is the **closure half only**: the base-facts half
    /// has no account-side carrier, because contract's `check` reads `base_commitments`
    /// **nowhere** (0 references). Widen this when base facts become context-dependent.
    /// An `&&` over a field nothing reads would be **vacuously true** and would read as
    /// coverage it does not provide (ruled 2026-08-29, `seat:cca`).
    #[must_use]
    pub fn is_self_contained(&self) -> bool {
        self.closed_world.is_empty()
    }
}
