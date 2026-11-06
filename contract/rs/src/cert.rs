//! §3 (ADR 0007) Closed-model certificate — the sealed, finite, exact relation a
//! negated premise `\+ r(a)` discharges against. **[FIRM amendment · additive]**
//!
//! A `\+ r(a)` is sound only if the checker can verify that *all* of `r` has been
//! enumerated and that the enumeration is *exact* (no junk, no missing heads) under
//! this program / EDB / profile / stratification. That argument is a
//! [`ClosedModelCert`]: a sealed finite model of a **stratum prefix**, carrying
//!
//! - the **scope** it seals ([`StratumPrefix`]),
//! - the pins it is sealed against (program / profile / context / theory-config
//!   hashes, EDB snapshot hashes),
//! - the finite **domains** every value must stay within ([`FiniteDomain`]),
//! - the exact **extensions** (relation tables) of the sealed predicates
//!   ([`RelationTable`]),
//! - a **support** witness (every sealed fact has a witness ⇒ `E ⊆ least model`)
//!   and a **closure** witness (every satisfied rule grounding has its head present
//!   ⇒ `least model ⊆ E`); together `E` is **exact**, so `a ∉ E ⇒ a` is false —
//!   absence is sound, not merely an upper bound,
//! - a [`CertSizeDecl`] of declared sizes the checker validates against its budgets
//!   **before** any scan.
//!
//! The checker re-derives the support and self-enumerates the closure over the
//! supplied finite [`domains`](ClosedModelCert::domains) — **verification, not
//! search**: every loop ranges over a supplied finite table pre-bounded by a budget.

use crate::literal::{GroundLiteral, Symbol};
use crate::program::ClauseId;
use crate::term::Subst;
use ontos_core::Value;

/// A 32-byte pin (e.g. a SHA-256 digest). The contract carries the raw bytes; how a
/// hash is *computed* is a consumer/kernel concern (the contract never learns the
/// scheme — it only compares pins for equality).
pub type Hash = [u8; 32];

/// An index into [`Derivation::closed_world`](crate::derivation::Derivation::closed_world).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CertId(pub u64);

impl CertId {
    /// The protocol index: an integer, never a host offset (#2735).
    pub fn index(self) -> u64 {
        self.0
    }

    /// The offset into a carried-certificate list of `len`, or `None` when it names none.
    pub fn offset(self, len: usize) -> Option<usize> {
        crate::index_offset(self.0, len)
    }
}

impl From<u64> for CertId {
    fn from(i: u64) -> Self {
        CertId(i)
    }
}

/// How a `\+ r(a)` premise's non-membership is witnessed against the cited cert. In
/// v1 the only form is a [`NonMemberProof::DirectLookup`] — the checker scans the
/// sealed [`RelationTable`] directly. The enum exists so a future compression scheme
/// (e.g. a sorted-run / Merkle non-membership proof) is an *additive* variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NonMemberProof {
    /// Direct membership scan of the sealed relation table.
    DirectLookup,
}

/// The scope a [`ClosedModelCert`] seals: a **stratum prefix** — all predicates up
/// to (and including) stratification `level`. A prefix (not a single predicate) is
/// needed because mutually-recursive positive SCCs must be sealed together.
///
/// `predicates` is kept **sorted and deduped** (by [`Symbol`] byte order) so membership
/// and scope-equality are canonical; build one via [`StratumPrefix::new`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StratumPrefix {
    /// The stratification level this prefix seals (predicates at levels `0..=level`).
    pub level: u32,
    /// The sealed predicate symbols, sorted + deduped. **Invariant, not a hint** (#839):
    /// [`seals`](Self::seals) is a binary search, so a struct literal built with unsorted
    /// predicates compiles fine and then fails membership lookups arbitrarily. Build via
    /// [`StratumPrefix::new`]; `verify_cert` rejects a non-canonical prefix up front.
    pub predicates: Vec<Symbol>,
}

impl StratumPrefix {
    /// Build a prefix, sorting + deduping the predicate set canonically.
    pub fn new(level: u32, predicates: impl IntoIterator<Item = Symbol>) -> Self {
        let mut predicates: Vec<Symbol> = predicates.into_iter().collect();
        predicates.sort();
        predicates.dedup();
        StratumPrefix { level, predicates }
    }

    /// Is `predicates` actually sorted + deduped (strictly increasing by [`Symbol`]
    /// order) — the invariant [`seals`](Self::seals) relies on? A struct literal can
    /// violate it; [`StratumPrefix::new`] cannot.
    pub fn is_canonical(&self) -> bool {
        self.predicates.windows(2).all(|w| w[0] < w[1])
    }

    /// Is `pred` sealed by this prefix?
    pub fn seals(&self, pred: &Symbol) -> bool {
        debug_assert!(
            self.is_canonical(),
            "StratumPrefix.predicates is not sorted+deduped - built via a struct literal instead of StratumPrefix::new? (issue #839)"
        );
        self.predicates.binary_search(pred).is_ok()
    }
}

/// A finite, typed value domain — the set of values an argument of a sealed
/// predicate may take. The closure join never enumerates them (#1829); a satisfied
/// grounding whose head value escapes every domain is `cert_out_of_domain`.
///
/// `values` is kept **sorted + deduped** by canonical [`ontos_codec`] bytes (ontos
/// `Value` has no `Ord`), so domain membership is a canonical binary search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteDomain {
    /// An opaque type tag naming this domain (e.g. `subject`, `action`).
    pub type_tag: Symbol,
    /// The domain's values, sorted + deduped by canonical codec bytes. **Invariant,
    /// not a hint** (#839): [`contains`](Self::contains) is a binary search, so a
    /// struct literal built with unsorted values compiles fine and then reports
    /// present values absent, arbitrarily per lookup. Build via [`FiniteDomain::new`];
    /// `verify_cert` rejects a non-canonical domain up front.
    pub values: Vec<Value>,
}

impl FiniteDomain {
    /// Build a domain, sorting + deduping its values by canonical codec bytes.
    pub fn new(type_tag: impl Into<Symbol>, values: impl IntoIterator<Item = Value>) -> Self {
        let mut values: Vec<Value> = values.into_iter().collect();
        values.sort_by_cached_key(ontos_codec::encode);
        values.dedup();
        FiniteDomain {
            type_tag: type_tag.into(),
            values,
        }
    }

    /// Is `values` actually sorted + deduped (strictly increasing by canonical codec
    /// bytes) — the invariant [`contains`](Self::contains) relies on? A struct literal
    /// can violate it; [`FiniteDomain::new`] cannot.
    pub fn is_canonical(&self) -> bool {
        self.values
            .windows(2)
            .all(|w| ontos_codec::encode(&w[0]) < ontos_codec::encode(&w[1]))
    }

    /// Does this domain contain `v`? (canonical binary search by codec bytes)
    pub fn contains(&self, v: &Value) -> bool {
        debug_assert!(
            self.is_canonical(),
            "FiniteDomain.values is not sorted+deduped by codec bytes - built via a struct literal instead of FiniteDomain::new? (issue #839)"
        );
        let key = ontos_codec::encode(v);
        self.values
            .binary_search_by(|x| {
                crate::ops::count_compare();
                ontos_codec::encode(x).cmp(&key)
            })
            .is_ok()
    }
}

/// The exact extension (relation table) of one sealed predicate: every ground fact
/// the sealed least model assigns to `pred`. Membership and absence are decided
/// against this table (the rows are kept sorted + deduped by canonical codec bytes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationTable {
    pub pred: Symbol,
    pub arity: u32,
    /// The exact rows, sorted + deduped by canonical codec bytes ([`ground_key`]).
    /// **Invariant, not a hint** (#839): [`contains`](Self::contains) is a binary
    /// search, so a struct literal built with unsorted rows compiles fine and then
    /// reports present rows absent, arbitrarily per lookup. Build via
    /// [`RelationTable::new`]; `verify_cert` rejects a non-canonical table up front.
    pub rows: Vec<GroundLiteral>,
}

impl RelationTable {
    /// Build a table, sorting + deduping its rows by canonical codec bytes.
    pub fn new(
        pred: impl Into<Symbol>,
        arity: u32,
        rows: impl IntoIterator<Item = GroundLiteral>,
    ) -> Self {
        let mut rows: Vec<GroundLiteral> = rows.into_iter().collect();
        sort_dedup_by_ground_key(&mut rows);
        RelationTable {
            pred: pred.into(),
            arity,
            rows,
        }
    }

    /// Is `rows` actually sorted + deduped (strictly increasing by [`ground_key`]) —
    /// the invariant [`contains`](Self::contains) relies on? A struct literal can
    /// violate it; [`RelationTable::new`] cannot.
    pub fn is_canonical(&self) -> bool {
        // #2511: each row's key once, not twice (a key per side of every adjacent pair).
        let keys: Vec<Vec<u8>> = self.rows.iter().map(ground_key).collect();
        keys.windows(2).all(|w| {
            crate::ops::count_compare();
            w[0] < w[1]
        })
    }

    /// Does this table contain `fact`? (canonical binary search)
    pub fn contains(&self, fact: &GroundLiteral) -> bool {
        debug_assert!(
            self.is_canonical(),
            "RelationTable.rows is not sorted+deduped by ground_key - built via a struct literal instead of RelationTable::new? (issue #839)"
        );
        let key = ground_key(fact);
        self.rows
            .binary_search_by(|x| {
                crate::ops::count_compare();
                ground_key(x).cmp(&key)
            })
            .is_ok()
    }
}

/// Sort `rows` by [`ground_key`] and keep one row per key: the canonical SET order (#2279).
/// [`RelationTable::new`] and [`edb_table_hash`](crate::spi::edb_table_hash) both use it, so a
/// sealed table and an EDB snapshot built from the same rows agree by construction. Rows are
/// equal exactly when their keys are, which is also how [`RelationTable::contains`] decides
/// membership; this replaces a structural `dedup()` that could disagree with the key.
pub(crate) fn sort_dedup_by_ground_key<T: std::borrow::Borrow<GroundLiteral>>(rows: &mut Vec<T>) {
    // Fully qualified: for `T = &GroundLiteral` a bare `.borrow()` could also resolve through
    // the blanket `Borrow<T> for T`.
    let key = |g: &T| ground_key(<T as std::borrow::Borrow<GroundLiteral>>::borrow(g));
    // #2511: each row's key ONCE. The dedupe used to re-encode both rows of every adjacent pair
    // after the cached sort, three encodes per row where one does. A stable sort on the keys and a
    // dedupe keeping the first of each run is exactly what the cached sort and `dedup_by` did.
    let mut keyed: Vec<(Vec<u8>, T)> = rows.drain(..).map(|g| (key(&g), g)).collect();
    keyed.sort_by(|a, b| {
        crate::ops::count_compare();
        a.0.cmp(&b.0)
    });
    keyed.dedup_by(|a, b| {
        crate::ops::count_compare();
        a.0 == b.0
    });
    rows.extend(keyed.into_iter().map(|(_, g)| g));
}

/// Canonical sort/compare key for a [`GroundLiteral`]: the codec bytes of its
/// labeled-compound value `Tuple[Atom(pred), args…]`. Total + deterministic.
pub fn ground_key(g: &GroundLiteral) -> Vec<u8> {
    crate::ops::count_encode();
    let mut items = Vec::with_capacity(g.args.len() + 1);
    items.push(Value::atom(g.pred.bytes().to_vec()));
    items.extend(g.args.iter().cloned());
    ontos_codec::encode(&Value::tuple(items))
}

/// A reference inside a [`SupportEdge`]'s body — how one body literal of the cited
/// rule is satisfied, with the rank discipline that prevents self-justification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SupportRef {
    /// A positive dependency on a fact **in the same sealed stratum**. Its `rank`
    /// MUST be **strictly smaller** than the supported fact's rank — the semi-naive
    /// discipline that rejects the `p :- p` self-justification (a fact cannot derive
    /// itself at equal or higher rank).
    SameStratum { fact: GroundLiteral, rank: u32 },
    /// A positive dependency on a fact in a **strictly lower** sealed stratum; it
    /// must be *present* in the cited lower cert's table.
    LowerStratum { cert: CertId, atom: GroundLiteral },
    /// A builtin/theory atom, decided `Holds` by the pinned `Theory`.
    Builtin { atom: GroundLiteral },
    /// A **negated** dependency on a fact in a strictly lower sealed stratum; it must
    /// be *absent* from the cited lower cert's table.
    NegLower { cert: CertId, atom: GroundLiteral },
    /// A **count** (ADR 0023) over a relation in a strictly lower sealed stratum (#2258 L3.3b):
    /// the edge's substitution fixes the count's filter and its claimed result, and the checker
    /// recomputes the aggregate over the cited lower cert's exact table and requires equality. It
    /// carries no copy of the result (`seat:caa`'s Q3: one source per fact) and adds no rank.
    CountLower { cert: CertId },
}

/// One support edge: a witness that a single sealed fact is in the least model —
/// the cited clause, grounded by `subst`, with head equal to `fact`, whose body
/// literals each resolve via a [`SupportRef`], at semi-naive `rank`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportEdge {
    /// The sealed fact this edge justifies (must equal the grounded clause head).
    pub fact: GroundLiteral,
    /// The clause whose grounding produced `fact`.
    pub clause: ClauseId,
    /// The grounding substitution applied to the clause.
    pub subst: Subst,
    /// One reference per clause body literal, in body order.
    pub body_refs: Vec<SupportRef>,
    /// The semi-naive rank assigned to `fact` (must strictly dominate every
    /// `SameStratum` body ref's rank).
    pub rank: u32,
}

/// The support witness: one [`SupportEdge`] per sealed IDB fact (`E ⊆ least model`).
/// Every fact in the sealed [`extensions`](ClosedModelCert::extensions) must have at
/// least one edge here — no junk.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SupportWitness(pub Vec<SupportEdge>);

/// The closure witness (`least model ⊆ E`).
///
/// **The checker does the closure itself (ADR 0007; #1829).** Rather than trust an
/// engine-supplied closure trace, the checker joins every scope clause's positive sealed
/// literals over the sealed tables and demands each body-true grounding's head be present
/// in the table (the theorem is stated stratum by stratum in `check/cert.rs`, #3022). The
/// engine therefore need only supply `domains` + `extensions`.
///
/// In v1 this type is an **empty marker** (closure carries no engine-supplied data):
/// it is kept as a named field so a future scheme (e.g. an engine-provided
/// grounding plan to bound enumeration further) is an *additive* change, not a
/// shape break.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClosureWitness;

/// The declared sizes of a certificate — every field validated against the [`CheckLimits`]
/// cert budgets **before** any scan, and every counted field against its ACTUAL value, so a
/// lying declaration is caught (`cert_decl_mismatch`, #2335) whichever field lies. The comparison
/// point differs by field: `cert_facts`, `domain_values` and `support_edges` are read off
/// the artifact and compared BEFORE the scan; `rule_groundings` and `join_steps` are the
/// closure scan's own counters and are compared AS IT RUNS (#1852), tripping the moment the
/// count exceeds the declaration — so a checked certificate's scan cost is bounded by
/// `min(declared, budget)`, never by the budget alone. `cert_bytes` is compared BEFORE the scan
/// too, and since #2524 it is also MEASURED: the certificate's canonical encoded size
/// ([`cert_encoded_bytes`](crate::cert_encoded_bytes)) must not exceed it, so `max_cert_bytes`
/// bounds what a certificate is, not only what it declares. Bounding the bytes a host READS
/// before decoding is the transport's (#2528).
///
/// [`crate::check::CheckLimits`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertSizeDecl {
    /// Declared total number of sealed facts (rows across all `extensions`).
    pub cert_facts: u64,
    /// Declared total number of domain values (across all `domains`).
    pub domain_values: u64,
    /// Declared total number of support edges.
    pub support_edges: u64,
    /// Declared number of rule groundings the closure join will emit — one per body-true
    /// tuple of a sealed-scope clause (#1829; before it, the groundings of `|∪domains|^vars`
    /// the self-enumeration would visit, an upper bound on this figure).
    pub rule_groundings: u64,
    /// Declared number of join steps the closure join will perform — one per candidate
    /// examined at one body literal: a sealed-table row offered to a binder, or the current
    /// tuple offered to a filter (#1829).
    pub join_steps: u64,
    /// Declared serialized size of the certificate, in bytes.
    pub cert_bytes: u64,
}

/// A sealed finite-model certificate for a **stratum prefix** (ADR 0007). Verified
/// once per citing derivation; a `\+ r(a)` premise reuses the verified result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedModelCert {
    /// The stratum prefix this cert seals.
    pub scope: StratumPrefix,
    /// Pin of the program the cert was computed against.
    pub program_hash: Hash,
    /// Pin of the check profile (leaves/admit identities).
    pub profile_hash: Hash,
    /// Pin of the verification context snapshot.
    pub ctx_hash: Hash,
    /// Pin of the theory configuration (so `not` means the same builtin semantics).
    pub theory_config_hash: Hash,
    /// Pins of the complete EDB snapshots the sealed extensions were drawn from.
    pub edb_snapshot_hashes: Vec<Hash>,
    /// The finite, typed value domains every sealed value must stay within.
    pub domains: Vec<FiniteDomain>,
    /// The exact extensions (relation tables) of the sealed predicates.
    pub extensions: Vec<RelationTable>,
    /// The support witness (`E ⊆ least model`, no junk).
    pub supports: SupportWitness,
    /// The closure witness (`least model ⊆ E`, no missing heads) — checked by the join.
    pub closure: ClosureWitness,
    /// Declared sizes, validated against the [`CheckLimits`](crate::check::CheckLimits)
    /// cert budgets before any scan.
    pub limits_decl: CertSizeDecl,
    /// **ADR 0029 D10 — the SLICE SEAL.** `None` (the default, and every pre-D10 cert) means
    /// [`program_hash`](Self::program_hash) pins the COMPLETE live clause set, which is ADR 0007
    /// §3.1's rule and what [`check`](crate::check) has always recomputed.
    ///
    /// `Some(pin)` means this cert was minted for ONE COMPONENT of a decomposition, so
    /// `program_hash` pins only that component's downward-closed SLICE — and `pin` is the digest
    /// of the `DecompositionWitness` that authorized the decomposition. The bound
    /// [`CertContext`](crate::check::CertContext) must carry the SAME pin, or the cert is refused:
    /// a cert sealed under one decomposition can never replay under another.
    ///
    /// **The contract tier never interprets this value.** It is 32 opaque bytes compared for
    /// equality. It cannot be anything richer: `DecompositionWitness` lives in `logos-kernel`,
    /// which depends DOWN on this crate (ADR 0004), so the checker can neither construct one nor
    /// re-derive the analysis behind it. The kernel — which holds the witness — is what binds the
    /// pin; `check` only enforces that the two ends agree.
    ///
    /// **Why a slice seal is sound at all:** scope downward-closure is verified against the
    /// COMPLETE live program regardless of this field (see `check_scope_downward_closed`, which
    /// walks every clause of `program`). So D10 changes only WHICH CLAUSE SET THE PIN COVERS; the
    /// gate that makes the sealed ideal provably closed is untouched.
    pub decomposition_witness: Option<Hash>,
    /// **ADR 0030 D1 — the PARTIAL sub-scope.** `None` (the default, and every pre-0030 cert)
    /// means every sealed table is exact: `E = least model` per predicate, which is what the
    /// support and closure witnesses together assert. `Some(p)` names the sealed predicates
    /// whose extension tables are **lower bounds** of their least-model relations — sealed at
    /// a round-budget trip (`TruncationReason::MaxRounds`), not at a fixpoint.
    ///
    /// The checker enforces three invariants before any table is consulted, each a
    /// `cert_partial_scope_invalid` refusal: `p ⊆ scope` and `p` is canonical (sorted + deduped
    /// by symbol byte order — build it via [`StratumPrefix::new`], #839); partial-ness is
    /// UPWARD-CLOSED within the sealed prefix (a "complete" table may depend only on complete
    /// tables, or its closure proof would be closed over `E` and vacuous for the rows the lower
    /// bound is missing); and an extensional table is never partial (it is snapshot-bound).
    ///
    /// What the mark changes in `check`: closure is NOT verified for a table in `p` (its
    /// failure is the truth of a lower bound, not a defect); support is verified as always
    /// (`E ⊆ least model` holds of a lower bound too); a `Neg` premise citing a predicate in
    /// `p` is refused `neg_atom_partial` and a `Count` premise `count_over_partial` — absence
    /// from, or a cardinality over, a lower bound proves nothing. Positive premises never read
    /// a certificate table at all.
    ///
    /// A `StratumPrefix` rather than a per-table flag on purpose: the mark is a predicate-set
    /// fact, `seals` gives the membership machinery, and a flag on `RelationTable` would change
    /// the arity of every table's wire tuple, i.e. every certificate ever pinned. This is the
    /// 12th trailing-optional element of the certificate tuple (ADR 0030 D4, the D10 shape).
    pub partial_scope: Option<StratumPrefix>,
}

impl ClosedModelCert {
    /// Is `pred`'s sealed table a LOWER BOUND (ADR 0030 D1)? `false` for every predicate of a
    /// cert with no `partial_scope`, i.e. every pre-0030 cert.
    pub fn is_partial(&self, pred: &Symbol) -> bool {
        self.partial_scope.as_ref().is_some_and(|p| p.seals(pred))
    }

    /// Look the exact table for `pred` up among this cert's extensions, if sealed.
    pub fn table(&self, pred: &Symbol) -> Option<&RelationTable> {
        self.extensions.iter().find(|t| &t.pred == pred)
    }

    /// Find the domain whose values contain `v` (used for the negated-atom typing
    /// check); `None` if no supplied domain contains it.
    pub fn domain_containing(&self, v: &Value) -> Option<&FiniteDomain> {
        self.domains.iter().find(|d| d.contains(v))
    }
}
