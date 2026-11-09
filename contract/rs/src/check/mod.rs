//! §4 Checker SPI — the P0 deliverable. **[FIRM core obligations · STABLE v1 seam params]**
//!
//! [`check`] is **total** and performs **no search**. In one forward pass over the
//! DAG it verifies every node is locally valid and that the root concludes the
//! claim. Consumer-specific decisions enter only through the bound profile
//! (`Theory` / `LeafVerifier` / `RuleAdmissibility`), so the *signature* is stable
//! while the *bindings* are consumer-supplied.
//!
//! This module is the rule-check forward pass + verdict taxonomy; the ADR-0007
//! closed-model-certificate machinery a `Neg` premise discharges against lives in
//! the private [`cert`] submodule (a pure file split — `verify_cert`,
//! `verify_neg_premise`, and the public [`program_digest`] are re-bound here, so the
//! crate-root re-exports and the public `check` signature are byte-identical).

mod cert;
mod cert_count;
mod cert_stack;
mod cert_support;
mod cert_truth;
#[cfg(test)]
mod fragment_replay;
mod join_index;
#[cfg(test)]
mod tests;
mod world_memo;

// The cert machinery the rule-check pass delegates to, re-bound into this module so
// the file split is internal: `check_with_cert_context` verifies each cited cert via
// `verify_cert`, `check_node` discharges a `Neg` premise via `verify_neg_premise`, and
// `program_digest` stays a public `check::` item (a crate-root re-export consumer
// derives a `CertContext::program_hash` from). See [`cert`] for the soundness argument.
pub use cert::{
    cert_size_over_budget, closure_join_cost, closure_join_cost_in_world, program_digest,
};
use cert::{
    verify_cert, verify_count_premise, verify_neg_premise, CertPlace, CertStatus, WorldProgram,
};
pub use cert_stack::seal_contexts;
pub use world_memo::WorldMemo;

use crate::cert::{Hash, SupportRef};
use crate::completion::{Completion, NonCompletion, NonCompletionKind, TheoryDecision};
use crate::derivation::{index_offset, Derivation, Node, Premise};
use crate::literal::{Goal, GroundLiteral, Symbol};
use crate::program::{BodyLit, ClauseId, Program};
use crate::spi::{LeafOutcome, LeafVerifier, RuleAdmissibility, RuleOutcome, Theory};
use crate::term::{Subst, Term};
use ontos_core::Value;
use std::collections::BTreeSet;

// **Every certified literal claim is EXACT** (#3022, research 0028; `seat:caa`'s ruling). `check`
// compares ground terms STRUCTURALLY at every site: the root against the claim, a Rule's
// instantiated head against its conclusion, a positive premise against the grounded body literal,
// a negated atom, and a count's `k`. The profile's `TermIdentity` is not read here.
//
// Before #3022 the default identity compared four of those sites under #277's ACCOUNT EQUALITY
// (the cons and `list(…)` spellings of a proper list as one term). That relation is not a
// congruence (the list normal form never rewrites a cons TAIL), so a label-tolerant site could
// certify a claim true in neither the exact model nor the list quotient: `p([b]). r([a|X]) :-
// p(X).` with `X = list(b)` concluded `r([a|list(b)])`. The list spelling a producer shows a
// consumer is presentation, carried beside the exact fact
// (`crate::engine::PresentedFact`), never certified in place of it.

/// #2177 A: whether a clause literal under `subst` provably equals a ground literal, decided
/// without allocating. The allocating path (`substitute` + `as_ground` + structural equality)
/// builds a fresh term and value per literal per node, which was most of `check`'s per-node cost.
///
/// **One-sided** (`seat:caa`'s ruling on #2177, A1). `true` only when
/// `goal.substitute(subst).as_ground()` is `Some(g)` and `g` is structurally equal to `lit`, a
/// case the allocating path also calls equal. `false` means "not proven here",
/// never "unequal": the caller falls back to the allocating path, which alone decides and alone
/// mints every rejection. The walk mirrors [`Term::substitute`]: one pass, so a bound variable's
/// image is compared as it stands, and an image that still holds a variable is not ground. An
/// unbound variable, any structural difference, and every cons/`list` reification pair all
/// answer `false` and fall back.
///
/// The recursion is bounded: `check_term_depths` has already held every cited clause term,
/// substitution image and node conclusion to `max_term_depth` before the forward pass runs.
fn goal_eq_under_subst(goal: &Goal, subst: &Subst, lit: &GroundLiteral) -> bool {
    goal.pred == lit.pred
        && goal.args.len() == lit.args.len()
        && goal
            .args
            .iter()
            .zip(&lit.args)
            .all(|(term, value)| term_eq_under_subst(term, subst, value))
}

/// [`goal_eq_under_subst`] for one argument.
///
/// #2275 layer 3: over an explicit stack of pairs, not one native frame per nesting level. Each
/// pair carries whether substitution still applies: a variable is substituted ONCE, and the image
/// it resolves to is compared as it stands (one pass), so a variable inside an image means it is
/// not ground and the pair is unequal.
fn term_eq_under_subst(term: &Term, subst: &Subst, value: &Value) -> bool {
    let mut work: Vec<(&Term, &Value, bool)> = vec![(term, value, true)];
    while let Some((term, value, under)) = work.pop() {
        match (term, value) {
            (Term::Var(id), _) if under => match subst.get(id) {
                Some(image) => work.push((image, value, false)),
                None => return false,
            },
            (Term::Var(_), _) => return false,
            (Term::Atom(bytes), Value::Atom(atom)) if atom.bytes() == bytes.as_slice() => {}
            (Term::Tuple(children), Value::Tuple(tuple))
                if tuple.items().len() == children.len() =>
            {
                work.extend(
                    children
                        .iter()
                        .zip(tuple.items())
                        .map(|(child, item)| (child, item, under)),
                );
            }
            _ => return false,
        }
    }
    true
}

/// [`goal_eq_under_subst`], with its one-sidedness re-checked against the allocating path in
/// debug builds (#2177 A2). That makes every `check` test, from the vector corpus to the tamper,
/// forgery and mutation suites, a differential test of the fast path.
fn proved_equal_fast(goal: &Goal, subst: &Subst, lit: &GroundLiteral) -> bool {
    let fast = goal_eq_under_subst(goal, subst, lit);
    debug_assert!(
        !fast
            || goal
                .substitute(subst)
                .as_ground()
                .is_some_and(|ground| ground == *lit),
        "#2177: the fast path proved equal where the allocating path does not"
    );
    fast
}

/// The result of [`check`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Accept,
    Reject { code: RejectionCode, detail: String },
}

impl Outcome {
    fn reject(code: RejectionCode, detail: impl Into<String>) -> Outcome {
        Outcome::Reject {
            code,
            detail: detail.into(),
        }
    }

    pub fn is_accept(&self) -> bool {
        matches!(self, Outcome::Accept)
    }
}

/// Rejection codes (§4). Two bands:
///
/// - **structural band** (FIRM, closed, frozen tri-core) — the codes the kernel
///   itself emits. Branch on these, not on `detail`.
/// - **host-extension band** (STABLE v1 *mechanism*; sub-code set open) — the three
///   wrappers a delegated extension point raises; the seam's own sub-code is
///   carried in `Outcome::Reject.detail`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RejectionCode {
    // ---- structural band (FIRM) ----
    EmptyDerivation,
    TooManyNodes,
    TooDeep,
    /// A single term nests deeper than `CheckLimits::max_term_depth` (issue #253) — a
    /// pathologically deep term that would overflow the native stack in the recursive
    /// term traversals of the trusted path. Distinct from `TooDeep`, which bounds
    /// DAG/premise-chain depth: a single node's term can be arbitrarily deep within
    /// one node, so the DAG-depth cap does not bound it.
    TermTooDeep,
    RootOutOfRange,
    NonGroundConclusion,
    UnknownClause,
    InstantiationMismatch,
    BadDependencyOrder,
    RootConclusionMismatch,
    SealedViolation,
    PredicatePartitionViolation,
    UnknownNodeKind,
    // ---- closed-model certificate band (ADR 0007, structural / FIRM) ----
    /// A `Neg` premise cites a `closed_world` index out of range.
    CertOutOfRange,
    /// The certificate's CLOSURE work exceeds the caller's `CheckLimits` closure budget: its
    /// declared `rule_groundings` / `join_steps`, or the count the closure scan reaches live, is
    /// over `max_rule_groundings` / `max_join_steps`. The caller's verify budget, not an engine
    /// fault (#2335). ⚠ Until CHECKER_VERSION 10 this code ALSO covered the four size budgets
    /// (now `cert_size_exceeded`) and a lying declaration (now `cert_decl_mismatch`), so a verdict
    /// stored under an older version meant something wider.
    CertBudgetExceeded,
    /// The certificate's declared SIZE exceeds the caller's `CheckLimits` size budget: its
    /// `cert_bytes` / `cert_facts` / `domain_values` / `support_edges` is over the matching
    /// `max_*`. The caller's verify budget, not an engine fault (#2335).
    CertSizeExceeded,
    /// The certificate's ACTUAL size or closure work exceeds its OWN declaration
    /// (`limits_decl`): the producer under-declared, so an engine fault. Split from
    /// `cert_budget_exceeded` by #2335, which until then named both parties.
    CertDeclMismatch,
    /// A certificate's pinned hashes do not match the check context.
    CertContextMismatch,
    /// A `\+ atom`'s predicate is not sealed by the cited certificate.
    NegAtomNotSealed,
    /// The negated predicate is not in a strictly-lower stratum than the rule head.
    NegStratumNotLower,
    /// The negated atom is not ground / well-typed within the cert's finite domain.
    NegAtomIllTyped,
    /// The negated atom IS present in the sealed relation (so `\+` does not hold).
    NegAtomPresent,
    /// A sealed fact lacks a valid support edge (the relation is not `⊆ least model`).
    CertUnsupported,
    /// A satisfied rule grounding's head is absent from the table (not closed).
    CertNotClosed,
    /// A satisfied grounding produces a value outside the sealed finite domain.
    CertOutOfDomain,
    /// The sealed stratum prefix is not downward-closed: a defining clause's body
    /// references a predicate that is neither sealed by the scope nor theory-owned
    /// (so closure cannot soundly evaluate it).
    CertScopeIncomplete,
    /// A `Neg`-bearing derivation supplied an all-zero (unbound) cert context — a
    /// certificate must be bound to the live program/profile, never trusted free.
    CertContextUnbound,
    /// A sealed extensional table does not match the live EDB snapshot (its rows are
    /// not the complete EDB-of-record for that predicate).
    CertEdbMismatch,
    /// A cert's `partial_scope` (ADR 0030 D1) breaks one of its three invariants: it is not
    /// canonical or not a sub-scope of `scope`; it marks an extensional table (snapshot-bound,
    /// complete by definition); or it is not upward-closed within the sealed prefix — a
    /// "complete" table's defining clause reads (positively or under a count) a predicate
    /// marked partial, so its closure proof would be closed over `E` and vacuous for the rows
    /// the lower bound is missing.
    CertPartialScopeInvalid,
    /// A `\+ atom`'s predicate is sealed by the cited certificate but marked PARTIAL (ADR
    /// 0030 D2): its table is a lower bound, so absence from it proves nothing — a later
    /// round could derive the atom.
    NegAtomPartial,
    // ---- certifiable aggregation band (ADR 0023, structural / FIRM) ----
    /// A `Count` premise's counted predicate is not in a strictly-lower stratum than
    /// the rule head (a count is non-monotone, so it must read a sealed lower stratum).
    CountStratumNotLower,
    /// A `Count` premise's filter position or `count_distinct` projection attribute is
    /// outside the counted predicate's arity.
    CountAttrOutOfRange,
    /// A `Count` premise's claimed cardinality `k` does not equal the count recomputed
    /// over the proven-exact sealed relation (the core dual-conformance guarantee).
    CountMismatch,
    /// A `min`/`max` aggregate (ADR 0023 #587 follow-on) folds **no** matching rows: the
    /// minimum/maximum of an empty set is **undefined**. v1 rejects rather than minting an
    /// infinity or sentinel (an empty `sum` is `0`, never this code).
    AggEmptyUndefined,
    /// A `Count` premise's counted predicate is sealed by the cited certificate but marked
    /// PARTIAL (ADR 0030 D2): a cardinality over a lower bound is itself a lower bound, never
    /// the claimed `k`. The count twin of `neg_atom_partial`.
    CountOverPartial,
    // ---- host-extension band (STABLE v1 mechanism; sub-code in `detail`) ----
    BuiltinFailed,
    /// #3126: the theory did not DECIDE a builtin literal the derivation relies on (its
    /// [`decide_ground`](crate::spi::Theory::decide_ground) stopped: a work cap, a capacity).
    /// `check` refuses rather than reading the stop as a decision, in every position: a positive
    /// `Builtin` node, a support edge's builtin, and a closure rule instance whose body is not
    /// decided and whose head is absent. The sub-code in `detail` is the stop's kind tag
    /// (`work_cap`, …), as `builtin_failed` carries the theory's own code.
    BuiltinNotDecided,
    LeafRejected,
    RuleInadmissible,
    /// The caller's configuration is invalid. No proof has been assessed.
    InvalidCheckLimits,
}

impl RejectionCode {
    /// The stable, cross-language rejection-code string — the **normative**
    /// artifact (the `Display`/`detail` text is diagnostic only). These strings are
    /// byte-identical across the `{rs,go}` bindings and equal the `code` field in
    /// the shared conformance vectors.
    pub fn code(&self) -> &'static str {
        match self {
            RejectionCode::EmptyDerivation => "empty_derivation",
            RejectionCode::TooManyNodes => "too_many_nodes",
            RejectionCode::TooDeep => "too_deep",
            RejectionCode::TermTooDeep => "term_too_deep",
            RejectionCode::RootOutOfRange => "root_out_of_range",
            RejectionCode::NonGroundConclusion => "non_ground_conclusion",
            RejectionCode::UnknownClause => "unknown_clause",
            RejectionCode::InstantiationMismatch => "instantiation_mismatch",
            RejectionCode::BadDependencyOrder => "bad_dependency_order",
            RejectionCode::RootConclusionMismatch => "root_conclusion_mismatch",
            RejectionCode::SealedViolation => "sealed_violation",
            RejectionCode::PredicatePartitionViolation => "predicate_partition_violation",
            RejectionCode::UnknownNodeKind => "unknown_node_kind",
            RejectionCode::CertOutOfRange => "cert_out_of_range",
            RejectionCode::CertBudgetExceeded => "cert_budget_exceeded",
            RejectionCode::CertSizeExceeded => "cert_size_exceeded",
            RejectionCode::CertDeclMismatch => "cert_decl_mismatch",
            RejectionCode::CertContextMismatch => "cert_context_mismatch",
            RejectionCode::NegAtomNotSealed => "neg_atom_not_sealed",
            RejectionCode::NegStratumNotLower => "neg_stratum_not_lower",
            RejectionCode::NegAtomIllTyped => "neg_atom_ill_typed",
            RejectionCode::NegAtomPresent => "neg_atom_present",
            RejectionCode::CertUnsupported => "cert_unsupported",
            RejectionCode::CertNotClosed => "cert_not_closed",
            RejectionCode::CertOutOfDomain => "cert_out_of_domain",
            RejectionCode::CertScopeIncomplete => "cert_scope_incomplete",
            RejectionCode::CertContextUnbound => "cert_context_unbound",
            RejectionCode::CertEdbMismatch => "cert_edb_mismatch",
            RejectionCode::CertPartialScopeInvalid => "cert_partial_scope_invalid",
            RejectionCode::NegAtomPartial => "neg_atom_partial",
            RejectionCode::CountStratumNotLower => "count_stratum_not_lower",
            RejectionCode::CountAttrOutOfRange => "count_attr_out_of_range",
            RejectionCode::CountMismatch => "count_mismatch",
            RejectionCode::AggEmptyUndefined => "agg_empty_undefined",
            RejectionCode::CountOverPartial => "count_over_partial",
            RejectionCode::BuiltinFailed => "builtin_failed",
            RejectionCode::BuiltinNotDecided => "builtin_not_decided",
            RejectionCode::LeafRejected => "leaf_rejected",
            RejectionCode::RuleInadmissible => "rule_inadmissible",
            RejectionCode::InvalidCheckLimits => "invalid_check_limits",
        }
    }

    /// True for the closed FIRM structural band — the codes a `check` over
    /// well-typed input may itself emit. (`non_ground_conclusion` and
    /// `unknown_node_kind` are in the band but are *decoder*-emitted: a well-typed
    /// [`Node`] always concludes a ground literal and is one of three known kinds,
    /// so `check` over typed input never raises them — a decoder building a `Node`
    /// from untrusted bytes does.)
    pub fn is_structural(&self) -> bool {
        !matches!(
            self,
            RejectionCode::BuiltinFailed
                | RejectionCode::BuiltinNotDecided
                | RejectionCode::LeafRejected
                | RejectionCode::RuleInadmissible
                | RejectionCode::InvalidCheckLimits
        )
    }
}

/// #3126: the refusal of a theory literal whose ground decision did not complete,
/// `builtin_not_decided` with the stop's kind tag as its sub-code. Every position `check` reads
/// a theory's ground verdict in names it through here.
pub(super) fn builtin_not_decided(cause: NonCompletion) -> (RejectionCode, String) {
    (
        RejectionCode::BuiltinNotDecided,
        cause.kind().tag().to_string(),
    )
}

/// Whether a non-completion is the fault the default `decide_ground` reports for a `NotMine`
/// (#3126): the theory disowned an atom its `owns` claimed. Each reader keeps the refusal it gave
/// `NotMine` for it, so an inconsistent theory reads as before.
pub(super) fn is_disowned(cause: &NonCompletion) -> bool {
    cause.kind() == NonCompletionKind::InconsistentTheory
}

/// The TERM IDENTITY (#2226, §4.3). **INERT since #3022** (`seat:caa`'s ruling on #3037): `check`
/// ignores it and compares every site structurally, and the check-profile digest does not fold it,
/// so two profiles that differ only here give identical verdicts and share one digest. Pinned
/// inert by `vectors/exact_claims.json`, which the conformance harness drives under each identity,
/// and by the completeness gate's `exact_answer_set` test under each identity.
///
/// It is slated for DELETION in #3022's step 5: out of [`CheckLimits`] (ADR 0035 D1, since removing
/// a field is a v1 signature change) and its pins out of the negotiation wire. It does not move to
/// the representation axis: how a list is spelled on display is the consumer's rendering choice
/// ([`crate::engine::PresentedFact`]), not a property of what is certified.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum TermIdentity {
    /// The default tag (#159). Inert, as is [`Exact`](Self::Exact).
    #[default]
    ReifyLists,
    /// The other tag (#2226). Inert: `check` gives the verdict it gives under the default.
    Exact,
}

impl TermIdentity {
    /// The stable tag: `reify_lists` or `exact`.
    pub fn tag(self) -> &'static str {
        match self {
            TermIdentity::ReifyLists => "reify_lists",
            TermIdentity::Exact => "exact",
        }
    }
}

/// The checker's **behaviour parameters** (§4.3): budgets on the **untrusted** supplied
/// derivation, plus the INERT [`term_identity`](Self::term_identity). The budgets are distinct
/// from search-effort limits: they bound *proof size on verify*, and the node cap is a hard,
/// deterministic rejection checked **before any node delegation**.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckLimits {
    /// Max total node count (`> max_nodes` → `too_many_nodes`).
    pub max_nodes: usize,
    /// Max DAG depth (longest premise chain) (`> max_depth` → `too_deep`).
    pub max_depth: usize,
    /// Max **single-term nesting depth** (`> max_term_depth` → `term_too_deep`,
    /// issue #253). Bounds the depth of every term the trusted path traverses
    /// recursively (node conclusions, the claim, and every cited clause's head/body/
    /// subst terms), so a pathologically deep term cannot overflow the native stack.
    /// Distinct from `max_depth` (DAG/premise-chain depth). Default
    /// [`MAX_TERM_DEPTH_DEFAULT`](crate::term::MAX_TERM_DEPTH_DEFAULT).
    pub max_term_depth: usize,
    // ---- closed-model certificate budgets (ADR 0007) ----
    // Each bounds one dimension of a cited `ClosedModelCert`. Validated **before**
    // any scan (against the cert's `limits_decl` AND its actual sizes), so an
    // oversized or lying certificate is refused without doing its work.
    /// Max serialized certificate size, in bytes (`> max_cert_bytes` → reject).
    pub max_cert_bytes: usize,
    /// Max total sealed facts across a certificate's extensions.
    pub max_cert_facts: usize,
    /// Max total domain values across a certificate's domains.
    pub max_domain_values: usize,
    /// Max number of support edges in a certificate.
    pub max_support_edges: usize,
    /// Max number of rule groundings the closure join may emit (one per body-true tuple
    /// of a sealed-scope clause, #1829); tripped incrementally during the scan.
    pub max_rule_groundings: usize,
    /// Max number of join steps the closure join may perform (one per candidate examined
    /// at one body literal, #1829); tripped incrementally during the scan.
    pub max_join_steps: usize,
    // ---- the term identity (#2226), INERT since #3022 ----
    /// INERT (#3022): `check` ignores it and the check-profile digest does not fold it. Slated for
    /// deletion in #3022's step 5 (ADR 0035 D1); see [`TermIdentity`].
    pub term_identity: TermIdentity,
}

impl Default for CheckLimits {
    fn default() -> Self {
        // Mirrors arche-core's MAX_NODES=100_000; the depth cap is logos's addition.
        // The cert budgets are finite, generous defaults (a cert larger than these is
        // a verification-cost DoS, refused before any scan).
        CheckLimits {
            max_nodes: 100_000,
            max_depth: 4096,
            max_term_depth: crate::term::MAX_TERM_DEPTH_DEFAULT,
            max_cert_bytes: 16 * 1024 * 1024,
            max_cert_facts: 1_000_000,
            max_domain_values: 1_000_000,
            max_support_edges: 1_000_000,
            max_rule_groundings: 10_000_000,
            max_join_steps: 100_000_000,
            term_identity: TermIdentity::ReifyLists,
        }
    }
}

/// A native proof budget outside the protocol index domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckLimitError {
    /// The offending field in the checker configuration.
    pub field: &'static str,
    /// The count supplied by the caller.
    pub count: u64,
}

impl std::fmt::Display for CheckLimitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "check limits: {}={} exceeds {}",
            self.field,
            self.count,
            crate::derivation_wire::INDEX_MAX
        )
    }
}

impl std::error::Error for CheckLimitError {}

/// A proof count in the portable index domain. The protocol domain is
/// independent of the executing host's word size.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofBudgetCount(u64);

impl ProofBudgetCount {
    /// Validate a count and identify the caller's field on refusal.
    pub const fn new(field: &'static str, count: u64) -> Result<Self, CheckLimitError> {
        if count > crate::derivation_wire::INDEX_MAX {
            return Err(CheckLimitError { field, count });
        }
        Ok(Self(count))
    }

    /// The exact portable value, including on 32-bit hosts.
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl From<u32> for ProofBudgetCount {
    fn from(count: u32) -> Self {
        Self(u64::from(count))
    }
}

impl CheckLimits {
    /// Validate the caller's counts before reading evidence or consulting an extension.
    pub fn validate(&self) -> Result<(), CheckLimitError> {
        for (field, count) in self.budgets() {
            ProofBudgetCount::new(field, count as u64)?;
        }
        Ok(())
    }

    /// Every budget a caller can raise, by its field name, in declaration order (#2733, R3). The
    /// names are the keys a vector case's `limits` object uses. `term_identity` is not a budget and
    /// is not listed. Read from [`budgets_mut`](Self::budgets_mut), the one place the struct is
    /// destructured, so every reader of the checker's budgets takes the list from one site.
    pub fn budgets(&self) -> [(&'static str, usize); 9] {
        let mut copy = *self;
        copy.budgets_mut().map(|(name, value)| (name, *value))
    }

    /// Every budget, by its field name, to set in place. The struct is destructured with no `..`,
    /// so a new field does not compile until it is placed here.
    pub fn budgets_mut(&mut self) -> [(&'static str, &mut usize); 9] {
        let CheckLimits {
            max_nodes,
            max_depth,
            max_term_depth,
            max_cert_bytes,
            max_cert_facts,
            max_domain_values,
            max_support_edges,
            max_rule_groundings,
            max_join_steps,
            term_identity: _,
        } = self;
        [
            ("max_nodes", max_nodes),
            ("max_depth", max_depth),
            ("max_term_depth", max_term_depth),
            ("max_cert_bytes", max_cert_bytes),
            ("max_cert_facts", max_cert_facts),
            ("max_domain_values", max_domain_values),
            ("max_support_edges", max_support_edges),
            ("max_rule_groundings", max_rule_groundings),
            ("max_join_steps", max_join_steps),
        ]
    }
}

/// The bound extension points + config + limits `check` verifies against (§4).
/// `theory` is config-pinned (its config is held inside the value, not generic
/// over the context `C` — see [`Theory`]). `leaves`/`admit` are generic over `C`.
pub struct CheckProfile<C> {
    pub theory: Box<dyn Theory>,
    pub leaves: Box<dyn LeafVerifier<C>>,
    pub admit: Box<dyn RuleAdmissibility<C>>,
    pub limits: CheckLimits,
}

/// One bound-component slot of a [`CheckProfile`] — the three slots a profile digest folds
/// a component binding for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProfileSlot {
    /// The profile's [`Theory`].
    Theory,
    /// The profile's [`LeafVerifier`].
    Leaves,
    /// The profile's [`RuleAdmissibility`].
    Admit,
}

impl ProfileSlot {
    /// The slot's stable name — the identifier the shared vector and every core agree on.
    pub fn name(self) -> &'static str {
        match self {
            ProfileSlot::Theory => "theory",
            ProfileSlot::Leaves => "leaves",
            ProfileSlot::Admit => "admit",
        }
    }
}

/// Which of a live profile's bound components read as [`ComponentIdentity::unidentified`] —
/// the unidentified-component advisory ([#708](https://github.com/Bitspark/logos/issues/708)
/// leg (a)).
///
/// `identity()` is an additive defaulted method returning `unidentified()`, so a component
/// that never overrides it contributes a **constant** to the profile digest. Two different
/// `LeafVerifier`s — one strict, one permissive — both on the default produce the **same**
/// digest. For that slot the digest discharges *nothing*, while still being a computed
/// 32-byte value that reads as evidence.
///
/// **This lives in the contract tier deliberately** ([#815](https://github.com/Bitspark/logos/issues/815)).
/// It reads only contract types — a [`CheckProfile`] and [`ComponentIdentity`] — and touches
/// nothing the kernel owns. It was originally written beside the kernel's digest derivation,
/// which put it out of reach of any consumer binding `logos-contract` alone: `contract →
/// kernel` is an upward edge on the ADR 0004 tier stack, so a re-export was impossible and
/// those consumers could not self-measure at all. Placement follows what a function reads,
/// not what it was written next to.
///
/// A consumer that pins a digest and freezes law against it should treat a non-empty result
/// as: *the frozen digest says nothing about this slot.* It does **not** mean the profile is
/// wrong — an anonymous component is legal, and remains so.
pub fn unidentified_profile_slots<C>(profile: &CheckProfile<C>) -> Vec<ProfileSlot> {
    unidentified_profile_slots_allowing(profile, &[])
}

/// The same report, minus the slots the caller has **explicitly declared** it accepts as
/// anonymous — [ADR 0026](../../../../docs/architecture/decisions/0026-unidentified-component-refusal-gating.md)
/// gate **G4**, the deliberate escape.
///
/// Those slots are omitted; every other anonymous slot is still named, in the unchanged fold
/// order `theory ‖ leaves ‖ admit`.
///
/// **Declared, never defaulted.** An empty allowance is the default —
/// [`unidentified_profile_slots`] *is* this function with `&[]` — and allowing every slot
/// requires naming all three. There is deliberately no "allow all" shorthand: the value of an
/// escape is the legible trace it leaves at the call site.
///
/// **It does not touch the digest.** Like the report it filters, this reads identities and
/// participates in no fold. Allowing a slot changes what you are *told*, never what is
/// *derived*.
pub fn unidentified_profile_slots_allowing<C>(
    profile: &CheckProfile<C>,
    allow_unidentified: &[ProfileSlot],
) -> Vec<ProfileSlot> {
    // Fold order is identity-bearing: theory ‖ leaves ‖ admit, unchanged by the allowance.
    [
        (
            ProfileSlot::Theory,
            profile.theory.identity().is_unidentified(),
        ),
        (
            ProfileSlot::Leaves,
            profile.leaves.identity().is_unidentified(),
        ),
        (
            ProfileSlot::Admit,
            profile.admit.identity().is_unidentified(),
        ),
    ]
    .into_iter()
    .filter(|(slot, anonymous)| *anonymous && !allow_unidentified.contains(slot))
    .map(|(slot, _)| slot)
    .collect()
}

/// True iff every bound component of `profile` attests a real identity — i.e.
/// [`unidentified_profile_slots`] is empty, so the derived digest distinguishes all three
/// slots.
pub fn profile_is_fully_identified<C>(profile: &CheckProfile<C>) -> bool {
    unidentified_profile_slots(profile).is_empty()
}

/// The four pins a closed-model certificate is sealed against (ADR 0007). A
/// `Neg`-bearing derivation's certificates are valid only for the program / profile
/// / context / theory-config they were sealed against; [`check_with_cert_context`]
/// compares a cert's pins against this context.
///
/// **Additive (ADR 0007).** A plain [`check`] supplies a *zero* context; it is
/// **never consulted** when `closed_world` is empty, so positive `check` behavior —
/// and its bytes/outcomes — are byte-identical to the pre-amendment checker. A
/// consumer that uses negation derives this context from the *live* program/profile
/// it actually ran (the same provenance the kernel uses for the check-profile
/// digest, see [`crate::spi::ComponentIdentity`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertContext {
    pub program_hash: Hash,
    pub profile_hash: Hash,
    pub ctx_hash: Hash,
    pub theory_config_hash: Hash,
    /// **ADR 0029 D10.** The decomposition the caller ran under, as an opaque 32-byte pin, or
    /// `None` for an ordinary whole-program run (every pre-D10 caller, and the zero context).
    ///
    /// This is the CALLER's half of the slice seal: a cert whose
    /// [`decomposition_witness`](crate::ClosedModelCert::decomposition_witness) is `Some` is
    /// admitted only when this field carries the same pin. The contract tier never interprets it
    /// — see the field on `ClosedModelCert` for why it cannot.
    pub decomposition_witness: Option<Hash>,
}

impl CertContext {
    /// An explicit context over the four pins.
    pub fn new(
        program_hash: Hash,
        profile_hash: Hash,
        ctx_hash: Hash,
        theory_config_hash: Hash,
    ) -> Self {
        CertContext {
            program_hash,
            profile_hash,
            ctx_hash,
            theory_config_hash,
            decomposition_witness: None,
        }
    }

    /// This context, bound to the decomposition `witness` authorized (ADR 0029 D10).
    ///
    /// Additive and opt-in: a caller that does not decompose never calls it, and its context is
    /// byte-identical to the pre-D10 one. A caller that DOES decompose must set this, or every
    /// slice-sealed cert its components mint is refused `cert_context_mismatch` — which is the
    /// pre-D10 behaviour and the safe direction.
    pub fn with_decomposition(mut self, witness: Hash) -> Self {
        self.decomposition_witness = Some(witness);
        self
    }

    /// The all-zero context. Supplied by the plain [`check`] wrapper and **never
    /// consulted** for an all-positive (`closed_world`-empty) derivation; for a
    /// certifying check it is the *unbound* sentinel (see [`CertContext::is_unbound`]).
    pub fn zero() -> Self {
        CertContext {
            program_hash: [0u8; 32],
            profile_hash: [0u8; 32],
            ctx_hash: [0u8; 32],
            theory_config_hash: [0u8; 32],
            // The unbound sentinel decomposes nothing: `is_unbound` reads the four PINS, and a
            // slice-sealed cert under an unbound context is already hard-rejected
            // `cert_context_unbound` before D10's comparison is reached.
            decomposition_witness: None,
        }
    }

    /// `true` iff every pin is all-zero — the *unbound* sentinel (ADR 0007 §3.1). A
    /// certifying check (`closed_world` non-empty) under an unbound context is hard-
    /// rejected `cert_context_unbound`; a real consumer derives a non-zero context
    /// from the live program/profile.
    pub fn is_unbound(&self) -> bool {
        self.program_hash == [0u8; 32]
            && self.profile_hash == [0u8; 32]
            && self.ctx_hash == [0u8; 32]
            && self.theory_config_hash == [0u8; 32]
    }
}

/// Verify a derivation (§4). Total, no search.
///
/// Order of obligations (normative §4): empty / node-cap / root-range up front
/// (the node cap **before any delegation**); then a single forward pass where each
/// node is validated *structurally* and only **then** delegated to its extension
/// point; finally the root must conclude `claim`.
///
/// **Positive-identical (ADR 0007).** This is a thin wrapper over
/// [`check_with_cert_context`] supplying a *zero* [`CertContext`]. For an
/// all-positive derivation (`deriv.closed_world` empty) the context is **never
/// consulted**, so an existing positive check behaves byte-for-byte as before.
///
/// **Negation requires a bound context.** A zero context is the *unbound* sentinel,
/// never a credential: if `deriv.closed_world` is non-empty (a certifying check),
/// this wrapper **hard-rejects `cert_context_unbound`** — a certificate must be
/// verified against a context DERIVED from the live program/profile the consumer
/// actually ran ([`check_with_cert_context`]), not against an all-zero placeholder
/// that any all-zero-pinned cert would trivially satisfy.
/// # Example — a complete, runnable check
///
/// Everything a consumer must supply, in one place: a [`Program`], the `claim`, a
/// [`Derivation`] concluding it, a verification context `C`, and a [`CheckProfile`]
/// (theory + leaves + admit + limits). The two `impl`s are not ceremony — [`Theory`]
/// and [`LeafVerifier`] are the extension points §4 delegates to, so a consumer must
/// bind them even to check a single positive rule. There is no shorter honest form,
/// which is why this example exists (logos#1027).
///
/// ```
/// use logos_contract::{
///     check, AlwaysAdmit, CheckLimits, CheckProfile, Clause, ClauseId, Derivation, Evidence,
///     Goal, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, Outcome,
///     PredicateSet, Premise, Subst, Symbol, Term, Theory, TheoryOutcome,
/// };
/// use ontos_core::Value;
/// use std::collections::BTreeMap;
///
/// // 1. The two extension points. This program uses no builtins, so the theory owns
/// //    nothing; `grant` is the one extensional (leaf) predicate.
/// struct NoTheory;
/// impl Theory for NoTheory {
///     fn owns(&self, _pred: &Symbol) -> bool { false }
///     fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome { TheoryOutcome::NotMine }
///     // Copying is a declared capability (#2722): `check` never copies, so this one declines.
///     logos_contract::cannot_copy!(Theory, "an example theory; check never copies it");
/// }
///
/// struct Leaves(PredicateSet);
/// impl LeafVerifier<()> for Leaves {
///     fn extensional(&self) -> &PredicateSet { &self.0 }
///     fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
///         LeafOutcome::Admit // a real consumer checks its own evidence here
///     }
/// }
///
/// // 2. The program: `permit(S) :- grant(S).`
/// let program = MapProgram::new().with(
///     "permit_rule",
///     Clause::new(
///         Goal::new("permit", [Term::var("S")]),
///         [Goal::new("grant", [Term::var("S")])],
///     ),
/// );
///
/// // 3. The derivation: a `grant(alice)` leaf, then the rule concluding `permit(alice)`.
/// //    `premises` cites the leaf BY INDEX, and the root index is the last argument.
/// let alice = Value::atom(b"alice".to_vec());
/// let grant = GroundLiteral::new("grant", [alice.clone()]);
/// let permit = GroundLiteral::new("permit", [alice]);
/// let mut subst: Subst = BTreeMap::new();
/// subst.insert("S".into(), Term::atom(b"alice".to_vec()));
///
/// let deriv = Derivation::new(
///     vec![
///         Node::Leaf { conclusion: grant, evidence: Evidence::none() },
///         Node::Rule {
///             conclusion: permit.clone(),
///             clause: ClauseId::new("permit_rule"),
///             subst,
///             premises: vec![Premise::pos(0)],
///             meta: NodeMeta::none(),
///         },
///     ],
///     1, // root = the rule node
/// );
///
/// let profile = CheckProfile {
///     theory: Box::new(NoTheory),
///     leaves: Box::new(Leaves(PredicateSet::from_iter(["grant"]))),
///     admit: Box::new(AlwaysAdmit),
///     limits: CheckLimits::default(),
/// };
///
/// // 4. Check it. `()` is the verification context this profile is generic over.
/// assert!(check(&program, &permit, &deriv, &(), &profile).is_accept());
///
/// // And the other direction: the root must conclude the CLAIM. Ask the same
/// // derivation to justify a different literal and it is rejected, not accepted.
/// let other = GroundLiteral::new("permit", [Value::atom(b"bob".to_vec())]);
/// assert!(!check(&program, &other, &deriv, &(), &profile).is_accept());
/// ```
pub fn check<C>(
    program: &dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    ctx: &C,
    profile: &CheckProfile<C>,
) -> Outcome {
    check_with_cert_context(program, claim, deriv, ctx, profile, &CertContext::zero())
}

/// Verify a closed-model certificate CHAIN on its own, with no derivation citing it: the
/// completeness gate's certificate check (#2313, design 0008 §1.4.3). Each cert, at its place in
/// the chain, passes exactly the verification a cert cited by a `Neg` premise passes in
/// [`check_with_cert_context`]: the same term-depth cap on its deep data, the same
/// context-unbound gate, and the same `verify_cert`, unchanged. So no verdict of that function
/// moves.
///
/// The first invalid cert rejects, with its own code and a detail prefixed by its index. An EMPTY
/// chain rejects as `cert_out_of_range`, because it has no cert to seal anything. A vacuous accept
/// would certify a completeness claim that nothing backs.
pub fn check_closed_model_chain<C>(
    program: &dyn Program,
    certs: &[crate::ClosedModelCert],
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_context: &CertContext,
) -> Outcome {
    if let Err(error) = profile.limits.validate() {
        return Outcome::reject(RejectionCode::InvalidCheckLimits, error.to_string());
    }
    if certs.is_empty() {
        return Outcome::reject(
            RejectionCode::CertOutOfRange,
            "empty certificate chain: no closed-model certificate to verify",
        );
    }
    for (own, cert) in certs.iter().enumerate() {
        if let Err(what) = cert_depths_within(cert, profile.limits.max_term_depth) {
            return Outcome::reject(
                RejectionCode::TermTooDeep,
                format!(
                    "chain cert {own}: {what} nests deeper than max_term_depth {}",
                    profile.limits.max_term_depth
                ),
            );
        }
    }
    if cert_context.is_unbound() {
        return Outcome::reject(
            RejectionCode::CertContextUnbound,
            "certifying check supplied an all-zero (unbound) cert context",
        );
    }
    // STACKED certificates (#2258 (a)): the chain is the world, verified in ascending scope level
    // exactly as a derivation's closed world is, so a cert that reads a lower cert's seal does so
    // only once that cert's status is final. The first invalid cert in that order rejects.
    let mut status: Vec<Option<CertStatus>> = vec![None; certs.len()];
    let source = WorldProgram::new(program);
    for own in cert_stack::verification_order(certs) {
        let place = CertPlace {
            own,
            world_len: certs.len(),
        };
        let verdict = verify_cert(
            &certs[own],
            place,
            certs,
            &status,
            &source,
            profile,
            ctx,
            cert_context,
            &profile.limits,
        );
        if let CertStatus::Invalid(code, detail) = &verdict {
            return Outcome::reject(*code, format!("chain cert {own}: {detail}"));
        }
        status[own] = Some(verdict);
    }
    Outcome::Accept
}

/// Verify a derivation that may carry closed-model certificates (ADR 0007). Total,
/// no search; the cert obligations are bounded deterministic verification over the
/// supplied finite tables/domains, every loop pre-bounded by a [`CheckLimits`] cert
/// budget validated up front.
///
/// `cert_context` pins the program/profile/context/theory configuration the cited
/// certificates must have been sealed against. It is consulted **only** when a cert
/// is actually verified (i.e. only for a `Neg`-bearing derivation).
pub fn check_with_cert_context<C>(
    program: &dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_context: &CertContext,
) -> Outcome {
    if let Some(reject) = derivation_prechecks(program, claim, deriv, profile) {
        return reject;
    }
    let cert_status = verify_world(&deriv.closed_world, program, profile, ctx, cert_context);
    check_nodes(program, claim, deriv, ctx, profile, &cert_status)
}

/// [`check_with_cert_context`], with the derivation's closed world verified through `memo` (#2565
/// term 1, `seat:caa`'s ruling on #2565): a run that checks many derivations citing the SAME
/// certificates verifies them once, not once per derivation.
///
/// The verdict is exactly [`check_with_cert_context`]'s. Only step 3a, the per-certificate
/// verification, can be served from the memo, and only when everything it depends on is the same
/// as when the memo was filled (see [`WorldMemo`]). The node cap, root range, term-depth cap, the
/// forward pass over the derivation's own nodes and every premise's own checks run on every call.
/// `memo` is opaque: it holds statuses only the checker computed, so a caller can present a memo
/// but never a verdict.
pub fn check_with_cert_memo<'a, C>(
    program: &'a dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    ctx: &'a C,
    profile: &'a CheckProfile<C>,
    cert_context: &CertContext,
    memo: &mut WorldMemo<'a, C>,
) -> Outcome {
    if let Some(reject) = derivation_prechecks(program, claim, deriv, profile) {
        return reject;
    }
    let cert_status = memo.statuses(program, profile, ctx, cert_context, &deriv.closed_world);
    check_nodes(program, claim, deriv, ctx, profile, cert_status)
}

/// Steps 1 to 3b of [`check_with_cert_context`]: the checks that run before any certificate or
/// node is inspected. `Some` is the rejection.
fn derivation_prechecks<C>(
    program: &dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    profile: &CheckProfile<C>,
) -> Option<Outcome> {
    if let Err(error) = profile.limits.validate() {
        return Some(Outcome::reject(
            RejectionCode::InvalidCheckLimits,
            error.to_string(),
        ));
    }
    // 1. non-empty.
    if deriv.nodes.is_empty() {
        return Some(Outcome::reject(
            RejectionCode::EmptyDerivation,
            "derivation has no nodes",
        ));
    }
    // 2. node cap — BEFORE any delegation, strict `>` (§4.3). An oversized untrusted
    //    proof is refused without inspecting (delegating) a single node.
    if deriv.nodes.len() > profile.limits.max_nodes {
        return Some(Outcome::reject(
            RejectionCode::TooManyNodes,
            format!(
                "{} nodes exceeds max_nodes {}",
                deriv.nodes.len(),
                profile.limits.max_nodes
            ),
        ));
    }
    // 3. root in range: the root is a protocol index, an offset only if it names a node (#2735).
    if deriv.root_offset().is_none() {
        return Some(Outcome::reject(
            RejectionCode::RootOutOfRange,
            format!(
                "root {} out of range (len {})",
                deriv.root,
                deriv.nodes.len()
            ),
        ));
    }
    // 3b. TERM-NESTING DEPTH CAP (issue #253) — BEFORE any recursive term traversal
    //     (cert verification in 3a, the forward pass in 4, the root `eq` in 5). A
    //     single term can nest arbitrarily deep within one node, which neither the
    //     node cap nor the DAG-depth cap bounds; a pathologically deep term would
    //     overflow the native stack in `erase_ground`/`substitute`/structural `eq`/
    //     the account `quote`/`Drop`. The measurement is iterative with an early
    //     cutoff (`Term::depth_le` / `value_depth_le`), so checking the depth of a
    //     deep term does not itself overflow. Over → `term_too_deep` (graceful
    //     rejection, never a crash).
    if let reject @ Outcome::Reject { .. } =
        check_term_depths(program, claim, deriv, &profile.limits)
    {
        return Some(reject);
    }
    None
}

/// Step 3a of [`check_with_cert_context`]: every certificate of `world` verified, into the status
/// vector the forward pass reads. A pure function of its arguments, which is what lets
/// [`WorldMemo`] serve it again for an equal world under the same inputs.
fn verify_world<C>(
    world: &[crate::ClosedModelCert],
    program: &dyn Program,
    profile: &CheckProfile<C>,
    ctx: &C,
    cert_context: &CertContext,
) -> Vec<CertStatus> {
    // 3a. verify every cited certificate ONCE, up front, memoized into a parallel
    //     `Vec<CertStatus>`. A `Neg` premise reuses the cached result. For an
    //     all-positive derivation `closed_world` is empty, so this is a no-op and the
    //     zero `cert_context` is never consulted — positive behavior is byte-identical.
    //
    //     CONTEXT-UNBOUND GATE (ADR 0007 §3.1): a certifying check needs a context
    //     DERIVED from the live program/profile. An all-zero context is the *unbound*
    //     sentinel — if any cert is cited under it, every cert is invalid with
    //     `cert_context_unbound` (a zero context must never *satisfy* a cert's pins).
    //
    //     STACKED certificates (#2258 (a)): certs are verified in ascending scope level, so a
    //     cert that reads a predicate from a strictly lower cert does so only once that cert's
    //     status is final (validity precedes citation).
    let context_unbound = !world.is_empty() && cert_context.is_unbound();
    let mut status: Vec<Option<CertStatus>> = vec![None; world.len()];
    let source = WorldProgram::new(program);
    for own in cert_stack::verification_order(world) {
        let verdict = if context_unbound {
            CertStatus::Invalid(
                RejectionCode::CertContextUnbound,
                "certifying check supplied an all-zero (unbound) cert context".into(),
            )
        } else {
            let place = CertPlace {
                own,
                world_len: world.len(),
            };
            verify_cert(
                &world[own],
                place,
                world,
                &status,
                &source,
                profile,
                ctx,
                cert_context,
                &profile.limits,
            )
        };
        status[own] = Some(verdict);
    }
    // The order covers every index, so every status is set; a gap would be a checker defect,
    // refused rather than read as Valid.
    status
        .into_iter()
        .map(|s| {
            s.unwrap_or_else(|| {
                CertStatus::Invalid(
                    RejectionCode::CertScopeIncomplete,
                    "certificate was never verified".into(),
                )
            })
        })
        .collect()
}

/// Steps 4 and 5 of [`check_with_cert_context`]: the forward pass over the derivation's nodes,
/// reading the certificates' statuses, then the root against the claim.
fn check_nodes<C>(
    program: &dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_status: &[CertStatus],
) -> Outcome {
    // 4. one forward pass: validate each node (structural, then delegate).
    let mut depth = vec![0usize; deriv.nodes.len()];
    for (i, node) in deriv.nodes.iter().enumerate() {
        match check_node(
            i,
            node,
            program,
            deriv,
            ctx,
            profile,
            cert_status,
            &mut depth,
        ) {
            Outcome::Accept => {}
            reject => return reject,
        }
    }

    // 5. root concludes the claim, structurally (#3022): the certified claim is exactly the
    //    fact the root proves, never another spelling of it.
    if deriv.nodes[deriv
        .root_offset()
        .expect("step 3 rejects a root that names no node")]
    .conclusion()
        != claim
    {
        return Outcome::reject(
            RejectionCode::RootConclusionMismatch,
            "root conclusion does not equal claim",
        );
    }

    Outcome::Accept
}

/// A positive premise's node offset, once step (b) has checked it names a node below the citing
/// one: every use after (b) is inside the same node's pass, so the index is in range (#2735).
fn cited_offset(p: u64, below: usize) -> usize {
    index_offset(p, below).expect("step (b) rejects a positive premise that names no earlier node")
}

#[allow(clippy::too_many_arguments)]
fn check_node<C>(
    i: usize,
    node: &Node,
    program: &dyn Program,
    deriv: &Derivation,
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_status: &[CertStatus],
    depth: &mut [usize],
) -> Outcome {
    match node {
        Node::Rule {
            conclusion,
            clause: clause_id,
            subst,
            premises,
            meta,
        } => {
            // (a) cited clause exists.
            let Some(clause) = program.clause(clause_id) else {
                return Outcome::reject(
                    RejectionCode::UnknownClause,
                    format!("no clause for id {:?}", clause_id.as_str()),
                );
            };
            // (b) positive premise indices reference strictly earlier nodes (acyclic
            //     DAG). A `Neg` premise carries no node index — it is a checked
            //     side-condition against a certificate, validated in (f).
            for premise in premises {
                if let Premise::Pos { node: p } = premise {
                    if index_offset(*p, i).is_none() {
                        return Outcome::reject(
                            RejectionCode::BadDependencyOrder,
                            format!("premise {p} not < node {i}"),
                        );
                    }
                }
            }
            // (c) depth (positive premises are < i, so already computed); cap →
            //     too_deep. A `Neg`/`Count` premise contributes no depth (no node
            //     chain — both are checked side-conditions against a certificate).
            //     saturating_add keeps this total even under a pathological
            //     consumer-set max_depth near usize::MAX (never attacker-reachable,
            //     since the node cap bounds chain length first) — defensive only.
            depth[i] = premises
                .iter()
                .filter_map(|premise| match premise {
                    Premise::Pos { node: p } => Some(depth[cited_offset(*p, i)]),
                    Premise::Neg { .. } | Premise::Count { .. } => None,
                })
                .max()
                .unwrap_or(0)
                .saturating_add(1);
            if depth[i] > profile.limits.max_depth {
                return Outcome::reject(
                    RejectionCode::TooDeep,
                    format!(
                        "depth {} exceeds max_depth {}",
                        depth[i], profile.limits.max_depth
                    ),
                );
            }
            // (d) subst applied to the head is ground and STRUCTURALLY equals the conclusion
            //     (#3022: a conclusion is never a relabeling of the instantiated head). The fast
            //     path (#2177 A) can only prove equality; otherwise the allocating path decides.
            if !proved_equal_fast(&clause.head, subst, conclusion) {
                let Some(head) = clause.head.substitute(subst).as_ground() else {
                    return Outcome::reject(
                        RejectionCode::InstantiationMismatch,
                        "clause head not ground under subst",
                    );
                };
                if head != *conclusion {
                    return Outcome::reject(
                        RejectionCode::InstantiationMismatch,
                        "instantiated head != conclusion",
                    );
                }
            }
            // (e) one premise per body literal.
            if premises.len() != clause.body.len() {
                return Outcome::reject(
                    RejectionCode::InstantiationMismatch,
                    format!(
                        "premise count {} != body length {}",
                        premises.len(),
                        clause.body.len()
                    ),
                );
            }
            // (f) premise k matches body literal k under subst, *with polarity*:
            //     - Pos body lit   ↔ Pos premise: the cited node's conclusion equals
            //       the grounded body literal.
            //     - Neg body lit   ↔ Neg premise: the grounded body literal equals the
            //       premise's `atom`, which is then discharged as ABSENT from the
            //       cited (verified) certificate.
            //     - Count body lit ↔ Count premise (ADR 0023): the grounded count
            //       literal's pred/filter/project/k equal the premise's, which is then
            //       discharged by recomputing the count over the cited (verified) cert.
            //     A polarity/kind mismatch in any direction is an `instantiation_mismatch`.
            //
            //     Every comparison here is STRUCTURAL (#3022). With (d) structural too, every
            //     node's conclusion is its exact fact, so the exact cone #2256 kept for
            //     spelling-sensitive clauses now holds for every clause by construction.
            for (k, body_lit) in clause.body.iter().enumerate() {
                match (&premises[k], body_lit) {
                    (Premise::Pos { node: p }, BodyLit::Pos(lit)) => {
                        // The cited node's conclusion must be EXACTLY the grounded body literal,
                        // for every cited node kind (#3022; #2232 already required it of a
                        // Builtin, whose theory decides on its own spelling). Fast path first
                        // (#2177 A); the allocating path alone rejects.
                        let premise = deriv.nodes[cited_offset(*p, i)].conclusion();
                        if !proved_equal_fast(lit, subst, premise) {
                            let Some(expected) = lit.substitute(subst).as_ground() else {
                                return Outcome::reject(
                                    RejectionCode::InstantiationMismatch,
                                    format!("body literal {k} not ground under subst"),
                                );
                            };
                            if premise != &expected {
                                return Outcome::reject(
                                    RejectionCode::InstantiationMismatch,
                                    format!(
                                        "premise {k} conclusion != body literal {k} under subst"
                                    ),
                                );
                            }
                        }
                    }
                    (
                        Premise::Neg {
                            atom,
                            cert,
                            nonmember,
                        },
                        BodyLit::Neg(lit),
                    ) => {
                        let Some(expected) = lit.substitute(subst).as_ground() else {
                            return Outcome::reject(
                                RejectionCode::InstantiationMismatch,
                                format!("body literal {k} not ground under subst"),
                            );
                        };
                        // #2227: the premise's `atom` must EXACTLY equal the grounded negated
                        // body literal. Its absence is then looked up by exact membership in the
                        // sealed table, so a match under account equality would transfer an
                        // absence judged about one spelling to another.
                        if atom != &expected {
                            return Outcome::reject(
                                RejectionCode::InstantiationMismatch,
                                format!("neg premise {k} atom != body literal {k} under subst"),
                            );
                        }
                        match verify_neg_premise(
                            atom,
                            *cert,
                            *nonmember,
                            &conclusion.pred,
                            deriv,
                            cert_status,
                        ) {
                            Outcome::Accept => {}
                            reject => return reject,
                        }
                    }
                    (
                        Premise::Count {
                            pred,
                            filter,
                            project,
                            k: k_claim,
                            cert,
                        },
                        BodyLit::Count(_),
                    ) => {
                        // The grounded count body literal must agree with the premise's
                        // pred/filter/project/k (positional + value agreement) before the
                        // count is re-derived against the cited (verified) cert.
                        let Some(count_lit) = body_lit.substitute(subst).as_count().map(|c| {
                            // ground the filter terms + the count slot.
                            (
                                c.pred.clone(),
                                c.filter
                                    .iter()
                                    .map(|(pos, t)| t.erase_ground().map(|v| (*pos, v)))
                                    .collect::<Option<Vec<_>>>(),
                                c.project,
                                c.count.erase_ground(),
                            )
                        }) else {
                            return Outcome::reject(
                                RejectionCode::InstantiationMismatch,
                                format!("count body literal {k} is not a Count under subst"),
                            );
                        };
                        let (g_pred, g_filter, g_project, g_count) = count_lit;
                        let (Some(g_filter), Some(g_count)) = (g_filter, g_count) else {
                            return Outcome::reject(
                                RejectionCode::InstantiationMismatch,
                                format!("count body literal {k} not ground under subst"),
                            );
                        };
                        // Structural, like every site (#3022).
                        if &g_pred != pred
                            || g_filter != *filter
                            || g_project != *project
                            || g_count != *k_claim
                        {
                            return Outcome::reject(
                                RejectionCode::InstantiationMismatch,
                                format!("count premise {k} != body literal {k} under subst"),
                            );
                        }
                        match verify_count_premise(
                            pred,
                            filter,
                            *project,
                            k_claim,
                            *cert,
                            &conclusion.pred,
                            deriv,
                            cert_status,
                        ) {
                            Outcome::Accept => {}
                            reject => return reject,
                        }
                    }
                    (_, _) => {
                        return Outcome::reject(
                            RejectionCode::InstantiationMismatch,
                            format!("premise {k} polarity != body literal {k} polarity"),
                        );
                    }
                }
            }
            // (g) sealing / partition on the head predicate (local checks, §4.2/§4.4):
            //     a clause head must be intensional — not extensional, not theory-owned.
            if profile.leaves.extensional().contains(&conclusion.pred) {
                return Outcome::reject(
                    RejectionCode::SealedViolation,
                    "rule head collides with an extensional predicate",
                );
            }
            if profile.theory.owns(&conclusion.pred) {
                return Outcome::reject(
                    RejectionCode::PredicatePartitionViolation,
                    "rule head predicate is owned by a theory",
                );
            }
            // (h) THEN delegate metadata admissibility (§4 ob.2: structural-then-delegate).
            match profile.admit.admissible(clause, meta, ctx) {
                RuleOutcome::Admit => Outcome::Accept,
                RuleOutcome::Reject { code } => {
                    Outcome::reject(RejectionCode::RuleInadmissible, code)
                }
            }
        }

        Node::Builtin { conclusion } => {
            depth[i] = 1;
            if depth[i] > profile.limits.max_depth {
                return Outcome::reject(RejectionCode::TooDeep, "depth 1 exceeds max_depth");
            }
            let owned = profile.theory.owns(&conclusion.pred);
            // partition: a builtin predicate must be theory-owned, and not also
            // extensional (overlap is a partition violation, §4.4).
            if !owned {
                return Outcome::reject(
                    RejectionCode::PredicatePartitionViolation,
                    "no theory owns the builtin predicate",
                );
            }
            if profile.leaves.extensional().contains(&conclusion.pred) {
                return Outcome::reject(
                    RejectionCode::PredicatePartitionViolation,
                    "builtin predicate is also extensional",
                );
            }
            // #3126: the ground verdict, which can say "not decided". The detail of a false is the
            // theory's own code, read before any conversion into the algebra.
            match profile.theory.decide_ground(conclusion) {
                Completion::Completed(TheoryDecision::Holds) => Outcome::Accept,
                Completion::Completed(TheoryDecision::Fails { code }) => {
                    Outcome::reject(RejectionCode::BuiltinFailed, code)
                }
                Completion::LimitExceeded(never) => match never {},
                // owns() said yes but decide disowns: an inconsistent theory.
                Completion::NotCompleted(cause) if is_disowned(&cause) => Outcome::reject(
                    RejectionCode::PredicatePartitionViolation,
                    "theory owns predicate but returned NotMine",
                ),
                // A stop is refused by name, never read as a decision (#3126).
                Completion::NotCompleted(cause) => {
                    let (code, detail) = builtin_not_decided(cause);
                    Outcome::reject(code, detail)
                }
            }
        }

        Node::Leaf {
            conclusion,
            evidence,
        } => {
            depth[i] = 1;
            if depth[i] > profile.limits.max_depth {
                return Outcome::reject(RejectionCode::TooDeep, "depth 1 exceeds max_depth");
            }
            let extensional = profile.leaves.extensional().contains(&conclusion.pred);
            let owned = profile.theory.owns(&conclusion.pred);
            // sealing / partition (§4.2/§4.4): a leaf may conclude only an
            // extensional predicate.
            if extensional && owned {
                return Outcome::reject(
                    RejectionCode::PredicatePartitionViolation,
                    "leaf predicate is both extensional and theory-owned",
                );
            }
            if !extensional {
                return if owned {
                    Outcome::reject(
                        RejectionCode::PredicatePartitionViolation,
                        "leaf predicate is owned by a theory, not extensional",
                    )
                } else {
                    // not extensional and not a builtin ⇒ it is intensional: a leaf
                    // concluding an intensional predicate is the sealing error.
                    Outcome::reject(
                        RejectionCode::SealedViolation,
                        "leaf concludes a non-extensional (intensional) predicate",
                    )
                };
            }
            match profile.leaves.verify(conclusion, evidence, ctx) {
                LeafOutcome::Admit => Outcome::Accept,
                LeafOutcome::Reject { code } => Outcome::reject(RejectionCode::LeafRejected, code),
            }
        }
    }
}

/// The certificate half of [`check_term_depths`] (its block (c)): every deep datum of one
/// closed-model certificate that the cert path traverses recursively is within `max`. `Err` names
/// the first datum over the bound, in the same words the derivation path reports. Shared with
/// [`check_closed_model_chain`] (#2313), whose certificates are cited by no derivation.
fn cert_depths_within(cert: &crate::ClosedModelCert, max: usize) -> Result<(), &'static str> {
    for table in &cert.extensions {
        for fact in &table.rows {
            if !ground_within(fact, max) {
                return Err("certificate extension row argument");
            }
        }
    }
    for domain in &cert.domains {
        for v in &domain.values {
            if !crate::term::value_depth_le(v, max) {
                return Err("certificate domain value");
            }
        }
    }
    for edge in &cert.supports.0 {
        if !ground_within(&edge.fact, max) {
            return Err("certificate support-edge fact argument");
        }
        for term in edge.subst.values() {
            if !term.depth_le(max) {
                return Err("certificate support-edge subst image");
            }
        }
        for body_ref in &edge.body_refs {
            let atom = match body_ref {
                SupportRef::SameStratum { fact, .. } => fact,
                SupportRef::LowerStratum { atom, .. }
                | SupportRef::Builtin { atom }
                | SupportRef::NegLower { atom, .. } => atom,
                // #2258 L3.3b: a count ref carries no atom; its values are the subst's.
                SupportRef::CountLower { .. } => continue,
            };
            if !ground_within(atom, max) {
                return Err("certificate support-ref atom argument");
            }
        }
    }
    Ok(())
}

/// §4.3 TERM-NESTING DEPTH CAP (issue #253). Validate, **iteratively with an early
/// cutoff**, that no term the trusted path will traverse recursively nests deeper than
/// `limits.max_term_depth`. Covers every term/value reachable on the trusted path:
///
/// - the `claim`'s args (compared by recursive `Value` `eq` against the root, §5);
/// - every node's conclusion args (`Value`) and, for a `Rule` node, its subst image
///   terms (substituted recursively, §4 ob.d/f);
/// - every **cited** clause's head + body literal args (`Term`, substituted/erased);
/// - every cited [`ClosedModelCert`]'s deep data — extension rows, domain values,
///   support-edge facts / subst images / body-ref atoms, and `Neg`-premise atoms —
///   all of which the cert path traverses recursively (`ground_key`/codec encode,
///   `erase_ground`, `domain_containing`).
///
/// Returns [`Outcome::Accept`] when every term is within bound, else a
/// `term_too_deep` rejection. Each `*_depth_le` call is itself non-recursive and cuts
/// off at the bound, so this gate's own cost is bounded by `max_term_depth`, not by
/// the (unbounded) depth of a pathological term.
fn check_term_depths(
    program: &dyn Program,
    claim: &GroundLiteral,
    deriv: &Derivation,
    limits: &CheckLimits,
) -> Outcome {
    let max = limits.max_term_depth;
    let too_deep = |what: &str| {
        Outcome::reject(
            RejectionCode::TermTooDeep,
            format!("{what} nests deeper than max_term_depth {max}"),
        )
    };
    // (a) the claim.
    if !ground_within(claim, max) {
        return too_deep("claim argument");
    }
    // (b) every node conclusion + (for Rule) subst images, and every cited clause.
    //
    // #2177 B: a cited clause is trusted program data, the same at every node that cites it, so
    // it is measured once per id per call. An id is recorded only AFTER a successful lookup and a
    // passing measurement, so an unknown id is still refused by the forward pass exactly as
    // before, and a too-deep clause still rejects at the first node that cites it. Node
    // conclusions and substitution images come from the untrusted derivation and are still
    // measured at every node.
    let mut clauses_within: BTreeSet<&ClauseId> = BTreeSet::new();
    for node in &deriv.nodes {
        if !ground_within(node.conclusion(), max) {
            return too_deep("node conclusion argument");
        }
        if let Node::Rule {
            clause: clause_id,
            subst,
            ..
        } = node
        {
            for term in subst.values() {
                if !term.depth_le(max) {
                    return too_deep("subst image term");
                }
            }
            // The cited clause is traversed (head/body substituted + erased). A
            // missing clause is the structural `unknown_clause` error raised later in
            // the forward pass; here we only depth-check a clause that exists.
            if clauses_within.contains(clause_id) {
                continue;
            }
            if let Some(clause) = program.clause(clause_id) {
                if !goal_within(&clause.head, max) {
                    return too_deep("cited clause head argument");
                }
                for bl in &clause.body {
                    match bl {
                        BodyLit::Pos(l) | BodyLit::Neg(l) => {
                            if !l.args.iter().all(|t| t.depth_le(max)) {
                                return too_deep("cited clause body-literal argument");
                            }
                        }
                        // ADR 0023: a Count body literal carries filter terms + the
                        // count slot term, all of which the trusted path substitutes.
                        BodyLit::Count(c) => {
                            if !c.filter.iter().all(|(_, t)| t.depth_le(max))
                                || !c.count.depth_le(max)
                            {
                                return too_deep("cited clause count-literal argument");
                            }
                        }
                    }
                }
                clauses_within.insert(clause_id);
            }
        }
    }
    // (c) every cited closed-model certificate's deep data (ADR 0007). For an
    //     all-positive derivation `closed_world` is empty, so this is a no-op and the
    //     positive path is byte-identical (it never reaches a `term_too_deep`).
    for cert in &deriv.closed_world {
        if let Err(what) = cert_depths_within(cert, max) {
            return too_deep(what);
        }
    }
    // (d) every `Neg` premise's atom + every `Count` premise's filter/k values
    //     (ground data the cert path traverses recursively).
    for node in &deriv.nodes {
        if let Node::Rule { premises, .. } = node {
            for premise in premises {
                match premise {
                    Premise::Neg { atom, .. } => {
                        if !ground_within(atom, max) {
                            return too_deep("negated premise atom argument");
                        }
                    }
                    Premise::Count { filter, k, .. } => {
                        if !filter
                            .iter()
                            .all(|(_, v)| crate::term::value_depth_le(v, max))
                            || !crate::term::value_depth_le(k, max)
                        {
                            return too_deep("count premise filter/k value");
                        }
                    }
                    Premise::Pos { .. } => {}
                }
            }
        }
    }
    Outcome::Accept
}

/// Every argument of a [`GroundLiteral`] nests within `max` (iterative cutoff).
fn ground_within(lit: &GroundLiteral, max: usize) -> bool {
    lit.args.iter().all(|v| crate::term::value_depth_le(v, max))
}

/// Every argument term of a [`Goal`](crate::literal::Goal) nests within `max`.
fn goal_within(goal: &crate::literal::Goal, max: usize) -> bool {
    goal.args.iter().all(|t| t.depth_le(max))
}

/// The `Builtin` predicates in `deriv` that **no theory bound by this profile owns** — the
/// pre-check capability query ([#1371](https://github.com/Bitspark/logos/issues/1371)).
///
/// Ask this **before** [`check`]. An empty result means this host can decide every builtin the
/// derivation cites; a non-empty one names exactly the predicates it cannot, so a caller knows
/// **which theory to bind** rather than only that something is missing.
///
/// ## Why it exists
///
/// `check` re-decides every `Builtin` node through `profile.theory`. On a host that binds no
/// theory owning the predicate, the rejection is `PredicatePartitionViolation` — a
/// **structural-band** code whose meaning is *this account is malformed*. But the account may be
/// perfectly sound: it is the **verifier** that lacks a capability. A consumer whose CI referee
/// branches on the code then dispatches an investigator at the **producer**, when nothing is
/// wrong anywhere except the binding set of the host doing the re-check.
///
/// This query separates the two **without touching the code space**: capability is answered
/// ahead of time, so a later `predicate_partition_violation` on a Builtin node can be read as
/// what it is.
///
/// ## ⚠ What an empty result does NOT promise
///
/// It does **not** mean `check` will accept. It answers **one** condition — theory ownership.
/// Two other conditions raise the same structural code and are untouched here, correctly so:
/// a builtin predicate that is **also extensional** (a genuine partition overlap), and a theory
/// whose `owns()` says yes while `decide()` returns `NotMine` (an inconsistent theory). Both are
/// real defects that this query is not about, and both still reject.
///
/// So: **empty means no capability refusal will occur, never that the account is valid.** Read
/// as a verifiability oracle it would be a check whose PASS is compatible with the thing still
/// failing — see [the unenforced-guard catalogue](../../../../docs/guides/unenforced-guards.md).
///
/// ## Scope
///
/// Additive and non-breaking: a helper adapter over existing contract types, adding no
/// `RejectionCode` variant and moving no vector. It reads `Node::Builtin` conclusions and
/// `Theory::owns` and nothing else — no `decide()` call, so it is **total and side-effect-free**
/// even against a theory whose `decide` is expensive.
///
/// Order is the derivation node order, deduplicated on first appearance, so the result is
/// deterministic for a given derivation.
pub fn unowned_builtin_predicates<C>(deriv: &Derivation, profile: &CheckProfile<C>) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    for node in &deriv.nodes {
        if let Node::Builtin { conclusion } = node {
            if !profile.theory.owns(&conclusion.pred) && !out.contains(&conclusion.pred) {
                out.push(conclusion.pred.clone());
            }
        }
    }
    out
}

/// `true` when this profile can decide every `Builtin` predicate `deriv` cites — the boolean
/// convenience over [`unowned_builtin_predicates`].
///
/// ⚠ **Same limit as the report it wraps:** `true` means *no capability refusal will occur*, not
/// *`check` will accept*. Prefer the list form when reporting to a human or a log — it names
/// what to bind, and a bare `false` invites exactly the "the account is bad" reading this whole
/// query exists to prevent.
pub fn profile_decides_all_builtins<C>(deriv: &Derivation, profile: &CheckProfile<C>) -> bool {
    unowned_builtin_predicates(deriv, profile).is_empty()
}

/// The `Builtin` conclusions this profile's theory **owns but disowns** — `owns(pred)` is
/// `true` while `decide_ground(conclusion)` reports the disowning fault, which is what a
/// [`TheoryOutcome::NotMine`](crate::spi::TheoryOutcome::NotMine) from `decide` becomes (#3126). A
/// theory that stopped (a work cap) is not listed: it did not disown the atom.
///
/// A non-empty result is a **verifier-side defect**: the bound [`Theory`](crate::spi::Theory)
/// violates the coherence obligation of §5, which requires `decide` to reach a verdict on
/// every atom whose predicate `owns` claims. `check` rejects this with the structural code
/// [`RejectionCode::PredicatePartitionViolation`] — correctly, since the account cannot be
/// verified by this profile — but a consumer reading that code alone is pointed at the
/// **producer** for what is a bug in the host's own theory binding. This query is the
/// attribution the code cannot carry (issue #1378): it names the atoms that expose it.
///
/// ## ⚠ Unlike [`unowned_builtin_predicates`], this one CALLS `decide`
///
/// Ownership is a property of a *predicate*, but incoherence is only observable per *atom*,
/// so the question cannot be answered without deciding. This therefore costs what the
/// corresponding part of `check` costs and is **not** side-effect-free against a theory whose
/// `decide` is expensive or stateful. Its value is **attribution after a rejection**, not
/// avoidance before one — prefer the sibling query when a cheap pre-flight is all you need.
///
/// ## ⛔ An empty result does NOT certify the theory coherent
///
/// It witnesses only that no atom **this derivation cites** exposes the disagreement; a
/// theory incoherent on any other atom returns empty here. That is a PASS compatible with the
/// thing still failing — [form 33](../../../../docs/guides/unenforced-guards.md). Read it as
/// *"this rejection is not that bug"*, never as *"the theory is sound"*.
///
/// ## Scope
///
/// Additive and non-breaking: a helper adapter over existing contract types, adding no
/// `RejectionCode` variant and moving no vector. Order is derivation node order, deduplicated
/// on first appearance, so the result is deterministic for a given derivation. The dedup test
/// precedes the `decide` call, so a repeated offending atom is decided once.
pub fn incoherent_builtin_atoms<C>(
    deriv: &Derivation,
    profile: &CheckProfile<C>,
) -> Vec<GroundLiteral> {
    let mut out: Vec<GroundLiteral> = Vec::new();
    for node in &deriv.nodes {
        if let Node::Builtin { conclusion } = node {
            if profile.theory.owns(&conclusion.pred)
                && !out.contains(conclusion)
                && matches!(
                    profile.theory.decide_ground(conclusion),
                    Completion::NotCompleted(cause) if is_disowned(&cause)
                )
            {
                out.push(conclusion.clone());
            }
        }
    }
    out
}
