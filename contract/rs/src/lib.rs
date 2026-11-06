//! # logos-contract
//!
//! The shared artifact between **search** and **check**:
//!
//! ```text
//!         SEARCH                         CHECK
//!   Program × Goal  ──evaluator──▶  Derivation  ──checker──▶  Accept | Reject
//!        (logos)                    (shared DTO)              (arche, logos, …)
//! ```
//!
//! One artifact — the [`Derivation`] — flows between two directions: an engine
//! *produces* it by searching; a checker *consumes* it by verifying, with no
//! search. This crate is that artifact plus the checker SPI a check-only consumer
//! binds. It depends only on [`ontos`](ontos_core) (the frozen `Atom|Tuple` value
//! model); it contains **no** engine.
//!
//! ## A worked `check()` (#1027)
//!
//! The whole check-side API in one call. Nothing here is hand-rolled: every
//! [`CheckProfile`] slot binds a shipped value, so this is the shortest correct
//! consumer rather than a sketch.
//!
//! ```
//! use logos_contract::{
//!     check, AlwaysAdmit, CheckLimits, CheckProfile, Clause, ClauseId, CompoundTheory,
//!     Derivation, Evidence, Goal, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram,
//!     Node, NodeMeta, PredicateSet, Premise, Subst, Term,
//! };
//! use ontos_core::Value;
//!
//! // The ONE seam a check-only consumer must implement: which predicates are leaves
//! // (extensional), and whether a given leaf's evidence is acceptable.
//! struct FixtureLeaves(PredicateSet);
//! impl LeafVerifier<()> for FixtureLeaves {
//!     fn extensional(&self) -> &PredicateSet { &self.0 }
//!     fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
//!         // This fixture's EDB is trusted. A consumer that must VERIFY evidence
//!         // decides here — that decision is the whole purpose of the seam.
//!         LeafOutcome::Admit
//!     }
//! }
//!
//! // The program a derivation may cite:  permit(S) :- grant(S).
//! let program = MapProgram::new().with(
//!     "permit_rule",
//!     Clause::new(
//!         Goal::new("permit", [Term::var("S")]),
//!         [Goal::new("grant", [Term::var("S")])],
//!     ),
//! );
//!
//! let grant_s1 = GroundLiteral::new("grant", [Value::atom(b"s1".to_vec())]);
//! let permit_s1 = GroundLiteral::new("permit", [Value::atom(b"s1".to_vec())]);
//!
//! // The derivation: node 0 is the leaf `grant(s1)`; node 1 applies the rule to it and
//! // is the ROOT (the trailing `1` is the root index, not a count).
//! let mut subst = Subst::new();
//! subst.insert("S".into(), Term::atom(b"s1".to_vec()));
//! let derivation = Derivation::new(
//!     vec![
//!         Node::Leaf { conclusion: grant_s1, evidence: Evidence::none() },
//!         Node::Rule {
//!             conclusion: permit_s1.clone(),
//!             clause: ClauseId::new("permit_rule"),
//!             subst,
//!             premises: vec![Premise::pos(0)],
//!             meta: NodeMeta::none(),
//!         },
//!     ],
//!     1,
//! );
//!
//! // The profile IS the checker's trust policy — what it decides, what it takes on faith:
//! let profile = CheckProfile {
//!     theory: Box::new(CompoundTheory::new(vec![])), // no builtins in this program
//!     leaves: Box::new(FixtureLeaves(PredicateSet::from_iter(["grant"]))),
//!     admit: Box::new(AlwaysAdmit),                  // no rule-admissibility policy
//!     limits: CheckLimits::default(),
//! };
//!
//! // `check` SEARCHES FOR NOTHING. It verifies the derivation it was handed, against the
//! // program it was handed, under that profile.
//! assert!(check(&program, &permit_s1, &derivation, &(), &profile).is_accept());
//!
//! // Change the claim and the same derivation no longer proves it:
//! let permit_s2 = GroundLiteral::new("permit", [Value::atom(b"s2".to_vec())]);
//! assert!(!check(&program, &permit_s2, &derivation, &(), &profile).is_accept());
//! ```
//!
//! ⚠ `FixtureLeaves` admits every leaf **without verifying it**, which is correct only
//! because the fixture IS the trusted EDB. [`LeafVerifier`] is the one profile slot with no
//! shipped binding, so every consumer writes those six lines today — see #1027 for the
//! decision to ship an identified one, which is a tri-core change because the binding's
//! identity enters `check_profile_digest`.
//!
//! ## Three firmness layers (see `docs/spec/logos-contract.md`)
//!
//! - **[FIRM] — the account** ([`term`], [`literal`], [`program`], [`derivation`],
//!   and the *structural* obligations + rejection band of [`check`]): the
//!   `Rule | Builtin | Leaf` closed-positive proof grammar and structural verdict
//!   taxonomy. The trust artifact (ADR 0001).
//! - **[STABLE v1] — the checker-facing SPI** (`logos-checker-spi v1`):
//!   [`check`](check::check), [`Theory`](spi::Theory),
//!   [`LeafVerifier`](spi::LeafVerifier), [`RuleAdmissibility`](spi::RuleAdmissibility),
//!   [`CheckProfile`](check::CheckProfile), [`CheckLimits`](check::CheckLimits),
//!   [`Outcome`](check::Outcome). Additive-only within v1 (ADR 0003). The standard
//!   checkable [`Theory`](spi::Theory) impls bind here too —
//!   [`ArithmeticTheory`](arithmetic::ArithmeticTheory) over [`intval`] (ADR 0014,
//!   tri-core with `contract/{go,ts}`) — so `contract` also depends on the frozen
//!   `ontos-data` embeddings it reads operands through (amending ADR 0004 D4).
//! - **[PROPOSED] — the engine-facing seam** ([`engine`]): the
//!   search-side scheduler seam (`BottomUpEngine`, `PhysicalOperator`,
//!   `ResourceLimits`, `TruncationReason`) the generic fixpoint loop in
//!   [`logos-core`](https://github.com/Bitspark/logos) (`drive<E>`) binds. Per
//!   ADR 0002 these shapes are proposed, not frozen — the loop depends only on
//!   the *trait*, never on an engine `impl`, so no engine crate is in the graph
//!   (the ADR 0004 V3 layering fix).
//! - **[PROPOSED] — the completion algebra** ([`completion`]): an outcome that keeps
//!   "established false" apart from "did not finish", and the scoped strong-Kleene
//!   `not`/`and`/`or` over it (research 0031 row 15). Additive and unused by
//!   [`Theory`](spi::Theory) until checker SPI v2 (ADR 0036 D8) adopts it.
//!
//! The **dual-conformance law** ties the two directions: every solution an engine
//! emits must have a derivation that `check` accepts.

// The checker is the trust root, so no `match` in it may end in a wildcard over an enum (#3197,
// research 0025 A22): a member added later would take the wildcard's answer without anyone deciding
// it, and here that fails silently in the direction that matters most. Name every member instead.
// Where the question is about ONE member and the other branch is right for every member, a later one
// included, `let … else` or `matches!` states exactly that.
#![deny(clippy::wildcard_enum_match_arm)]

pub mod account;
pub mod aggregate;
pub mod answer_set;
pub mod arithmetic;
pub mod cert;
pub mod cert_wire;
pub mod check;
pub mod completion;
pub mod decval;
pub mod derivation;
pub mod derivation_wire;
pub mod engine;
pub mod fragment;
pub mod intval;
pub mod list_theory;
pub mod literal;
#[doc(hidden)]
pub mod ops;
pub mod prelude;
pub mod program;
pub mod program_serde;
pub mod reify;
pub mod spi;
pub mod term;
pub mod term_theory;
pub mod text;
mod wire_sink;
pub use wire_sink::closed_model_cert_write;

// ---- the account (FIRM) ----
pub use cert_wire::{
    cert_bytes_slack, cert_span_over_budget, cert_wire_spans, cert_wire_spans_at, cert_wire_tag,
    cert_wire_walk, decode_derivation_wire_v1_bounded, BoundedWireError, CertSpan, CertWireError,
    PathStep, DERIVATION_WIRE_V1_CERT_PATH,
};
pub use derivation::{
    index_offset, CertStack, Derivation, Evidence, GroundFilter, Node, NodeMeta, Premise,
};
pub use derivation_wire::{
    cert_encoded_bytes, cert_tables_encoded_bytes, decode_derivation_wire_v1,
    derivation_wire_payload_v1_from_value, derivation_wire_payload_v1_to_value,
    derivation_wire_v1_from_value, derivation_wire_v1_to_value, encode_derivation_wire_v1,
    ground_literal_as_value, ground_literal_from_value_v1, DecodeError, DERIVATION_WIRE_V1_TAG,
};
pub use literal::{escaped_name, Goal, GroundLiteral, Literal, Symbol};
pub use program::{
    BodyLit, Clause, ClauseId, CountLit, MapProgram, PredicateRef, Program, ProjectSpec,
};
pub use reify::{quote, reify};
pub use term::{
    canonicalize_lists, value_depth_le, EraseError, Subst, Term, VarId, MAX_TERM_DEPTH_DEFAULT,
    TERM_RECURSION_BUDGET, VALUE_TOO_DEEP,
};
// ClauseId::canonical (§9) + the account-codec helpers (§2a/§9).
pub use account::{clause_bytes, clause_from_value, clause_value, CLAUSE_PREFIX};
// G4, the completeness gate's set comparison (#3023, research 0028 A16).
pub use answer_set::{check_answer_set, AnswerSetMismatch};
// §10 program (de)serialization — MapProgram ⇄ canonical ground Value (issue #310).
pub use program_serde::{
    program_bytes, program_from_value, program_to_value, reserved_predicate, ProgramSerdeError,
    PROGRAM_SERDE_VERSION, RESERVED_COUNT_SYMBOL, RESERVED_PREDICATE_SYMBOL,
    RESERVED_PREDICATE_SYMBOLS,
};
// ---- closed-model certificates (ADR 0007, additive FIRM amendment) ----
pub use cert::{
    CertId, CertSizeDecl, ClosedModelCert, ClosureWitness, FiniteDomain, Hash, NonMemberProof,
    RelationTable, StratumPrefix, SupportEdge, SupportRef, SupportWitness,
};

// ---- the checker-facing SPI (STABLE v1) ----
pub use check::{
    cert_size_over_budget, check, check_closed_model_chain, check_with_cert_context,
    check_with_cert_memo, closure_join_cost, closure_join_cost_in_world, incoherent_builtin_atoms,
    profile_decides_all_builtins, profile_is_fully_identified, program_digest,
    unidentified_profile_slots, unidentified_profile_slots_allowing, unowned_builtin_predicates,
    CertContext, CheckLimits, CheckProfile, Outcome, ProfileSlot, RejectionCode, TermIdentity,
    WorldMemo,
};
pub use spi::{
    compound_identity_of, edb_table_hash, ground_from_legacy, legacy_outcome, standard_theory,
    AlwaysAdmit, ComponentIdentity, CompoundTheory, CopyIncapacity, DecisionCompletion,
    LeafOutcome, LeafVerifier, PredicateSet, RuleAdmissibility, RuleOutcome, Theory, TheoryOutcome,
    EDB_PREFIX,
};
// ---- standard checkable Theory impls (STABLE v1; ADR 0014, ADR 0016 "Shelf A") ----
// The standard theories live in the contract tier (tri-core with contract/{go,ts}); the
// search-side solvers stay in logos-core, sharing these crates' semantics so check and
// search cannot drift. `ArithmeticTheory` over `intval`/`arithmetic`; `TextTheory` over
// raw `Atom` bytes (mirroring the search-side contains/starts_with/ends_with builtins);
// `TermTheory` over the term algebra (A0 recognizers + standard order, ADR 0016);
// `ListTheory` over the reified `list` embedding (A1 list relations, ADR 0016).
pub use arithmetic::ArithmeticTheory;
pub use decval::BigDecimal;
pub use list_theory::ListTheory;
pub use term_theory::{compare_values, TermTheory};
pub use text::TextTheory;
// ---- the Shelf-B hash-pinned Horn-clause prelude (STABLE v1; ADR 0016 "Shelf B") ----
// A loaded bundle's clauses are ordinary account `Rule` nodes the EXISTING `check` verifies —
// zero new trusted code. `load_prelude` recomputes the `program_digest` over the deserialized
// clauses and rejects a mismatch; `PreludeBundle::merge_into` program-prepends them (no new
// `CheckProfile` field). See `prelude/<name>@<version>.json` + `vectors/prelude.json`.
pub use prelude::{
    bundle_digest, canonical_clause_bytes, load_prelude, PreludeBundle, PreludeError,
};

// ---- the engine-facing seam (PROPOSED — ADR 0002) ----
pub use engine::{
    reify_lists, BottomUpEngine, BuiltinSolver, Cost, DerivationBuilder, Exhausted, LeafSource,
    NoCallerLimit, OperatorId, OperatorSelectionPolicy, PhysicalOperator, PresentedFact,
    ResourceLimits, RoundOutcome, SearchReport, SolverReport, StratumSeed, StratumSummary,
    TruncationReason,
};

/// Declare, inside an `impl Theory` or `impl LeafSource` block, that the implementor does not copy
/// itself (#2722 item 1): `cannot_copy!(Theory, "<why>");` or `cannot_copy!(LeafSource, "<why>");`.
///
/// It expands to the REQUIRED `boxed_clone` returning [`CopyIncapacity::declared`] with the reason.
/// The reason is MANDATORY and must be a non-empty string literal: there is no zero-argument form,
/// because a reason-less incapacity is a default by another name (`seat:caa`'s ruling), and an
/// empty literal fails to compile.
#[macro_export]
macro_rules! cannot_copy {
    (Theory, $reason:literal) => {
        fn boxed_clone(
            &self,
        ) -> ::core::result::Result<
            ::std::boxed::Box<dyn $crate::Theory + ::core::marker::Send + ::core::marker::Sync>,
            $crate::CopyIncapacity,
        > {
            const { assert!(!$reason.is_empty(), "cannot_copy! needs a reason") };
            ::core::result::Result::Err($crate::CopyIncapacity::declared($reason))
        }
    };
    (LeafSource, $reason:literal) => {
        fn boxed_clone(
            &self,
        ) -> ::core::result::Result<
            ::std::boxed::Box<dyn $crate::LeafSource + ::core::marker::Send + ::core::marker::Sync>,
            $crate::CopyIncapacity,
        > {
            const { assert!(!$reason.is_empty(), "cannot_copy! needs a reason") };
            ::core::result::Result::Err($crate::CopyIncapacity::declared($reason))
        }
    };
}

/// #3197: the wildcard lint stays on the checker crate. Without its `deny`, every check stays green
/// while the guard is gone, so the crate-level attribute is pinned here (as #2892 pins the kernel's).
#[cfg(test)]
mod wildcard_lint_3197 {
    #[test]
    fn the_checker_crate_denies_a_wildcard_arm_over_an_enum() {
        let src = include_str!("lib.rs").replace("\r\n", "\n");
        assert!(
            src.lines()
                .any(|l| l == "#![deny(clippy::wildcard_enum_match_arm)]"),
            "#3197: logos-contract lost its crate-level wildcard deny"
        );
    }
}
