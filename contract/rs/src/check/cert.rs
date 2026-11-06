//! ADR-0007 closed-model-certificate verification — the cert machinery a `Neg`
//! premise `\+ r(a)` discharges against. **[FIRM amendment · additive]**
//!
//! Split out of the rule-check forward pass ([`super`]) as a pure file partition (no
//! behavior change): [`super::check_with_cert_context`] verifies every cited
//! [`ClosedModelCert`] up front via [`verify_cert`], a `Neg` premise reuses the
//! memoized [`CertStatus`] via [`verify_neg_premise`], and [`program_digest`] is
//! re-exported from [`super`] so the public `check::program_digest` item and the
//! crate-root re-export are byte-identical. The soundness argument (support ⇒
//! `E ⊆ least model`, closure ⇒ `least model ⊆ E`, so `E` is exact) is unchanged —
//! see the banner comment below.

use super::cert_stack::{resolve_lower_seals, CertView};
use super::cert_support::check_cert_support;
use super::cert_truth::{body_continues, filter_outcome, truth};
use super::{builtin_not_decided, CertContext, CheckLimits, CheckProfile, Outcome, RejectionCode};
use crate::cert::{CertId, CertSizeDecl, ClosedModelCert, Hash, NonMemberProof, SupportRef};
use crate::completion::{self, Completion, GroundOutcome};
use crate::derivation::{Derivation, GroundFilter};
use crate::engine::NoCallerLimit;
use crate::fragment::{classify_sealed_clause, Outside, ScopeGraph};
use crate::intval::BigInt;
use crate::literal::{GroundLiteral, Symbol};
use crate::program::{BodyLit, Clause, PredicateRef, Program, ProjectSpec};
use crate::spi::{LeafVerifier, Theory};
use crate::term::Term;
use ontos_core::Value;

// ====================== ADR 0007 closed-model certificates =====================
//
// SOUNDNESS, stratum by stratum (#3022 step 3; research 0028's advice §2, row A4). Let L be the
// already-verified interpretation of the strictly lower strata: the lower certificates a sealed
// clause reads, each Valid before it is cited (#2258 (a)), and the pinned Theory's decisions. Let
// T_s^L be the immediate-consequence operator of this certificate's scope, with every negation and
// count evaluated against L. Two obligations make the sealed finite table E_s EXACTLY lfp(T_s^L):
//
//   * SUPPORT gives E_s ⊆ lfp(T_s^L) ("no junk"): every fact in E_s has a support edge, a cited
//     clause grounded so its head equals the fact, whose body literals each hold in E_s or L, and
//     whose same-stratum positive dependencies have a STRICTLY SMALLER rank than the fact. The
//     strict rank rejects the `p :- p` upper-bound trap: `{p}` is closed, but p's only edge would
//     need a same-stratum dependency `p` ranked below itself. By induction on rank.
//
//   * CLOSURE gives T_s^L(E_s) ⊆ E_s ("no missing heads"), hence lfp(T_s^L) ⊆ E_s: for every
//     clause of the scope, taken from the trusted program, every grounding whose body is true
//     against E_s and L has its head in E_s. The checker meets those groundings by a COMPLETE
//     relational join over the sealed tables (#1829), never by enumerating the domains: under the
//     safety gate every clause variable occurs in a positive sealed, non-builtin literal, so a
//     satisfied grounding binds each variable from a row that exists, and the structural matcher
//     meets it. A satisfied grounding whose head leaves the supplied domains is refused
//     (cert_out_of_domain), and an undecidable or inconsistent literal (a Theory's NotMine after
//     owns()) refuses by name, never reads as false, so the closure cannot under-fire.
//
// Support and closure give E_s = lfp(T_s^L), so `a ∉ E_s` proves `a` absent from the stratum's
// least model: absence is sound, not an upper bound. Neither obligation needs the program to be
// constructor-acyclic: a finiteness guarantee is an admission promise that evaluation ends, and
// closure is the evidence that this table is complete.
//
// Every loop below ranges over a SUPPLIED finite table, pre-bounded by a CheckLimits cert budget
// validated BEFORE any scan. No fixpoint, no Herbrand enumeration, no engine call.

/// The memoized verification status of one cited [`ClosedModelCert`]. Computed once,
/// up front, into a `Vec` parallel to `Derivation::closed_world`; a `Neg` premise
/// reuses the cached result rather than re-verifying.
#[derive(Clone, Debug)]
pub(super) enum CertStatus {
    /// The cert passed budget + context + support + closure.
    Valid,
    /// The cert failed; the carried code/detail is surfaced when a `Neg` premise
    /// cites it (so the failure is attributed to the citing rule node).
    Invalid(RejectionCode, String),
}

/// Where a certificate sits in its derivation's `closed_world`: its own index and the world's
/// length. A lower-stratum support ref names a cert index, and #2258 C3 checks it against this.
#[derive(Clone, Copy, Debug)]
pub(super) struct CertPlace {
    /// This cert's index in `closed_world`.
    pub(super) own: usize,
    /// `closed_world.len()`.
    pub(super) world_len: usize,
}

/// Verify one certificate fully, ONCE, in the normative order
/// **budget → context → scope-closure → domain → support → closure → EDB** (ADR
/// 0007 §3), with a canonical-form precheck (1b, issue #839) between budget and
/// context — not a new semantic gate, but the representation invariant every
/// later gate's binary-search lookups assume. The budget gate is first (before
/// any scan); context is *recomputed*,
/// not merely compared; the scope-closure + domain gates establish the well-formed
/// invariants that make the support and closure checks sound; the EDB gate
/// binds extensional tables to the live snapshot.
///
/// `world` is the derivation's `closed_world` and `status` the statuses computed so far, in the
/// [`super::cert_stack::verification_order`]: every certificate at a lower level is final, so a
/// predicate this cert reads from one is read only once that cert is known Valid (#2258 (a)).
#[allow(clippy::too_many_arguments)]
pub(super) fn verify_cert<C>(
    cert: &ClosedModelCert,
    place: CertPlace,
    world: &[ClosedModelCert],
    status: &[Option<CertStatus>],
    program: &dyn Program,
    profile: &CheckProfile<C>,
    ctx: &C,
    cert_context: &CertContext,
    limits: &CheckLimits,
) -> CertStatus {
    let theory = profile.theory.as_ref();
    // 1. BUDGET GATE — first, before any scan.
    if let Err((code, detail)) = check_cert_budget(cert, limits) {
        return CertStatus::Invalid(code, detail);
    }
    // 1b. CANONICAL FORM (issue #839) — every binary-searched collection the cert
    //     carries (scope predicates, domain values, extension rows) must actually BE
    //     sorted + deduped by its canonical key. The pub fields make a non-canonical
    //     literal representable (the constructors sort; wire decode and struct
    //     literals do not have to), and a defeated binary search does not fail loudly
    //     — it fabricates arbitrary per-lookup verdicts. Reject deterministically
    //     here, bounded by the budget just validated, before any gate consults a
    //     lookup. Each defect carries the code its silent defeat would otherwise
    //     have fabricated, with a detail naming the real cause.
    if let Err((code, detail)) = check_cert_canonical_form(cert) {
        return CertStatus::Invalid(code, detail);
    }
    // 1c. PARTIAL SUB-SCOPE (ADR 0030 D1) — before any table is consulted: `partial_scope` is
    //     the one field a malicious producer would most like the checker to trust, so its three
    //     invariants are verified up front. A cert with no `partial_scope` passes untouched.
    if let Err((code, detail)) =
        check_cert_partial_scope(cert, program, profile.leaves.extensional())
    {
        return CertStatus::Invalid(code, detail);
    }
    // 2. CONTEXT (§3.1) — RECOMPUTE program_hash from the live program (a trusted
    //    whole-program canonical digest), require the cert's pin to equal it, AND
    //    require all four cert pins to equal the caller-derived context.
    if let Err((code, detail)) = check_cert_context(cert, program, cert_context) {
        return CertStatus::Invalid(code, detail);
    }
    // 2a. PARTITION GATE (admissible fragment) — a stratum prefix holds only
    //     intensional/extensional predicates, NEVER theory-owned builtins (§4.4: the
    //     builtin partition is decided LIVE by the Theory, not sealed in a table). A
    //     sealed theory-owned pred would let `\+ b(a)` be discharged against a
    //     FABRICATED table instead of the theory — reject before any model gate.
    for pred in cert.scope.predicates.iter() {
        if theory.owns(pred) {
            return CertStatus::Invalid(
                RejectionCode::CertScopeIncomplete,
                format!(
                    "sealed scope predicate {:?} is theory-owned (builtins are a separate partition, decided live — not sealable)",
                    String::from_utf8_lossy(pred.bytes())
                ),
            );
        }
    }
    // 2b. STACKED READS (#2258 (a)) — every predicate a sealed clause reads without this cert
    //     sealing it resolves to the UNIQUE certificate at a strictly lower level that seals it
    //     EXACTLY and is Valid; an invalid one invalidates this cert with its own code. The
    //     verification order made every lower status final, so validity precedes citation.
    let view = match resolve_lower_seals(cert, place.own, world, Some(status), program, theory) {
        Ok(view) => view,
        Err((code, detail)) => return CertStatus::Invalid(code, detail),
    };
    // 3. SCOPE DOWNWARD-CLOSURE (§3.2) — the sealed prefix must be self-contained:
    //    every defining clause of a sealed head touches only sealed, theory-owned or
    //    lower-sealed (2b) predicates, and an intra-scope `\+` is forbidden. Establishes the
    //    invariant that `eval_body_literal` can decide every in-scope body literal.
    if let Err((code, detail)) = check_scope_downward_closed(&view, program, theory) {
        return CertStatus::Invalid(code, detail);
    }
    // 4. DOMAIN COVERAGE (§3.4) — every value reachable through the cert (extension
    //    rows, support refs, subst images) must lie in ∪domains, so every tuple the
    //    closure join emits is a point of the finite space a self-enumeration over
    //    ∪domains would have visited (the join demands nothing more, #1829).
    if let Err((code, detail)) = check_cert_domain_coverage(cert, program) {
        return CertStatus::Invalid(code, detail);
    }
    // 5. SUPPORT (§3.5) — E ⊆ least model (no junk; rank-consistent strict descent).
    //    Extensional (EDB) facts are the base case: vouched by the §3.6 EDB snapshot
    //    gate, not by support edges, so support exempts them.
    if let Err((code, detail)) =
        check_cert_support(&view, place, program, theory, profile.leaves.extensional())
    {
        return CertStatus::Invalid(code, detail);
    }
    // 6. CLOSURE (§3.3) — least model ⊆ E, driven by the TRUSTED enumerated defining
    //    clauses of the sealed scope (NOT the support witness's cited clauses).
    if let Err((code, detail)) = check_cert_closure(&view, program, theory, limits) {
        return CertStatus::Invalid(code, detail);
    }
    // 7. EDB BINDING (§3.6) — every sealed extensional predicate's table must equal
    //    the live EDB snapshot the bound LeafVerifier attests.
    if let Err((code, detail)) = check_cert_edb(cert, &*profile.leaves, ctx) {
        return CertStatus::Invalid(code, detail);
    }
    // 8. exact.
    CertStatus::Valid
}

/// 1c. PARTIAL SUB-SCOPE (ADR 0030 D1). A cert with `partial_scope: None` passes untouched —
/// every pre-0030 cert, and every cert of an exact seal. Otherwise the three invariants, each a
/// `cert_partial_scope_invalid` refusal, verified BEFORE any table is consulted because a
/// certificate is untrusted input:
///
///  1. `p ⊆ scope`, `p` canonical (sorted + deduped by symbol byte order, #839), and `p` names
///     the sealed prefix's own level;
///  2. **upward-closed within the sealed prefix**: a sealed clause whose head is COMPLETE may
///     not read (positively, or under a count) a predicate marked partial — its closure proof
///     would be closed over `E` and vacuous for the rows the lower bound is missing. The
///     producer of D3 never mints this shape (partial = exactly the tripping stratum, nothing
///     sealed above it); the checker verifies it regardless;
///  3. an extensional table is never partial: it is snapshot-bound (`cert_edb_mismatch`), and a
///     snapshot is complete by definition.
fn check_cert_partial_scope(
    cert: &ClosedModelCert,
    program: &dyn Program,
    extensional: &crate::PredicateSet,
) -> Result<(), (RejectionCode, String)> {
    let Some(partial) = cert.partial_scope.as_ref() else {
        return Ok(());
    };
    let invalid = |detail: String| (RejectionCode::CertPartialScopeInvalid, detail);
    // 1. canonical, a sub-scope, the same level.
    if !partial.is_canonical() {
        return Err(invalid(
            "partial_scope predicates are not sorted+deduped by symbol byte order - build it via StratumPrefix::new, not a struct literal (issue #839)"
                .into(),
        ));
    }
    if partial.predicates.is_empty() {
        return Err(invalid(
            "partial_scope is present but names no predicate - encode an exact seal as an ABSENT partial_scope".into(),
        ));
    }
    if partial.level != cert.scope.level {
        return Err(invalid(format!(
            "partial_scope level {} is not the sealed prefix's level {}",
            partial.level, cert.scope.level
        )));
    }
    for pred in &partial.predicates {
        if !cert.scope.seals(pred) {
            return Err(invalid(format!(
                "partial_scope names predicate {:?} that the sealed scope does not seal",
                String::from_utf8_lossy(pred.bytes())
            )));
        }
        // 3. extensional tables are never partial.
        if extensional.contains(pred) {
            return Err(invalid(format!(
                "partial_scope marks extensional predicate {:?} as partial - an EDB table is snapshot-bound and complete by definition",
                String::from_utf8_lossy(pred.bytes())
            )));
        }
    }
    // 2. upward-closed: no COMPLETE sealed head reads a PARTIAL predicate.
    let mut err: Option<(RejectionCode, String)> = None;
    program.for_each_clause(&mut |_id, clause| {
        if err.is_some() || !cert.scope.seals(&clause.head.pred) || cert.is_partial(&clause.head.pred)
        {
            return;
        }
        for bl in &clause.body {
            // An intra-scope negation is already refused by the scope gate; a positive or
            // counting read of a lower bound is what makes a "complete" closure vacuous.
            if bl.is_neg() {
                continue;
            }
            if cert.is_partial(bl.pred()) {
                err = Some(invalid(format!(
                    "partial_scope is not upward-closed: complete sealed predicate {:?} is defined by a clause that reads partial predicate {:?}",
                    String::from_utf8_lossy(clause.head.pred.bytes()),
                    String::from_utf8_lossy(bl.pred().bytes())
                )));
                return;
            }
        }
    });
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// 1b. CANONICAL FORM (issue #839). The cert's three binary-searched collections
/// must be sorted + deduped by their canonical keys, or every membership decision
/// downstream is unsound — silently: an unsorted `FiniteDomain` reports present
/// values absent per lookup luck, surfacing as an arbitrary `cert_out_of_domain`
/// with every correct value in the list. Reject deterministically instead, with the
/// code that collection's defeated search would have fabricated and a detail that
/// names the canonicalizing constructor.
fn check_cert_canonical_form(cert: &ClosedModelCert) -> Result<(), (RejectionCode, String)> {
    if !cert.scope.is_canonical() {
        return Err((
            RejectionCode::CertScopeIncomplete,
            "sealed scope predicates are not sorted+deduped by symbol byte order - build the prefix via StratumPrefix::new, not a struct literal (issue #839)"
                .into(),
        ));
    }
    for domain in &cert.domains {
        if !domain.is_canonical() {
            return Err((
                RejectionCode::CertOutOfDomain,
                format!(
                    "finite domain {:?} values are not sorted+deduped by canonical codec bytes, so binary-search membership is defeated - build the domain via FiniteDomain::new, not a struct literal (issue #839)",
                    String::from_utf8_lossy(domain.type_tag.bytes())
                ),
            ));
        }
    }
    for table in &cert.extensions {
        if !table.is_canonical() {
            return Err((
                RejectionCode::CertUnsupported,
                format!(
                    "sealed table {:?} rows are not sorted+deduped by canonical codec bytes, so binary-search membership is defeated - build the table via RelationTable::new, not a struct literal (issue #839)",
                    String::from_utf8_lossy(table.pred.bytes())
                ),
            ));
        }
    }
    Ok(())
}

/// Domain separator for the recomputed canonical program digest (ADR 0007 §3.1).
const PROGRAM_PREFIX: &[u8] = b"logos/account/program/v1\n";

/// §3.1 CONTEXT. Recompute `program_hash` from the live program — a canonical digest
/// over every clause's frozen account bytes (sorted, so it is order-independent and
/// commits to the COMPLETE clause set) — and require the cert's pin to equal it; then
/// require the cert's four pins to equal the caller-derived `cert_context`.
fn check_cert_context(
    cert: &ClosedModelCert,
    program: &dyn Program,
    cert_context: &CertContext,
) -> Result<(), (RejectionCode, String)> {
    // ADR 0029 D10 — WHICH CLAUSE SET DOES `program_hash` PIN?
    //
    // Not slice-sealed (every pre-D10 cert): the COMPLETE live clause set, ADR 0007 §3.1,
    // byte-for-byte the behaviour this function has always had.
    //
    // Slice-sealed: the component's own downward-closed slice. The seal is admitted ONLY when
    // the caller's bound context carries the SAME witness pin — so a cert minted under one
    // decomposition cannot replay under another, and one minted under a decomposition cannot
    // replay in a whole-program run at all (that context's pin is `None`).
    //
    // ⚠ The DOWNWARD-CLOSURE gate is deliberately NOT relaxed here: `check_scope_downward_closed`
    // walks every clause of the COMPLETE `program` whatever this branch decides. That is what
    // makes a slice seal sound — the sealed ideal is still proved closed in the whole program,
    // and only the PIN's coverage narrows.
    let recomputed = match (
        cert.decomposition_witness,
        cert_context.decomposition_witness,
    ) {
        (None, _) => recompute_program_hash(program),
        (Some(sealed), Some(bound)) if sealed == bound => {
            recompute_program_hash_over_scope(program, cert)
        }
        (Some(_), Some(_)) => {
            return Err((
                RejectionCode::CertContextMismatch,
                "certificate is sealed over a decomposition slice, but the bound check context \
                 names a DIFFERENT decomposition — a slice seal is valid only under the \
                 decomposition that authorized it (ADR 0029 D10)"
                    .into(),
            ));
        }
        (Some(_), None) => {
            return Err((
                RejectionCode::CertContextMismatch,
                "certificate is sealed over a decomposition slice, but the bound check context \
                 declares no decomposition — a slice-sealed cert cannot discharge a negation in \
                 a whole-program run (ADR 0029 D10)"
                    .into(),
            ));
        }
    };
    if cert.program_hash != recomputed {
        return Err((
            RejectionCode::CertContextMismatch,
            "certificate program_hash does not match the recomputed live program".into(),
        ));
    }
    // The remaining three pins must match the bound context in EVERY case: profile, verification
    // context and theory configuration are properties of the RUN, and a component does not get its
    // own profile or its own `not`.
    if cert.profile_hash != cert_context.profile_hash
        || cert.ctx_hash != cert_context.ctx_hash
        || cert.theory_config_hash != cert_context.theory_config_hash
    {
        return Err((
            RejectionCode::CertContextMismatch,
            "certificate pins do not match the bound check context".into(),
        ));
    }
    // `program_hash` is the ONE pin whose coverage D10 narrows, so it is compared separately.
    //
    // Whole-program cert: it must equal the caller's own program pin, exactly as before.
    //
    // Slice-sealed cert: it MUST NOT, and requiring it would make D10 unsatisfiable — the cert
    // pins the component's slice while the caller pins the complete program it ran, and those are
    // different clause sets by construction (that difference is the whole point). The seal is
    // already tied to the run by two checks above: the witness pins agree, and `program_hash`
    // equals the slice recomputed from the caller's OWN live program — so the component cannot be
    // re-pointed at a different program without failing the recompute.
    if cert.decomposition_witness.is_none() && cert.program_hash != cert_context.program_hash {
        return Err((
            RejectionCode::CertContextMismatch,
            "certificate pins do not match the bound check context".into(),
        ));
    }
    Ok(())
}

/// The canonical program digest: `SHA-256(PROGRAM_PREFIX ‖ ⨁ len-prefixed sorted
/// clause_bytes)` over the program's COMPLETE clause set ([`Program::for_each_clause`]).
/// Sorting the per-clause frozen account bytes makes the digest independent of
/// enumeration order and commits to the whole clause set — a dropped or added clause
/// changes the digest, so an attacker cannot hide a defining clause.
///
/// Public so a consumer that wants certifiable negation can DERIVE the `program_hash`
/// of its bound [`CertContext`] from the live program it runs (ADR 0007 §3.1).
pub fn program_digest(program: &dyn Program) -> Hash {
    recompute_program_hash(program)
}

/// The canonical program digest over the SLICE a slice-sealed cert covers (ADR 0029 D10): the
/// defining clauses of the cert's sealed scope, and nothing else.
///
/// Identical construction to [`recompute_program_hash`] — same prefix, same per-clause frozen
/// account bytes, same sort — over a SUBSET of the clauses. So the two digests are directly
/// comparable and a slice can never collide with a complete program except by both holding the
/// same clause set, which is the degenerate case where the distinction does not matter.
///
/// A predicate that is a dependency-edge TARGET but not a stratum member (an EDB predicate)
/// contributes no clause, exactly as it contributes none to the component.
fn recompute_program_hash_over_scope(program: &dyn Program, cert: &ClosedModelCert) -> Hash {
    let mut clause_byte_vecs: Vec<Vec<u8>> = Vec::new();
    program.for_each_clause(&mut |_id, clause| {
        if cert.scope.seals(&clause.head.pred) {
            clause_byte_vecs.push(crate::account::clause_bytes(clause));
        }
    });
    clause_byte_vecs.sort();
    let mut hasher = sha2::Sha256::new();
    use sha2::Digest as _;
    hasher.update(PROGRAM_PREFIX);
    for bytes in &clause_byte_vecs {
        hasher.update((bytes.len() as u64).to_be_bytes());
        hasher.update(bytes);
    }
    hasher.finalize().into()
}

fn recompute_program_hash(program: &dyn Program) -> Hash {
    let mut clause_byte_vecs: Vec<Vec<u8>> = Vec::new();
    program.for_each_clause(&mut |_id, clause| {
        clause_byte_vecs.push(crate::account::clause_bytes(clause));
    });
    clause_byte_vecs.sort();
    let mut hasher = sha2::Sha256::new();
    use sha2::Digest as _;
    hasher.update(PROGRAM_PREFIX);
    for bytes in &clause_byte_vecs {
        // Length-prefix each clause's bytes so concatenation is unambiguous.
        hasher.update((bytes.len() as u64).to_be_bytes());
        hasher.update(bytes);
    }
    hasher.finalize().into()
}

/// The certificate SIZE budgets (`max_cert_bytes`, `max_cert_facts`, `max_domain_values`,
/// `max_support_edges`), checked against a declaration in the order the checker checks them: the
/// first one `decl` exceeds, as the detail a [`RejectionCode::CertSizeExceeded`] rejection carries,
/// or `None`.
///
/// #2497: the ONE list of size fields. [`check_cert_budget`] rejects through it, and a producer
/// predicts that rejection through it (`cert_size_over_budget`), so a size field added here reaches
/// both by construction. The closure budgets (`cert_budget_exceeded`) stay in `check_cert_budget`.
/// A declared count past a host budget, compared in the protocol domain (#2735): the count is a
/// `u64` integer, never narrowed to a host offset to be compared, so a 32-bit build compares the
/// same numbers a 64-bit one does.
fn exceeds(declared: u64, budget: usize) -> bool {
    u64::try_from(budget).is_ok_and(|budget| declared > budget)
}

/// An actual (host-counted) size past its own declaration, compared in the protocol domain.
fn above(actual: usize, declared: u64) -> bool {
    u64::try_from(actual).map_or(true, |actual| actual > declared)
}

pub fn cert_size_over_budget(decl: &CertSizeDecl, limits: &CheckLimits) -> Option<String> {
    let over_size =
        |name: &str, got: u64, max: usize| format!("declared {name} {got} exceeds budget {max}");
    if exceeds(decl.cert_bytes, limits.max_cert_bytes) {
        return Some(over_size(
            "cert_bytes",
            decl.cert_bytes,
            limits.max_cert_bytes,
        ));
    }
    if exceeds(decl.cert_facts, limits.max_cert_facts) {
        return Some(over_size(
            "cert_facts",
            decl.cert_facts,
            limits.max_cert_facts,
        ));
    }
    if exceeds(decl.domain_values, limits.max_domain_values) {
        return Some(over_size(
            "domain_values",
            decl.domain_values,
            limits.max_domain_values,
        ));
    }
    if exceeds(decl.support_edges, limits.max_support_edges) {
        return Some(over_size(
            "support_edges",
            decl.support_edges,
            limits.max_support_edges,
        ));
    }
    None
}

/// Step 1 — validate the declared sizes against the `CheckLimits` cert budgets, AND
/// the cert's ACTUAL sizes against the declaration (a lying decl is caught). All
/// strict `>` comparisons; the budget gate must pass before any scan.
fn check_cert_budget(
    cert: &ClosedModelCert,
    limits: &CheckLimits,
) -> Result<(), (RejectionCode, String)> {
    let decl: &CertSizeDecl = &cert.limits_decl;
    // (a) declared ≤ budget. Both halves are the CALLER's verify budget (#2335), and each
    // family has its own code so the kernel's check-limit table can name one kind per code: the
    // four SIZE fields are `cert_size_exceeded`, the two CLOSURE fields `cert_budget_exceeded`
    // (the code the live closure scan and the producer's closure decline already name).
    // The SIZE family, through the one list a producer shares (#2497).
    if let Some(over) = cert_size_over_budget(decl, limits) {
        return Err((RejectionCode::CertSizeExceeded, over));
    }
    let over = |name: &str, got: u64, max: usize| {
        (
            RejectionCode::CertBudgetExceeded,
            format!("declared {name} {got} exceeds budget {max}"),
        )
    };
    if exceeds(decl.rule_groundings, limits.max_rule_groundings) {
        return Err(over(
            "rule_groundings",
            decl.rule_groundings,
            limits.max_rule_groundings,
        ));
    }
    if exceeds(decl.join_steps, limits.max_join_steps) {
        return Err(over("join_steps", decl.join_steps, limits.max_join_steps));
    }
    // (b) actual ≤ declared (no under-declaration to slip past the budget). A cert whose actual
    // size exceeds its OWN declaration lied: the producer's fault, `cert_decl_mismatch` (#2335),
    // never the caller's budget.
    let actual_facts: usize = cert.extensions.iter().map(|t| t.rows.len()).sum();
    let actual_domain_values: usize = cert.domains.iter().map(|d| d.values.len()).sum();
    let actual_support_edges = cert.supports.0.len();
    let liar = |name: &str, actual: u64, decl: u64| {
        (
            RejectionCode::CertDeclMismatch,
            format!("actual {name} {actual} exceeds declared {decl}"),
        )
    };
    if above(actual_facts, decl.cert_facts) {
        return Err(liar("cert_facts", actual_facts as u64, decl.cert_facts));
    }
    if above(actual_domain_values, decl.domain_values) {
        return Err(liar(
            "domain_values",
            actual_domain_values as u64,
            decl.domain_values,
        ));
    }
    if above(actual_support_edges, decl.support_edges) {
        return Err(liar(
            "support_edges",
            actual_support_edges as u64,
            decl.support_edges,
        ));
    }
    // #2524: the BYTES, measured on the canonical encoding, so `max_cert_bytes` bounds what the
    // certificate IS, not only what it declares (declared <= budget is checked above).
    let actual_bytes = crate::cert_encoded_bytes(cert);
    if actual_bytes > decl.cert_bytes {
        return Err(liar("cert_bytes", actual_bytes, decl.cert_bytes));
    }
    Ok(())
}

/// §3.2 SCOPE DOWNWARD-CLOSURE. The sealed prefix must be self-contained: for EVERY
/// clause (from the TRUSTED whole-program enumeration) whose head is sealed by the
/// scope, every body literal's predicate must be sealed-by-scope OR theory-owned —
/// else `cert_scope_incomplete` (the cert cannot soundly evaluate that literal, so
/// closure would silently under-fire). Additionally, a `Neg` body literal whose
/// predicate is sealed by THIS cert's OWN scope is rejected: an intra-prefix negation
/// must target a strictly-lower, SEPARATELY-sealed stratum, never the same prefix.
///
/// A predicate this cert does not seal may also be read from the unique, exact, Valid
/// certificate at a strictly lower level that seals it (#2258 (a), resolved into `view` by
/// step 2b), positively or under `\+`.
///
/// This establishes the invariant `eval_body_literal` relies on: every in-scope body
/// literal is decidable against a table of `view` or the pinned `Theory`.
pub(super) fn check_scope_downward_closed(
    view: &CertView<'_>,
    program: &dyn Program,
    theory: &dyn Theory,
) -> Result<(), (RejectionCode, String)> {
    let cert = view.cert;
    // #3067 (research 0028 row A15): every gate below is the contract tier's ONE classification,
    // `classify_sealed_clause`, which the seal plan calls too. `check` builds the clause's context
    // from this certificate and the lower certificates it resolved (step 2b), and the scope's
    // dependency graph from the bound program, and renders the first gate a clause fails as
    // `cert_scope_incomplete`. It never trusts the producer's classification.
    let ctx = view.seal_context();
    let mut graph = ScopeGraph::new();
    let in_scope = |pred: &Symbol| cert.scope.seals(pred);
    program.for_each_clause(&mut |_id, clause| graph.add(clause, &in_scope));
    let owns = |pred: &Symbol| theory.owns(pred);
    let mut err: Option<(RejectionCode, String)> = None;
    program.for_each_clause(&mut |_id, clause| {
        if err.is_some() || !cert.scope.seals(&clause.head.pred) {
            return;
        }
        if let Some(outside) = classify_sealed_clause(clause, &ctx, &graph, &owns, &owns) {
            err = Some((
                RejectionCode::CertScopeIncomplete,
                scope_incomplete_detail(clause, &outside),
            ));
        }
    });
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// `cert_scope_incomplete`'s detail for the first gate a sealed clause fails, worded as `check` has
/// always worded each gate. The match is exhaustive: a new gate must say how it reads.
fn scope_incomplete_detail(clause: &Clause, outside: &Outside) -> String {
    let name = |pred: &Symbol| String::from_utf8_lossy(pred.bytes()).into_owned();
    match outside {
        Outside::CountNotLower { pred, same_scope } => {
            let why = if *same_scope {
                "which this same certificate seals (a count must read a strictly lower certificate, never the table under construction)"
            } else {
                "which no unique, exact, Valid strictly lower certificate seals"
            };
            format!(
                "scope-defining clause body contains a count over predicate {:?}, {why}",
                name(pred)
            )
        }
        Outside::CountOpenCompound { pred } => format!(
            "scope-defining clause count over predicate {:?} contains an open compound (a Term::Tuple with a variable) term (not function-free)",
            name(pred)
        ),
        Outside::ConstructorCycle { through } => format!(
            "scope-defining clause head {:?} constructs an open compound (a Term::Tuple with a variable) on a dependency cycle through {:?} (outside the constructor-acyclic fragment)",
            name(&clause.head.pred),
            name(through)
        ),
        Outside::Unserved { pred } => format!(
            "scope-defining clause body references predicate {:?} that is neither sealed nor theory-owned, nor sealed by a strictly lower certificate",
            name(pred)
        ),
        Outside::IntraScopeNegation { pred } => format!(
            "scope-defining clause negates predicate {:?} sealed by this same prefix (intra-scope negation)",
            name(pred)
        ),
        Outside::UnboundCountFilter { pred, var } => format!(
            "scope-defining clause count over predicate {:?} has filter variable {:?} not bound by any positive sealed-relation body literal (range-restriction)",
            name(pred),
            var.as_str()
        ),
        Outside::UnboundVariable { var } => format!(
            "scope-defining clause has unsafe variable {:?}: not bound by any positive sealed-relation body literal (range-restriction)",
            var.as_str()
        ),
    }
}

/// §3.4 DOMAIN COVERAGE. Every value the cert can introduce — every argument of every
/// extension row, every support-ref `atom`/`fact` argument, and every value in every
/// `edge.subst` image — MUST lie in ∪domains, else `cert_out_of_domain`. This makes
/// ∪domains a provable SUPERSET of the active domain, so no satisfiable grounding can
/// be silenced by an omitted value — and, since #1829's closure join iterates the sealed
/// rows rather than ∪domains, it is what makes every tuple the join emits a point of the
/// space a self-enumeration would have visited.
fn check_cert_domain_coverage(
    cert: &ClosedModelCert,
    program: &dyn Program,
) -> Result<(), (RejectionCode, String)> {
    let oob = |what: &str| {
        (
            RejectionCode::CertOutOfDomain,
            format!("{what} carries a value outside the certificate's finite domains"),
        )
    };
    // #2511: the domains' values as a set, built once. Membership by value is the relation the
    // codec-byte binary search decides (the encoding is injective), and the canonicity gate above
    // has already rejected an unsorted domain; the search encoded a value at every step, for
    // about ten values per sealed fact.
    let domain: std::collections::HashSet<&Value> =
        cert.domains.iter().flat_map(|d| d.values.iter()).collect();
    let check_val = |v: &Value| domain.contains(v);
    let check_ground = |g: &GroundLiteral| g.args.iter().all(check_val);

    // (a) every extension row's args.
    for table in &cert.extensions {
        for fact in &table.rows {
            if !check_ground(fact) {
                return Err(oob("a sealed extension row"));
            }
        }
    }
    // (b) every support edge: subst image values + each body ref's atom/fact args.
    for edge in &cert.supports.0 {
        for term in edge.subst.values() {
            if let Some(v) = term.erase_ground() {
                if !check_val(&v) {
                    return Err(oob("a support edge subst image"));
                }
            } else {
                return Err((
                    RejectionCode::CertUnsupported,
                    "support edge subst image is not ground".into(),
                ));
            }
        }
        if !check_ground(&edge.fact) {
            return Err(oob("a support edge fact"));
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
            if !check_ground(atom) {
                return Err(oob("a support ref atom"));
            }
        }
    }
    // (c) defensive: program is in hand but no per-clause values to cover here
    //     (clauses carry variables, not ground values) — the coverage is over cert
    //     data only. Touch `program` to keep the signature meaningful/uniform.
    let _ = program;
    Ok(())
}

/// §3.6 EDB BINDING. For every sealed predicate that the bound `LeafVerifier`
/// declares extensional, the cert's sealed table must equal the live EDB snapshot:
/// `edb_table_hash(p, cert.table(p).rows) == leaves.edb_snapshot(p, ctx)`. A `None`
/// snapshot (the fail-closed default) means the cert cannot bind `p` to the live EDB
/// → `cert_edb_mismatch`. This is the load-bearing "least model ⊆ E" obligation for
/// extensional predicates (an omitted/added EDB fact is otherwise free).
fn check_cert_edb<C>(
    cert: &ClosedModelCert,
    leaves: &dyn LeafVerifier<C>,
    ctx: &C,
) -> Result<(), (RejectionCode, String)> {
    let extensional = leaves.extensional();
    for pred in cert.scope.predicates.iter() {
        if !extensional.contains(pred) {
            continue; // an IDB predicate — bound by support/closure, not the EDB gate.
        }
        let rows: &[GroundLiteral] = cert.table(pred).map(|t| t.rows.as_slice()).unwrap_or(&[]);
        let recomputed = crate::spi::edb_table_hash(pred, rows);
        match leaves.edb_snapshot(pred, ctx) {
            Some(attested) if attested == recomputed => {}
            Some(_) => {
                return Err((
                    RejectionCode::CertEdbMismatch,
                    format!(
                        "sealed extensional table {:?} does not match the live EDB snapshot",
                        String::from_utf8_lossy(pred.bytes())
                    ),
                ));
            }
            None => {
                return Err((
                    RejectionCode::CertEdbMismatch,
                    format!(
                        "no live EDB snapshot attested for sealed extensional predicate {:?}",
                        String::from_utf8_lossy(pred.bytes())
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// §3.3 CLOSURE: least model ⊆ E, by a checker JOIN over the sealed extensions of the
/// TRUSTED defining-clause set (#1829). For EVERY clause in the whole program (via the
/// trusted [`Program::for_each_clause`]) whose head is sealed by `cert.scope`, join its
/// positive sealed body literals over their sealed tables; every tuple the join emits is
/// a grounding whose body is true against `E` (+ the pinned Theory), so its head MUST be
/// present in `E`, else `cert_not_closed`. A satisfied grounding whose head value escapes
/// the domain is `cert_out_of_domain`.
///
/// SOUNDNESS (the fix). The defining-clause set is taken from the trusted program
/// enumeration — NOT from the attacker-chosen support witness — and the program
/// digest (recomputed in §3.1) commits to the COMPLETE clause set, so an attacker
/// cannot hide a defining clause (a non-cited clause that derives a fact is still
/// enumerated here; an omitted clause would change the program_hash and fail §3.1).
///
/// WHY A JOIN DEMANDS EXACTLY WHAT THE ENUMERATION DEMANDED. The self-enumeration this
/// replaced visited `|∪domains|^vars` groundings per clause and evaluated the body at each.
/// Two gates that run BEFORE closure make the join's obligation set equal to that one:
///  - §3.2's SAFETY gate ([`check_scope_downward_closed`]): every variable of a sealed-head
///    clause occurs in a positive body literal whose predicate is sealed and not
///    theory-owned — so the join binds every variable, and every theory or negated literal
///    reaches a point at which it is ground;
///  - §3.4's DOMAIN COVERAGE ([`check_cert_domain_coverage`]): every sealed-table value lies
///    in ∪domains — so every tuple the join emits is a point of the enumeration's own space,
///    and the join can demand nothing the enumeration would not have demanded.
///
/// A grounding the enumeration would have found satisfied has, for each positive sealed
/// literal, a row of that literal's table matching it — which is exactly a tuple the join
/// emits. So neither direction under-fires.
///
/// #2759: a DESTRUCTURING body literal (`item(tag(X))`) binds `X` to a sub-term of a row's
/// value, which need not lie in ∪domains. The enumeration could never have visited that
/// binding, so it would under-fire, and the scope gate was function-free while it stood. The
/// join visits it: it binds `X` by unifying the pattern with the row (`bind_row`), so every
/// satisfied grounding is still emitted, and its head is verified present and in-domain.
fn check_cert_closure(
    view: &CertView<'_>,
    program: &dyn Program,
    theory: &dyn Theory,
    limits: &CheckLimits,
) -> Result<(), (RejectionCode, String)> {
    let cert = view.cert;
    let mut groundings: usize = 0;
    let mut joins: usize = 0;
    let mut err: Option<(RejectionCode, String)> = None;

    // Iterate EVERY defining clause of a sealed predicate from the trusted program.
    program.for_each_clause(&mut |_id, clause| {
        if err.is_some() {
            return;
        }
        // Only close clauses whose head is a sealed scope predicate.
        if !cert.scope.seals(&clause.head.pred) {
            return;
        }
        // ADR 0030 D2: closure is NOT verified for a table in `partial_scope` — it is a lower
        // bound sealed at a round-budget trip, so a satisfied grounding whose head it omits is
        // the truth of the mark, not a defect. Its support is still verified (`E ⊆ least
        // model` holds of a lower bound), and no negation or count may cite it (3b gates).
        // The upward-closure invariant (`check_cert_partial_scope`) is what keeps every
        // COMPLETE table's closure proof meaningful: a complete table never reads a partial one.
        if cert.is_partial(&clause.head.pred) {
            return;
        }
        if let Err(e) = join_groundings(
            clause,
            view,
            theory,
            limits,
            true,
            &mut groundings,
            &mut joins,
        ) {
            err = Some(e);
        }
    });
    match err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// The closure join's COST for `cert` over `program`, counted without verifying it — the
/// groundings it emits and the join steps it performs, exactly as [`check_cert_closure`]
/// will count them at check time (#1829 increment 2). This is what a producer DECLARES in
/// [`CertSizeDecl`]: the declaration is then equal to the scan, not an upper bound on a
/// scan nobody performs.
///
/// Counts against `limits` and stops the moment either counter exceeds its budget
/// (`Err(cert_budget_exceeded)`), so a producer measuring against a run's wall never
/// spends past the wall it is about to refuse. `Err(cert_scope_incomplete)` if a
/// sealed-scope clause cannot be planned — §3.2 refuses such a cert before closure anyway.
/// No head is verified here (the model the producer sealed is its own answer to that);
/// everything else — clause selection, the partial-scope skip, binders, filters, the
/// counters — is the checker's code path.
pub fn closure_join_cost(
    cert: &ClosedModelCert,
    program: &dyn Program,
    theory: &dyn Theory,
    limits: &CheckLimits,
) -> Result<(usize, usize), (RejectionCode, String)> {
    closure_join_cost_over(&CertView::own(cert), program, theory, limits)
}

/// [`closure_join_cost`] for the certificate at `own` in a STACKED `closed_world` (#2258 (a)):
/// a predicate its sealed clauses read from a strictly lower certificate is read from that
/// certificate's table, exactly as the checker will read it, and the rows offered to it are
/// counted as this certificate's join steps. Resolution here is structural (a unique, exact
/// lower seal), since a producer measures before anything is verified; the checker adds the
/// validity of the lower certificate. For a certificate that reads nothing from below, this is
/// [`closure_join_cost`] exactly.
///
/// `Err(cert_out_of_range)` if `own` is not an index of `world`; otherwise as
/// [`closure_join_cost`], plus the resolution's own refusals (`cert_scope_incomplete` for an
/// ambiguous or partial lower seal).
pub fn closure_join_cost_in_world(
    world: &[ClosedModelCert],
    own: usize,
    program: &dyn Program,
    theory: &dyn Theory,
    limits: &CheckLimits,
) -> Result<(usize, usize), (RejectionCode, String)> {
    let Some(cert) = world.get(own) else {
        return Err((
            RejectionCode::CertOutOfRange,
            format!("certificate {own} out of range {}", world.len()),
        ));
    };
    let view = resolve_lower_seals(cert, own, world, None, program, theory)?;
    closure_join_cost_over(&view, program, theory, limits)
}

fn closure_join_cost_over(
    view: &CertView<'_>,
    program: &dyn Program,
    theory: &dyn Theory,
    limits: &CheckLimits,
) -> Result<(usize, usize), (RejectionCode, String)> {
    let cert = view.cert;
    let mut groundings: usize = 0;
    let mut joins: usize = 0;
    let mut err: Option<(RejectionCode, String)> = None;
    program.for_each_clause(&mut |_id, clause| {
        if err.is_some()
            || !cert.scope.seals(&clause.head.pred)
            || cert.is_partial(&clause.head.pred)
        {
            return;
        }
        if let Err(e) = join_groundings(
            clause,
            view,
            theory,
            limits,
            false,
            &mut groundings,
            &mut joins,
        ) {
            err = Some(e);
        }
    });
    match err {
        Some(e) => Err(e),
        None => Ok((groundings, joins)),
    }
}

/// The closure join over `view`, on either path, with the counters it reached, a trip's
/// included: what #2511's differential row compares between the indexed join and a full scan.
#[cfg(test)]
pub(super) fn closure_join_trace(
    view: &CertView<'_>,
    program: &dyn Program,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
) -> (Result<(), (RejectionCode, String)>, usize, usize) {
    let cert = view.cert;
    let mut groundings: usize = 0;
    let mut joins: usize = 0;
    let mut result = Ok(());
    program.for_each_clause(&mut |_id, clause| {
        if result.is_err()
            || !cert.scope.seals(&clause.head.pred)
            || cert.is_partial(&clause.head.pred)
        {
            return;
        }
        result = join_groundings(
            clause,
            view,
            theory,
            limits,
            verify,
            &mut groundings,
            &mut joins,
        );
    });
    (result, groundings, joins)
}

/// Collect the [`VarId`]s appearing in a goal's argument terms.
fn collect_vars_goal(goal: &crate::literal::Goal, out: &mut Vec<crate::term::VarId>) {
    for t in &goal.args {
        collect_vars_term(t, out);
    }
}

fn collect_vars_term(term: &Term, out: &mut Vec<crate::term::VarId>) {
    // #2275 layer 3: the shared, recursion-bounded variable walk (every occurrence, in order).
    term.for_each_var(|v| out.push(v.clone()));
}

/// The join plan of ONE sealed-scope clause (#1829). The order is pinned — identically in
/// the three cores, because the join-step count depends on it:
///
///  - a POSITIVE body literal whose predicate is sealed by the scope and not theory-owned,
///    or read from a strictly lower certificate (#2258 (a)), is a BINDER: it is iterated over
///    its sealed extension, in declared order, unifying on a repeated variable (`runs(R, R)`
///    binds `R` on the first occurrence and filters on the second);
///  - a COUNT over a strictly lower certificate's relation (#2258 L3.3b) is a COUNT STAGE, due
///    at the FIRST point its filter's variables are bound: before any binder if the filter is
///    ground, else right after the binder that binds the last of them. It binds its result
///    variable (or tests it, if already bound), and costs one join step per lower row it scans;
///  - every other literal — a theory literal of either polarity, or a negated sealed
///    literal (unreachable past §3.2's intra-scope gate, evaluated soundly if met) — is a
///    FILTER, evaluated at the FIRST point all its variables are bound: before any binder
///    if it is ground or reads only the results of counts due there, else right after the
///    binder whose point first binds the last of them (a count due at a point binds its result
///    there).
///
/// At each point the count stages run first, in declared order, then the filters, in declared
/// order. A count-free clause's plan is exactly what it was before counts were admitted.
///
/// §3.2's safety gate guarantees that point exists for every filter and that the head is
/// ground once every binder has bound; a clause that reaches here without that property is
/// refused `cert_scope_incomplete` rather than enumerated over anything.
struct JoinPlan<'a> {
    /// Steps due before any row is examined: counts over a ground filter, then filters that are
    /// ground as written or read only those counts' results.
    leading: Vec<Step<'a>>,
    /// The binders in declared order, each with the steps due once it has bound.
    binders: Vec<(&'a crate::literal::Goal, Vec<Step<'a>>)>,
    /// #2511: each binder's candidate index, keyed on the positions its earlier binders bound.
    /// It changes which rows the join VISITS, never which it COUNTS (see `join_index`).
    indexes: Vec<super::join_index::BinderIndex>,
}

/// One step of a closure join that is not a binder: a filter literal, or (#2258 L3.3b) a count
/// over a strictly lower certificate's relation.
enum Step<'a> {
    Filter(&'a BodyLit<Term>),
    Count(&'a crate::program::CountLit<Term>),
}

/// Run one step at its evaluation point: a filter is decided (`filter_outcome`), a count folds
/// and binds or tests its result (`cert_count::count_stage`), recording what it bound in `newly`.
/// #3165: the step's outcome is three-valued, since a theory filter may not be decided.
#[allow(clippy::too_many_arguments)]
fn run_step(
    step: &Step<'_>,
    subst: &mut crate::term::Subst,
    view: &CertView<'_>,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
    joins: &mut usize,
    newly: &mut Vec<crate::term::VarId>,
) -> Result<GroundOutcome<NoCallerLimit>, (RejectionCode, String)> {
    match step {
        Step::Filter(f) => filter_outcome(f, subst, view, theory, limits, verify, joins),
        Step::Count(count) => {
            super::cert_count::count_stage(count, subst, view, limits, verify, joins, newly)
                .map(truth)
        }
    }
}

fn plan_join<'a>(
    clause: &'a Clause,
    view: &CertView<'_>,
    theory: &dyn Theory,
) -> Result<JoinPlan<'a>, (RejectionCode, String)> {
    let scope_incomplete = |detail: String| (RejectionCode::CertScopeIncomplete, detail);
    let is_binder = |bl: &BodyLit<Term>| -> bool {
        !bl.is_neg()
            && bl.as_inner().is_some_and(|g| {
                (view.cert.scope.seals(&g.pred) && !theory.owns(&g.pred))
                    || view.reads_lower(&g.pred)
            })
    };
    let mut plan = JoinPlan {
        leading: Vec::new(),
        binders: Vec::new(),
        indexes: Vec::new(),
    };
    // The variables bound once binder `i` has bound: the cumulative union, in declared order.
    let mut bound_after: Vec<Vec<crate::term::VarId>> = Vec::new();
    let mut bound: Vec<crate::term::VarId> = Vec::new();
    for bl in &clause.body {
        // A count is not a binder: it is a count stage, placed below (#2258 L3.3b).
        if !is_binder(bl) {
            continue;
        }
        let Some(goal) = bl.as_inner() else { continue };
        // Keyed on what the binders BEFORE it bound: `bound` is still their sorted union here.
        plan.indexes
            .push(super::join_index::BinderIndex::new(goal, &bound));
        collect_vars_goal(goal, &mut bound);
        bound.sort();
        bound.dedup();
        bound_after.push(bound.clone());
        plan.binders.push((goal, Vec::new()));
    }
    // #2258 L3.3b: each count stage at the first point its filter is bound, and the results it
    // binds there. `available[i]` is then everything bound once point `i` has run.
    let mut leading_results: Vec<crate::term::VarId> = Vec::new();
    let mut results_at: Vec<Vec<crate::term::VarId>> = vec![Vec::new(); plan.binders.len()];
    for bl in &clause.body {
        let BodyLit::Count(count) = bl else { continue };
        let mut vars: Vec<crate::term::VarId> = Vec::new();
        for (_, term) in &count.filter {
            collect_vars_term(term, &mut vars);
        }
        let mut results: Vec<crate::term::VarId> = Vec::new();
        collect_vars_term(&count.count, &mut results);
        if vars.is_empty() {
            plan.leading.push(Step::Count(count));
            leading_results.extend(results);
            continue;
        }
        match bound_after
            .iter()
            .position(|b| vars.iter().all(|v| b.binary_search(v).is_ok()))
        {
            Some(i) => {
                plan.binders[i].1.push(Step::Count(count));
                results_at[i].extend(results);
            }
            None => {
                return Err(scope_incomplete(format!(
                    "closure count over predicate {:?} has a filter variable no positive sealed literal binds (unsafe existential)",
                    String::from_utf8_lossy(count.pred.pred.bytes())
                )))
            }
        }
    }
    leading_results.sort();
    leading_results.dedup();
    let mut available: Vec<Vec<crate::term::VarId>> = Vec::with_capacity(plan.binders.len());
    let mut seen: Vec<crate::term::VarId> = leading_results.clone();
    for (i, after) in bound_after.iter().enumerate() {
        seen.extend(after.iter().cloned());
        seen.extend(results_at[i].iter().cloned());
        seen.sort();
        seen.dedup();
        available.push(seen.clone());
    }
    for bl in &clause.body {
        if is_binder(bl) || bl.is_count() {
            continue;
        }
        let Some(goal) = bl.as_inner() else { continue };
        let mut vars: Vec<crate::term::VarId> = Vec::new();
        collect_vars_goal(goal, &mut vars);
        vars.sort();
        vars.dedup();
        if vars
            .iter()
            .all(|v| leading_results.binary_search(v).is_ok())
        {
            plan.leading.push(Step::Filter(bl));
            continue;
        }
        match available
            .iter()
            .position(|b| vars.iter().all(|v| b.binary_search(v).is_ok()))
        {
            Some(i) => plan.binders[i].1.push(Step::Filter(bl)),
            None => {
                return Err(scope_incomplete(format!(
                    "closure body literal on predicate {:?} has a variable no positive sealed literal binds (unsafe existential)",
                    String::from_utf8_lossy(goal.pred.bytes())
                )))
            }
        }
    }
    Ok(plan)
}

/// Join one sealed-scope clause over the sealed extensions, checking the closure obligation
/// on every tuple it emits. The two counters are the certificate's cost model, pinned across
/// the three cores: a GROUNDING is one body-true tuple the join emits; a JOIN STEP is one
/// candidate examined at one body literal — a table row offered to a binder, or the current
/// tuple offered to a filter. Both trip incrementally: `cert_budget_exceeded` the moment the
/// count exceeds `max_rule_groundings` / `max_join_steps`, or, on the checker's path,
/// `cert_decl_mismatch` (#2335) the moment it exceeds the certificate's OWN DECLARATION of them
/// (#1852). The pre-scan gate has already established
/// declared ≤ budget, so the declaration is the tighter wall, a lying declaration is caught
/// like the other three fields' are, and a scan is never paid past `min(declared, budget)`.
///
/// `verify` selects the checker's path (every emitted tuple's head is verified present in
/// `E` and in-domain, and the counters are held to the declaration) or the count-only path
/// a producer uses to DERIVE the declaration ([`closure_join_cost`]) — there the declaration
/// is not yet written, so only the budgets apply; the counters themselves are identical on
/// both.
#[allow(clippy::too_many_arguments)]
fn join_groundings(
    clause: &Clause,
    view: &CertView<'_>,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
    groundings: &mut usize,
    joins: &mut usize,
) -> Result<(), (RejectionCode, String)> {
    let plan = plan_join(clause, view, theory)?;
    let mut subst: crate::term::Subst = std::collections::BTreeMap::new();
    // What a leading count binds stays bound for the whole clause, so nothing is undone.
    let mut leading_bound: Vec<crate::term::VarId> = Vec::new();
    // #3165: the body folded so far, three-valued. A leading filter's stop is carried into every
    // tuple of the clause.
    let mut body = truth(true);
    for step in &plan.leading {
        let outcome = run_step(
            step,
            &mut subst,
            view,
            theory,
            limits,
            verify,
            joins,
            &mut leading_bound,
        )?;
        body = completion::and(body, outcome);
        if !body_continues(&body)? {
            return Ok(());
        }
    }
    join_stage(
        clause, &plan, 0, body, &mut subst, view, theory, limits, verify, groundings, joins,
    )
}

#[allow(clippy::too_many_arguments)]
fn join_stage(
    clause: &Clause,
    plan: &JoinPlan<'_>,
    stage: usize,
    body: GroundOutcome<NoCallerLimit>,
    subst: &mut crate::term::Subst,
    view: &CertView<'_>,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
    groundings: &mut usize,
    joins: &mut usize,
) -> Result<(), (RejectionCode, String)> {
    let cert = view.cert;
    let not_closed = |detail: String| (RejectionCode::CertNotClosed, detail);
    if stage == plan.binders.len() {
        // Every binder has bound and every filter has passed: one body-true tuple, or (#3165) one
        // whose body is not decided, which the counters count the same way.
        *groundings += 1;
        if *groundings > limits.max_rule_groundings {
            return Err((
                RejectionCode::CertBudgetExceeded,
                format!(
                    "counted rule_groundings {} exceeds budget {}",
                    *groundings, limits.max_rule_groundings
                ),
            ));
        }
        if !verify {
            return Ok(());
        }
        if above(*groundings, cert.limits_decl.rule_groundings) {
            return Err((
                RejectionCode::CertDeclMismatch,
                format!(
                    "actual rule_groundings {} exceeds declared {}",
                    *groundings, cert.limits_decl.rule_groundings
                ),
            ));
        }
        let Some(head) = clause.head.substitute(subst).as_ground() else {
            // §3.2 binds every head variable through a binder, so this cannot happen.
            return Err(not_closed("closure head not ground under join".into()));
        };
        // #3165: a body that is not decided holds the instance only through a present head. If
        // the head is absent (or cannot be), the instance's truth is not established: refused by
        // name, never read as closed and never as a violation.
        let undecided = match body {
            Completion::NotCompleted(cause) => Some(cause),
            Completion::Completed(_) | Completion::LimitExceeded(_) => None,
        };
        // The head's argument values must all be within the supplied domain.
        for arg in &head.args {
            if !view.in_domain(arg) {
                if let Some(cause) = undecided {
                    return Err(builtin_not_decided(cause));
                }
                return Err((
                    RejectionCode::CertOutOfDomain,
                    "satisfied grounding produces a head value outside the sealed domain".into(),
                ));
            }
        }
        return match cert.table(&head.pred) {
            Some(t) if view.contains(t, &head) => Ok(()),
            _ => Err(match undecided {
                Some(cause) => builtin_not_decided(cause),
                None => not_closed(format!(
                    "satisfied grounding of a scope rule has head {:?} absent from E",
                    String::from_utf8_lossy(head.pred.bytes())
                )),
            }),
        };
    }
    let (goal, _) = &plan.binders[stage];
    let Some(table) = view.table(&goal.pred) else {
        return Err((
            RejectionCode::CertScopeIncomplete,
            format!(
                "closure body literal on predicate {:?} is sealed by the scope but has no sealed extension (undecidable)",
                String::from_utf8_lossy(goal.pred.bytes())
            ),
        ));
    };
    // #2511: the rows that can unify, from the binder's index. Every other row is refused by
    // `bind_row` at no cost but its join step, so the rows between two candidates are charged
    // together, in table order, and the counters (and any trip) are the ones the full scan gave.
    let Some(candidates) = plan.indexes[stage].candidates(goal, table, subst) else {
        for row in &table.rows {
            count_join_step(joins, cert, limits, verify)?;
            offer_row(
                clause, plan, stage, body, row, subst, view, theory, limits, verify, groundings,
                joins,
            )?;
        }
        return Ok(());
    };
    let mut charged = 0usize;
    for &position in candidates {
        super::join_index::charge_join_steps(joins, position + 1 - charged, cert, limits, verify)?;
        charged = position + 1;
        offer_row(
            clause,
            plan,
            stage,
            body,
            &table.rows[position],
            subst,
            view,
            theory,
            limits,
            verify,
            groundings,
            joins,
        )?;
    }
    super::join_index::charge_join_steps(joins, table.rows.len() - charged, cert, limits, verify)
}

/// Offer ONE row, already charged its join step, to binder `stage`: unify, run the filters due
/// there, and join the next stage on a match, then undo what the unification bound.
#[allow(clippy::too_many_arguments)]
fn offer_row(
    clause: &Clause,
    plan: &JoinPlan<'_>,
    stage: usize,
    body: GroundOutcome<NoCallerLimit>,
    row: &GroundLiteral,
    subst: &mut crate::term::Subst,
    view: &CertView<'_>,
    theory: &dyn Theory,
    limits: &CheckLimits,
    verify: bool,
    groundings: &mut usize,
    joins: &mut usize,
) -> Result<(), (RejectionCode, String)> {
    let (goal, steps) = &plan.binders[stage];
    let mut newly: Vec<crate::term::VarId> = Vec::new();
    let matched = bind_row(goal, row, subst, &mut newly);
    let result = if matched {
        let mut pass = true;
        let mut body = body;
        for step in steps {
            // A count stage's result is recorded in `newly` too, so it is undone below.
            let outcome = run_step(step, subst, view, theory, limits, verify, joins, &mut newly)?;
            body = completion::and(body, outcome);
            if !body_continues(&body)? {
                pass = false;
                break;
            }
        }
        if pass {
            join_stage(
                clause,
                plan,
                stage + 1,
                body,
                subst,
                view,
                theory,
                limits,
                verify,
                groundings,
                joins,
            )
        } else {
            Ok(())
        }
    } else {
        Ok(())
    };
    for v in newly {
        subst.remove(&v);
    }
    result
}

/// Unify a binder's arguments against one sealed row under `subst`: a bound variable or a
/// constant must EQUAL the row's value at that position; an unbound variable is bound to it
/// (recorded in `newly` so the caller can undo it). `false` on the first mismatch.
fn bind_row(
    goal: &crate::literal::Goal,
    row: &GroundLiteral,
    subst: &mut crate::term::Subst,
    newly: &mut Vec<crate::term::VarId>,
) -> bool {
    if row.pred != goal.pred || row.args.len() != goal.args.len() {
        return false;
    }
    goal.args
        .iter()
        .zip(&row.args)
        .all(|(term, value)| unify_ground(term, &Term::from_value(value), subst, newly))
}

fn unify_ground(
    term: &Term,
    ground: &Term,
    subst: &mut crate::term::Subst,
    newly: &mut Vec<crate::term::VarId>,
) -> bool {
    // #2275 layer 3: pairs on an explicit stack, depth-first and left to right, so `newly` records
    // the variables in the order the recursion bound them, and the first mismatch is its.
    let mut work: Vec<(&Term, &Term)> = vec![(term, ground)];
    while let Some((term, ground)) = work.pop() {
        match term {
            Term::Var(v) => match subst.get(v) {
                Some(bound) => {
                    if bound != ground {
                        return false;
                    }
                }
                None => {
                    subst.insert(v.clone(), ground.clone());
                    newly.push(v.clone());
                }
            },
            Term::Atom(_) => {
                if term != ground {
                    return false;
                }
            }
            Term::Tuple(children) => match ground {
                Term::Tuple(values) if values.len() == children.len() => {
                    work.extend(children.iter().zip(values).rev());
                }
                Term::Atom(_) | Term::Tuple(_) | Term::Var(_) => return false,
            },
        }
    }
    true
}

/// Charge one join step and trip `cert_budget_exceeded` the moment the count exceeds the
/// run's budget, or, on the checker's path (`verify`), `cert_decl_mismatch` (#2335) the moment
/// it exceeds the certificate's own declared `join_steps` (#1852). The budget is tested first so
/// that at declared == budget the budget
/// wording wins; the pre-scan gate guarantees declared ≤ budget, so the declaration can only
/// be the tighter of the two, and the scan is bounded by it. The count-only path
/// ([`closure_join_cost`]) runs before the declaration is written and is held to the budget
/// alone.
pub(super) fn count_join_step(
    joins: &mut usize,
    cert: &ClosedModelCert,
    limits: &CheckLimits,
    verify: bool,
) -> Result<(), (RejectionCode, String)> {
    *joins += 1;
    if *joins > limits.max_join_steps {
        return Err((
            RejectionCode::CertBudgetExceeded,
            format!(
                "counted join_steps {} exceeds budget {}",
                *joins, limits.max_join_steps
            ),
        ));
    }
    if verify && above(*joins, cert.limits_decl.join_steps) {
        return Err((
            RejectionCode::CertDeclMismatch,
            format!(
                "actual join_steps {} exceeds declared {}",
                *joins, cert.limits_decl.join_steps
            ),
        ));
    }
    Ok(())
}

/// Verify a single `Neg { atom, cert, nonmember }` premise against the (already
/// memoized) certificate status — the per-`Neg` obligations of ADR 0007 §4:
///  1. the cited cert index is in range (`cert_out_of_range`);
///  2. the cert is `Valid` (else surface its failure code);
///  3. the negated predicate is sealed by the cert scope (`neg_atom_not_sealed`);
///  4. the negated predicate is in a STRICTLY LOWER stratum than the rule head
///     (`neg_stratum_not_lower`) — i.e. the head predicate is NOT sealed by the
///     cert's lower-stratum scope (stratified negation looks only downward);
///  5. the atom is ground + within a supplied finite domain (`neg_atom_ill_typed`);
///  6. the atom is ABSENT from the sealed table (`neg_atom_present` if present).
pub(super) fn verify_neg_premise(
    atom: &GroundLiteral,
    cert_id: CertId,
    _nonmember: NonMemberProof,
    head_pred: &Symbol,
    deriv: &Derivation,
    cert_status: &[CertStatus],
) -> Outcome {
    // 1. cert index in range: a protocol index, an offset only if it names a carried cert (#2735).
    let Some(idx) = cert_id.offset(deriv.closed_world.len()) else {
        return Outcome::reject(
            RejectionCode::CertOutOfRange,
            format!(
                "neg premise cites cert {} out of range {}",
                cert_id.index(),
                deriv.closed_world.len()
            ),
        );
    };
    let cert = &deriv.closed_world[idx];

    // 2. the cert must be Valid (reuse the memoized status).
    if let CertStatus::Invalid(code, detail) = &cert_status[idx] {
        return Outcome::Reject {
            code: *code,
            detail: detail.clone(),
        };
    }

    // 3. predicate sealed by the cert scope.
    if !cert.scope.seals(&atom.pred) {
        return Outcome::reject(
            RejectionCode::NegAtomNotSealed,
            "negated predicate is not sealed by the cited certificate",
        );
    }

    // 3b. sealed EXACTLY (ADR 0030 D2): a table in `partial_scope` is a lower bound of its
    //     least-model relation, so absence from it proves nothing — a later round could
    //     derive the atom. Sealed, but not sealed exactly, sits between "not sealed" (3)
    //     and "not lower" (4).
    if cert.is_partial(&atom.pred) {
        return Outcome::reject(
            RejectionCode::NegAtomPartial,
            "negated predicate's sealed table is marked PARTIAL (a lower bound) — absence from it proves nothing (ADR 0030 D2)",
        );
    }

    // 4. strictly lower stratum: the RULE HEAD predicate must NOT be in the cert's
    //    (lower) scope — negation may only depend on a strictly lower stratum.
    if cert.scope.seals(head_pred) {
        return Outcome::reject(
            RejectionCode::NegStratumNotLower,
            "rule head predicate is in the same (or lower) sealed stratum as the negated atom",
        );
    }

    // 5. ground + well-typed within a supplied finite domain (every argument value
    //    must lie in some domain).
    for arg in &atom.args {
        if cert.domain_containing(arg).is_none() {
            return Outcome::reject(
                RejectionCode::NegAtomIllTyped,
                "negated atom argument is outside the certificate's finite domain",
            );
        }
    }

    // 6. ABSENT from the sealed relation (else `\+` fails — the atom IS present).
    let Some(table) = cert.table(&atom.pred) else {
        // Sealed by scope (step 3) but no extension table ⇒ ill-formed cert.
        return Outcome::reject(
            RejectionCode::NegAtomNotSealed,
            "negated predicate sealed but has no extension table",
        );
    };
    if table.contains(atom) {
        return Outcome::reject(
            RejectionCode::NegAtomPresent,
            "negated atom IS present in the sealed relation",
        );
    }

    Outcome::Accept
}

/// Verify a single `Count { pred, filter, project, k, cert }` premise against the
/// (already memoized) certificate status — the per-`Count` obligations of ADR 0023 §
/// "what the checker verifies". A structural clone of [`verify_neg_premise`]: steps
/// 1–4 are identical (cert in range + `Valid`, predicate sealed, **strictly-lower
/// stratum**, filter/project well-typed in domain); step 5 swaps the membership test
/// for a counted projection — recompute `n` over the proven-exact `RelationTable` and
/// require `n == k`, else `count_mismatch`.
///
///  1. the cited cert index is in range (`cert_out_of_range`);
///  2. the cert is `Valid` (else surface its failure code) — the entire ADR-0007
///     exactness apparatus (support + closure) is REUSED unchanged; the count does not
///     re-prove it;
///  3. the counted predicate is sealed by the cert scope (`neg_atom_not_sealed`);
///  4. the counted predicate is in a STRICTLY LOWER stratum than the rule head
///     (`count_stratum_not_lower`) — a count is non-monotone, so it must read a sealed
///     lower stratum (the negation discipline applies unchanged);
///  5. `filter`/`project` are well-typed: every bound position is `< arity` and ground
///     in the cert's finite domain, and a `count_distinct` attr index is `< arity`
///     (`count_attr_out_of_range`); then recompute `n` over the table's rows applying
///     the filter (and, for `count_distinct`, project + dedup by canonical `ground_key`,
///     EXCLUDING `null()`) and require `n == k` (`count_mismatch`).
#[allow(clippy::too_many_arguments)]
pub(super) fn verify_count_premise(
    pred: &PredicateRef,
    filter: &GroundFilter,
    project: ProjectSpec,
    k: &Value,
    cert_id: CertId,
    head_pred: &Symbol,
    deriv: &Derivation,
    cert_status: &[CertStatus],
) -> Outcome {
    // 1. cert index in range: a protocol index, an offset only if it names a carried cert (#2735).
    let Some(idx) = cert_id.offset(deriv.closed_world.len()) else {
        return Outcome::reject(
            RejectionCode::CertOutOfRange,
            format!(
                "count premise cites cert {} out of range {}",
                cert_id.index(),
                deriv.closed_world.len()
            ),
        );
    };
    let cert = &deriv.closed_world[idx];

    // 2. the cert must be Valid (reuse the memoized status — support+closure already
    //    proved the sealed relation EXACT; the count does not re-prove exactness).
    if let CertStatus::Invalid(code, detail) = &cert_status[idx] {
        return Outcome::Reject {
            code: *code,
            detail: detail.clone(),
        };
    }

    // 3. predicate sealed by the cert scope (matched by name; arity is checked in 5).
    if !cert.scope.seals(&pred.pred) {
        return Outcome::reject(
            RejectionCode::NegAtomNotSealed,
            "counted predicate is not sealed by the cited certificate",
        );
    }

    // 3b. sealed EXACTLY (ADR 0030 D2): a cardinality over a lower bound is itself a lower
    //     bound, never the claimed `k` — the count twin of `neg_atom_partial`.
    if cert.is_partial(&pred.pred) {
        return Outcome::reject(
            RejectionCode::CountOverPartial,
            "counted predicate's sealed table is marked PARTIAL (a lower bound) — a count over it is a lower bound, never the claimed k (ADR 0030 D2)",
        );
    }

    // 4. strictly lower stratum: the RULE HEAD predicate must NOT be sealed by the
    //    cert's (lower) scope — a count may only depend on a strictly lower stratum.
    if cert.scope.seals(head_pred) {
        return Outcome::reject(
            RejectionCode::CountStratumNotLower,
            "rule head predicate is in the same (or lower) sealed stratum as the counted relation",
        );
    }

    // 5. recompute n over the sealed table.
    let Some(table) = cert.table(&pred.pred) else {
        // Sealed by scope (step 3) but no extension table ⇒ ill-formed cert.
        return Outcome::reject(
            RejectionCode::NegAtomNotSealed,
            "counted predicate sealed but has no extension table",
        );
    };
    let arity = table.arity as usize;

    // 5·#581 ARITY AGREEMENT. The counted relation is matched by name AND arity: a
    //     `PredicateRef` whose arity disagrees with the sealed table would otherwise
    //     count rows of a DIFFERENT-arity relation under the same name. A wrong arity is
    //     `count_attr_out_of_range` (the filter/project positions are interpreted against
    //     the claimed arity; a mismatch makes every position suspect).
    if pred.arity as usize != arity {
        return Outcome::reject(
            RejectionCode::CountAttrOutOfRange,
            format!(
                "count predicate arity {} does not match the sealed table arity {arity}",
                pred.arity
            ),
        );
    }

    // 5a. filter well-typed: each position is within arity and its value is ground +
    //     within the cert's finite domain.
    for (pos, val) in filter {
        if (*pos as usize) >= arity {
            return Outcome::reject(
                RejectionCode::CountAttrOutOfRange,
                format!("count filter position {pos} is outside predicate arity {arity}"),
            );
        }
        if cert.domain_containing(val).is_none() {
            return Outcome::reject(
                RejectionCode::NegAtomIllTyped,
                "count filter value is outside the certificate's finite domain",
            );
        }
    }

    // 5b. projection/fold attr (count_distinct / sum / min / max) within arity.
    if let Some(attr) = project.attr() {
        if (attr as usize) >= arity {
            return Outcome::reject(
                RejectionCode::CountAttrOutOfRange,
                format!("aggregate projection attr {attr} is outside predicate arity {arity}"),
            );
        }
    }

    // 5c. ONE LINEAR SCAN over the proven-exact rows, through ADR 0023's one aggregate semantics
    //     (`crate::aggregate`), the fold the producer claims `k` with and a bottom-up engine
    //     evaluates a count clause with (#2258 L3.3). The rows are already sorted+deduped by
    //     canonical bytes, so this is verification, not search.
    let recomputed = match crate::aggregate::evaluate_aggregate(
        &pred.pred,
        table.rows.iter(),
        filter,
        project,
    ) {
        Ok(n) => n,
        Err((code, detail)) => return Outcome::reject(code, detail),
    };

    // 5d. compare the recomputed fold against the claimed k (the canonical int embedding).
    let Some(claimed) = BigInt::from_int_term(&Term::from_value(k)) else {
        return Outcome::reject(
            RejectionCode::CountMismatch,
            "aggregate premise k is not a canonical int value",
        );
    };
    if recomputed != claimed {
        return Outcome::reject(
            RejectionCode::CountMismatch,
            format!(
                "claimed aggregate {} != recomputed aggregate {}",
                claimed.to_decimal_string(),
                recomputed.to_decimal_string()
            ),
        );
    }

    Outcome::Accept
}
