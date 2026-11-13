// §4 (ADR 0007) Closed-model certificate VERIFICATION — the total, non-searching `\+`
// verifier. TS sibling of the cert obligations in contract/rs/src/check.rs (the
// `verify_cert` / support / closure / EDB gates + `verify_neg_premise`). Split out of
// check.ts to keep each source file under the CI LOC ceiling.
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
//     (cert_out_of_domain), and an undecidable or inconsistent literal (a Theory disowning it after
//     owns()) refuses by name, never reads as false, so the closure cannot under-fire.
//
// Support and closure give E_s = lfp(T_s^L), so `a ∉ E_s` proves `a` absent from the stratum's
// least model: absence is sound, not an upper bound. Neither obligation needs the program to be
// constructor-acyclic: a finiteness guarantee is an admission promise that evaluation ends, and
// closure is the evidence that this table is complete.
//
// Every loop below ranges over a SUPPLIED finite table, pre-bounded by a CheckLimits cert budget
// validated BEFORE any scan. No fixpoint, no Herbrand enumeration, no engine call.

import type { OctetSource } from "./octets.js";
import { decodeUtf8Lossy } from "./utf8.js";
import { encode } from "@bitspark/ontos-codec";
import { equals as valueEquals, type Value } from "@bitspark/ontos-core";
import { encodeInt, readInt } from "@bitspark/ontos-data";

import { programDigest } from "./account.js";
import { evaluateAggregate, type AggregateResult } from "./aggregate.js";
import { CertView, type CertWorld, resolveLowerSeals, verificationOrder } from "./cert_stack.js";
import {
  type CertId,
  type CertSizeDecl,
  type ClosedModelCert,
  groundKey,
  type Hash,
  hashEquals,
  hashFromBytes,
  type SupportRef,
  zeroHash,
} from "./cert.js";
import {
  type CountPremise,
  type Derivation,
  type GroundFilterEntry,
  type NegPremise,
} from "./derivation.js";
import { certEncodedBytes } from "./derivation_wire.js";
import { captureClause } from "./native_copy.js";
import { captureCertContext, captureWorld } from "./capture.js";
import { classifySealedClause, type Outside, ScopeGraph } from "./fragment.js";
import { type GroundLiteral, type Symbol } from "./literal.js";
import { type BodyLit, type Clause, type ClauseId, type CompleteProgram, type CountLit, type PredicateRef, type Program, type ProjectSpec } from "./program.js";
import { edbTableHash, type LeafVerifier, type PredicateSet, type Theory } from "./spi.js";
import {
  and as completionAnd,
  completed,
  decisionOf,
  fails as falseDecision,
  holds as trueDecision,
  isAbsorbable,
  not as completionNot,
  type GroundOutcome,
  type NoCallerLimit,
} from "./completion.js";
import { isDisowned, readGround } from "./ground_reading.js";
import { Subst, Term, type VarId } from "./term.js";
import {
  captureCheckProfile,
  type CheckLimits,
  type CheckProfile,
  type Outcome,
  type RejectionCode,
  Verdict,
} from "./check.js";
import { Tally } from "./check_report.js";
import { certDepthsWithin, refAtom } from "./cert_depth.js";

/**
 * The four pins a closed-model certificate is sealed against (ADR 0007). A
 * `Neg`-bearing derivation's certificates are valid only for the program / profile /
 * context / theory-config they were sealed against. Mirrors Rust's `CertContext`.
 *
 * Additive: a plain `check` supplies a ZERO context; it is NEVER consulted when
 * `closedWorld` is empty, so positive behavior is byte-identical. A consumer using
 * negation derives this context from the LIVE program/profile it actually ran.
 */
export interface CertContext {
  readonly programHash: Hash;
  readonly profileHash: Hash;
  readonly ctxHash: Hash;
  readonly theoryConfigHash: Hash;
  /**
   * ADR 0029 D10 — the decomposition this run is bound to, or `undefined` for an ordinary
   * whole-program run. A slice-sealed cert is admitted only when this carries the same pin.
   */
  readonly decompositionWitness?: Hash;
}

export const CertContext = Object.freeze({
  /** An explicit context over the four pins. */
  of(programHash: OctetSource, profileHash: OctetSource, ctxHash: OctetSource, theoryConfigHash: OctetSource): CertContext {
    return {
      programHash: hashFromBytes(programHash), profileHash: hashFromBytes(profileHash),
      ctxHash: hashFromBytes(ctxHash), theoryConfigHash: hashFromBytes(theoryConfigHash),
    };
  },
  /**
   * This context bound to a decomposition witness (ADR 0029 D10). Additive and opt-in: a caller
   * that does not decompose never calls it and its context is byte-identical to the pre-D10 one.
   */
  withDecomposition(c: CertContext, witness: OctetSource): CertContext {
    const base = CertContext.of(c.programHash, c.profileHash, c.ctxHash, c.theoryConfigHash);
    return { ...base, decompositionWitness: hashFromBytes(witness) };
  },
  /**
   * The all-zero context. Supplied by the plain `check` wrapper and NEVER consulted for
   * an all-positive (`closedWorld`-empty) derivation; for a certifying check it is the
   * UNBOUND sentinel (see `isUnbound`).
   */
  zero(): CertContext {
    return { programHash: zeroHash(), profileHash: zeroHash(), ctxHash: zeroHash(), theoryConfigHash: zeroHash() };
  },
  /**
   * `true` iff every pin is all-zero — the UNBOUND sentinel (ADR 0007 §3.1). A certifying
   * check under an unbound context is hard-rejected `cert_context_unbound`.
   */
  isUnbound(c: CertContext): boolean {
    const z = zeroHash();
    return (
      hashEquals(c.programHash, z) &&
      hashEquals(c.profileHash, z) &&
      hashEquals(c.ctxHash, z) &&
      hashEquals(c.theoryConfigHash, z)
    );
  },
});

/**
 * The memoized verification status of one cited `ClosedModelCert`. Computed once, up
 * front, into an array parallel to `Derivation.closedWorld`; a `Neg` premise reuses the
 * cached result rather than re-verifying. Mirrors Rust's `CertStatus`.
 */
export type CertStatus =
  | { readonly kind: "valid" }
  | { readonly kind: "invalid"; readonly code: RejectionCode; readonly detail: string };

const VALID: CertStatus = Object.freeze({ kind: "valid" });
function invalid(code: RejectionCode, detail: string): CertStatus {
  return { kind: "invalid", code, detail };
}

/** A gate result: `undefined` on success, else a `[code, detail]` rejection. */
type GateErr = readonly [RejectionCode, string] | undefined;

/**
 * Verify a closed-model certificate CHAIN on its own, with no derivation citing it: the
 * completeness gate's certificate check (#2313, design 0008 §1.4.3). Each cert, at its place in
 * the chain, passes exactly the verification a cert cited by a `Neg` premise passes in
 * `checkWithCertContext`: the same term-depth cap on its deep data, the same context-unbound gate,
 * and the same `verifyCert`, unchanged. So no verdict of that function moves.
 *
 * The first invalid cert rejects, with its own code and a detail prefixed by its index. An EMPTY
 * chain rejects as `cert_out_of_range`, because it has no cert to seal anything. A vacuous accept
 * would certify a completeness claim that nothing backs. Mirrors Rust's `check_closed_model_chain`.
 *
 * The outcome's report (#3111) counts each certificate verified, in verification order, up to and
 * including the first invalid one. A refused configuration and an empty chain report zeros, and an
 * unbound context only the term depths it measured.
 */
export function checkClosedModelChain<C>(
  program: Program,
  chain: readonly ClosedModelCert[],
  ctx: C,
  profile: CheckProfile<C>,
  certContext: CertContext,
): Outcome {
  const tally = new Tally();
  return tally.outcome(verifyChain(program, chain, ctx, profile, certContext, tally));
}

/** `checkClosedModelChain`'s verdict, its work counted into `tally`. */
function verifyChain<C>(
  program: Program,
  chain: readonly ClosedModelCert[],
  ctx: C,
  profile: CheckProfile<C>,
  certContext: CertContext,
  tally: Tally,
): Verdict {
  const bound = captureCheckProfile(profile);
  if (!bound.ok) return Verdict.reject("invalid_check_limits", bound.error.message);
  profile = bound.value;
  const captured = captureWorld(chain, profile.limits);
  if (captured.kind === "reject") return captured;
  const certs = captured.value;
  if (certs.length === 0) {
    return Verdict.reject(
      "cert_out_of_range",
      "empty certificate chain: no closed-model certificate to verify",
    );
  }
  certContext = captureCertContext(certContext);
  const max = profile.limits.maxTermDepth;
  for (let own = 0; own < certs.length; own += 1) {
    const what = certDepthsWithin(certs[own]!, max, tally);
    if (what !== undefined) {
      return Verdict.reject(
        "term_too_deep",
        `chain cert ${own}: ${what} nests deeper than max_term_depth ${max}`,
      );
    }
  }
  if (CertContext.isUnbound(certContext)) {
    return Verdict.reject(
      "cert_context_unbound",
      "certifying check supplied an all-zero (unbound) cert context",
    );
  }
  // STACKED certificates (#2258 (a)): the chain is the world, verified in ascending scope level
  // exactly as a derivation's closed world is, so a cert that reads a lower cert's seal does so
  // only once that cert's status is final. The first invalid cert in that order rejects.
  const status: (CertStatus | undefined)[] = certs.map(() => undefined);
  const readClauses = worldClauses(program);
  for (const own of verificationOrder(certs)) {
    const verdict = verifyCert(
      certs[own]!,
      program,
      profile,
      ctx,
      certContext,
      profile.limits,
      { own, worldLen: certs.length },
      { certs, status },
      readClauses,
      tally,
    );
    if (verdict.kind === "invalid") {
      return Verdict.reject(verdict.code, `chain cert ${own}: ${verdict.detail}`);
    }
    status[own] = verdict;
  }
  return Verdict.Accept;
}

// =============================== whole-cert verifier ===============================

/**
 * Step 3a of `checkWithCertContext`: every certificate of `world` verified, into the status array
 * the forward pass reads. The statuses are a pure function of its arguments, which is what lets a
 * `WorldMemo` serve them again for an equal world under the same inputs; the calling check's `tally`
 * counts the verification's work (#3111).
 */
export function verifyWorld<C>(
  world: readonly ClosedModelCert[],
  program: Program,
  profile: CheckProfile<C>,
  ctx: C,
  certContext: CertContext,
  tally: Tally,
): CertStatus[] {
  // 3a. verify every cited certificate ONCE, up front, memoized into a parallel array. A
  //     `Neg` premise reuses the cached result. For an all-positive derivation
  //     closedWorld is empty, so this is a no-op and the zero certContext is never
  //     consulted — positive behavior is byte-identical.
  //
  //     CONTEXT-UNBOUND GATE (ADR 0007 §3.1): a certifying check needs a context DERIVED
  //     from the live program/profile. An all-zero context is the UNBOUND sentinel — if
  //     any cert is cited under it, every cert is invalid with `cert_context_unbound`.
  //
  //     STACKED certificates (#2258 (a)): certs are verified in ascending scope level, so a cert
  //     that reads a predicate from a strictly lower cert does so only once that cert's status is
  //     final (validity precedes citation).
  const contextUnbound = world.length > 0 && CertContext.isUnbound(certContext);
  const status: (CertStatus | undefined)[] = world.map(() => undefined);
  const readClauses = worldClauses(program);
  for (const own of verificationOrder(world)) {
    status[own] = contextUnbound
      ? { kind: "invalid", code: "cert_context_unbound", detail: "certifying check supplied an all-zero (unbound) cert context" }
      : verifyCert(world[own]!, program, profile, ctx, certContext, profile.limits, {
          own,
          worldLen: world.length,
        }, { certs: world, status }, readClauses, tally);
  }
  // The order covers every index, so every status is set; a gap would be a checker defect,
  // refused rather than read as Valid.
  return status.map(
    (s) => s ?? { kind: "invalid", code: "cert_scope_incomplete", detail: "certificate was never verified" },
  );
}

/**
 * Verify one certificate fully, ONCE, in the normative order
 * budget → context → partition → scope-closure → domain → support → closure → EDB
 * (ADR 0007 §3). The budget gate is first (before any scan); context is RECOMPUTED, not
 * merely compared; the scope-closure + domain gates establish the invariants that make
 * the support and closure checks sound; the EDB gate binds extensional tables to
 * the live snapshot. Mirrors Rust's `verify_cert`.
 *
 * `world` is the derivation's `closedWorld` with the statuses computed so far, in
 * `verificationOrder`: every certificate at a lower level is final, so a predicate this cert
 * reads from one is read only once that cert is known Valid (#2258 (a)). The whole-chain check owns the status table.
 */
function verifyCert<C>(
  cert: ClosedModelCert,
  program: Program,
  profile: CheckProfile<C>,
  ctx: C,
  certContext: CertContext,
  limits: CheckLimits,
  place: CertPlace,
  world: CertWorld,
  readClauses: () => readonly Clause[] | undefined,
  tally: Tally,
): CertStatus {
  // certsVerified: this certificate's verification runs, whatever status it ends in.
  tally.certsVerified += 1;
  const theory = profile.theory;
  // 1. BUDGET GATE — first, before any scan.
  let e: GateErr = checkCertBudget(cert, limits);
  if (e) return invalid(e[0], e[1]);
  // 1b. CANONICAL FORM (issue #839) — the cert's sorted-invariant collections (scope
  //     predicates, domain values, extension rows) must actually BE sorted + deduped
  //     by their canonical keys. ts scans linearly so an unsorted collection would
  //     still evaluate correctly HERE — but rs/go binary-search these collections, so
  //     a non-canonical cert is ill-formed everywhere and every core must reject it
  //     IDENTICALLY (the verdict is core-independent). Each defect carries the code
  //     the defeated rs/go search would otherwise have fabricated, with a detail
  //     naming the real cause.
  e = checkCertCanonicalForm(cert, tally);
  if (e) return invalid(e[0], e[1]);
  const clauses = readClauses();
  if (clauses === undefined) return invalid("cert_scope_incomplete", "program does not supply complete clause enumeration");
  // 1c. PARTIAL SUB-SCOPE (ADR 0030 D1) — canonical, a non-empty subset of the sealed prefix
  //     at its own level, upward-closed within it, never an extensional table. Verified
  //     before any table is consulted: a certificate is untrusted input.
  e = checkCertPartialScope(cert, clauses, profile.leaves.extensional());
  if (e) return invalid(e[0], e[1]);
  // 2. CONTEXT — recompute program_hash from the live program; require the cert pin to
  //    equal it AND all four pins to equal the caller-derived context.
  e = checkCertContext(cert, clauses, certContext);
  if (e) return invalid(e[0], e[1]);
  // 2a. PARTITION GATE — a stratum prefix holds only intensional/extensional predicates,
  //     NEVER theory-owned builtins (decided LIVE by the Theory, not sealed in a table).
  for (const pred of cert.scope.predicates) {
    if (theory.owns(pred)) {
      return invalid(
        "cert_scope_incomplete",
        `sealed scope predicate ${predDebug(pred)} is theory-owned (builtins are a separate partition, decided live — not sealable)`,
      );
    }
  }
  // 2b. STACKED READS (#2258 (a)) — every predicate a sealed clause reads without this cert
  //     sealing it resolves to the UNIQUE certificate at a strictly lower level that seals it
  //     EXACTLY and is Valid; an invalid one invalidates this cert with its own code. The inventory is shared
  //     by all certificates of this world.
  const resolved = resolveLowerSeals(cert, place.own, world, clauses, theory);
  if ("err" in resolved) return invalid(resolved.err[0], resolved.err[1]);
  const view = resolved.view;
  e = verifyGates(view, place, program, clauses, profile, ctx, limits, tally);
  // theoryDecisions: the `decideGround` calls the support and closure gates made, which the view
  // counted where they were made.
  tally.theoryDecisions += view.theoryDecisions;
  if (e) return invalid(e[0], e[1]);
  // 8. exact.
  return VALID;
}

/** Steps 3 to 7 of `verifyCert`, over the view step 2b resolved: the first gate the certificate fails. */
function verifyGates<C>(
  view: CertView,
  place: CertPlace,
  program: Program,
  clauses: readonly Clause[],
  profile: CheckProfile<C>,
  ctx: C,
  limits: CheckLimits,
  tally: Tally,
): GateErr {
  const theory = profile.theory;
  // 3. SCOPE DOWNWARD-CLOSURE — the sealed prefix must be self-contained.
  return checkScopeClauses(view, clauses, theory) ??
    // 4. DOMAIN COVERAGE — every value reachable through the cert lies in ∪domains.
    checkCertDomainCoverage(view.cert) ??
    // 5. SUPPORT — E ⊆ least model (no junk; rank-consistent strict descent).
    checkCertSupport(view, place, program, theory, profile.leaves.extensional()) ??
    // 6. CLOSURE — least model ⊆ E, driven by the TRUSTED enumerated defining clauses.
    checkCertClosure(view, clauses, theory, limits, tally) ??
    // 7. EDB BINDING — every sealed extensional predicate's table == the live EDB snapshot.
    checkCertEdb(view.cert, profile.leaves, ctx);
}

// ----------------------------- 1c partial sub-scope gate (ADR 0030) -----------------------------

/**
 * 1c. PARTIAL SUB-SCOPE (ADR 0030 D1). A cert with no `partialScope` passes untouched (every
 * pre-0030 cert, every exact seal). Otherwise the three invariants, each
 * `cert_partial_scope_invalid`: (1) p ⊆ scope, canonical, at the prefix's own level;
 * (2) upward-closed within the sealed prefix — a sealed clause whose head is COMPLETE may not
 * read (positively, or under a count) a predicate marked partial, or its closure proof would
 * be closed over E and vacuous for the rows the lower bound is missing; (3) an extensional
 * table is never partial (snapshot-bound, complete by definition). Mirrors rs
 * `check_cert_partial_scope` / go `checkCertPartialScope` — same code, same order.
 */
function checkCertPartialScope(cert: ClosedModelCert, clauses: readonly Clause[], extensional: PredicateSet): GateErr {
  const p = cert.partialScope;
  if (p === undefined) return undefined;
  const bad = (detail: string): GateErr => ["cert_partial_scope_invalid", detail];
  if (!p.isCanonical()) {
    return bad(
      "partial_scope predicates are not sorted+deduped by symbol byte order — build it via StratumPrefix.of, not a struct literal (issue #839)",
    );
  }
  if (p.predicates.length === 0) {
    return bad("partial_scope is present but names no predicate — encode an exact seal as an ABSENT partial_scope");
  }
  if (p.level !== cert.scope.level) {
    return bad(`partial_scope level ${p.level} is not the sealed prefix's level ${cert.scope.level}`);
  }
  for (const pred of p.predicates) {
    if (!cert.scope.seals(pred)) {
      return bad(`partial_scope names predicate ${predDebug(pred)} that the sealed scope does not seal`);
    }
    if (extensional.contains(pred)) {
      return bad(
        `partial_scope marks extensional predicate ${predDebug(pred)} as partial — an EDB table is snapshot-bound and complete by definition`,
      );
    }
  }
  for (const clause of clauses) {
    if (!cert.scope.seals(clause.head.pred) || cert.isPartial(clause.head.pred)) continue;
    for (const bl of clause.body) {
      // An intra-scope negation is already refused by the scope gate; a positive or counting
      // read of a lower bound is what makes a "complete" closure vacuous.
      if (bl.isNeg()) continue;
      if (cert.isPartial(bl.pred())) {
        return bad(
          `partial_scope is not upward-closed: complete sealed predicate ${predDebug(clause.head.pred)} is defined by a clause that reads partial predicate ${predDebug(bl.pred())}`,
        );
      }
    }
  }
  return undefined;
}

// ----------------------------- 1b canonical-form gate -----------------------------

/**
 * 1b. CANONICAL FORM (issue #839). Every sorted-invariant collection the cert carries
 * must actually be sorted + deduped by its canonical key. Mirrors rs
 * `check_cert_canonical_form` / go `checkCertCanonicalForm` — same codes, same order.
 *
 * `certTablesRead` / `certRowsRead` are counted here, as each table is begun: this gate is the
 * first to read a table's rows.
 */
function checkCertCanonicalForm(cert: ClosedModelCert, tally: Tally): GateErr {
  if (!cert.scope.isCanonical()) {
    return [
      "cert_scope_incomplete",
      "sealed scope predicates are not sorted+deduped by symbol byte order - build the prefix via StratumPrefix.of (issue #839)",
    ];
  }
  for (const d of cert.domains) {
    if (!d.isCanonical()) {
      return [
        "cert_out_of_domain",
        `finite domain ${predDebug(d.typeTag)} values are not sorted+deduped by canonical codec bytes, so rs/go binary-search membership is defeated - build the domain via FiniteDomain.of (issue #839)`,
      ];
    }
  }
  for (const t of cert.extensions) {
    // certTablesRead / certRowsRead: this gate begins the table and reads every row.
    tally.certTablesRead += 1;
    tally.certRowsRead += t.rows.length;
    if (!t.isCanonical()) {
      return [
        "cert_unsupported",
        `sealed table ${predDebug(t.pred)} rows are not sorted+deduped by canonical codec bytes, so rs/go binary-search membership is defeated - build the table via RelationTable.of (issue #839)`,
      ];
    }
  }
  return undefined;
}

// ------------------------------- §3.1 context gate -------------------------------

/**
 * §3.1 CONTEXT. Recompute `programHash` from the live program (a canonical digest over
 * every clause's frozen account bytes, sorted) and require the cert's pin to equal it;
 * then require the cert's four pins to equal the caller-derived `certContext`. A program
 * that cannot be enumerated (no `forEachClause`) is `cert_scope_incomplete`.
 */
function checkCertContext(cert: ClosedModelCert, clauses: readonly Clause[], certContext: CertContext): GateErr {
  // ADR 0029 D10 — WHICH CLAUSE SET DOES programHash PIN? See the rs twin in
  // contract/rs/src/check/cert.rs for the full argument; the four cases are identical.
  //
  // The downward-closure gate is deliberately NOT relaxed: checkScopeDownwardClosed walks every
  // clause of the COMPLETE program whatever this decides. That is what makes a slice seal sound —
  // only the PIN's coverage narrows.
  let recomputed: Hash;
  if (cert.decompositionWitness === undefined) {
    recomputed = programDigest(clauses);
  } else if (certContext.decompositionWitness === undefined) {
    return [
      "cert_context_mismatch",
      "certificate is sealed over a decomposition slice, but the bound check context declares no " +
        "decomposition — a slice-sealed cert cannot discharge a negation in a whole-program run (ADR 0029 D10)",
    ];
  } else if (!hashEquals(cert.decompositionWitness, certContext.decompositionWitness)) {
    return [
      "cert_context_mismatch",
      "certificate is sealed over a decomposition slice, but the bound check context names a " +
        "DIFFERENT decomposition — a slice seal is valid only under the decomposition that authorized it (ADR 0029 D10)",
    ];
  } else {
    recomputed = programDigestOverScope(clauses, cert);
  }
  if (!hashEquals(cert.programHash, recomputed)) {
    return ["cert_context_mismatch", "certificate program_hash does not match the recomputed live program"];
  }
  // The other three pins are properties of the RUN and must match in every case: a component gets
  // neither its own profile nor its own `not`.
  if (
    !hashEquals(cert.profileHash, certContext.profileHash) ||
    !hashEquals(cert.ctxHash, certContext.ctxHash) ||
    !hashEquals(cert.theoryConfigHash, certContext.theoryConfigHash)
  ) {
    return ["cert_context_mismatch", "certificate pins do not match the bound check context"];
  }
  // programHash is the ONE pin whose coverage D10 narrows, so it is compared separately. A slice
  // seal MUST NOT equal the caller's whole-program pin — requiring it would make D10 unsatisfiable,
  // since the two cover different clause sets by construction. The seal is already tied to the run
  // by the witness pins agreeing and by the slice recompute above.
  if (cert.decompositionWitness === undefined && !hashEquals(cert.programHash, certContext.programHash)) {
    return ["cert_context_mismatch", "certificate pins do not match the bound check context"];
  }
  return undefined;
}

/**
 * The canonical program digest over ONLY the clauses this cert's scope seals — ADR 0029 D10's
 * slice. Same prefix, same per-clause frozen account bytes and same sort as `programDigest`,
 * over the subset. Sibling of Go's `programDigestOverScope` and rs's
 * `recompute_program_hash_over_scope`.
 */
export function programDigestOverScope(clauses: readonly Clause[], cert: ClosedModelCert): Hash {
  return programDigest(clauses.filter((c) => cert.scope.seals(c.head.pred)));
}

/** Own each emitted clause before returning to a provider that may reuse its buffers. */
function collectClauses(program: Program): Clause[] | undefined {
  const enumerate = program.forEachClause;
  if (typeof enumerate !== "function") return undefined;
  const clauses: Clause[] = [];
  const visit = (_id: ClauseId, clause: Clause): void => { clauses.push(captureClause(clause)); };
  Reflect.apply(enumerate, program, [visit]);
  return clauses;
}

/** Resolve the inventory once for the world, after a certificate's size and form gates. */
function worldClauses(program: Program): () => readonly Clause[] | undefined {
  let read = false;
  let clauses: Clause[] | undefined;
  return () => {
    if (!read) {
      clauses = collectClauses(program);
      read = true;
    }
    return clauses;
  };
}

/** The canonical digest of every clause of a complete program, independent of traversal order. */
export function programDigestOf(program: CompleteProgram): Hash {
  const clauses = collectClauses(program);
  if (clauses === undefined) throw new TypeError("programDigestOf requires complete clause enumeration");
  return programDigest(clauses);
}

// -------------------------------- §step1 budget gate -----------------------------

/**
 * Step 1 — validate the declared sizes against the cert budgets, AND the cert's ACTUAL
 * sizes against the declaration (a lying decl is caught). All strict `>` comparisons;
 * the budget gate must pass before any scan. Mirrors Rust's `check_cert_budget`.
 */
function checkCertBudget(cert: ClosedModelCert, limits: CheckLimits): GateErr {
  const decl: CertSizeDecl = cert.limitsDecl;
  // (a) declared ≤ budget — same order as Rust (cert_bytes first). Both halves are the CALLER's
  // verify budget (#2335), and each family has its own code so the kernel's check-limit table
  // can name one kind per code: the four SIZE fields are `cert_size_exceeded`, the two CLOSURE
  // fields `cert_budget_exceeded`.
  const overSize = (name: string, got: number, max: number): GateErr =>
    ["cert_size_exceeded", `declared ${name} ${got} exceeds budget ${max}`];
  const over = (name: string, got: number, max: number): GateErr =>
    ["cert_budget_exceeded", `declared ${name} ${got} exceeds budget ${max}`];
  if (decl.certBytes > limits.maxCertBytes) return overSize("cert_bytes", decl.certBytes, limits.maxCertBytes);
  if (decl.certFacts > limits.maxCertFacts) return overSize("cert_facts", decl.certFacts, limits.maxCertFacts);
  if (decl.domainValues > limits.maxDomainValues) {
    return overSize("domain_values", decl.domainValues, limits.maxDomainValues);
  }
  if (decl.supportEdges > limits.maxSupportEdges) {
    return overSize("support_edges", decl.supportEdges, limits.maxSupportEdges);
  }
  if (decl.ruleGroundings > limits.maxRuleGroundings) {
    return over("rule_groundings", decl.ruleGroundings, limits.maxRuleGroundings);
  }
  if (decl.joinSteps > limits.maxJoinSteps) return over("join_steps", decl.joinSteps, limits.maxJoinSteps);
  // (b) actual ≤ declared (no under-declaration to slip past the budget). A cert whose actual
  // size exceeds its OWN declaration lied: the producer's fault, `cert_decl_mismatch` (#2335).
  const liar = (name: string, actual: number, d: number): GateErr =>
    ["cert_decl_mismatch", `actual ${name} ${actual} exceeds declared ${d}`];
  let actualFacts = 0;
  for (const t of cert.extensions) actualFacts += t.rows.length;
  let actualDomainValues = 0;
  for (const d of cert.domains) actualDomainValues += d.values.length;
  const actualSupportEdges = cert.supports.length;
  if (actualFacts > decl.certFacts) return liar("cert_facts", actualFacts, decl.certFacts);
  if (actualDomainValues > decl.domainValues) return liar("domain_values", actualDomainValues, decl.domainValues);
  if (actualSupportEdges > decl.supportEdges) return liar("support_edges", actualSupportEdges, decl.supportEdges);
  // #2524: the BYTES, measured on the canonical encoding, so `maxCertBytes` bounds what the
  // certificate IS, not only what it declares (declared <= budget is checked above).
  const actualBytes = certEncodedBytes(cert);
  if (actualBytes > decl.certBytes) return liar("cert_bytes", actualBytes, decl.certBytes);
  return undefined;
}

// -------------------------- §3.2 scope downward-closure --------------------------

/**
 * §3.2 SCOPE DOWNWARD-CLOSURE. For EVERY clause (whole-program) whose head is sealed by
 * the scope: it must be CONSTRUCTOR-ACYCLIC (#2759: an open compound in its head only when the
 * clause is on no dependency cycle of the scope; in a body literal freely), every
 * body literal's predicate must be sealed-by-scope OR theory-owned, an intra-prefix
 * `\+` is forbidden, and the clause must be SAFE (every variable bound by a positive
 * sealed-relation body literal). Mirrors Rust's `check_scope_downward_closed`.
 */
export function checkScopeDownwardClosed(
  view: CertView,
  program: Program,
  theory: Theory,
): readonly [RejectionCode, string] | undefined {
  const clauses = collectClauses(program);
  if (clauses === undefined) return ["cert_scope_incomplete", "program does not supply complete clause enumeration"];
  return checkScopeClauses(view, clauses, theory);
}

function checkScopeClauses(view: CertView, clauses: readonly Clause[], theory: Theory): GateErr {
  const cert = view.cert;
  // #3067 (research 0028 row A15): every gate is the contract tier's ONE classification,
  // `classifySealedClause`, which the seal plan calls too. check builds the clause's context from this
  // certificate and the lower certificates it resolved (step 2b), and the scope's dependency graph
  // from the bound program, and renders the first gate a clause fails as cert_scope_incomplete. It
  // never trusts the producer's classification. Mirrors rs.
  const ctx = view.sealContext();
  const graph = new ScopeGraph();
  for (const clause of clauses) graph.add(clause, (pred) => cert.scope.seals(pred));
  for (const clause of clauses) {
    if (!cert.scope.seals(clause.head.pred)) continue;
    const owns = (pred: Symbol): boolean => theory.owns(pred);
    const outside = classifySealedClause(clause, ctx, graph, owns, owns);
    if (outside !== undefined) return ["cert_scope_incomplete", scopeIncompleteDetail(clause, outside)];
  }
  return undefined;
}

/**
 * cert_scope_incomplete's detail for the first gate a sealed clause fails, worded as check has
 * always worded each gate. The switch is exhaustive over `Outside`: a new gate must say how it reads.
 */
function scopeIncompleteDetail(clause: Clause, outside: Outside): string {
  switch (outside.kind) {
    case "count_not_lower": {
      const why = outside.sameScope
        ? "which this same certificate seals (a count must read a strictly lower certificate, never the table under construction)"
        : "which no unique, exact, Valid strictly lower certificate seals";
      return `scope-defining clause body contains a count over predicate ${predDebug(outside.pred)}, ${why}`;
    }
    case "count_open_compound":
      return `scope-defining clause count over predicate ${predDebug(outside.pred)} contains an open compound (a Term::Tuple with a variable) term (not function-free)`;
    case "constructor_cycle":
      return `scope-defining clause head ${predDebug(clause.head.pred)} constructs an open compound (a Term::Tuple with a variable) on a dependency cycle through ${predDebug(outside.through)} (outside the constructor-acyclic fragment)`;
    case "unserved":
      return `scope-defining clause body references predicate ${predDebug(outside.pred)} that is neither sealed nor theory-owned, nor sealed by a strictly lower certificate`;
    case "intra_scope_negation":
      return `scope-defining clause negates predicate ${predDebug(outside.pred)} sealed by this same prefix (intra-scope negation)`;
    case "unbound_count_filter":
      return `scope-defining clause count over predicate ${predDebug(outside.pred)} has filter variable "${outside.var.asStr()}" not bound by any positive sealed-relation body literal (range-restriction)`;
    case "unbound_variable":
      return `scope-defining clause has unsafe variable "${outside.var.asStr()}": not bound by any positive sealed-relation body literal (range-restriction)`;
    default: {
      const unhandled: never = outside;
      throw new Error(`scopeIncompleteDetail: an Outside with no wording: ${JSON.stringify(unhandled)}`);
    }
  }
}

function collectVarsGoal(goal: import("./literal.js").Goal, out: VarId[]): void {
  for (const t of goal.args) collectVarsTerm(t, out);
}

// Non-recursive (#2366): an explicit stack, children pushed in reverse so the variables
// come out in the same left-to-right order the recursive walk gave.
function collectVarsTerm(term: Term, out: VarId[]): void {
  const work: Term[] = [term];
  while (work.length > 0) {
    const t = work.pop()!;
    if (t.kind === "var") {
      out.push(t.id());
    } else if (t.kind === "tuple") {
      const children = t.children();
      for (let i = children.length - 1; i >= 0; i -= 1) work.push(children[i]!);
    }
  }
}

// ------------------------------- §3.4 domain coverage -----------------------------

/**
 * §3.4 DOMAIN COVERAGE. Every value the cert can introduce — every extension row arg,
 * every support-ref atom/fact arg, and every value in every edge.subst image — MUST lie
 * in ∪domains, else `cert_out_of_domain`. A non-ground subst image is `cert_unsupported`.
 * Mirrors Rust's `check_cert_domain_coverage`.
 */
function checkCertDomainCoverage(cert: ClosedModelCert): GateErr {
  const oob = (what: string): GateErr => [
    "cert_out_of_domain",
    `${what} carries a value outside the certificate's finite domains`,
  ];
  const checkVal = (v: Value): boolean => cert.domainContaining(v) !== undefined;
  const checkGround = (g: GroundLiteral): boolean => g.args.every(checkVal);

  for (const table of cert.extensions) {
    for (const fact of table.rows) {
      if (!checkGround(fact)) return oob("a sealed extension row");
    }
  }
  for (const edge of cert.supports) {
    for (const term of edge.subst.values()) {
      const v = Term.eraseGround(term);
      if (v === undefined) return ["cert_unsupported", "support edge subst image is not ground"];
      if (!checkVal(v)) return oob("a support edge subst image");
    }
    if (!checkGround(edge.fact)) return oob("a support edge fact");
    for (const ref of edge.bodyRefs) {
      const atom = refAtom(ref);
      if (atom === undefined) continue; // #2258 L3.3b: a count ref carries no atom; its values are the subst's.
      if (!checkGround(atom)) return oob("a support ref atom");
    }
  }
  return undefined;
}

// ----------------------------------- §3.5 support ---------------------------------

/**
 * §3.5 SUPPORT: every sealed IDB fact has a support edge (E ⊆ least model). Extensional
 * (EDB) facts are exempt — they are the well-founded base case, vouched by the §3.6 EDB
 * snapshot gate. Mirrors Rust's `check_cert_support`.
 */
function checkCertSupport(
  view: CertView,
  place: CertPlace,
  program: Program,
  theory: Theory,
  extensional: PredicateSet,
): GateErr {
  const cert = view.cert;
  const unsupported = (detail: string): GateErr => ["cert_unsupported", detail];

  // §3.5 RANK CONSISTENCY pre-pass: pin each fact's support rank to the rank on its OWN
  // edge; a fact with two edges carrying DIFFERENT ranks is ill-formed.
  const factEdgeRank = new Map<string, number>();
  for (const edge of cert.supports) {
    const key = bytesHex(groundKey(edge.fact));
    const existing = factEdgeRank.get(key);
    if (existing !== undefined && existing !== edge.rank) {
      return unsupported(
        `fact ${predDebug(edge.fact.pred)} has inconsistent edge ranks ${existing} and ${edge.rank}`,
      );
    }
    factEdgeRank.set(key, edge.rank);
  }

  const covered = new Set<string>();
  for (const edge of cert.supports) {
    if (!cert.scope.seals(edge.fact.pred)) {
      return unsupported(`support edge fact predicate ${predDebug(edge.fact.pred)} is not sealed by the cert scope`);
    }
    const table = cert.table(edge.fact.pred);
    if (table === undefined) return unsupported("support edge fact has no sealed extension");
    if (!table.contains(edge.fact)) return unsupported("support edge fact absent from its sealed table");
    const clause = program.clause(edge.clause);
    if (clause === undefined) return unsupported(`support edge cites unknown clause "${edge.clause.asStr()}"`);
    const head = clause.head.substitute(edge.subst).asGround();
    if (head === undefined) return unsupported("support clause head not ground under subst");
    if (!head.equals(edge.fact)) return unsupported("support clause head != supported fact");
    if (edge.bodyRefs.length !== clause.body.length) {
      return unsupported(
        `support edge has ${edge.bodyRefs.length} body refs != clause body length ${clause.body.length}`,
      );
    }
    for (let k = 0; k < clause.body.length; k += 1) {
      const bodyLit = clause.body[k]!;
      const bodyRef = edge.bodyRefs[k]!;
      // #2258 L3.3b: a count body literal is resolved by a count_lower ref against the strictly
      // lower certificate it reads (the scope gate admitted it only over such a table).
      if (bodyLit.isCount()) {
        if (bodyRef.kind !== "count_lower") {
          return unsupported(`support body ref ${k} kind does not match body literal polarity (a count needs a CountLower ref)`);
        }
        const err = resolveCountLower(k, bodyLit.countLit!, bodyRef.cert, edge.subst, view, place);
        if (err) return err;
        continue;
      }
      const grounded = bodyLit.substitute(edge.subst).asInner()?.asGround();
      if (grounded === undefined) return unsupported(`support body literal ${k} not ground under subst`);
      const err = resolveSupportRef(k, bodyLit, bodyRef, grounded, edge.rank, view, place, theory, factEdgeRank, extensional);
      if (err) return err;
    }
    covered.add(bytesHex(groundKey(edge.fact)));
  }

  // No junk: every IDB fact in every extension must be covered. EDB facts are exempt.
  for (const table of cert.extensions) {
    if (extensional.contains(table.pred)) continue;
    for (const fact of table.rows) {
      if (!covered.has(bytesHex(groundKey(fact)))) {
        return unsupported(`sealed fact ${predDebug(fact.pred)} has no support edge (junk / unfounded)`);
      }
    }
  }
  return undefined;
}

/**
 * Resolve one body reference of a support edge, enforcing the polarity match with the
 * body literal and the rank-consistent strict same-stratum descent (§3.5). Mirrors
 * Rust's `resolve_support_ref`.
 */
function resolveSupportRef(
  k: number,
  bodyLit: BodyLit,
  bodyRef: SupportRef,
  grounded: GroundLiteral,
  factRank: number,
  view: CertView,
  place: CertPlace,
  theory: Theory,
  factEdgeRank: Map<string, number>,
  extensional: PredicateSet,
): GateErr {
  const cert = view.cert;
  const unsupported = (detail: string): GateErr => ["cert_unsupported", detail];
  const pos = !bodyLit.isNeg();

  if (pos && bodyRef.kind === "same_stratum") {
    if (!bodyRef.fact.equals(grounded)) return unsupported(`support body ref ${k} fact != grounded body literal`);
    if (bodyRef.rank >= factRank) {
      return unsupported(`support body ref ${k} rank ${bodyRef.rank} not strictly < fact rank ${factRank} (unfounded)`);
    }
    const depKey = bytesHex(groundKey(bodyRef.fact));
    const actual = factEdgeRank.get(depKey);
    if (actual === undefined) {
      return unsupported(`support body ref ${k} same-stratum dep has no support edge (cannot anchor rank)`);
    }
    if (actual !== bodyRef.rank) {
      return unsupported(
        `support body ref ${k} claims rank ${bodyRef.rank} but dep is supported at rank ${actual} (fabricated rank)`,
      );
    }
    const t = cert.table(bodyRef.fact.pred);
    if (t !== undefined && t.contains(bodyRef.fact)) return undefined;
    return unsupported(`same-stratum dep ${k} absent from its sealed table`);
  }

  if (pos && bodyRef.kind === "lower_stratum") {
    const cited = checkSupportRefCert(k, bodyRef.cert, bodyRef.atom.pred, view, place);
    if ("err" in cited) return cited.err;
    if (!bodyRef.atom.equals(grounded)) return unsupported(`support body ref ${k} lower atom != grounded body literal`);
    // #2258 (a): a strictly lower certificate is exact on its own (verified first), so a positive
    // dependency on one of its IDB facts needs no rank anchor here.
    if (cited.lower !== undefined) {
      if (cited.lower.table.contains(bodyRef.atom)) return undefined;
      return unsupported(`lower-stratum dep ${k} absent from certificate ${cited.lower.index}'s sealed table`);
    }
    // INTRA-PREFIX BAN: a LowerStratum ref to a sealed INTENSIONAL predicate is illegal.
    if (cert.scope.seals(bodyRef.atom.pred) && !extensional.contains(bodyRef.atom.pred)) {
      return unsupported(
        `support body ref ${k}: intra-prefix positive dependency on sealed intensional predicate ${predDebug(bodyRef.atom.pred)} must be cited as SameStratum with strict rank descent, not LowerStratum`,
      );
    }
    const t = cert.table(bodyRef.atom.pred);
    if (t !== undefined && t.contains(bodyRef.atom)) return undefined;
    return unsupported(`lower-stratum dep ${k} absent from the sealed table`);
  }

  if (pos && bodyRef.kind === "builtin") {
    if (!bodyRef.atom.equals(grounded)) return unsupported(`support body ref ${k} builtin atom != grounded body literal`);
    if (!theory.owns(bodyRef.atom.pred)) return unsupported(`support builtin ref ${k} predicate not theory-owned`);
    // A stop is refused by name (#3126), never read as the literal's truth.
    // theoryDecisions: one `decideGround` call, counted on the view.
    view.countDecision();
    const verdict = readGround(theory.decideGround(bodyRef.atom));
    if (verdict.arm === "holds") return undefined;
    if (verdict.arm === "not_decided" && !isDisowned(verdict)) return ["builtin_not_decided", verdict.cause.kind];
    return unsupported(`support builtin ref ${k} does not hold`);
  }

  if (!pos && bodyRef.kind === "neg_lower") {
    const cited = checkSupportRefCert(k, bodyRef.cert, bodyRef.atom.pred, view, place);
    if ("err" in cited) return cited.err;
    if (!bodyRef.atom.equals(grounded)) return unsupported(`support body ref ${k} neg-lower atom != grounded body literal`);
    if (cited.lower !== undefined) {
      if (!cited.lower.table.contains(bodyRef.atom)) return undefined;
      return unsupported(`neg-lower dep ${k} is PRESENT in certificate ${cited.lower.index}'s sealed table (negation fails)`);
    }
    if (cert.scope.seals(bodyRef.atom.pred)) {
      return unsupported(
        `support body ref ${k}: NegLower negated dependency on sealed predicate ${predDebug(bodyRef.atom.pred)} is intra-prefix (negation must target a strictly-lower, separately-sealed stratum)`,
      );
    }
    const t = cert.table(bodyRef.atom.pred);
    if (t === undefined) return unsupported(`neg-lower dep ${k} predicate is not sealed`);
    if (!t.contains(bodyRef.atom)) return undefined;
    return unsupported(`neg-lower dep ${k} is PRESENT in the sealed table (negation fails)`);
  }

  return unsupported(`support body ref ${k} kind does not match body literal polarity`);
}

/**
 * Where a certificate sits in its derivation's `closedWorld`: its own index and the world's
 * length. A lower-stratum support ref names a cert index, and #2258 C3 checks it against this.
 * Mirrors Rust's `CertPlace`.
 */
interface CertPlace {
  readonly own: number;
  readonly worldLen: number;
}

/**
 * #2258: the cert index a `lower_stratum` / `neg_lower` support ref names must be one this checker
 * can honour. An index outside `closedWorld` is `cert_out_of_range`, as for a `Neg` premise (C3).
 * The ref's OWN cert resolves against its own tables, as it always has (`lower` undefined). Any
 * other index must be the certificate the ref's predicate RESOLVED to (#2258 (a)): the unique,
 * exact, Valid certificate at a strictly lower level that seals it, whose table is returned.
 * Validity precedes citation because statuses are computed in level order before support runs.
 * Anything else is `cert_unsupported`. Mirrors Rust.
 */
function checkSupportRefCert(
  k: number,
  cited: CertId,
  pred: Symbol,
  view: CertView,
  place: CertPlace,
):
  | { readonly lower: { readonly index: number; readonly table: import("./cert.js").RelationTable } | undefined }
  | { readonly err: readonly [RejectionCode, string] } {
  if (cited < 0 || cited >= place.worldLen) {
    return { err: ["cert_out_of_range", `support body ref ${k} cites cert ${cited} out of range ${place.worldLen}`] };
  }
  if (cited === place.own) return { lower: undefined };
  const table = view.table(pred);
  if (view.lowerIndex(pred) === cited && table !== undefined) return { lower: { index: cited, table } };
  return {
    err: [
      "cert_unsupported",
      `support body ref ${k} cites cert ${cited}, which is neither its own cert ${place.own} nor the unique exact certificate at a strictly lower level sealing ${predDebug(pred)} (#2258 (a))`,
    ],
  };
}

// ----------------------------------- §3.3 closure ---------------------------------

/**
 * §3.3 CLOSURE: least model ⊆ E, by a checker JOIN over the sealed extensions of the TRUSTED
 * defining-clause set (#1829). For EVERY clause in the whole program whose head is sealed by
 * `cert.scope`, join its positive sealed body literals over their sealed tables; every tuple
 * the join emits is a grounding whose body is true against `E` (+ the pinned Theory), so its
 * head MUST be present in `E`, else `cert_not_closed`. A satisfied grounding whose head value
 * escapes the domain is `cert_out_of_domain`.
 *
 * WHY A JOIN DEMANDS EXACTLY WHAT THE ENUMERATION DEMANDED. The self-enumeration this replaced
 * visited `|∪domains|^vars` groundings per clause and evaluated the body at each. Two gates
 * that run BEFORE closure make the join's obligation set equal to that one: §3.2's SAFETY gate
 * (`checkScopeDownwardClosed`) — every variable of a sealed-head clause occurs in a positive
 * body literal whose predicate is sealed and not theory-owned, so the join binds every
 * variable and every theory or negated literal reaches a point at which it is ground; and
 * §3.4's DOMAIN COVERAGE (`checkCertDomainCoverage`) — every sealed-table value lies in
 * ∪domains, so every tuple the join emits is a point of the enumeration's own space. A
 * grounding the enumeration would have found satisfied has, for each positive sealed literal,
 * a row of that literal's table matching it — exactly a tuple the join emits. Neither
 * direction under-fires. Mirrors Rust's `check_cert_closure`.
 */
function checkCertClosure(
  view: CertView,
  clauses: readonly Clause[],
  theory: Theory,
  limits: CheckLimits,
  tally: Tally,
): GateErr {
  const cert = view.cert;
  const counters = { groundings: 0, joins: 0 };
  let err: GateErr;
  for (const clause of clauses) {
    if (!cert.scope.seals(clause.head.pred)) continue;
    // ADR 0030 D2: closure is NOT verified for a table the cert marks partial — it is a
    // lower bound by declaration, and 1c has already refused any complete table that
    // reads it. Support (step 5) is verified for its rows exactly as for an exact seal.
    if (cert.isPartial(clause.head.pred)) continue;
    err = joinGroundings(clause, view, theory, limits, counters);
    if (err) break;
  }
  // joinStepsUsed / groundingsEnumerated: what this closure spent against its two budget meters,
  // as they stand when it ends (a tripped meter at the count it tripped at).
  tally.joinStepsUsed += counters.joins;
  tally.groundingsEnumerated += counters.groundings;
  return err;
}

/**
 * The join plan of ONE sealed-scope clause (#1829). The order is pinned — identically in the
 * three cores, because the join-step count depends on it:
 *
 *  - a POSITIVE body literal whose predicate is sealed by the scope and not theory-owned is a
 *    BINDER: it is iterated over its sealed extension, in declared order, unifying on a
 *    repeated variable (`runs(R, R)` binds `R` on the first occurrence and filters on the
 *    second);
 *  - a COUNT over a strictly lower certificate's relation (#2258 L3.3b) is a COUNT STAGE, due at
 *    the FIRST point its filter's variables are bound: before any binder if the filter is ground,
 *    else right after the binder that binds the last of them. It binds its result variable (or
 *    tests it, if already bound), and costs one join step per lower row it scans;
 *  - every other literal — a theory literal of either polarity, or a negated sealed literal
 *    (unreachable past §3.2's intra-scope gate, evaluated soundly if met) — is a FILTER,
 *    evaluated at the FIRST point all its variables are bound: before any binder if it is
 *    ground or reads only the results of counts due there, else right after the binder whose
 *    point first binds the last of them (a count due at a point binds its result there).
 *
 * At each point the count stages run first, in declared order, then the filters, in declared
 * order. A count-free clause's plan is exactly what it was before counts were admitted.
 *
 * §3.2's safety gate guarantees that point exists for every filter and that the head is
 * ground once every binder has bound; a clause that reaches here without that property is
 * refused `cert_scope_incomplete` rather than enumerated over anything. Mirrors Rust's
 * `JoinPlan` / `plan_join`.
 */
interface JoinPlan {
  /**
   * The steps due before any row is examined: counts over a ground filter, then filters that
   * are ground as written or read only those counts' results.
   */
  readonly leading: JoinStep[];
  /** The binders in declared order. */
  readonly binders: import("./literal.js").Goal[];
  /** `steps[i]` — the steps due once `binders[i]` has bound. */
  readonly steps: JoinStep[][];
}

/**
 * One step of a closure join that is not a binder: a filter literal, or (#2258 L3.3b) a count
 * over a strictly lower certificate's relation.
 */
type JoinStep = { readonly kind: "filter"; readonly lit: BodyLit } | { readonly kind: "count"; readonly count: CountLit };

type PlanResult = { readonly plan: JoinPlan } | { readonly err: readonly [RejectionCode, string] };

function planJoin(clause: Clause, view: CertView, theory: Theory): PlanResult {
  // A positive literal on a predicate this cert seals (and no theory owns), or reads from a
  // strictly lower certificate (#2258 (a)), is a BINDER over that sealed table.
  const isBinder = (bl: BodyLit): boolean => {
    if (bl.isNeg()) return false;
    const g = bl.asInner();
    return g !== null && ((view.cert.scope.seals(g.pred) && !theory.owns(g.pred)) || view.readsLower(g.pred));
  };
  const plan: JoinPlan = { leading: [], binders: [], steps: [] };
  // The variables bound once binder `i` has bound: the cumulative set, in declared order.
  const boundAfter: Set<string>[] = [];
  const bound = new Set<string>();
  for (const bl of clause.body) {
    // A count is not a binder: it is a count stage, placed below (#2258 L3.3b).
    if (!isBinder(bl)) continue;
    const g = bl.asInner()!;
    const vars: VarId[] = [];
    collectVarsGoal(g, vars);
    for (const v of vars) bound.add(v.asStr());
    boundAfter.push(new Set(bound));
    plan.binders.push(g);
    plan.steps.push([]);
  }
  // #2258 L3.3b: each count stage at the first point its filter is bound, and the results it
  // binds there. available[i] is then everything bound once point i has run.
  const leadingResults = new Set<string>();
  const resultsAt: Set<string>[] = plan.binders.map(() => new Set<string>());
  for (const bl of clause.body) {
    if (!bl.isCount()) continue;
    const count = bl.countLit!;
    const vars: VarId[] = [];
    for (const e of count.filter) collectVarsTerm(e.term, vars);
    const results: VarId[] = [];
    collectVarsTerm(count.count, results);
    if (vars.length === 0) {
      plan.leading.push({ kind: "count", count });
      for (const v of results) leadingResults.add(v.asStr());
      continue;
    }
    const at = boundAfter.findIndex((b) => vars.every((v) => b.has(v.asStr())));
    if (at < 0) {
      return {
        err: [
          "cert_scope_incomplete",
          `closure count over predicate ${predDebug(count.pred.pred)} has a filter variable no positive sealed literal binds (unsafe existential)`,
        ],
      };
    }
    plan.steps[at]!.push({ kind: "count", count });
    for (const v of results) resultsAt[at]!.add(v.asStr());
  }
  const available: Set<string>[] = [];
  const seen = new Set<string>(leadingResults);
  for (let i = 0; i < plan.binders.length; i += 1) {
    for (const v of boundAfter[i]!) seen.add(v);
    for (const v of resultsAt[i]!) seen.add(v);
    available.push(new Set(seen));
  }
  for (const bl of clause.body) {
    if (isBinder(bl) || bl.isCount()) continue;
    const g = bl.asInner();
    if (g === null) continue;
    const vars: VarId[] = [];
    collectVarsGoal(g, vars);
    if (vars.every((v) => leadingResults.has(v.asStr()))) {
      plan.leading.push({ kind: "filter", lit: bl });
      continue;
    }
    const at = available.findIndex((b) => vars.every((v) => b.has(v.asStr())));
    if (at < 0) {
      return {
        err: [
          "cert_scope_incomplete",
          `closure body literal on predicate ${predDebug(g.pred)} has a variable no positive sealed literal binds (unsafe existential)`,
        ],
      };
    }
    plan.steps[at]!.push({ kind: "filter", lit: bl });
  }
  return { plan };
}

/**
 * Join one sealed-scope clause over the sealed extensions, checking the closure obligation on
 * every tuple it emits. The two counters are the certificate's cost model, pinned across the
 * three cores: a GROUNDING is one body-true tuple the join emits; a JOIN STEP is one candidate
 * examined at one body literal — a table row offered to a binder, or the current tuple
 * offered to a filter. Both trip incrementally: `cert_budget_exceeded` the moment the count
 * exceeds `maxRuleGroundings` / `maxJoinSteps`, or `cert_decl_mismatch` (#2335) the moment it
 * exceeds the certificate's OWN DECLARATION of them (#1852). The pre-scan gate has already
 * established declared ≤ budget, so the
 * declaration is the tighter wall, a lying declaration is caught like the other three
 * fields' are, and a scan is never paid past min(declared, budget). Mirrors Rust's
 * `join_groundings`.
 */
export function joinGroundings(
  clause: Clause,
  view: CertView,
  theory: Theory,
  limits: CheckLimits,
  counters: JoinCounters,
): readonly [RejectionCode, string] | undefined {
  const planned = planJoin(clause, view, theory);
  if ("err" in planned) return planned.err;
  const plan = planned.plan;
  const subst = new Subst();
  // What a leading count binds stays bound for the whole clause, so nothing is undone.
  const leadingBound: VarId[] = [];
  // #3165: the body folded so far, three-valued. A leading filter's stop is carried into every
  // tuple of the clause.
  let body = truthOf(true);
  for (const step of plan.leading) {
    const r = runStep(step, subst, view, theory, limits, counters, leadingBound);
    if ("err" in r) return r.err;
    body = completionAnd(body, r.truth);
    const cont = bodyContinues(body);
    if ("err" in cont) return cont.err;
    if (!cont.ok) return undefined;
  }
  return joinStage(clause, plan, 0, body, subst, view, theory, limits, counters);
}

/**
 * The join's two counters, and (P9 I5a, ADR 0031 D5) an optional recorder: when set, each grounding
 * the join emits is handed to it, with whether its body is decided, and no head is verified (rs
 * `join_groundings` with `verify = false`). Without one, the boolean path is unchanged.
 */
export interface JoinCounters {
  groundings: number;
  joins: number;
  record?: (subst: Subst, decided: boolean) => void;
}

function joinStage(
  clause: Clause,
  plan: JoinPlan,
  stage: number,
  body: ClosureTruth,
  subst: Subst,
  view: CertView,
  theory: Theory,
  limits: CheckLimits,
  counters: JoinCounters,
): GateErr {
  const cert = view.cert;
  if (stage === plan.binders.length) {
    // Every binder has bound and every filter has passed: one body-true tuple, or (#3165) one whose
    // body is not decided, which the counters count the same way.
    counters.groundings += 1;
    if (counters.groundings > limits.maxRuleGroundings) {
      return [
        "cert_budget_exceeded",
        `counted rule_groundings ${counters.groundings} exceeds budget ${limits.maxRuleGroundings}`,
      ];
    }
    if (counters.record !== undefined) {
      counters.record(subst, body.kind !== "not_completed");
      return undefined;
    }
    if (counters.groundings > cert.limitsDecl.ruleGroundings) {
      return [
        "cert_decl_mismatch",
        `actual rule_groundings ${counters.groundings} exceeds declared ${cert.limitsDecl.ruleGroundings}`,
      ];
    }
    const head = clause.head.substitute(subst).asGround();
    // §3.2 binds every head variable through a binder, so this cannot happen.
    if (head === undefined) return ["cert_not_closed", "closure head not ground under join"];
    // #3165: a body that is not decided holds the instance only through a present head. If the head
    // is absent (or cannot be), the instance's truth is not established: refused by name, never
    // read as closed and never as a violation.
    const undecided = body.kind === "not_completed" ? body.cause.kind : undefined;
    for (const arg of head.args) {
      if (cert.domainContaining(arg) === undefined) {
        if (undecided !== undefined) return ["builtin_not_decided", undecided];
        return ["cert_out_of_domain", "satisfied grounding produces a head value outside the sealed domain"];
      }
    }
    const t = cert.table(head.pred);
    if (t === undefined || !t.contains(head)) {
      if (undecided !== undefined) return ["builtin_not_decided", undecided];
      return ["cert_not_closed", `satisfied grounding of a scope rule has head ${predDebug(head.pred)} absent from E`];
    }
    return undefined;
  }
  const goal = plan.binders[stage]!;
  const table = view.table(goal.pred);
  if (table === undefined) {
    return [
      "cert_scope_incomplete",
      `closure body literal on predicate ${predDebug(goal.pred)} is sealed by the scope but has no sealed extension (undecidable)`,
    ];
  }
  for (const row of table.rows) {
    const stepped = countJoinStep(counters, cert, limits);
    if (stepped !== undefined) return stepped;
    const newly: VarId[] = [];
    let result: GateErr = undefined;
    if (bindRow(goal, row, subst, newly)) {
      let pass = true;
      let tuple = body;
      for (const step of plan.steps[stage]!) {
        // A count stage's result is recorded in newly too, so it is undone below.
        const r = runStep(step, subst, view, theory, limits, counters, newly);
        if ("err" in r) {
          result = r.err;
          break;
        }
        tuple = completionAnd(tuple, r.truth);
        const cont = bodyContinues(tuple);
        if ("err" in cont) {
          result = cont.err;
          break;
        }
        if (!cont.ok) {
          pass = false;
          break;
        }
      }
      if (result === undefined && pass) {
        result = joinStage(clause, plan, stage + 1, tuple, subst, view, theory, limits, counters);
      }
    }
    for (const v of newly) subst.delete(v);
    if (result !== undefined) return result;
  }
  return undefined;
}

/**
 * Unify a binder's arguments against one sealed row under `subst`: a bound variable or a
 * constant must EQUAL the row's value at that position; an unbound variable is bound to it
 * (recorded in `newly` so the caller can undo it). `false` on the first mismatch.
 */
function bindRow(
  goal: import("./literal.js").Goal,
  row: GroundLiteral,
  subst: Subst,
  newly: VarId[],
): boolean {
  if (!row.pred.equals(goal.pred) || row.args.length !== goal.args.length) return false;
  for (let i = 0; i < goal.args.length; i += 1) {
    if (!unifyGround(goal.args[i]!, Term.fromValue(row.args[i]!), subst, newly)) return false;
  }
  return true;
}

function unifyGround(term: Term, ground: Term, subst: Subst, newly: VarId[]): boolean {
  switch (term.kind) {
    case "var": {
      const key = term.id();
      const bound = subst.get(key);
      if (bound !== undefined) return bound.equals(ground);
      subst.set(key, ground);
      newly.push(key);
      return true;
    }
    case "atom":
      return term.equals(ground);
    case "tuple": {
      if (ground.kind !== "tuple") return false;
      const children = term.children();
      const values = ground.children();
      if (children.length !== values.length) return false;
      for (let i = 0; i < children.length; i += 1) {
        if (!unifyGround(children[i]!, values[i]!, subst, newly)) return false;
      }
      return true;
    }
  }
}

/** The result of evaluating a body literal: a boolean truth, or a hard error. */
type BodyResult = { readonly ok: boolean } | { readonly err: readonly [RejectionCode, string] };

/** #3165: a closure literal's, or a body's, three-valued truth, in the completion algebra. */
type ClosureTruth = GroundOutcome<NoCallerLimit>;

/** A filter's or a step's three-valued truth, or the refusal that stops the closure. */
type TruthResult = { readonly truth: ClosureTruth } | { readonly err: readonly [RejectionCode, string] };

/** A decided truth value in the completion algebra. */
function truthOf(holds: boolean): ClosureTruth {
  return completed(holds ? trueDecision : falseDecision("unsatisfied"));
}

/**
 * #3165: what a tuple's body, folded so far with `and`, lets the join do. `{ok:false}` prunes the
 * tuple: a decided false makes the rule instance hold whatever the head, and it absorbs a
 * literal-scoped stop (F ∧ U = F). `{ok:true}` continues, the body true so far or not decided at a
 * scope another literal's false may still absorb. A stop no false can absorb is refused at once
 * (`builtin_not_decided`): the instance's truth cannot be established.
 *
 * The join prunes at the FIRST decided false and evaluates nothing after it, as its pinned cost
 * model requires, so a stop in a later literal is never seen. That is sound: the false is a
 * completed decision, and the instance it falsifies holds whatever the later literal is. Rust's
 * `body_continues`.
 */
function bodyContinues(body: ClosureTruth): BodyResult {
  switch (body.kind) {
    case "completed":
      return { ok: body.value.kind === "holds" };
    case "not_completed": {
      const cause = body.cause;
      if ("scope" in cause && isAbsorbable(cause.scope)) return { ok: true };
      return { err: ["builtin_not_decided", cause.kind] };
    }
    case "limit_exceeded":
      // No caller's limit reaches a theory (`NoCallerLimit` is `never`), so a limit here is a value
      // nobody could build: the fault `malformed_outcome`, refused by name.
      return { err: ["builtin_not_decided", "malformed_outcome"] };
    default: {
      const unhandled: never = body;
      throw new Error(`cert_check: a closure truth of no known kind: ${JSON.stringify(unhandled)}`);
    }
  }
}

/**
 * Charge one join step and trip `cert_budget_exceeded` the moment the count exceeds the run's
 * budget, or, past that, `cert_decl_mismatch` (#2335) the moment it exceeds the certificate's
 * own declared `joinSteps` (#1852). The budget is
 * tested first so that at declared == budget the budget wording wins; the pre-scan gate
 * guarantees declared ≤ budget, so the declaration can only be the tighter of the two, and the
 * scan is bounded by it. Mirrors Rust's `count_join_step`.
 */
function countJoinStep(
  counters: { joins: number },
  cert: ClosedModelCert,
  limits: CheckLimits,
): GateErr {
  counters.joins += 1;
  if (counters.joins > limits.maxJoinSteps) {
    return ["cert_budget_exceeded", `counted join_steps ${counters.joins} exceeds budget ${limits.maxJoinSteps}`];
  }
  if (counters.joins > cert.limitsDecl.joinSteps) {
    return ["cert_decl_mismatch", `actual join_steps ${counters.joins} exceeds declared ${cert.limitsDecl.joinSteps}`];
  }
  return undefined;
}

/**
 * Evaluate one FILTER literal at its evaluation point: it must be ground there (§3.2), and is
 * decided against `E` (+ the pinned Theory) with polarity by `evalBodyLiteral`. Costs one join
 * step. Never a silent false: a literal that is not ground at its point is a HARD error
 * (`cert_scope_incomplete`), the same backstop the enumeration carried. Mirrors Rust's
 * `filter_true`.
 */
function filterOutcome(
  bodyLit: BodyLit,
  subst: Subst,
  view: CertView,
  theory: Theory,
  limits: CheckLimits,
  counters: { joins: number },
): TruthResult {
  const stepped = countJoinStep(counters, view.cert, limits);
  if (stepped !== undefined) return { err: stepped };
  const grounded = bodyLit.substitute(subst).asInner()?.asGround();
  if (grounded === undefined) {
    return {
      err: [
        "cert_scope_incomplete",
        `closure body literal on predicate ${predDebug(bodyLit.pred())} is not ground at its evaluation point (unsafe existential)`,
      ],
    };
  }
  return evalBodyLiteral(bodyLit, grounded, view, theory);
}

/**
 * One grounded body literal's truth against `E` (+ Theory), with polarity (#3165: three-valued; a
 * theory literal may be not decided, and not(U) = U) — against this cert's own table, or the exact
 * table of the strictly lower
 * certificate it reads the predicate from (#2258 (a)). An undecidable literal (neither sealed
 * for this cert nor theory-owned) is a HARD error (`cert_scope_incomplete`). Mirrors Rust's
 * `eval_body_literal`.
 */
function evalBodyLiteral(
  bodyLit: BodyLit,
  grounded: GroundLiteral,
  view: CertView,
  theory: Theory,
): TruthResult {
  const undecidable = (): TruthResult => ({
    err: [
      "cert_scope_incomplete",
      `closure body literal on predicate ${predDebug(grounded.pred)} is neither sealed nor theory-owned (undecidable)`,
    ],
  });
  if (!bodyLit.isNeg()) {
    if (theory.owns(grounded.pred)) return theoryTruth(view, theory, grounded, false);
    const t = view.table(grounded.pred);
    if (t === undefined) return undecidable();
    return { truth: truthOf(t.contains(grounded)) };
  }
  if (theory.owns(grounded.pred)) return theoryTruth(view, theory, grounded, true);
  const t = view.table(grounded.pred);
  if (t === undefined) return undecidable();
  return { truth: truthOf(!t.contains(grounded)) };
}

/**
 * A theory-owned literal's truth inside the closure (#3022 step 4, research 0028 A8; #3165), negated
 * when `negated`: the theory's ground verdict (`decideGround`), through the ONE conversion into the
 * algebra (`decisionOf`). `holds` is true, `fails` false, and a stop stays NOT DECIDED, never false
 * (not(U) = U): the join folds it and refuses the instance unless a false absorbs it or the head is
 * present. The disowning fault (`inconsistent_theory` after `owns()` said yes) is an inconsistent
 * theory, and it REFUSES by name (`predicate_partition_violation`, as a Builtin node's does), never
 * reads as false: a positive filter read false would let the closure under-fire and pass a table that
 * is not closed. So does an outcome no constructor could have built. rs `theory_truth`.
 */
function theoryTruth(view: CertView, theory: Theory, grounded: GroundLiteral, negated: boolean): TruthResult {
  // theoryDecisions: one `decideGround` call, counted on the view.
  view.countDecision();
  const ground = theory.decideGround(grounded);
  const verdict = readGround(ground);
  if (isDisowned(verdict)) {
    return {
      err: [
        "predicate_partition_violation",
        `closure body literal on predicate ${predDebug(grounded.pred)}: the theory owns it but returned NotMine`,
      ],
    };
  }
  if (verdict.arm === "not_decided" && verdict.cause.kind === "malformed_outcome") {
    return {
      err: [
        "predicate_partition_violation",
        `closure body literal on predicate ${predDebug(grounded.pred)}: the theory owns it but returned no outcome it could have built`,
      ],
    };
  }
  const truth = decisionOf(ground);
  return { truth: negated ? completionNot(truth) : truth };
}

// ------------------------- a count over a lower certificate (#2258 L3.3b) -------------------------
//
// A COUNT (ADR 0023) inside a sealed clause, over a relation a strictly lower certificate seals.
// Admission is the NegLower rule (seat:caa's Q2): the counted predicate must resolve to the
// unique, exact, Valid certificate at a strictly lower level that seals it. The closure evaluates
// it as a count stage (it binds or tests its result, one join step per lower row it scans), and a
// `count_lower` support ref recomputes it against that table. min/max over no matching row has no
// value (the count literal is false); a non-integer column is unserved, count_attr_out_of_range.
// Mirrors rs contract/rs/src/check/cert_count.rs and go check_cert_count.go.

/** Run one non-binder join step at its evaluation point, recording what a count binds in `newly`. */
function runStep(
  step: JoinStep,
  subst: Subst,
  view: CertView,
  theory: Theory,
  limits: CheckLimits,
  counters: { joins: number },
  newly: VarId[],
): TruthResult {
  if (step.kind === "count") {
    const r = countStage(step.count, subst, view, limits, counters, newly);
    return "err" in r ? r : { truth: truthOf(r.ok) };
  }
  return filterOutcome(step.lit, subst, view, theory, limits, counters);
}

/**
 * Fold `count` over `table` under the ground `filter`: the counted relation's arity must agree
 * with the table's, and every filter position and the projected column must lie inside it
 * (count_attr_out_of_range, the structural checks `verifyCountPremise` runs before its fold).
 */
function aggregateOver(count: CountLit, filter: readonly GroundFilterEntry[], table: import("./cert.js").RelationTable): AggregateResult {
  const arity = table.arity;
  if (count.pred.arity !== arity) {
    return { err: ["count_attr_out_of_range", `count predicate arity ${count.pred.arity} does not match the sealed table arity ${arity}`] };
  }
  for (const e of filter) {
    if (e.pos >= arity) return { err: ["count_attr_out_of_range", `count filter position ${e.pos} is outside predicate arity ${arity}`] };
  }
  const attr = count.project.kind === "rows" ? undefined : count.project.attr;
  if (attr !== undefined && attr >= arity) {
    return { err: ["count_attr_out_of_range", `aggregate projection attr ${attr} is outside predicate arity ${arity}`] };
  }
  return evaluateAggregate(table.rows, filter, count.project);
}

/** The count's filter under `subst`, each value ground, or `undefined` if one is not. */
function groundCountFilter(count: CountLit, subst: Subst): GroundFilterEntry[] | undefined {
  const filter: GroundFilterEntry[] = [];
  for (const e of count.filter) {
    const value = Term.eraseGround(Term.substitute(e.term, subst));
    if (value === undefined) return undefined;
    filter.push({ pos: e.pos, value });
  }
  return filter;
}

/**
 * One CLOSURE COUNT STAGE at its evaluation point: charge one join step per row of the lower table
 * it scans, fold, then bind the result variable (recorded in `newly`) or test a result already
 * ground. False when the count has no value (agg_empty_undefined) or differs from a ground result;
 * a count over no strictly lower table, or a filter not ground here, is cert_scope_incomplete,
 * never a silent false.
 */
function countStage(
  count: CountLit,
  subst: Subst,
  view: CertView,
  limits: CheckLimits,
  counters: { joins: number },
  newly: VarId[],
): BodyResult {
  const pred = count.pred.pred;
  const table = view.readsLower(pred) ? view.table(pred) : undefined;
  if (table === undefined) {
    return { err: ["cert_scope_incomplete", `count over predicate ${predDebug(pred)}, which no strictly lower certificate seals`] };
  }
  for (let i = 0; i < table.rows.length; i += 1) {
    const stepped = countJoinStep(counters, view.cert, limits);
    if (stepped !== undefined) return { err: stepped };
  }
  const filter = groundCountFilter(count, subst);
  if (filter === undefined) {
    return {
      err: [
        "cert_scope_incomplete",
        `closure count over predicate ${predDebug(pred)} has a filter that is not ground at its evaluation point (unsafe existential)`,
      ],
    };
  }
  const agg = aggregateOver(count, filter, table);
  if ("err" in agg) return agg.err[0] === "agg_empty_undefined" ? { ok: false } : { err: agg.err };
  const folded = encodeInt(agg.value);
  const slot = Term.substitute(count.count, subst);
  if (slot.kind === "var") {
    const key = slot.id();
    subst.set(key, Term.fromValue(folded));
    newly.push(key);
    return { ok: true };
  }
  const v = Term.eraseGround(slot);
  return { ok: v !== undefined && valueEquals(v, folded) };
}

/**
 * Resolve a support edge's `count_lower` ref for body literal `k`, a count: `cited` must be the
 * strictly lower certificate the counted predicate resolved to (its own certificate is refused),
 * the filter and the result must be ground under `subst`, and the aggregate recomputed over the
 * lower table must equal the result. A count with no value supports nothing.
 */
function resolveCountLower(
  k: number,
  count: CountLit,
  cited: CertId,
  subst: Subst,
  view: CertView,
  place: CertPlace,
): GateErr {
  const unsupported = (detail: string): GateErr => ["cert_unsupported", detail];
  const pred = count.pred.pred;
  const resolved = checkSupportRefCert(k, cited, pred, view, place);
  if ("err" in resolved) return resolved.err;
  const lower = resolved.lower;
  if (lower === undefined) {
    return unsupported(
      `support body ref ${k}: CountLower cites its own certificate for predicate ${predDebug(pred)} (a count must read a strictly lower certificate)`,
    );
  }
  const filter = groundCountFilter(count, subst);
  if (filter === undefined) return unsupported(`support body ref ${k}: count filter not ground under subst`);
  const claimed = Term.eraseGround(Term.substitute(count.count, subst));
  if (claimed === undefined) return unsupported(`support body ref ${k}: count result not ground under subst`);
  const agg = aggregateOver(count, filter, lower.table);
  if ("err" in agg) {
    if (agg.err[0] === "agg_empty_undefined") {
      return unsupported(`support body ref ${k}: the count has no value over certificate ${lower.index}'s table (${agg.err[1]})`);
    }
    return agg.err;
  }
  let n: bigint | undefined;
  try {
    n = readInt(claimed);
  } catch {
    n = undefined;
  }
  if (n === agg.value) return undefined;
  return unsupported(
    `support body ref ${k}: count result does not equal the aggregate recomputed over certificate ${lower.index}'s table (${agg.value})`,
  );
}

// ------------------------------------ §3.6 EDB ------------------------------------

/**
 * §3.6 EDB BINDING. For every sealed predicate the bound `LeafVerifier` declares
 * extensional, the cert's sealed table must equal the live EDB snapshot:
 * `edbTableHash(p, cert.table(p).rows) == leaves.edbSnapshot(p, ctx)`. An `undefined`
 * snapshot (fail-closed default) is `cert_edb_mismatch`. Mirrors Rust's `check_cert_edb`.
 */
function checkCertEdb<C>(cert: ClosedModelCert, leaves: LeafVerifier<C>, ctx: C): GateErr {
  const extensional = leaves.extensional();
  for (const pred of cert.scope.predicates) {
    if (!extensional.contains(pred)) continue; // IDB — bound by support/closure.
    const table = cert.table(pred);
    const rows: readonly GroundLiteral[] = table ? table.rows : [];
    const recomputed = edbTableHash(pred, rows);
    const snapshot = leaves.edbSnapshot;
    const attested = typeof snapshot === "function" ? Reflect.apply(snapshot, leaves, [pred, ctx]) : undefined;
    if (attested === undefined) {
      return ["cert_edb_mismatch", `no live EDB snapshot attested for sealed extensional predicate ${predDebug(pred)}`];
    }
    if (!hashEquals(attested, recomputed)) {
      return ["cert_edb_mismatch", `sealed extensional table ${predDebug(pred)} does not match the live EDB snapshot`];
    }
  }
  return undefined;
}

// =============================== per-Neg-premise gate ==============================

/**
 * Verify a single `NegPremise` against the (already memoized) certificate status — the
 * per-`Neg` obligations of ADR 0007 §4. Mirrors Rust's `verify_neg_premise`.
 */
export function verifyNegPremise(
  premise: NegPremise,
  headPred: Symbol,
  deriv: Derivation,
  certStatus: readonly CertStatus[],
): Verdict {
  const atom = premise.atom;
  const idx: CertId = premise.cert;
  // 1. cert index in range.
  if (idx < 0 || idx >= deriv.closedWorld.length) {
    return Verdict.reject("cert_out_of_range", `neg premise cites cert ${idx} out of range ${deriv.closedWorld.length}`);
  }
  const cert = deriv.closedWorld[idx]!;

  // 2. the cert must be Valid (reuse the memoized status).
  const status = certStatus[idx]!;
  if (status.kind === "invalid") {
    return Verdict.reject(status.code, status.detail);
  }

  // 3. predicate sealed by the cert scope.
  if (!cert.scope.seals(atom.pred)) {
    return Verdict.reject("neg_atom_not_sealed", "negated predicate is not sealed by the cited certificate");
  }
  // 3b. ADR 0030 D2: sealed as a LOWER BOUND — absence from it proves nothing.
  if (cert.isPartial(atom.pred)) {
    return Verdict.reject(
      "neg_atom_partial",
      "negated predicate is sealed as a lower bound (partial_scope) by the cited certificate; absence from a partial table is not a proof of absence",
    );
  }

  // 4. strictly lower stratum: the RULE HEAD predicate must NOT be in the cert's scope.
  if (cert.scope.seals(headPred)) {
    return Verdict.reject(
      "neg_stratum_not_lower",
      "rule head predicate is in the same (or lower) sealed stratum as the negated atom",
    );
  }

  // 5. ground + well-typed within a supplied finite domain.
  for (const arg of atom.args) {
    if (cert.domainContaining(arg) === undefined) {
      return Verdict.reject("neg_atom_ill_typed", "negated atom argument is outside the certificate's finite domain");
    }
  }

  // 6. ABSENT from the sealed relation.
  const table = cert.table(atom.pred);
  if (table === undefined) {
    return Verdict.reject("neg_atom_not_sealed", "negated predicate sealed but has no extension table");
  }
  if (table.contains(atom)) {
    return Verdict.reject("neg_atom_present", "negated atom IS present in the sealed relation");
  }

  return Verdict.Accept;
}

// ============================ per-Count-premise gate (ADR 0023) ====================

/**
 * Verify a single `CountPremise` against the (already memoized) certificate status — the
 * per-`Count` obligations of ADR 0023 §"what the checker verifies". A structural clone of
 * `verifyNegPremise` (steps 1–4 identical: cert in range + Valid, predicate sealed,
 * strictly-lower stratum); step 5 swaps the membership test for a counted projection —
 * recompute `n` over the proven-exact `RelationTable` and require `n == k`, else
 * `count_mismatch`. Mirrors Rust's `verify_count_premise`.
 */
export function verifyCountPremise(
  premise: CountPremise,
  headPred: Symbol,
  deriv: Derivation,
  certStatus: readonly CertStatus[],
): Verdict {
  const pred: PredicateRef = premise.pred;
  const idx: CertId = premise.cert;
  // 1. cert index in range.
  if (idx < 0 || idx >= deriv.closedWorld.length) {
    return Verdict.reject(
      "cert_out_of_range",
      `count premise cites cert ${idx} out of range ${deriv.closedWorld.length}`,
    );
  }
  const cert = deriv.closedWorld[idx]!;

  // 2. the cert must be Valid (reuse the memoized status).
  const status = certStatus[idx]!;
  if (status.kind === "invalid") {
    return Verdict.reject(status.code, status.detail);
  }

  // 3. predicate sealed by the cert scope (matched by name; arity is checked in 5).
  if (!cert.scope.seals(pred.pred)) {
    return Verdict.reject("neg_atom_not_sealed", "counted predicate is not sealed by the cited certificate");
  }
  // 3b. ADR 0030 D2: sealed as a LOWER BOUND — a count over it is not the count.
  if (cert.isPartial(pred.pred)) {
    return Verdict.reject(
      "count_over_partial",
      "counted predicate is sealed as a lower bound (partial_scope) by the cited certificate; a count over a partial table is not the count",
    );
  }

  // 4. strictly lower stratum: the RULE HEAD predicate must NOT be sealed by the cert's scope.
  if (cert.scope.seals(headPred)) {
    return Verdict.reject(
      "count_stratum_not_lower",
      "rule head predicate is in the same (or lower) sealed stratum as the counted relation",
    );
  }

  // 5. recompute n over the sealed table.
  const table = cert.table(pred.pred);
  if (table === undefined) {
    return Verdict.reject("neg_atom_not_sealed", "counted predicate sealed but has no extension table");
  }
  const arity = table.arity;

  // 5·#581 ARITY AGREEMENT: matched by name AND arity, else count_attr_out_of_range.
  if (pred.arity !== arity) {
    return Verdict.reject(
      "count_attr_out_of_range",
      `count predicate arity ${pred.arity} does not match the sealed table arity ${arity}`,
    );
  }

  // 5a. filter well-typed: each position within arity and value in the cert's finite domain.
  for (const e of premise.filter) {
    if (e.pos >= arity) {
      return Verdict.reject(
        "count_attr_out_of_range",
        `count filter position ${e.pos} is outside predicate arity ${arity}`,
      );
    }
    if (cert.domainContaining(e.value) === undefined) {
      return Verdict.reject("neg_atom_ill_typed", "count filter value is outside the certificate's finite domain");
    }
  }

  // 5b. projection/fold attr (count_distinct / sum / min / max) within arity.
  const projAttr = premise.project.kind === "rows" ? undefined : premise.project.attr;
  if (projAttr !== undefined && projAttr >= arity) {
    return Verdict.reject(
      "count_attr_out_of_range",
      `aggregate projection attr ${projAttr} is outside predicate arity ${arity}`,
    );
  }

  // 5c. ONE LINEAR SCAN over the proven-exact rows: `evaluateAggregate`, ADR 0023's one fold
  //     (count rows / distinct projected values, null() excluded / an integer sum, min or max),
  //     the same one a closure count stage and a count_lower ref evaluate (#2258 L3.3b).
  const agg = evaluateAggregate(table.rows, premise.filter, premise.project);
  if ("err" in agg) return Verdict.reject(agg.err[0], agg.err[1]);
  const recomputed = agg.value;

  // 5d. compare the recomputed fold against the claimed k (the canonical int embedding).
  let claimed: bigint;
  try {
    claimed = readInt(premise.k);
  } catch {
    return Verdict.reject("count_mismatch", "aggregate premise k is not a canonical int value");
  }
  if (claimed !== recomputed) {
    return Verdict.reject("count_mismatch", `claimed aggregate ${claimed} != recomputed aggregate ${recomputed}`);
  }

  return Verdict.Accept;
}

/** Positional + value agreement of two ground count filters (ADR 0023): exact value equality. */
export function equalGroundFilter(a: readonly GroundFilterEntry[], b: readonly GroundFilterEntry[]): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) {
    if (a[i]!.pos !== b[i]!.pos || !valueEquals(a[i]!.value, b[i]!.value)) return false;
  }
  return true;
}

/** Project equality re-exported for the check premise loop (ADR 0023 + #587). */
export function projectEquals(a: ProjectSpec, b: ProjectSpec): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "rows" || b.kind === "rows") return true;
  return a.attr === b.attr;
}

// ================================== small helpers =================================

/** A predicate symbol rendered for a diagnostic detail string (utf-8 lossy, quoted). */
function predDebug(pred: Symbol): string {
  return `"${decodeUtf8Lossy(pred.bytes())}"`;
}

/** Lowercase-hex of a byte slice (a stable map key for canonical codec bytes). */
function bytesHex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}

/** Canonical codec bytes of a value (used as a universe dedup key). */
function encodeValue(v: Value): Uint8Array {
  return encode(v);
}
