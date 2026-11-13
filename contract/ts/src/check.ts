// §4 Checker SPI — the P0 deliverable. [FIRM core obligations · STABLE v1 seams]
// TS sibling of contract/rs/src/check.rs.

import { equals as valueEquals, type Value } from "@bitspark/ontos-core";
import {
  type Derivation,
  type GroundFilterEntry,
  isCountPremise,
  isNegPremise,
  type Node,
} from "./derivation.js";
import { type GroundLiteral, type Goal, type Symbol as PredicateSymbol } from "./literal.js";
import { type Program } from "./program.js";
import { ComponentIdentity, type LeafVerifier, type RuleAdmissibility, type Theory } from "./spi.js";
import { isDisowned, readGround } from "./ground_reading.js";
import { Term, MAX_TERM_DEPTH_DEFAULT } from "./term.js";
import { captureCertContext, captureDerivation } from "./capture.js";
import { type CheckReport, Tally } from "./check_report.js";
import { copyArray } from "./native_copy.js";
import {
  CertContext,
  type CertStatus,
  equalGroundFilter,
  projectEquals,
  verifyWorld,
  verifyCountPremise,
  verifyNegPremise,
} from "./cert_check.js";
import { checkCertTermDepths } from "./cert_depth.js";
import type { ClosedModelCert } from "./cert.js";
import { nativeCertificateKey } from "./wire_sink.js";

/**
 * Rejection codes (§4). Two bands: a FIRM structural band (the kernel emits these;
 * branch on the code STRING, not on detail) and a host-extension band (the three
 * wrappers a delegated extension point raises). The `code` strings are the
 * normative cross-language artifact.
 */
export type RejectionCode =
  // ---- structural band (FIRM) ----
  | "empty_derivation"
  | "too_many_nodes"
  | "too_deep"
  // term_too_deep: a single term nests deeper than CheckLimits.maxTermDepth (issue
  // #253) — a pathologically deep term that would overflow the JS call stack in the
  // recursive term traversals. Distinct from too_deep (DAG/premise-chain depth).
  | "term_too_deep"
  | "root_out_of_range"
  | "non_ground_conclusion"
  | "unknown_clause"
  | "instantiation_mismatch"
  | "bad_dependency_order"
  | "root_conclusion_mismatch"
  | "sealed_violation"
  | "predicate_partition_violation"
  | "unknown_node_kind"
  // ---- closed-model certificate band (ADR 0007, structural / FIRM) ----
  // A `Neg` premise cites a `closedWorld` index out of range.
  | "cert_out_of_range"
  // The certificate's CLOSURE work exceeds the caller's `CheckLimits` closure budget: its
  // declared `ruleGroundings` / `joinSteps`, or the count the closure scan reaches live, is over
  // `maxRuleGroundings` / `maxJoinSteps`. The caller's verify budget, not an engine fault (#2335).
  // Until CHECKER_VERSION 10 this code ALSO covered the four size budgets (now
  // `cert_size_exceeded`) and a lying declaration (now `cert_decl_mismatch`), so a verdict stored
  // under an older version meant something wider.
  | "cert_budget_exceeded"
  // The certificate's declared SIZE exceeds the caller's `CheckLimits` size budget: its
  // `certBytes` / `certFacts` / `domainValues` / `supportEdges` is over the matching `max*`.
  // The caller's verify budget, not an engine fault (#2335).
  | "cert_size_exceeded"
  // The certificate's ACTUAL size or closure work exceeds its OWN declaration (`limitsDecl`):
  // the producer under-declared, so an engine fault. Split from `cert_budget_exceeded` by
  // #2335, which until then named both parties.
  | "cert_decl_mismatch"
  // A certificate's pinned hashes do not match the check context.
  | "cert_context_mismatch"
  // A `\+ atom`'s predicate is not sealed by the cited certificate.
  | "neg_atom_not_sealed"
  // The negated predicate is not in a strictly-lower stratum than the rule head.
  | "neg_stratum_not_lower"
  // The negated atom is not ground / well-typed within the cert's finite domain.
  | "neg_atom_ill_typed"
  // The negated atom IS present in the sealed relation (so `\+` does not hold).
  | "neg_atom_present"
  // A sealed fact lacks a valid support edge (the relation is not `⊆ least model`).
  | "cert_unsupported"
  // A satisfied rule grounding's head is absent from the table (not closed).
  | "cert_not_closed"
  // A satisfied grounding produces a value outside the sealed finite domain.
  | "cert_out_of_domain"
  // The sealed stratum prefix is not downward-closed (closure cannot soundly evaluate).
  | "cert_scope_incomplete"
  // A `Neg`-bearing derivation supplied an all-zero (unbound) cert context.
  | "cert_context_unbound"
  // A sealed extensional table does not match the live EDB snapshot.
  | "cert_edb_mismatch"
  // ADR 0030: `partial_scope` is ill-formed — not canonical, empty, not a subset of `scope` at
  // its own level, names an extensional table, or is not upward-closed within the prefix.
  | "cert_partial_scope_invalid"
  // ADR 0030: a `Neg` premise over a table the cert marks PARTIAL — absence from a lower bound
  // proves nothing.
  | "neg_atom_partial"
  // ---- certifiable aggregation band (ADR 0023, structural / FIRM) ----
  // A Count premise's counted predicate is not in a strictly-lower stratum than the head.
  | "count_stratum_not_lower"
  // A Count premise's filter position, count_distinct attr, or predicate arity is out of range.
  | "count_attr_out_of_range"
  // A Count premise's claimed cardinality k != the count recomputed over the proven-exact relation.
  | "count_mismatch"
  // A min/max aggregate (ADR 0023 #587) folds NO matching rows: min/max of an empty set is
  // undefined. v1 rejects rather than minting an infinity or sentinel (an empty sum is 0).
  | "agg_empty_undefined"
  // ADR 0030: a `Count` premise over a table the cert marks PARTIAL — a count over a lower
  // bound is not the count.
  | "count_over_partial"
  // ---- host-extension band (STABLE v1 mechanism; sub-code in `detail`) ----
  | "builtin_failed"
  // #3126: the theory did not DECIDE a builtin literal the derivation relies on (its
  // `decideGround` stopped: a work cap, a capacity). `check` refuses rather than reading the stop
  // as a decision, in every position: a positive Builtin node, a support edge's builtin, and a
  // closure rule instance whose body is not decided and whose head is absent. The sub-code in
  // `detail` is the stop's kind (`work_cap`, ...), as `builtin_failed` carries the theory's code.
  | "builtin_not_decided"
  | "leaf_rejected"
  | "rule_inadmissible"
  // Caller configuration. No proof or SPI decision is inspected.
  | "invalid_check_limits";

/** True for the closed FIRM structural band — the codes a `check` over well-typed input may itself emit. */
export function isStructural(code: RejectionCode): boolean {
  return (
    code !== "invalid_check_limits" &&
    code !== "builtin_failed" &&
    code !== "builtin_not_decided" &&
    code !== "leaf_rejected" &&
    code !== "rule_inadmissible"
  );
}

/** What `check` decided: accept, or reject with a code and its diagnostic detail. rs `Verdict`. */
export type Verdict =
  | { readonly kind: "accept" }
  | { readonly kind: "reject"; readonly code: RejectionCode; readonly detail: string };

export const Verdict = Object.freeze({
  Accept: Object.freeze({ kind: "accept" } as const satisfies Verdict),
  reject(code: RejectionCode, detail: string): Verdict {
    return { kind: "reject", code, detail };
  },
  isAccept(v: Verdict): boolean {
    return v.kind === "accept";
  },
  /** Two verdicts are equal when their kinds, codes and details are (rs `Verdict`'s equality). */
  equals(a: Verdict, b: Verdict): boolean {
    if (a.kind === "accept" || b.kind === "accept") return a.kind === b.kind;
    return a.code === b.code && a.detail === b.detail;
  },
});

/**
 * The result of `check` (checker SPI v2, ADR 0036 D8 change 5, #3111): its `verdict`, and the
 * `report` of the work it performed. rs `Outcome`.
 *
 * **Equality is the verdict's.** Two outcomes are equal (`Outcome.equals`) when their verdicts are,
 * whatever their reports say, so a counter can never turn a verdict test red (the coordinator's
 * ruling of 2026-11-12). Read `report` where the work is asked about.
 */
export type Outcome = {
  readonly verdict: Verdict;
  readonly report: CheckReport;
};

export const Outcome = Object.freeze({
  isAccept(o: Outcome): boolean {
    return o.verdict.kind === "accept";
  },
  /** Verdict-only equality: rs `Outcome`'s `PartialEq`, which compares the verdicts alone. */
  equals(a: Outcome, b: Outcome): boolean {
    return Verdict.equals(a.verdict, b.verdict);
  },
});


/**
 * The checker's BEHAVIOUR PARAMETERS (§4.3): budgets on the untrusted supplied derivation.
 * (Checker SPI v2, ADR 0036 D8 change 1, #3111: the inert term identity is deleted.) The budgets
 * bound proof size on verify, and the node cap is a hard, deterministic rejection checked before
 * any node delegation.
 */
export interface CheckLimits {
  /** Max total node count (`> maxNodes` → `too_many_nodes`). */
  readonly maxNodes: number;
  /** Max DAG depth (longest premise chain) (`> maxDepth` → `too_deep`). */
  readonly maxDepth: number;
  /**
   * Max single-term nesting depth (`> maxTermDepth` → `term_too_deep`, issue #253).
   * Bounds the depth of every term the trusted path traverses recursively (node
   * conclusions, the claim, and every cited clause's head/body/subst terms), so a
   * pathologically deep term cannot overflow the JS call stack. Distinct from
   * `maxDepth` (DAG/premise-chain depth). Default `MAX_TERM_DEPTH_DEFAULT`.
   */
  readonly maxTermDepth: number;
  // ---- closed-model certificate budgets (ADR 0007) ----
  // Each bounds one dimension of a cited `ClosedModelCert`. Validated BEFORE any scan
  // (against the cert's `limitsDecl` AND its actual sizes), so an oversized or lying
  // certificate is refused without doing its work.
  /** Max serialized certificate size, in bytes (`> maxCertBytes` → reject). */
  readonly maxCertBytes: number;
  /** Max total sealed facts across a certificate's extensions. */
  readonly maxCertFacts: number;
  /** Max total domain values across a certificate's domains. */
  readonly maxDomainValues: number;
  /** Max number of support edges in a certificate. */
  readonly maxSupportEdges: number;
  /**
   * Max number of rule groundings the closure join may emit (one per body-true tuple of a
   * sealed-scope clause, #1829); tripped incrementally during the scan.
   */
  readonly maxRuleGroundings: number;
  /**
   * Max number of join steps the closure join may perform (one per candidate examined at one
   * body literal, #1829); tripped incrementally during the scan.
   */
  readonly maxJoinSteps: number;
}

/**
 * Default limits — mirrors arche-core's MAX_NODES=100_000; the depth cap is logos's
 * addition; `maxTermDepth` is the issue #253 single-term nesting bound (tri-core-
 * consistent with contract/{rs,go}). The cert budgets are finite, generous defaults
 * (a cert larger than these is a verification-cost DoS, refused before any scan) —
 * byte-identical to Rust's `CheckLimits::default`.
 */
/**
 * Every budget a caller can raise (#2733, R3), each as the key a vector case's `limits` uses and
 * the field that holds it: the one list of the checker's budgets, which every reader takes rather
 * than keeping its own. `UnlistedBudget` below fails to compile when a field of `CheckLimits` is
 * not listed here.
 */
export const CHECK_BUDGETS = [
  ["max_nodes", "maxNodes"],
  ["max_depth", "maxDepth"],
  ["max_term_depth", "maxTermDepth"],
  ["max_cert_bytes", "maxCertBytes"],
  ["max_cert_facts", "maxCertFacts"],
  ["max_domain_values", "maxDomainValues"],
  ["max_support_edges", "maxSupportEdges"],
  ["max_rule_groundings", "maxRuleGroundings"],
  ["max_join_steps", "maxJoinSteps"],
] as const satisfies readonly (readonly [string, keyof CheckLimits])[];
for (const pair of CHECK_BUDGETS) Object.freeze(pair);
Object.freeze(CHECK_BUDGETS);

type UnlistedBudget = Exclude<keyof CheckLimits, (typeof CHECK_BUDGETS)[number][1]>;
const everyBudgetIsListed: [UnlistedBudget] extends [never] ? true : never = true;
void everyBudgetIsListed;

/** A caller budget is outside the range this host can represent exactly. */
export class CheckLimitError extends RangeError {
  constructor(readonly field: string, readonly value: unknown) {
    super(`check limits: ${field} must be a nonnegative safe integer`);
    this.name = "CheckLimitError";
  }
}

/** Inspect one proof budget before native construction or wire encoding. */
export function proofBudgetError(field: string, value: number): CheckLimitError | undefined {
  return Number.isSafeInteger(value) && value >= 0 ? undefined : new CheckLimitError(field, value);
}

/** Report the first invalid budget in declaration order. Zero is a valid cap. */
export function validateCheckLimits(limits: CheckLimits): CheckLimitError | undefined {
  for (const [field, key] of CHECK_BUDGETS) {
    const error = proofBudgetError(field, limits[key]);
    if (error !== undefined) return error;
  }
  return undefined;
}

/** A native policy value or the caller's first invalid proof budget. */
export type CheckPolicyResult<T> = { readonly ok: true; readonly value: T }
  | { readonly ok: false; readonly error: CheckLimitError };

/** The numeric proof policy carried on the wire. */
export type ProofBudgets = Pick<CheckLimits, (typeof CHECK_BUDGETS)[number][1]>;

/** Capture each effective numeric field once, refusing the first invalid count in wire order. */
export function captureProofBudgets(limits: ProofBudgets, overrides?: Partial<ProofBudgets>): CheckPolicyResult<ProofBudgets> {
  const counts = {} as Record<(typeof CHECK_BUDGETS)[number][1], number>;
  for (const [field, key] of CHECK_BUDGETS) {
    const value = overrides !== undefined && key in overrides ? overrides[key]! : limits?.[key];
    const error = proofBudgetError(field, value);
    if (error !== undefined) return { ok: false, error };
    counts[key] = value;
  }
  return { ok: true, value: Object.freeze(counts) };
}

/** Capture the effective native limits. Replacement fields take precedence without
 * consulting the original getters for those fields. Each retained value is read once. */
export function captureCheckLimits(limits: CheckLimits, overrides?: Partial<CheckLimits>): CheckPolicyResult<CheckLimits> {
  return captureProofBudgets(limits, overrides);
}

export function defaultLimits(): CheckLimits {
  return {
    maxNodes: 100_000,
    maxDepth: 4096,
    maxTermDepth: MAX_TERM_DEPTH_DEFAULT,
    maxCertBytes: 16 * 1024 * 1024,
    maxCertFacts: 1_000_000,
    maxDomainValues: 1_000_000,
    maxSupportEdges: 1_000_000,
    maxRuleGroundings: 10_000_000,
    maxJoinSteps: 100_000_000,
  };
}

/** The bound extension points + limits `check` verifies against (§4). */
export interface CheckProfile<C> {
  readonly theory: Theory;
  readonly leaves: LeafVerifier<C>;
  readonly admit: RuleAdmissibility<C>;
  readonly limits: CheckLimits;
}

/** Bind the verifier handles and their validated native limits without calling an SPI.
 * The application retains ownership of the component implementations and their context. */
export function captureCheckProfile<C>(profile: CheckProfile<C>): CheckPolicyResult<CheckProfile<C>> {
  if (profile == null) throw new TypeError("a live check profile is required");
  const limits = captureCheckLimits(profile.limits);
  if (!limits.ok) return limits;
  const { theory, leaves, admit } = profile;
  if (theory == null || leaves == null || admit == null) {
    throw new TypeError("a live check profile requires theory, leaves and rule admission");
  }
  return { ok: true, value: Object.freeze({ theory, leaves, admit, limits: limits.value }) };
}

/**
 * One bound-component slot of a {@link CheckProfile} — the three slots a profile digest
 * folds a component binding for.
 */
export type ProfileSlot = "theory" | "leaves" | "admit";

/**
 * Which of a live profile's bound components read as `ComponentIdentity.unidentified()` —
 * the unidentified-component advisory (#708 leg (a)).
 *
 * `identity?()` is optional, so a component that omits it contributes a **constant** to the
 * profile digest. Two different `LeafVerifier`s — one strict, one permissive — both omitting
 * it produce the **same** digest. For that slot the digest discharges *nothing*, while still
 * being a computed 32-byte value that reads as evidence.
 *
 * **This lives in the contract tier deliberately** (#815). It reads only contract types and
 * touches nothing the kernel owns; its original placement in `kernel` put it out of reach of
 * any consumer binding `@bitspark/logos-contract` alone, because `contract → kernel` is an
 * **upward** edge on the ADR 0004 tier stack. Placement follows what a function reads, not
 * what it was written next to.
 *
 * A non-empty result means: *the frozen digest says nothing about this slot.* It does not
 * mean the profile is wrong — an anonymous component is legal, and remains so.
 */
export function unidentifiedProfileSlots<C>(profile: CheckProfile<C>): ProfileSlot[] {
  return unidentifiedProfileSlotsAllowing(profile, []);
}

/**
 * The same report, minus the slots the caller has **explicitly declared** it accepts as
 * anonymous — ADR 0026 gate **G4**, the deliberate escape.
 *
 * **Declared, never defaulted.** An empty allowance is the default —
 * {@link unidentifiedProfileSlots} *is* this with `[]` — and allowing every slot requires
 * naming all three. There is deliberately no "allow all" shorthand: the value of an escape
 * is the legible trace it leaves at the call site.
 *
 * **It does not touch the digest.** This reads identities and participates in no fold.
 * Allowing a slot changes what you are *told*, never what is *derived*.
 */
export function unidentifiedProfileSlotsAllowing<C>(
  profile: CheckProfile<C>,
  allowUnidentified: readonly ProfileSlot[],
): ProfileSlot[] {
  const { theory, leaves, admit } = profile;
  const allowed = copyArray(allowUnidentified, slot => slot);
  const components = [["theory", theory], ["leaves", leaves], ["admit", admit]] as const;
  const unidentified: ProfileSlot[] = [];
  for (const [slot, component] of components) {
    const identity = ComponentIdentity.resolve(component);
    if (identity.isUnidentified() && !allowed.includes(slot)) unidentified.push(slot);
  }
  return unidentified;
}

/**
 * Whether every bound component attests an identity — the silent case of
 * {@link unidentifiedProfileSlots}.
 */
export function profileIsFullyIdentified<C>(profile: CheckProfile<C>): boolean {
  return unidentifiedProfileSlots(profile).length === 0;
}

/**
 * Verify a derivation (§4). Total, no search.
 *
 * Order of obligations (normative §4): empty / node-cap / root-range up front (the
 * node cap BEFORE any delegation, strict `>`); then a single forward pass where
 * each node is validated structurally and only THEN delegated to its extension
 * point; finally the root must conclude `claim`.
 *
 * Positive-identical (ADR 0007): a thin wrapper over `checkWithCertContext` supplying a
 * ZERO `CertContext`. For an all-positive derivation (`closedWorld` empty) the context
 * is NEVER consulted, so an existing positive check behaves byte-for-byte as before.
 *
 * Negation requires a bound context: a zero context is the UNBOUND sentinel, never a
 * credential. If `deriv.closedWorld` is non-empty (a certifying check), this wrapper
 * hard-rejects `cert_context_unbound` — a certificate must be verified against a context
 * DERIVED from the live program/profile (`checkWithCertContext`), not an all-zero
 * placeholder any all-zero-pinned cert would trivially satisfy.
 */
export function check<C>(
  program: Program,
  claim: GroundLiteral,
  deriv: Derivation,
  ctx: C,
  profile: CheckProfile<C>,
): Outcome {
  return checkWithCertContext(program, claim, deriv, ctx, profile, CertContext.zero());
}

/**
 * Verify a derivation that may carry closed-model certificates (ADR 0007). Total, no
 * search; the cert obligations are bounded deterministic verification over the supplied
 * finite tables/domains, every loop pre-bounded by a `CheckLimits` cert budget validated
 * up front. `certContext` pins the program/profile/context/theory configuration the
 * cited certificates must have been sealed against; it is consulted ONLY when a cert is
 * actually verified (i.e. only for a `Neg`-bearing derivation). Mirrors Rust's
 * `check_with_cert_context`.
 */
export function checkWithCertContext<C>(
  program: Program,
  claim: GroundLiteral,
  proposal: Derivation,
  ctx: C,
  profile: CheckProfile<C>,
  certContext: CertContext,
): Outcome {
  // #3111: one tally per check, threaded through it. A refusal before the walk (the profile and
  // derivation capture, the limits, an empty derivation, the node cap, the root range) reports zeros.
  const tally = new Tally();
  const bound = captureCheckProfile(profile);
  if (!bound.ok) return tally.outcome(Verdict.reject("invalid_check_limits", bound.error.message));
  profile = bound.value;
  const captured = captureDerivation(proposal, profile.limits);
  if (captured.kind === "reject") return tally.outcome(captured);
  const deriv = captured.value;
  if (deriv.closedWorld.length > 0) certContext = captureCertContext(certContext);
  const early = derivationPrechecks(program, claim, deriv, profile, tally);
  if (early !== undefined) {
    return tally.outcome(early);
  }
  const certStatus = verifyWorld(deriv.closedWorld, program, profile, ctx, certContext, tally);
  return tally.outcome(checkNodes(program, claim, deriv, ctx, profile, certStatus, tally));
}

const runBoundCheck = Symbol("check under the bound inputs");

/**
 * #2569 (the ts rung of #2565 term 1): a memo of one closed world's certificate verification, so
 * a run that checks many derivations citing the SAME certificates verifies them once.
 *
 * Its inputs are BOUND AT CONSTRUCTION, and the whole check runs under them: the program, profile,
 * ctx and CertContext are the memo's own, so a caller cannot pass a different one with it. The
 * per-call key is the derivation's WHOLE closed world, compared on the account fields with each support
 * handle read as its exact native code units. The stored world's keys are computed once on a miss.
 * That comparison does not depend on how
 * a class holds its state: ontos values and `Symbol` keep theirs in private fields, so a generic walk
 * of own properties would see every atom as equal. It is deliberately NOT short-circuited on object
 * identity: a certificate is frozen, but its hashes' bytes and its size declaration are not, so an
 * edit in place to a certificate already checked would be a stale hit under a reference test. Like
 * the rs and go memos, this one walks the world on every call and saves the verification.
 * `CheckLimits` are snapshotted and compared with the live profile's on every call.
 *
 * OBLIGATION (docs/spec/logos-contract.md §6): the program, profile components and ctx a memo is
 * built with MUST NOT be mutated while it is in use. A mutated program leaves the bound CertContext
 * stale, and the memo would serve a WRONG verdict, not a slow one. The kernel gate meets this by
 * construction.
 */
export class WorldMemo<C> {
  #keys: readonly Value[] = [];
  #status: readonly CertStatus[] = [];
  #limits: CheckLimits | undefined;
  #verified = 0;
  readonly #certContext: CertContext;

  constructor(
    readonly program: Program,
    readonly profile: CheckProfile<C>,
    readonly ctx: C,
    certContext: CertContext,
  ) {
    this.#certContext = captureCertContext(certContext);
    Object.freeze(this);
  }

  /** A detached reading of the pins bound at construction. */
  get certContext(): CertContext { return captureCertContext(this.#certContext); }

  /** Certificates verified through this memo, each world verified on a miss counted in full. */
  get certificatesVerified(): number {
    return this.#verified;
  }

  /**
   * The statuses of `world`: from the slot on a hit, verified and stored on a miss. An EMPTY world
   * (a positive derivation) needs no verification and does not touch the slot.
   *
   * The calling check's `tally` counts a hit's certificates as `certsMemoHits`, and a miss's
   * verification as that check's own work (#3111).
   */
  #statuses(world: readonly ClosedModelCert[], profile: CheckProfile<C>, tally: Tally): readonly CertStatus[] {
    if (world.length === 0) {
      return [];
    }
    if (this.#hit(world, profile.limits)) {
      // certsMemoHits: every certificate of the world, served instead of verified.
      tally.certsMemoHits += world.length;
    } else {
      const status = verifyWorld(world, this.program, profile, this.ctx, this.#certContext, tally);
      this.#keys = world.map(nativeCertificateKey);
      this.#status = status;
      this.#limits = profile.limits;
      this.#verified += world.length;
    }
    return this.#status;
  }

  #hit(world: readonly ClosedModelCert[], limits: CheckLimits): boolean {
    if (this.#limits === undefined || world.length !== this.#keys.length) {
      return false;
    }
    if (!sameLimits(this.#limits, limits)) {
      return false;
    }
    return world.every((cert, i) => valueEquals(nativeCertificateKey(cert), this.#keys[i]!));
  }

  static [runBoundCheck]<C>(memo: WorldMemo<C>, claim: GroundLiteral, proposal: Derivation): Outcome {
    if (!(#keys in memo)) throw new TypeError("checking requires a bound WorldMemo");
    const tally = new Tally();
    const bound = captureCheckProfile(memo.profile);
    if (!bound.ok) return tally.outcome(Verdict.reject("invalid_check_limits", bound.error.message));
    const profile = bound.value;
    const captured = captureDerivation(proposal, profile.limits);
    if (captured.kind === "reject") return tally.outcome(captured);
    const deriv = captured.value;
    const early = derivationPrechecks(memo.program, claim, deriv, profile, tally);
    if (early !== undefined) return tally.outcome(early);
    const statuses = memo.#statuses(deriv.closedWorld, profile, tally);
    return tally.outcome(checkNodes(memo.program, claim, deriv, memo.ctx, profile, statuses, tally));
  }
}
const checkBoundWorld = WorldMemo[runBoundCheck];

/** Every field of two `CheckLimits`, compared by value. */
function sameLimits(a: CheckLimits, b: CheckLimits): boolean {
  return CHECK_BUDGETS.every(([, key]) => a[key] === b[key]);
}

/**
 * `checkWithCertContext` under the memo's bound program, profile, ctx and CertContext, with the
 * derivation's closed world verified through the memo (#2569). The verdict is exactly
 * `checkWithCertContext`'s: only step 3a can be served from the memo.
 */
export function checkWithWorldMemo<C>(memo: WorldMemo<C>, claim: GroundLiteral, deriv: Derivation): Outcome {
  return checkBoundWorld(memo, claim, deriv);
}


function derivationPrechecks<C>(
  program: Program,
  claim: GroundLiteral,
  deriv: Derivation,
  profile: CheckProfile<C>,
  tally: Tally,
): Verdict | undefined {
  // Only step 3b counts work (`maxTermDepthReached`): every depth it measures goes into `tally`.
  // 3b. TERM-NESTING DEPTH CAP (issue #253) — BEFORE any recursive term traversal
  //     (cert verification in 3a, the forward pass in 4, the root `equals` in 5). A
  //     single term can nest arbitrarily deep within one node, which neither the node
  //     cap nor the DAG-depth cap bounds; a pathologically deep term would overflow the
  //     JS call stack in substitute/eraseGround/structural equals/the account quote. The
  //     measurement is iterative with an early cutoff (Term.depthLe / valueDepthLe), so
  //     checking the depth of a deep term does not itself overflow. Over → term_too_deep
  //     (graceful rejection, never a RangeError crash).
  {
    const result = checkTermDepths(program, claim, deriv, profile.limits, tally);
    if (result.kind !== "accept") {
      return result;
    }
    // The cert-deep term-depth check (cert extension rows / domains / support edges /
    // Neg-premise atoms). No-op for an all-positive derivation (closedWorld empty).
    const certDepth = checkCertTermDepths(deriv, profile.limits.maxTermDepth, tally);
    if (certDepth.kind !== "accept") {
      return certDepth;
    }
  }
  return undefined;
}

/** Steps 4 and 5 of `checkWithCertContext`: the forward pass, then the root against the claim. */
function checkNodes<C>(
  program: Program,
  claim: GroundLiteral,
  deriv: Derivation,
  ctx: C,
  profile: CheckProfile<C>,
  certStatus: readonly CertStatus[],
  tally: Tally,
): Verdict {
  // 4. one forward pass: validate each node (structural, then delegate).
  const depth = new Array<number>(deriv.nodes.length).fill(0);
  for (let i = 0; i < deriv.nodes.length; i += 1) {
    const node = deriv.nodes[i]!;
    const result = checkNode(i, node, program, deriv, ctx, profile, depth, certStatus, tally);
    if (result.kind !== "accept") {
      return result;
    }
  }

  // 5. root concludes the claim, structurally (#3022): the certified claim is exactly the fact
  //    the root proves, never another spelling of it.
  if (!deriv.nodes[deriv.root]!.conclusion.equals(claim)) {
    return Verdict.reject("root_conclusion_mismatch", "root conclusion does not equal claim");
  }

  return Verdict.Accept;
}

/**
 * §4.3 TERM-NESTING DEPTH CAP (issue #253). Validate, ITERATIVELY with an early
 * cutoff, that no term the trusted path will traverse recursively nests deeper than
 * `limits.maxTermDepth`. Covers the claim's args, every node's conclusion args + (for a
 * Rule) its subst image terms, and every cited clause's head + body-literal args.
 * Returns `Verdict.Accept` when every term is within bound, else a `term_too_deep`
 * rejection. Each measurement (`Term.depthLe`'s walk) is itself non-recursive and cuts off at
 * the bound, so this gate's own cost is bounded by `maxTermDepth`, not by the (unbounded) depth
 * of a pathological term. Every depth it measures goes into `tally` (`maxTermDepthReached`).
 */
function checkTermDepths(
  program: Program,
  claim: GroundLiteral,
  deriv: Derivation,
  limits: CheckLimits,
  tally: Tally,
): Verdict {
  const max = limits.maxTermDepth;
  const tooDeep = (what: string): Verdict =>
    Verdict.reject("term_too_deep", `${what} nests deeper than max_term_depth ${max}`);
  // (a) the claim.
  if (!groundWithin(claim, max, tally)) return tooDeep("claim argument");
  // (b) every node conclusion + (for Rule) subst images, and every cited clause.
  for (const node of deriv.nodes) {
    if (!groundWithin(node.conclusion, max, tally)) return tooDeep("node conclusion argument");
    if (node.kind === "rule") {
      for (const term of node.subst.values()) {
        if (!tally.termWithin(term, max)) return tooDeep("subst image term");
      }
      // A missing clause is the structural unknown_clause error raised later in the
      // forward pass; here we only depth-check a clause that exists.
      const clause = program.clause(node.clause);
      if (clause !== undefined) {
        if (!goalWithin(clause.head, max, tally)) return tooDeep("cited clause head argument");
        for (const bl of clause.body) {
          if (bl.isCount()) {
            // A count body literal has no single Goal: depth-check its filter terms + count slot.
            for (const e of bl.countLit!.filter) {
              if (!tally.termWithin(e.term, max)) return tooDeep("cited clause count filter term");
            }
            if (!tally.termWithin(bl.countLit!.count, max)) return tooDeep("cited clause count slot term");
            continue;
          }
          // Non-null: the count arm above covers the only inner-less form.
          if (!goalWithin(bl.asInner()!, max, tally)) {
            return tooDeep("cited clause body-literal argument");
          }
        }
      }
    }
  }
  return Verdict.Accept;
}

/** Every argument of a GroundLiteral nests within `max` (iterative cutoff), each measured into `tally`. */
function groundWithin(lit: GroundLiteral, max: number, tally: Tally): boolean {
  return lit.args.every((v) => tally.valueWithin(v, max));
}

/** Every argument term of a Goal nests within `max`, each measured into `tally`. */
function goalWithin(goal: Goal, max: number, tally: Tally): boolean {
  return goal.args.every((t) => tally.termWithin(t, max));
}

function checkNode<C>(
  i: number,
  node: Node,
  program: Program,
  deriv: Derivation,
  ctx: C,
  profile: CheckProfile<C>,
  depth: number[],
  certStatus: readonly CertStatus[],
  tally: Tally,
): Verdict {
  // nodesWalked: the walk begins this node, before any of its checks (a node that then rejects
  // counts). Its kind is counted first thing in its arm below.
  tally.nodesWalked += 1;
  switch (node.kind) {
    case "rule": {
      // ruleNodes
      tally.ruleNodes += 1;
      // (a) cited clause exists.
      const clause = program.clause(node.clause);
      if (clause === undefined) {
        return Verdict.reject("unknown_clause", `no clause for id "${node.clause.asStr()}"`);
      }
      // (b) positive premise indices reference strictly earlier nodes (acyclic DAG). A
      //     Neg / Count premise carries no node index — it is a checked cert side-condition,
      //     validated in (f).
      for (const p of node.premises) {
        if (typeof p === "number" && p >= i) {
          return Verdict.reject("bad_dependency_order", `premise ${p} not < node ${i}`);
        }
      }
      // (c) depth (positive premises are < i, so already computed); cap → too_deep. A
      //     Neg / Count premise contributes no depth (no node chain).
      let maxPremiseDepth = 0;
      for (const p of node.premises) {
        if (typeof p !== "number") continue;
        const d = depth[p]!;
        if (d > maxPremiseDepth) maxPremiseDepth = d;
      }
      depth[i] = maxPremiseDepth + 1;
      // maxDepthReached: the depth compared against maxDepth, a tripping one included.
      tally.reachDepth(depth[i]!);
      if (depth[i]! > profile.limits.maxDepth) {
        return Verdict.reject(
          "too_deep",
          `depth ${depth[i]} exceeds max_depth ${profile.limits.maxDepth}`,
        );
      }
      // (d) subst applied to the head is ground and equals the conclusion.
      const head = clause.head.substitute(node.subst).asGround();
      if (head === undefined) {
        return Verdict.reject("instantiation_mismatch", "clause head not ground under subst");
      }
      // Structural (#3022): a conclusion is never a relabeling of the instantiated head.
      if (!head.equals(node.conclusion)) {
        return Verdict.reject("instantiation_mismatch", "instantiated head != conclusion");
      }
      // (e) one premise per body literal.
      if (node.premises.length !== clause.body.length) {
        return Verdict.reject(
          "instantiation_mismatch",
          `premise count ${node.premises.length} != body length ${clause.body.length}`,
        );
      }
      // (f) premise k matches body literal k under subst, WITH polarity (ADR 0007):
      //     - Pos body lit ↔ Pos premise (bare index): the cited node's conclusion
      //       equals the grounded body literal.
      //     - Neg body lit ↔ Neg premise: the grounded body literal equals the premise's
      //       `atom`, which is then discharged as ABSENT from the cited (verified)
      //       certificate. A polarity mismatch in either direction is instantiation_mismatch.
      //
      //     Every comparison here is STRUCTURAL (#3022). With (d) structural too, every node's
      //     conclusion is its exact fact, so the exact cone #2256 kept for spelling-sensitive
      //     clauses now holds for every clause by construction.
      for (let k = 0; k < clause.body.length; k += 1) {
        const bodyLit = clause.body[k]!;
        // premisesPos / premisesNeg: (f) begins examining premise k, counted by its own kind (a
        // count premise is positive) before any of its checks.
        tally.premise(node.premises[k]!);
        // A Count body literal has no single underlying Goal (asInner() is null), so
        // branch on it BEFORE computing the Pos/Neg `expected` grounding.
        if (bodyLit.isCount()) {
          const premise = node.premises[k]!;
          if (!isCountPremise(premise)) {
            return Verdict.reject("instantiation_mismatch", `premise ${k} polarity != body literal ${k} polarity`);
          }
          // The grounded count body literal must agree with the premise's
          // pred/filter/project/k (positional + value agreement) before re-deriving the count.
          const gc = bodyLit.countLit!.substitute(node.subst);
          const gFilter: GroundFilterEntry[] = [];
          let groundOK = true;
          for (const e of gc.filter) {
            const v = Term.eraseGround(e.term);
            if (v === undefined) {
              groundOK = false;
              break;
            }
            gFilter.push({ pos: e.pos, value: v });
          }
          const gCount = Term.eraseGround(gc.count);
          if (!groundOK || gCount === undefined) {
            return Verdict.reject("instantiation_mismatch", `count body literal ${k} not ground under subst`);
          }
          // Structural, like every site (#3022).
          if (
            !gc.pred.equals(premise.pred) ||
            !equalGroundFilter(gFilter, premise.filter) ||
            !projectEquals(gc.project, premise.project) ||
            !valueEquals(gCount, premise.k)
          ) {
            return Verdict.reject("instantiation_mismatch", `count premise ${k} != body literal ${k} under subst`);
          }
          const countResult = verifyCountPremise(premise, node.conclusion.pred, deriv, certStatus);
          if (countResult.kind !== "accept") {
            return countResult;
          }
          continue;
        }
        // Non-null: the count premise arm above ends in `continue`.
        const expected = bodyLit.asInner()!.substitute(node.subst).asGround();
        if (expected === undefined) {
          return Verdict.reject(
            "instantiation_mismatch",
            `body literal ${k} not ground under subst`,
          );
        }
        const premise = node.premises[k]!;
        if (typeof premise === "number" && !bodyLit.isNeg()) {
          // Pos ↔ Pos (a bare node index against a positive body literal).
          // The cited node's conclusion must be EXACTLY the grounded body literal, for every cited
          // node kind (#3022; #2232 already required it of a Builtin, whose theory decides on its
          // own spelling).
          if (!deriv.nodes[premise]!.conclusion.equals(expected)) {
            return Verdict.reject(
              "instantiation_mismatch",
              `premise ${k} conclusion != body literal ${k} under subst`,
            );
          }
        } else if (isNegPremise(premise) && bodyLit.isNeg()) {
          // Neg ↔ Neg (#2227): the premise's atom must EXACTLY equal the grounded negated body
          // literal. Its absence is then looked up by exact membership in the sealed table, so a
          // match under account equality would transfer an absence judged about one spelling to
          // another. Then discharge it.
          if (!premise.atom.equals(expected)) {
            return Verdict.reject(
              "instantiation_mismatch",
              `neg premise ${k} atom != body literal ${k} under subst`,
            );
          }
          const negResult = verifyNegPremise(premise, node.conclusion.pred, deriv, certStatus);
          if (negResult.kind !== "accept") {
            return negResult;
          }
        } else {
          return Verdict.reject(
            "instantiation_mismatch",
            `premise ${k} polarity != body literal ${k} polarity`,
          );
        }
      }
      // (g) sealing / partition on the head predicate (local checks, §4.2/§4.4):
      //     a clause head must be intensional — not extensional, not theory-owned.
      if (profile.leaves.extensional().contains(node.conclusion.pred)) {
        return Verdict.reject(
          "sealed_violation",
          "rule head collides with an extensional predicate",
        );
      }
      if (profile.theory.owns(node.conclusion.pred)) {
        return Verdict.reject(
          "predicate_partition_violation",
          "rule head predicate is owned by a theory",
        );
      }
      // (h) THEN delegate metadata admissibility (§4 ob.2: structural-then-delegate).
      // admissibilityChecks: one `admissible` call.
      tally.admissibilityChecks += 1;
      const verdict = profile.admit.admissible(clause, node.meta, ctx);
      if (verdict.kind === "admit") {
        return Verdict.Accept;
      }
      return Verdict.reject("rule_inadmissible", verdict.code);
    }

    case "builtin": {
      // builtinNodes
      tally.builtinNodes += 1;
      depth[i] = 1;
      // maxDepthReached
      tally.reachDepth(depth[i]!);
      if (depth[i]! > profile.limits.maxDepth) {
        return Verdict.reject("too_deep", "depth 1 exceeds max_depth");
      }
      const owned = profile.theory.owns(node.conclusion.pred);
      // partition: a builtin predicate must be theory-owned, and not also
      // extensional (overlap is a partition violation, §4.4).
      if (!owned) {
        return Verdict.reject(
          "predicate_partition_violation",
          "no theory owns the builtin predicate",
        );
      }
      if (profile.leaves.extensional().contains(node.conclusion.pred)) {
        return Verdict.reject(
          "predicate_partition_violation",
          "builtin predicate is also extensional",
        );
      }
      // #3126: the ground verdict, which can say "not decided". The detail of a false is the
      // theory's own code, read before any conversion into the algebra.
      // theoryDecisions: one `decideGround` call.
      tally.theoryDecisions += 1;
      const verdict = readGround(profile.theory.decideGround(node.conclusion));
      switch (verdict.arm) {
        case "holds":
          return Verdict.Accept;
        case "fails":
          return Verdict.reject("builtin_failed", verdict.code);
        case "not_decided":
          if (isDisowned(verdict)) {
            // owns() said yes but decideGround disowns: an inconsistent theory.
            return Verdict.reject(
              "predicate_partition_violation",
              "theory owns predicate but returned NotMine",
            );
          }
          // A stop is refused by name, never read as a decision (#3126).
          return Verdict.reject("builtin_not_decided", verdict.cause.kind);
      }
    }

    case "leaf": {
      // leafNodes
      tally.leafNodes += 1;
      depth[i] = 1;
      // maxDepthReached
      tally.reachDepth(depth[i]!);
      if (depth[i]! > profile.limits.maxDepth) {
        return Verdict.reject("too_deep", "depth 1 exceeds max_depth");
      }
      const extensional = profile.leaves.extensional().contains(node.conclusion.pred);
      const owned = profile.theory.owns(node.conclusion.pred);
      // sealing / partition (§4.2/§4.4): a leaf may conclude only an extensional
      // predicate.
      if (extensional && owned) {
        return Verdict.reject(
          "predicate_partition_violation",
          "leaf predicate is both extensional and theory-owned",
        );
      }
      if (!extensional) {
        if (owned) {
          return Verdict.reject(
            "predicate_partition_violation",
            "leaf predicate is owned by a theory, not extensional",
          );
        }
        // not extensional and not a builtin ⇒ it is intensional: a leaf concluding
        // an intensional predicate is the sealing error.
        return Verdict.reject(
          "sealed_violation",
          "leaf concludes a non-extensional (intensional) predicate",
        );
      }
      // leafVerifications: one `verify` call.
      tally.leafVerifications += 1;
      const verdict = profile.leaves.verify(node.conclusion, node.evidence, ctx);
      if (verdict.kind === "admit") {
        return Verdict.Accept;
      }
      return Verdict.reject("leaf_rejected", verdict.code);
    }
  }
}

/**
 * The `Builtin` predicates in `deriv` that **no theory bound by this profile owns** - the
 * pre-check capability query (issue #1371).
 *
 * Ask this **before** {@link check}. An empty result means this host can decide every builtin
 * the derivation cites; a non-empty one names exactly the predicates it cannot, so a caller
 * knows **which theory to bind** rather than only that something is missing.
 *
 * ## Why it exists
 *
 * `check` re-decides every builtin node through `profile.theory`. On a host that binds no
 * theory owning the predicate, the rejection is `predicate_partition_violation` - a
 * **structural-band** code whose meaning is *this account is malformed*. But the account may
 * be sound: it is the **verifier** that lacks a capability. A consumer whose CI referee
 * branches on the code then dispatches an investigator at the **producer**, when nothing is
 * wrong anywhere except the binding set of the host doing the re-check.
 *
 * ## What an empty result does NOT promise
 *
 * It does **not** mean `check` will accept. It answers **one** condition - theory ownership.
 * Two other conditions raise the same structural code and are untouched here: a builtin
 * predicate that is **also extensional** (a genuine partition overlap), and a theory whose
 * `owns()` says yes while `decideGround()` disowns the atom (an inconsistent theory).
 *
 * So **empty means no capability refusal will occur, never that the account is valid.**
 *
 * ## Scope
 *
 * Additive and non-breaking: a helper over existing contract types, adding no rejection code
 * and moving no vector. It reads builtin conclusions and `theory.owns` only - no `decideGround()`
 * call, so it is total and side-effect-free. Order is derivation node order, deduplicated on
 * first appearance, so the result is deterministic for a given derivation.
 */
export function unownedBuiltinPredicates<C>(
  deriv: Derivation,
  profile: CheckProfile<C>,
): PredicateSymbol[] {
  const out: PredicateSymbol[] = [];
  for (const node of deriv.nodes) {
    if (node.kind !== "builtin") continue;
    const pred = node.conclusion.pred;
    if (profile.theory.owns(pred)) continue;
    if (!out.some((p) => p.equals(pred))) out.push(pred);
  }
  return out;
}

/**
 * `true` when this profile can decide every builtin predicate `deriv` cites - the boolean
 * convenience over {@link unownedBuiltinPredicates}.
 *
 * Same limit as the report it wraps: `true` means *no capability refusal will occur*, not
 * *`check` will accept*. Prefer the list form when reporting to a human or a log - it names
 * what to bind, and a bare `false` invites exactly the "the account is bad" reading this
 * query exists to prevent.
 */
export function profileDecidesAllBuiltins<C>(
  deriv: Derivation,
  profile: CheckProfile<C>,
): boolean {
  return unownedBuiltinPredicates(deriv, profile).length === 0;
}

/**
 * The `Builtin` conclusions this profile's theory **owns but disowns** - `owns(pred)` is
 * `true` while `decideGround(conclusion)` answers the disowning `inconsistent_theory` fault.
 *
 * A non-empty result is a **verifier-side defect**: the bound `Theory` violates the coherence
 * obligation of §5, which requires `decideGround` to reach a verdict on every atom whose predicate
 * `owns` claims. `check` rejects this with the structural code `predicate_partition_violation`
 * - correctly, since the account cannot be verified by this profile - but a consumer reading
 * that code alone is pointed at the **producer** for what is a bug in the host's own theory
 * binding. This query is the attribution the code cannot carry (issue #1378): it names the
 * atoms that expose it.
 *
 * ⚠ Unlike {@link unownedBuiltinPredicates}, this one CALLS `decideGround`. Ownership is a property
 * of a *predicate*, but incoherence is only observable per *atom*, so the question cannot be
 * answered without deciding. It therefore costs what the corresponding part of `check` costs
 * and is **not** side-effect-free against a theory whose `decideGround` is expensive or stateful.
 * Its value is **attribution after a rejection**, not avoidance before one.
 *
 * ⛔ An empty result does **not** certify the theory coherent. It witnesses only that no atom
 * *this derivation cites* exposes the disagreement; a theory incoherent on any other atom
 * returns empty here. Read it as *"this rejection is not that bug"*, never as *"the theory is
 * sound"*.
 *
 * Additive and non-breaking: no `RejectionCode` member, no vector moved. Order is derivation
 * node order, deduplicated on first appearance, so the result is deterministic for a given
 * derivation. The dedup test precedes the `decideGround` call, so a repeated offending atom is
 * decided once.
 */
export function incoherentBuiltinAtoms<C>(
  deriv: Derivation,
  profile: CheckProfile<C>,
): GroundLiteral[] {
  const out: GroundLiteral[] = [];
  for (const node of deriv.nodes) {
    if (node.kind !== "builtin") continue;
    const conc = node.conclusion;
    if (!profile.theory.owns(conc.pred)) continue;
    if (out.some((a) => a.equals(conc))) continue;
    // The disowning `inconsistent_theory` fault (#3126). A theory that stopped (a work cap) is not
    // listed: it did not disown the atom.
    if (isDisowned(readGround(profile.theory.decideGround(conc)))) out.push(conc);
  }
  return out;
}
