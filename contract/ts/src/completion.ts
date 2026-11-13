/**
 * The completion algebra: an outcome that keeps "established false" apart from "did not finish",
 * and the three-valued `not`/`and`/`or` over it (research 0031 row 15, #3164).
 *
 * PROPOSED: additive, and ratified by the ADR for research 0030 and 0031 (#3147). Since #3126 the
 * Theory SPI answers through it: a theory's `decideGround` returns a `TheoryGround`, and checker SPI
 * v2 (ADR 0036 D8) makes that member required. The Rust original is
 * `contract/rs/src/completion.rs`, which carries the full rationale; this is its TypeScript twin,
 * and `vectors/completion_algebra.json` pins all three cores.
 *
 * A decider that stops before it establishes a fact must not report that fact as false. A
 * `Completion` is `completed(value)`, `limit_exceeded(limit)` or `not_completed(cause)`. A ground
 * literal's outcome is a `GroundOutcome`, `Completion<Decision, L>`, where a `Decision` is `holds`
 * or `fails(code)`. The layer that sets a caller's limit owns its vocabulary, so the algebra is
 * generic over `L` and only carries it.
 *
 * A non-completion is a STOP or a FAULT (seat:caa's ruling on #3179). A stop's evidence is only
 * incomplete, so it carries the scope its effect reaches: `capacity`, `work_cap` and
 * `instantiation` at any scope, `host_refusal` and `reply_unreadable` at request scope only. A
 * fault (`inconsistent_theory`, `malformed_outcome`) says the evidence is invalid and carries no
 * scope. The `NonCompletion` type admits only these pairs, and `causeOf` refuses any other.
 *
 * `not`, `and` and `or` are strong Kleene (¬U = U, F ∧ U = F, H ∨ U = H), with scoped absorption: a
 * stop local to one literal, branch or enumeration may be absorbed by an independently decided
 * operand, but a stop at dependency, theory-snapshot or request scope, and a caller's limit, are
 * dominant and never absorbed, and a fault outranks even those. `and`/`or` return the operand of
 * the highest class, the leftmost on a tie:
 *
 *     and   holds < absorbable stop < fails < dominant stop or limit < fault
 *     or    fails < absorbable stop < holds < dominant stop or limit < fault
 *
 * TypeScript types do not establish what a value holds at run time. Every function here reads a
 * value outside these types (an unknown kind, an illegal cause, `null`) as the fault
 * `malformed_outcome`: never a logical answer.
 */

/** How far a stop's effect reaches, which decides whether another operand may absorb it. */
export type CauseScope =
  | "literal"
  | "branch"
  | "enumeration"
  | "dependency"
  | "theory_snapshot"
  | "request";

/** A stop that may reach any scope. */
export type ScopedStopKind = "capacity" | "work_cap" | "instantiation";

/** A stop that is always request-wide: the host refusal channel is sticky for the run. */
export type RequestStopKind = "host_refusal" | "reply_unreadable";

/**
 * A fault: the evidence is invalid, not merely incomplete. `malformed_outcome` is a value no
 * constructor could have built, or a host's reply to a declared builtin that is not a value of the
 * reply type: the host broke its channel's contract (#2734 3e-iii). A well-formed reply nested past
 * the reader's depth is not this fault: it is the `reply_unreadable` stop, a capacity of the reader.
 */
export type FaultKind = "inconsistent_theory" | "malformed_outcome";

/** Why a producer did not decide. */
export type NonCompletionKind = ScopedStopKind | RequestStopKind | FaultKind;

/** Why a producer did not decide: a stop with the scope its effect reaches, or a fault. */
export type NonCompletion =
  | { readonly kind: ScopedStopKind; readonly scope: CauseScope }
  | { readonly kind: RequestStopKind; readonly scope: "request" }
  | { readonly kind: FaultKind };

/** Why the language says a literal is false. No conversion from a `NonCompletion` exists. */
export type FalseCode = "unsatisfied";

/** The language's decision on a ground literal. */
export type Decision = { readonly kind: "holds" } | { readonly kind: "fails"; readonly code: FalseCode };

/** A producer's result: the value, a caller's limit reached, or a stop before the value was established. */
export type Completion<T, L> =
  | { readonly kind: "completed"; readonly value: T }
  | { readonly kind: "limit_exceeded"; readonly limit: L }
  | { readonly kind: "not_completed"; readonly cause: NonCompletion };

/** A ground literal's outcome: decided true or false, a caller's limit, or not decided. */
export type GroundOutcome<L> = Completion<Decision, L>;

export const holds: Decision = Object.freeze({ kind: "holds" });

export function fails(code: FalseCode): Decision {
  return { kind: "fails", code };
}

/** A stop that may reach any scope. */
export function stop(kind: ScopedStopKind, scope: CauseScope): NonCompletion {
  return { kind, scope };
}

/** A request-wide stop. */
export function requestStop(kind: RequestStopKind): NonCompletion {
  return { kind, scope: "request" };
}

/** A fault. */
export function fault(kind: FaultKind): NonCompletion {
  return { kind };
}

/** A kind and scope that do not form a `NonCompletion`. */
export class IllegalCauseError extends RangeError {
  constructor(
    readonly causeKind: string,
    readonly causeScope: string | undefined,
  ) {
    super(
      causeScope === undefined
        ? `illegal_cause: ${causeKind} with no scope`
        : `illegal_cause: ${causeKind} at ${causeScope} scope`,
    );
    this.name = "IllegalCauseError";
  }
}

/**
 * The checked constructor, for a decoder: the cause a kind and scope name, or an
 * `IllegalCauseError` when they do not form one (an unknown kind or scope, a fault with a scope, a
 * request-wide stop at a narrower scope, or a stop without one).
 */
export function causeOf(kind: string, scope?: string): NonCompletion {
  const c: unknown = scope === undefined ? { kind } : { kind, scope };
  if (!validCause(c)) throw new IllegalCauseError(kind, scope);
  return c;
}

export function completed<T, L>(value: T): Completion<T, L> {
  return { kind: "completed", value };
}

export function limitExceeded<T, L>(limit: L): Completion<T, L> {
  return { kind: "limit_exceeded", limit };
}

export function notCompleted<T, L>(c: NonCompletion): Completion<T, L> {
  return { kind: "not_completed", cause: c };
}

/**
 * Whether a stop at this scope may be absorbed by an independently established operand. Only a stop
 * local to one literal, branch or enumeration can; a value outside the type cannot.
 */
export function isAbsorbable(scope: CauseScope): boolean {
  switch (scope) {
    case "literal":
    case "branch":
    case "enumeration":
      return true;
    case "dependency":
    case "theory_snapshot":
    case "request":
      return false;
    default:
      return false;
  }
}

/** Whether the kind is a fault. */
export function isFault(kind: NonCompletionKind): boolean {
  switch (kind) {
    case "inconsistent_theory":
    case "malformed_outcome":
      return true;
    case "capacity":
    case "work_cap":
    case "instantiation":
    case "host_refusal":
    case "reply_unreadable":
      return false;
    default:
      return false;
  }
}

function validScope(scope: unknown): boolean {
  switch (scope as CauseScope) {
    case "literal":
    case "branch":
    case "enumeration":
    case "dependency":
    case "theory_snapshot":
    case "request":
      return true;
    default:
      return false;
  }
}

function validCode(code: FalseCode): boolean {
  switch (code) {
    case "unsatisfied":
      return true;
    default:
      return false;
  }
}

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null;
}

/** Whether a value is a `NonCompletion`: a legal kind and scope pair, with nothing else missing. */
function validCause(c: unknown): c is NonCompletion {
  if (!isObject(c)) return false;
  const scope = c["scope"];
  switch (c["kind"] as NonCompletionKind) {
    case "capacity":
    case "work_cap":
    case "instantiation":
      return validScope(scope);
    case "host_refusal":
    case "reply_unreadable":
      return scope === "request";
    case "inconsistent_theory":
    case "malformed_outcome":
      return scope === undefined;
    default:
      return false;
  }
}

function validDecision(d: Decision): boolean {
  if (!isObject(d)) return false;
  switch (d.kind) {
    case "holds":
      return true;
    case "fails":
      return validCode(d.code);
    default:
      return false;
  }
}

const MALFORMED: NonCompletion = Object.freeze({ kind: "malformed_outcome" });

/**
 * Every valid outcome unchanged; any other value (an unknown kind, an invalid decision, an illegal
 * cause, `null`) as the fault `malformed_outcome`.
 */
export function normalize<L>(o: GroundOutcome<L>): GroundOutcome<L> {
  if (!isObject(o)) return notCompleted(MALFORMED);
  switch (o.kind) {
    case "completed":
      return validDecision(o.value) ? o : notCompleted(MALFORMED);
    case "limit_exceeded":
      return o;
    case "not_completed":
      return validCause(o.cause) ? o : notCompleted(MALFORMED);
    default:
      return notCompleted(MALFORMED);
  }
}

type Class = "holds" | "fails" | "absorbable" | "dominant" | "fault";

/** The class of a normalized outcome. */
function classOf<L>(o: GroundOutcome<L>): Class {
  switch (o.kind) {
    case "completed":
      return o.value.kind === "holds" ? "holds" : "fails";
    case "not_completed": {
      const c = o.cause;
      if (isFault(c.kind) || !("scope" in c)) return "fault";
      return isAbsorbable(c.scope) ? "absorbable" : "dominant";
    }
    case "limit_exceeded":
      return "dominant";
    default:
      return "fault";
  }
}

function andRank(c: Class): number {
  switch (c) {
    case "holds":
      return 0;
    case "absorbable":
      return 1;
    case "fails":
      return 2;
    case "dominant":
      return 3;
    case "fault":
      return 4;
    default:
      return 4;
  }
}

function orRank(c: Class): number {
  switch (c) {
    case "fails":
      return 0;
    case "absorbable":
      return 1;
    case "holds":
      return 2;
    case "dominant":
      return 3;
    case "fault":
      return 4;
    default:
      return 4;
  }
}

/** The operand of the higher rank; `a` on a tie. */
function higher<L>(a: GroundOutcome<L>, b: GroundOutcome<L>, rank: (c: Class) => number): GroundOutcome<L> {
  const x = normalize(a);
  const y = normalize(b);
  return rank(classOf(y)) > rank(classOf(x)) ? y : x;
}

/** Strong-Kleene negation: ¬H = F, ¬F = H, and an undecided outcome or a limit is returned unchanged. */
export function not<L>(a: GroundOutcome<L>): GroundOutcome<L> {
  const x = normalize(a);
  switch (classOf(x)) {
    case "holds":
      return completed(fails("unsatisfied"));
    case "fails":
      return completed(holds);
    case "absorbable":
    case "dominant":
    case "fault":
      return x;
    default:
      return x;
  }
}

/**
 * Strong-Kleene conjunction with scoped absorption: F ∧ U = F only when U is an absorbable stop; a
 * dominant stop or a limit is never absorbed, and a fault outranks both. Returns the higher-class
 * operand, `a` on a tie.
 */
export function and<L>(a: GroundOutcome<L>, b: GroundOutcome<L>): GroundOutcome<L> {
  return higher(a, b, andRank);
}

/**
 * Strong-Kleene disjunction with scoped absorption: H ∨ U = H only when U is an absorbable stop; a
 * dominant stop or a limit is never absorbed, and a fault outranks both. Returns the higher-class
 * operand, `a` on a tie.
 */
export function or<L>(a: GroundOutcome<L>, b: GroundOutcome<L>): GroundOutcome<L> {
  return higher(a, b, orRank);
}

/**
 * A theory's decision on a ground literal (#3126, seat:caa's ruling (C)): what a theory's
 * `decideGround` returns inside a `Completion`. Two vocabularies, each with one owner: `FalseCode`
 * is the LANGUAGE's closed vocabulary, and the combinators fold over it; a theory's `fails` code is
 * an OPEN value space every theory and consumer owns, and `check` carries it as the
 * `builtin_failed` detail. So the theory's code rides here as data, and `decisionOf` is the one way
 * into the algebra. Rust's `completion::TheoryDecision`.
 */
export type TheoryDecision = { readonly kind: "holds" } | { readonly kind: "fails"; readonly code: string };

export const theoryHolds: TheoryDecision = Object.freeze({ kind: "holds" });

export function theoryFails(code: string): TheoryDecision {
  return { kind: "fails", code };
}

/** The limit vocabulary of a producer no caller's limit reaches (Rust's uninhabited `NoCallerLimit`). */
export type NoCallerLimit = never;

/**
 * What a theory's `decideGround` returns (checker SPI v2, ADR 0036 D8 change 3): its decision, or
 * NOT DECIDED. `completed(holds)` and `completed(fails(code))` are the decision; `not_completed(cause)`
 * is a stop before the fact was established (a work cap, a capacity), never a false; and an atom the
 * theory does not own is the named `inconsistent_theory` fault, {@link TheoryGround.disowned}. A
 * theory never reaches a caller's limit (`NoCallerLimit`). Rust's `TheoryGround`.
 */
export type TheoryGround = Completion<TheoryDecision, NoCallerLimit>;

/** The three answers a theory builds most often, Rust's `TheoryGround::{holds, fails, disowned}`. */
export const TheoryGround = Object.freeze({
  /** The atom holds. */
  holds(): TheoryGround {
    return completed(theoryHolds);
  },
  /**
   * The theory decided the atom does not hold; `code` is the theory's own name for why (surfaced
   * under `builtin_failed`).
   */
  fails(code: string): TheoryGround {
    return completed(theoryFails(code));
  },
  /**
   * Not this theory's predicate: the named `inconsistent_theory` fault. `check` routes by
   * `Theory.owns`, so a correctly-routed call never returns it.
   */
  disowned(): TheoryGround {
    return notCompleted(fault("inconsistent_theory"));
  },
});

/**
 * The ONE conversion from a theory's answer to the algebra's `GroundOutcome` (#3126, seat:caa's
 * ruling (C)). A theory's false code is the theory's own, so it becomes the language's
 * `unsatisfied`. A non-completion and a limit pass through unchanged: nothing here turns "not
 * decided" into a decision. Every site that folds a theory's answer with `not`/`and`/`or` calls
 * it; a reader that reports the theory's code (`check`'s `builtin_failed` detail) reads the
 * `TheoryDecision` before converting. A value outside the types is the fault `malformed_outcome`.
 * Rust's `completion::decision_of`.
 */
export function decisionOf<L>(o: Completion<TheoryDecision, L>): GroundOutcome<L> {
  if (!isObject(o)) return notCompleted(MALFORMED);
  switch (o.kind) {
    case "completed": {
      const v: unknown = o.value;
      if (isObject(v) && v.kind === "holds") return completed(holds);
      if (isObject(v) && v.kind === "fails" && typeof v.code === "string") return completed(fails("unsatisfied"));
      return notCompleted(MALFORMED);
    }
    case "limit_exceeded":
      return limitExceeded(o.limit);
    case "not_completed":
      return validCause(o.cause) ? notCompleted(o.cause) : notCompleted(MALFORMED);
    default:
      return notCompleted(MALFORMED);
  }
}
