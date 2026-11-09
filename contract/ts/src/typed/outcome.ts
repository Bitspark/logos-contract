import type { Expr } from "./expr.js";
import type { Policy, Statement } from "./model.js";
import { CHECKER, FOUNDATION } from "./model.js";

export type InvalidCode = "malformed-input" | "escaped-variable" | "unknown-constant"
  | "duplicate-constant" | "missing-assumptions" | "empty-constant-name"
  | "expected-universe" | "expected-function" | "expected-sigma" | "type-mismatch";
export type IncompleteCause = "input-nodes" | "input-depth" | "collection-entries"
  | "name-bytes" | "work" | "depth" | "universe-capacity" | "index-capacity";
export type UnsupportedCause = "foundation" | "unadmitted-foundation"
  | "unadmitted-checker" | "unadmitted-dependency";
export type Phase = "preflight" | "declaration" | "context" | "expected"
  | "candidate" | "policy" | "snapshot";
export interface Location { readonly phase: Phase; readonly index?: number }

export type Rejection =
  | { readonly kind: "invalid"; readonly code: InvalidCode; readonly location: Location }
  | { readonly kind: "incomplete"; readonly code: IncompleteCause; readonly location: Location }
  | { readonly kind: "unsupported"; readonly code: UnsupportedCause; readonly location: Location };

const mint = Symbol("typed checker acceptance");

// Not exported: the only callable public constructor is the checker. The token
// also refuses construction through JavaScript reflection on an existing value.
class AcceptedValue {
  readonly #brand = true;
  readonly foundation = FOUNDATION;
  readonly checker = CHECKER;
  readonly statement: Statement;
  readonly candidate: Expr;
  readonly policy: Policy;
  readonly dependencies: readonly string[];
  readonly usedConstants: readonly string[];
  readonly steps: number;

  constructor(token: symbol, statement: Statement, candidate: Expr, policy: Policy,
    dependencies: readonly string[], usedConstants: readonly string[], steps: number) {
    if (token !== mint) throw new TypeError("acceptance is constructed only by the checker");
    this.statement = statement;
    this.candidate = candidate;
    this.policy = policy;
    this.dependencies = Object.freeze([...dependencies]);
    this.usedConstants = Object.freeze([...usedConstants]);
    this.steps = steps;
    Object.freeze(this);
  }
}

/** A checker-issued result; its statement, policy and proof are immutable snapshots. */
export type Acceptance = AcceptedValue;
export type Outcome = { readonly kind: "accepted"; readonly accepted: Acceptance } | Rejection;

/** Internal mint; deliberately not exported by the public typed namespace. */
export function accepted(statement: Statement, candidate: Expr, policy: Policy,
  dependencies: readonly string[], usedConstants: readonly string[], steps: number): Outcome {
  return Object.freeze({ kind: "accepted", accepted: new AcceptedValue(mint, statement,
    candidate, policy, dependencies, usedConstants, steps) });
}

/** Internal structured exception. Unexpected host faults are never certified. */
export class CheckFailure {
  constructor(readonly outcome: Rejection) {}
}
