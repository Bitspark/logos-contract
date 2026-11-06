/** Version 1 in-process dependent-fragment checking. No byte decoder or engine. */
export { type Expr, sort, variable, constant, pi, lam, app, sigma, pair, fst, snd,
  nat, zero, succ, natElim, bool, falseValue, trueValue, boolElim, id, refl, transport } from "./expr.js";
export { FOUNDATION, CHECKER, MAX_INPUT_DEPTH, MAX_DEPTH, MAX_NATURAL,
  type Declaration, assume, define,
  type Statement, type StatementInput, statement,
  type Policy, type PolicyInput, policy,
  type Limits, type LimitsInput, limits, defaultLimits } from "./model.js";
export type { Accepted, Outcome, Rejection, InvalidCode, IncompleteCause,
  UnsupportedCause, Phase, Location } from "./outcome.js";
export { check } from "./check.js";
