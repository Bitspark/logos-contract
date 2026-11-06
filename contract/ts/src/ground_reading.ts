/**
 * Internal to the contract (not exported from `index.ts`): a theory's ground verdict read once, for
 * `check`'s readers (#3126).
 */
import { fault, type NonCompletion, type TheoryGround } from "./completion.js";

/**
 * A ground verdict read once, so each reader switches on three arms: the theory's code for a
 * false, the cause for a verdict it did not decide. A limit (no caller's limit reaches a theory) or
 * any value outside the type reads as the fault `malformed_outcome`.
 */
export type GroundReading =
  | { readonly arm: "holds" }
  | { readonly arm: "fails"; readonly code: string }
  | { readonly arm: "not_decided"; readonly cause: NonCompletion };

export function readGround(g: TheoryGround): GroundReading {
  if (g?.kind === "completed") {
    if (g.value?.kind === "holds") return { arm: "holds" };
    if (g.value?.kind === "fails" && typeof g.value.code === "string") return { arm: "fails", code: g.value.code };
  } else if (g?.kind === "not_completed" && typeof g.cause?.kind === "string") {
    return { arm: "not_decided", cause: g.cause };
  }
  return { arm: "not_decided", cause: fault("malformed_outcome") };
}

/** Whether a reading is the fault a `not_mine` from `decide` becomes (#3126). */
export function isDisowned(r: GroundReading): boolean {
  return r.arm === "not_decided" && r.cause.kind === "inconsistent_theory";
}

