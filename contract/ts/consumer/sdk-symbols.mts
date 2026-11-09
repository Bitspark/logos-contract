import type { Value } from "@bitspark/ontos-core";
import { Term, typed } from "@bitspark/logos-contract";
// @ts-expect-error Ontos owns ground Value.
import type { Value as LogosValue } from "@bitspark/logos-contract";
// @ts-expect-error The old receipt name is outside the supported namespace.
type OldReceipt = typed.Accepted;
export function lift(value: Value): Term { return Term.fromValue(value); }
export function acceptance(out: typed.Outcome): typed.Acceptance | undefined {
  return out.kind === "accepted" ? out.accepted : undefined;
}

export const checkTyped: (
  statement: typed.Statement, candidate: typed.Expr, policy: typed.Policy, limits?: typed.Limits,
) => typed.Outcome = typed.check;
// @ts-expect-error The receiver can name a checker receipt as a type. Only checking issues one.
void typed.Acceptance;
