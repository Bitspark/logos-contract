import {
  checkClosedModelChain, checkWithWorldMemo, type CertContext, type CheckProfile,
  type ClosedModelCert, type Derivation, type GroundLiteral, type Outcome, type Program, type WorldMemo,
} from "@bitspark/logos-contract";
// @ts-expect-error The checker owns the position of a certificate in the chain.
import type { CertPlace } from "@bitspark/logos-contract";
// @ts-expect-error Only the checker can establish the intermediate verification status.
import type { CertStatus } from "@bitspark/logos-contract";

export function checkChain<C>(program: Program, chain: readonly ClosedModelCert[], ctx: C,
  profile: CheckProfile<C>, pins: CertContext): Outcome {
  return checkClosedModelChain(program, chain, ctx, profile, pins);
}

export function checkMemo<C>(memo: WorldMemo<C>, claim: GroundLiteral, proof: Derivation): Outcome {
  return checkWithWorldMemo(memo, claim, proof);
}
