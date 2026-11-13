import { type CheckLimitError, type CheckLimits, type Verdict, captureCheckLimits } from "./check.js";
import { type ClosedModelCert, hashFromBytes } from "./cert.js";
import type { CertContext } from "./cert_check.js";
import { type Derivation } from "./derivation.js";
import { hasNativeTermShape, nativeSubst } from "./native_copy.js";
import { copyClosedWorld, copyDerivation } from "./proof_copy.js";
import { Term, type Subst } from "./term.js";
import { OctetWidthError } from "./octets.js";

export type CaptureResult<T> = { readonly kind: "captured"; readonly value: T } | Extract<Verdict, { kind: "reject" }>;

function budgetFault(error: CheckLimitError): Extract<Verdict, { kind: "reject" }> {
  return { kind: "reject", code: "invalid_check_limits", detail: error.message };
}

// The native term algebra is closed. Test the private fields before reading a
// child or calling a method. A prototype alone cannot supply immutable data. A key
// needs no test: a `Subst` holds only plain `VarId`s, whose names passed §2a (#3288).
function substitutionShapeFault(subst: Subst, limits: CheckLimits): Extract<Verdict, { kind: "reject" }> | undefined {
  for (const [id, term] of subst) {
    if (!hasNativeTermShape(term, limits.maxTermDepth)) {
      return { kind: "reject", code: "unknown_node_kind", detail: `substitution image of ${id.asStr()} is not a native term` };
    }
  }
  return undefined;
}

/** Capture a substitution of bounded native terms before grounding a goal.
 * Success establishes the shape of the data only. */
export function captureSubst(subst: Subst, limits: CheckLimits): CaptureResult<Subst> {
  const bound = captureCheckLimits(limits);
  if (!bound.ok) return budgetFault(bound.error);
  limits = bound.value;
  let answer: Subst;
  try {
    answer = nativeSubst(subst);
  } catch (error) {
    if (!(error instanceof TypeError)) throw error;
    return { kind: "reject", code: "unknown_node_kind", detail: "a substitution must be a Subst" };
  }
  const fault = substitutionShapeFault(answer, limits);
  if (fault !== undefined) return fault;
  for (const [id, term] of answer) {
    if (!Term.depthLe(term, limits.maxTermDepth)) {
      return { kind: "reject", code: "term_too_deep", detail: `substitution image of ${id.asStr()} exceeds max_term_depth ${limits.maxTermDepth}` };
    }
  }
  return { kind: "captured", value: answer };
}

/** Own a proposed proof for a subsequent check. Apply the checker's header
 * refusals before inspecting nodes or copying closed-world data. */
export function captureDerivation(proof: Derivation, limits: CheckLimits): CaptureResult<Derivation> {
  const bound = captureCheckLimits(limits);
  if (!bound.ok) return budgetFault(bound.error);
  limits = bound.value;
  try {
    const nodes = proof.nodes;
    if (!Array.isArray(nodes)) throw new TypeError("proof nodes must be an array");
    const count = nodes.length;
    if (count === 0) return { kind: "reject", code: "empty_derivation", detail: "derivation has no nodes" };
    if (count > limits.maxNodes) {
      return { kind: "reject", code: "too_many_nodes", detail: `${count} nodes exceeds max_nodes ${limits.maxNodes}` };
    }
    const root = proof.root;
    if (!Number.isSafeInteger(root) || root < 0 || root >= count) {
      const label = typeof root === "number" ? String(root) : "invalid";
      return { kind: "reject", code: "root_out_of_range", detail: `root ${label} out of range (len ${count})` };
    }
    const owned = copyDerivation(nodes, count, root, proof.closedWorld, limits.maxTermDepth);
    for (const node of owned.nodes) {
      if (node.kind === "rule") {
        const fault = substitutionShapeFault(node.subst, limits);
        if (fault !== undefined) return fault;
      }
    }
    return supportShapeFault(owned.closedWorld, limits) ?? { kind: "captured", value: owned };
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof OctetWidthError)) throw error;
    return { kind: "reject", code: "unknown_node_kind", detail: "unrecognized native proof data" };
  }
}

function supportShapeFault(world: readonly ClosedModelCert[], limits: CheckLimits): Extract<Verdict, { kind: "reject" }> | undefined {
  for (const cert of world) {
    for (const edge of cert.supports) {
      const fault = substitutionShapeFault(edge.subst, limits);
      if (fault !== undefined) return fault;
    }
  }
  return undefined;
}

/** Read a standalone certificate chain through the same account as a derivation. */
export function captureWorld(chain: readonly ClosedModelCert[], limits: CheckLimits): CaptureResult<ClosedModelCert[]> {
  const bound = captureCheckLimits(limits);
  if (!bound.ok) return budgetFault(bound.error);
  limits = bound.value;
  try {
    const world = copyClosedWorld(chain, limits.maxTermDepth);
    return supportShapeFault(world, limits) ?? { kind: "captured", value: world };
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof OctetWidthError)) throw error;
    return { kind: "reject", code: "unknown_node_kind", detail: "unrecognized native certificate data" };
  }
}

/** @internal Capture the native run pins before program or verifier callbacks. */
export function captureCertContext(context: CertContext): CertContext {
  const programHash = hashFromBytes(context.programHash);
  const profileHash = hashFromBytes(context.profileHash);
  const ctxHash = hashFromBytes(context.ctxHash);
  const theoryConfigHash = hashFromBytes(context.theoryConfigHash);
  const witness = context.decompositionWitness;
  return {
    programHash, profileHash, ctxHash, theoryConfigHash,
    ...(witness === undefined ? {} : { decompositionWitness: hashFromBytes(witness) }),
  };
}

