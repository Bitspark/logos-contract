import { ClosedModelCert, SupportEdge, copyCertificateTables, hashFromBytes, type SupportRef } from "./cert.js";
import { BuiltinNode, CountPremise, Derivation, LeafNode, NegPremise, RuleNode, type Node, type Premise } from "./derivation.js";
import { copyArray, nativeClauseId, nativeLiteral, nativePredicateRef, nativeSubst, nativeValue } from "./native_copy.js";

/** Detach the mutable containers of an in-process proof. Clause handles, opaque
 * verifier evidence and node order retain their original meanings. */
export function cloneDerivation(proof: Derivation): Derivation {
  const nodes = proof.nodes;
  return copyDerivation(nodes, nodes.length, proof.root, proof.closedWorld, Infinity);
}

export function copyDerivation(nodes: readonly Node[], count: number, root: number, world: readonly ClosedModelCert[], max: number): Derivation {
  return new Derivation(copyArray(nodes, node => copyNode(node, max), count), root, copyClosedWorld(world, max));
}

export function copyClosedWorld(world: readonly ClosedModelCert[], max: number): ClosedModelCert[] {
  return copyArray(world, cert => copyWorld(cert, max));
}

function unknownRecord(_record: never, kind: string): never {
  throw new TypeError(`unexpected ${kind}`);
}

function copyNode(node: Node, max: number): Node {
  switch (node.kind) {
    case "rule":
      return new RuleNode(nativeLiteral(node.conclusion, max), nativeClauseId(node.clause), nativeSubst(node.subst),
        copyArray(node.premises, premise => copyPremise(premise, max)), node.meta);
    case "builtin":
      return new BuiltinNode(nativeLiteral(node.conclusion, max));
    case "leaf":
      return new LeafNode(nativeLiteral(node.conclusion, max), node.evidence);
    default: return unknownRecord(node, "proof node");
  }
}

function copyPremise(premise: Premise, max: number): Premise {
  if (typeof premise === "number") return premise;
  switch (premise.kind) {
    case "neg": return new NegPremise(nativeLiteral(premise.atom, max), premise.cert, premise.nonmember);
    case "count":
      return new CountPremise(nativePredicateRef(premise.pred),
        copyArray(premise.filter, entry => ({ pos: entry.pos, value: nativeValue(entry.value, max) })),
        { ...premise.project }, nativeValue(premise.k, max), premise.cert);
    default: return unknownRecord(premise, "proof premise");
  }
}

function copyWorld(world: ClosedModelCert, max: number): ClosedModelCert {
  const witness = world.decompositionWitness;
  return new ClosedModelCert({
    ...copyCertificateTables(world, max),
    programHash: hashFromBytes(world.programHash), profileHash: hashFromBytes(world.profileHash),
    ctxHash: hashFromBytes(world.ctxHash), theoryConfigHash: hashFromBytes(world.theoryConfigHash),
    edbSnapshotHashes: copyArray(world.edbSnapshotHashes, hashFromBytes),
    supports: copyArray(world.supports, edge => new SupportEdge(nativeLiteral(edge.fact, max), nativeClauseId(edge.clause), nativeSubst(edge.subst),
      copyArray(edge.bodyRefs, ref => copySupportRef(ref, max)), edge.rank)),
    limitsDecl: { ...world.limitsDecl },
    decompositionWitness: witness === undefined ? undefined : hashFromBytes(witness),
  });
}

function copySupportRef(ref: SupportRef, max: number): SupportRef {
  switch (ref.kind) {
    case "same_stratum": return { kind: ref.kind, fact: nativeLiteral(ref.fact, max), rank: ref.rank };
    case "lower_stratum": return { kind: ref.kind, atom: nativeLiteral(ref.atom, max), cert: ref.cert };
    case "builtin": return { kind: ref.kind, atom: nativeLiteral(ref.atom, max) };
    case "neg_lower": return { kind: ref.kind, atom: nativeLiteral(ref.atom, max), cert: ref.cert };
    case "count_lower": return { kind: ref.kind, cert: ref.cert };
    default: return unknownRecord(ref, "support reference");
  }
}
