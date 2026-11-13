import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom } from "@bitspark/ontos-core";
import {
  ClauseId, ClosedModelCert, CountPremise, Derivation, GroundLiteral, PredicateRef,
  ProjectSpec, RuleNode, StratumPrefix, SupportEdge, SupportRef, Symbol, TermAtom,
  cloneDerivation,
  Subst,
  VarId,
} from "@bitspark/logos-contract";

test("a native proof copy retains opaque handles and detaches mutable proof and world data", () => {
  const bytes = Uint8Array.of(97);
  const term = new TermAtom(bytes);
  const pred = new Symbol(bytes);
  const fact = GroundLiteral.of(pred, [new Atom(bytes)]);
  const id = ClauseId.of(String.fromCharCode(0xd800));
  const answer = new Subst([[VarId.of("X"), term]]);
  const ref = SupportRef.sameStratum(fact, 0);
  const edge = new SupportEdge(fact, id, answer, [ref], 1);
  const hash = Buffer.alloc(32);
  const limits = { certFacts: 1, domainValues: 1, supportEdges: 1, ruleGroundings: 1, joinSteps: 1, certBytes: 1 };
  const world = new ClosedModelCert({
    scope: StratumPrefix.of(0, [pred]), programHash: hash, profileHash: hash, ctxHash: hash,
    theoryConfigHash: hash, edbSnapshotHashes: [hash], domains: [], extensions: [], supports: [edge],
    limitsDecl: limits, decompositionWitness: hash,
  });
  const filter = { pos: 0, value: new Atom(bytes) };
  const premise = new CountPremise(new PredicateRef(pred, 1), [filter], ProjectSpec.distinct(0), new Atom(bytes), 0);
  const copy = cloneDerivation(new Derivation([new RuleNode(fact, id, answer, [premise])], 0, [world]));

  bytes.fill(0);
  term.bytes().fill(0);
  pred.bytes().fill(0);
  answer.clear();
  hash.fill(1);
  filter.pos = 1;
  Object.assign(ref, { rank: 9 });
  limits.certFacts = 2;

  const node = copy.nodes[0];
  assert.ok(node?.kind === "rule");
  assert.equal(node.clause.asStr(), id.asStr());
  assert.deepEqual(node.conclusion.pred.bytes(), Uint8Array.of(97));
  const copiedTerm = node.subst.get(VarId.of("X"));
  assert.ok(copiedTerm?.kind === "atom");
  assert.deepEqual(copiedTerm.bytes(), Uint8Array.of(97));
  const counted = node.premises[0];
  assert.ok(counted instanceof CountPremise);
  assert.equal(counted.filter[0]?.pos, 0);
  const retained = copy.closedWorld[0]!;
  assert.equal(retained.programHash[0], 0);
  assert.equal(retained.decompositionWitness?.[0], 0);
  assert.equal(retained.limitsDecl.certFacts, 1);
  const support = retained.supports[0]!;
  assert.equal(support.clause.asStr(), id.asStr());
  assert.equal(support.subst.size, 1);
  const retainedRef = support.bodyRefs[0];
  assert.ok(retainedRef?.kind === "same_stratum" && retainedRef.rank === 0);
});
