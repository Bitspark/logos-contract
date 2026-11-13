import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom } from "@bitspark/ontos-core";
import {
  AlwaysAdmit, CertContext, Clause, ClauseId, ClauseIdEncodingError, ClosedModelCert,
  Derivation, FiniteDomain, Goal, GroundLiteral, MapProgram, PredicateSet, RelationTable,
  RuleNode, StratumPrefix, SupportEdge, Symbol, Term, WorldMemo, certEncodedBytes, check,
  checkClosedModelChain, checkWithWorldMemo, closedModelCertAsValue, decodeDerivationWireV1,
  defaultLimits, derivationAsValue, derivationWirePayloadV1ToValue, derivationWireV1ToValue,
  encodeDerivationWireV1, newStandardTheory, programDigestOf,
  Subst,
} from "@bitspark/logos-contract";

const a = new Atom([97]);
const claim = GroundLiteral.of("proved", [a]);
const clause = Clause.fact(Goal.of("proved", [Term.fromValue(a)]));
const profile = {
  theory: newStandardTheory(),
  leaves: { extensional: () => PredicateSet.from([]), verify: () => assert.fail("unexpected leaf") },
  admit: new AlwaysAdmit(), limits: defaultLimits(),
};
const pin = new Uint8Array(32).fill(1);
const portable = ClauseId.of("second-witness");

function evidence(handle) {
  const id = ClauseId.of(handle);
  const program = new MapProgram().with(id, clause).with(portable, clause);
  const context = CertContext.of(programDigestOf(program), pin, pin, pin);
  const declaration = new ClosedModelCert({
    ...context, scope: StratumPrefix.of(0, [claim.pred]),
    domains: [FiniteDomain.of(Symbol.of("domain"), [a])],
    extensions: [RelationTable.of(claim.pred, 1, [claim])],
    supports: [new SupportEdge(claim, id, new Subst(), [], 0)], edbSnapshotHashes: [],
    limitsDecl: { certFacts: 4, domainValues: 4, supportEdges: 4, ruleGroundings: 20, joinSteps: 20, certBytes: 8192 },
  });
  const cert = new ClosedModelCert({
    ...declaration, limitsDecl: { ...declaration.limitsDecl, certBytes: certEncodedBytes(declaration) },
  });
  const proof = (id, world) => new Derivation([new RuleNode(claim, id, new Subst(), [])], 0, world);
  return { program, context, cert, rule: proof(id, []), support: proof(portable, [cert]) };
}

test("portable rule and support handles round-trip as exact Unicode text", () => {
  for (const handle of ["", "A\ufffd", "A\u{1f600}B", "\ufeffid"]) {
    const { rule, support } = evidence(handle);
    for (const [proof, readId] of [
      [rule, d => d.nodes[0].clause.asStr()],
      [support, d => d.closedWorld[0].supports[0].clause.asStr()],
    ]) {
      const wire = encodeDerivationWireV1(proof);
      const decoded = decodeDerivationWireV1(wire);
      assert.equal(readId(decoded), handle);
      assert.deepEqual(encodeDerivationWireV1(decoded), wire);
    }
  }
});

test("native rule and support checking retain a nonportable handle", () => {
  for (const handle of ["A\ud800", "A\udc00"]) {
    const { program, context, rule, support, cert } = evidence(handle);
    assert.equal(check(program, claim, rule, undefined, profile).verdict.kind, "accept");
    assert.equal(checkClosedModelChain(program, [cert], undefined, profile, context).verdict.kind, "accept");
    const under = new ClosedModelCert({ ...cert, limitsDecl: { ...cert.limitsDecl, certBytes: cert.limitsDecl.certBytes - 1 } });
    assert.equal(checkClosedModelChain(program, [under], undefined, profile, context).verdict.code, "cert_decl_mismatch");
    const memo = new WorldMemo(program, profile, undefined, context);
    assert.equal(checkWithWorldMemo(memo, claim, support).verdict.kind, "accept");
    assert.equal(checkWithWorldMemo(memo, claim, support).verdict.kind, "accept");
    assert.equal(memo.certificatesVerified, 1);
    assert.ok(certEncodedBytes(cert) > 0);

    const refusal = error => error instanceof ClauseIdEncodingError && error.clauseId === handle;
    assert.throws(() => closedModelCertAsValue(cert), refusal);
    for (const proof of [rule, support]) {
      for (const write of [derivationAsValue, derivationWirePayloadV1ToValue, derivationWireV1ToValue, encodeDerivationWireV1]) {
        assert.throws(() => write(proof), refusal);
      }
    }
  }
});
