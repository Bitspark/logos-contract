import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom } from "@bitspark/ontos-core";
import {
  AlwaysAdmit, CertContext, Clause, ClauseId, ClosedModelCert, ComponentIdentity,
  Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, LeafNode, LeafOutcome,
  MapProgram, NegPremise, PredicateSet, RelationTable, RuleNode, StratumPrefix,
  Symbol, Term, TheoryOutcome, WorldMemo, checkClosedModelChain, checkWithCertContext,
  checkWithWorldMemo, compoundIdentityOf, defaultLimits, newCompoundTheory, programDigest,
  programDigestOf,
} from "@bitspark/logos-contract";

const bytes = text => new TextEncoder().encode(text);
const pin = byte => new Uint8Array(32).fill(byte);
const identity = (name, version = "1", config = 1) =>
  ComponentIdentity.of(bytes(name), bytes(version), pin(config));

test("a native identity owns its construction and inspection bytes", () => {
  const id = bytes("first");
  const version = bytes("1");
  const config = pin(1);
  const reported = ComponentIdentity.of(id, version, config);
  id.fill(0); version.fill(0); config.fill(0);
  reported.id.fill(0); reported.version.fill(0); reported.configDigest.fill(0);
  assert.ok(reported.equals(identity("first")));
});

test("a compound captures each independent member's completed identity report", () => {
  const first = { id: bytes("first"), version: bytes("1"), configDigest: pin(1) };
  const firstReport = identity("first");
  // The first member implements a relation over one application-owned atom.
  const relation = {
    owns: pred => pred.equals(Symbol.of("is_allowed")),
    decide: atom => atom.args.length === 1 && atom.args[0].equals(new Atom([97]))
      ? TheoryOutcome.Holds : TheoryOutcome.Fails("not_allowed"),
    identity: () => first,
  };
  // The second independently implements a zero-argument clock declaration.
  class Ready {
    owns(pred) { return pred.equals(Symbol.of("ready")); }
    decide(atom) { return atom.args.length === 0 ? TheoryOutcome.Holds : TheoryOutcome.Fails("wrong_arity"); }
    identity() {
      first.id.set(bytes("other"));
      first.version.set(bytes("2"));
      first.configDigest.set(pin(2));
      return identity("second", "3", 3);
    }
  }
  const compound = newCompoundTheory(relation, new Ready());
  const expected = compoundIdentityOf([firstReport, identity("second", "3", 3)]);
  assert.ok(compound.identity().equals(expected), "a later report rewrote the first member's contribution");
  assert.equal(compound.decide(GroundLiteral.of("is_allowed", [new Atom([97])])).kind, "holds");
  assert.equal(compound.decide(GroundLiteral.of("is_allowed", [new Atom([98])])).kind, "fails");
  assert.equal(compound.decide(GroundLiteral.of("ready", [])).kind, "holds");
  // A new operation can legitimately observe the first member's new identity.
  assert.ok(compound.identity().equals(compoundIdentityOf([
    identity("other", "2", 2), identity("second", "3", 3),
  ])));
});

test("the explicit compound fold reads each reported field exactly once", () => {
  const reads = { id: 0, version: 0, configDigest: 0 };
  const raw = {};
  const original = identity("first");
  const later = identity("other", "2", 2);
  for (const field of Object.keys(reads)) {
    Object.defineProperty(raw, field, {
      get() { reads[field]++; return (reads[field] === 1 ? original : later)[field]; },
    });
  }
  assert.ok(compoundIdentityOf([raw]).equals(compoundIdentityOf([original])));
  assert.deepEqual(reads, { id: 1, version: 1, configDigest: 1 });
});

test("a later slot cannot rewrite earlier bytes in the explicit compound fold", () => {
  const first = { id: bytes("first"), version: bytes("1"), configDigest: pin(1) };
  const members = [first];
  Object.defineProperty(members, 1, {
    get() {
      first.id.set(bytes("other")); first.version.set(bytes("2")); first.configDigest.set(pin(2));
      return identity("second");
    },
  });
  assert.ok(compoundIdentityOf(members).equals(compoundIdentityOf([identity("first"), identity("second")])));
});

const value = new Atom([97]);
const term = Term.atom([97]);
const claim = GroundLiteral.of("derived", [value]);
const absent = GroundLiteral.of("sealed", [value]);
const clauseId = ClauseId.of("negative");
const limitsDecl = { certFacts: 8, domainValues: 8, supportEdges: 8, ruleGroundings: 20, joinSteps: 20, certBytes: 4096 };
const profile = {
  theory: newCompoundTheory(),
  leaves: {
    extensional: () => PredicateSet.from(["allowed"]),
    verify: literal => literal.pred.equals(Symbol.of("allowed")) ? LeafOutcome.Admit : LeafOutcome.Reject("not_attested"),
  },
  admit: new AlwaysAdmit(), limits: defaultLimits(),
};

function fixture(sliced = false) {
  const base = new MapProgram().with(clauseId, Clause.withNeg(
    Goal.of("derived", [term]), [], [Goal.of("sealed", [term])],
  ));
  const bound = CertContext.of(programDigestOf(base), pin(1), pin(2), pin(3));
  if (sliced) bound.decompositionWitness = pin(4);
  const sealed = CertContext.of(bound.programHash, bound.profileHash, bound.ctxHash, bound.theoryConfigHash);
  const cert = new ClosedModelCert({
    ...sealed, programHash: sliced ? programDigest([]) : sealed.programHash,
    ...(sliced ? { decompositionWitness: pin(4) } : {}),
    scope: StratumPrefix.of(0, [absent.pred]),
    domains: [FiniteDomain.of(Symbol.of("domain"), [value])],
    extensions: [RelationTable.of(absent.pred, 1, [])], supports: [], edbSnapshotHashes: [], limitsDecl,
  });
  const proof = new Derivation([new RuleNode(claim, clauseId, new Map(), [new NegPremise(absent, 0)])], 0, [cert]);
  let during = () => {};
  let enumerations = 0;
  const program = {
    clause: id => base.clause(id),
    forEachClause(f) { enumerations++; during(); base.forEachClause(f); },
  };
  return { bound, cert, proof, program, mutate: f => { during = f; }, enumerations: () => enumerations };
}
const routes = [
  ["direct", f => checkWithCertContext(f.program, claim, f.proof, undefined, profile, f.bound)],
  ["whole chain", f => checkClosedModelChain(f.program, [f.cert], undefined, profile, f.bound)],
  ["memo", f => checkWithWorldMemo(new WorldMemo(f.program, profile, undefined, f.bound), claim, f.proof)],
];
for (const [name, run] of routes) {
  for (const field of ["programHash", "profileHash", "ctxHash", "theoryConfigHash", "decompositionWitness"]) {
    test(name + " retains the original mismatching " + field + " across program enumeration", () => {
      const positive = fixture(field === "decompositionWitness");
      assert.equal(run(positive).kind, "accept");
      const f = fixture(field === "decompositionWitness");
      const original = f.bound[field].slice();
      f.bound[field].fill(99);
      assert.equal(run(f).code, "cert_context_mismatch");
      f.mutate(() => f.bound[field].set(original));
      assert.equal(run(f).code, "cert_context_mismatch");
      assert.ok(f.enumerations() > 0);
    });
    test(name + " retains the original matching " + field + " across program enumeration", () => {
      const f = fixture(field === "decompositionWitness");
      f.mutate(() => f.bound[field].fill(99));
      assert.equal(run(f).kind, "accept");
      assert.ok(f.enumerations() > 0);
    });
  }
  test(name + " captures the structural context's declared fields once", () => {
    const f = fixture(true);
    const reads = {};
    const source = f.bound;
    f.bound = {};
    for (const field of ["programHash", "profileHash", "ctxHash", "theoryConfigHash", "decompositionWitness"]) {
      reads[field] = 0;
      Object.defineProperty(f.bound, field, {
        get() { reads[field]++; return reads[field] === 1 ? source[field] : pin(99); },
      });
    }
    assert.equal(run(f).kind, "accept");
    assert.deepEqual(reads, { programHash: 1, profileHash: 1, ctxHash: 1, theoryConfigHash: 1, decompositionWitness: 1 });
  });
}

test("an all-positive direct check never reads irrelevant certificate pins", () => {
  const bound = {};
  for (const field of ["programHash", "profileHash", "ctxHash", "theoryConfigHash", "decompositionWitness"]) {
    Object.defineProperty(bound, field, { get() { assert.fail("read an unused " + field); } });
  }
  const fact = GroundLiteral.of("allowed", [value]);
  const proof = new Derivation([new LeafNode(fact, Evidence.none())], 0);
  assert.equal(checkWithCertContext(new MapProgram(), fact, proof, undefined, profile, bound).kind, "accept");
  assert.equal(checkClosedModelChain(new MapProgram(), [], undefined, profile, bound).code, "cert_out_of_range");
});

