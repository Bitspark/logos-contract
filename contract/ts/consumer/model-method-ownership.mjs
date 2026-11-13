import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom } from "@bitspark/ontos-core";
import {
  AlwaysAdmit, BodyLit, CertContext, Clause, ClauseId, ClosedModelCert,
  Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, LeafNode, LeafOutcome,
  MapProgram, NegPremise, PredicateSet, RelationTable, RuleNode, ScopeGraph, SealContext, StratumPrefix, SupportEdge,
  Symbol, Term, WorldMemo, check, checkClosedModelChain, checkWithCertContext,
  checkWithWorldMemo, defaultLimits, edbTableHash, newStandardTheory, programDigestOf,
  Subst,
  VarId,
} from "@bitspark/logos-contract";

const a = new Atom([97]);
const b = new Atom([98]);
const fact = GroundLiteral.of("allowed", [a]);
const other = GroundLiteral.of("other", [a]);
const pin = new Uint8Array(32).fill(1);
const domainTag = Symbol.of("domain");
const termA = Term.atom([97]);
const termB = Term.atom([98]);

// This implementation attests fixed bytes independently of the model equality
// method being attacked. The application continues to own its evidence.
function leavesFor(attested = fact) {
  const predicate = Buffer.from(attested.pred.bytes());
  const argument = Buffer.from(attested.args[0].bytes());
  return {
    extensional: () => PredicateSet.from([attested.pred]),
    verify(literal) {
      return Buffer.from(literal.pred.bytes()).equals(predicate) &&
        literal.args.length === 1 &&
        Buffer.from(literal.args[0].bytes()).equals(argument)
        ? LeafOutcome.Admit : LeafOutcome.Reject("not_attested");
    },
    edbSnapshot(pred) {
      return Buffer.from(pred.bytes()).equals(predicate) ? edbTableHash(pred, [attested]) : undefined;
    },
  };
}
function profileFor(leaves = leavesFor()) {
  return { theory: newStandardTheory(), leaves, admit: new AlwaysAdmit(), limits: defaultLimits() };
}

const routes = [
  ["check", (p, c, d, profile) => check(p, c, d, undefined, profile)],
  ["explicit context", (p, c, d, profile) => checkWithCertContext(p, c, d, undefined, profile, CertContext.zero())],
  ["memo", (p, c, d, profile) => checkWithWorldMemo(new WorldMemo(p, profile, undefined, CertContext.zero()), c, d)],
];

function tryEdit(target, key, replacement, inspect) {
  const original = Object.getOwnPropertyDescriptor(target, key);
  const changed = Reflect.defineProperty(target, key, {
    value: replacement, configurable: true, writable: true,
  });
  try {
    inspect();
  } finally {
    if (changed) {
      if (original === undefined) Reflect.deleteProperty(target, key);
      else Reflect.defineProperty(target, key, original);
    }
  }
}

function refusalSurvives(run, code, target, key, replacement) {
  const expected = run();
  assert.equal(expected.verdict.kind, "reject");
  assert.equal(expected.verdict.code, code);
  tryEdit(target, key, replacement, () => assert.deepEqual(run().verdict, expected.verdict));
}

for (const [name, run] of routes) {
  test(name + " retains root equality after another importer edits the literal prototype", () => {
    const program = new MapProgram();
    const profile = profileFor();
    const proof = new Derivation([new LeafNode(fact, Evidence.none())], 0);
    assert.equal(run(program, fact, proof, profile).verdict.kind, "accept");
    refusalSurvives(() => run(program, other, proof, profile), "root_conclusion_mismatch",
      GroundLiteral.prototype, "equals", () => true);
    assert.equal(run(program, fact, proof, profile).verdict.kind, "accept");
  });

  for (const [label, target, method, replacement] of [
    ["goal substitution", Goal.prototype, "substitute", () => Goal.of("derived", [termB])],
    ["goal grounding", Goal.prototype, "asGround", () => GroundLiteral.of("derived", [b])],
    ["term substitution", Term, "substitute", () => termB],
    ["term grounding", Term, "eraseGround", () => b],
  ]) {
    test(name + " retains native " + label + " for the selected program", () => {
      const id = ClauseId.of("fixed");
      const program = new MapProgram().with(id, Clause.fact(Goal.of("derived", [termA])));
      const profile = profileFor();
      const valid = GroundLiteral.of("derived", [a]);
      const invalid = GroundLiteral.of("derived", [b]);
      const proof = value => new Derivation([new RuleNode(value, id, new Subst(), [])], 0);
      assert.equal(run(program, valid, proof(valid), profile).verdict.kind, "accept");
      refusalSurvives(() => run(program, invalid, proof(invalid), profile), "instantiation_mismatch",
        target, method, replacement);
    });
  }

  test(name + " cannot disable the depth cap by replacing the term operations", () => {
    const id = ClauseId.of("fixed");
    const program = new MapProgram().with(id, Clause.fact(Goal.of("derived", [termA])));
    const profile = profileFor();
    profile.limits.maxTermDepth = 1;
    const claim = GroundLiteral.of("derived", [a]);
    const proof = new Derivation([
      new RuleNode(claim, id, new Subst([[VarId.of("unused"), Term.tuple([termA])]]), []),
    ], 0);
    refusalSurvives(() => run(program, claim, proof, profile), "term_too_deep",
      Term, "depthLe", () => true);
  });

  test(name + " cannot reinterpret a negative obligation as a positive premise", () => {
    const id = ClauseId.of("negative");
    const goal = Goal.of("derived", [termA]);
    const program = new MapProgram().with(id,
      Clause.withNeg(goal, [], [Goal.of("allowed", [termA])]));
    const claim = goal.asGround();
    const profile = profileFor();
    const proof = new Derivation([
      new LeafNode(fact), new RuleNode(claim, id, new Subst(), [0]),
    ], 1);
    refusalSurvives(() => run(program, claim, proof, profile), "instantiation_mismatch",
      BodyLit.prototype, "isNeg", () => false);
  });

  test(name + " retains the verifier's extensional predicate partition", () => {
    const id = ClauseId.of("collision");
    const program = new MapProgram().with(id, Clause.fact(Goal.of("allowed", [termA])));
    const proof = new Derivation([new RuleNode(fact, id, new Subst(), [])], 0);
    const profile = profileFor();
    refusalSurvives(() => run(program, fact, proof, profile), "sealed_violation",
      PredicateSet.prototype, "contains", () => false);
  });
}

const limitsDecl = {
  certFacts: 4, domainValues: 4, supportEdges: 4,
  ruleGroundings: 20, joinSteps: 20, certBytes: 8192,
};
function boundTo(program) {
  return CertContext.of(programDigestOf(program), pin, pin, pin);
}
function certificate(bound, params = {}) {
  return new ClosedModelCert({
    ...bound, scope: StratumPrefix.of(0, []), domains: [],
    extensions: [], supports: [], edbSnapshotHashes: [], limitsDecl, ...params,
  });
}

test("a shared finite-domain method cannot authorize duplicate domain values", () => {
  const program = new MapProgram();
  const bound = boundTo(program);
  const profile = profileFor();
  const run = domain => checkClosedModelChain(program,
    [certificate(bound, { domains: [domain] })], undefined, profile, bound);
  assert.equal(run(FiniteDomain.of(domainTag, [a])).verdict.kind, "accept");
  const duplicate = new FiniteDomain(domainTag, [a, a]);
  refusalSurvives(() => run(duplicate), "cert_out_of_domain",
    FiniteDomain.prototype, "isCanonical", () => true);
});

test("a shared scope method cannot authorize duplicate sealed predicates", () => {
  const program = new MapProgram();
  const bound = boundTo(program);
  const profile = profileFor();
  const run = scope => checkClosedModelChain(program, [certificate(bound, {
    scope, domains: [FiniteDomain.of(domainTag, [a])],
    extensions: [RelationTable.of(fact.pred, 1, [fact])],
    edbSnapshotHashes: [edbTableHash(fact.pred, [fact])],
  })], undefined, profile, bound);
  assert.equal(run(StratumPrefix.of(0, [fact.pred])).verdict.kind, "accept");
  refusalSurvives(() => run(new StratumPrefix(0, [fact.pred, fact.pred])), "cert_scope_incomplete",
    StratumPrefix.prototype, "isCanonical", () => true);
});

test("a shared relation method cannot authorize duplicate sealed rows", () => {
  const program = new MapProgram();
  const bound = boundTo(program);
  const profile = profileFor();
  const run = table => checkClosedModelChain(program, [certificate(bound, {
    scope: StratumPrefix.of(0, [fact.pred]), domains: [FiniteDomain.of(domainTag, [a])],
    extensions: [table], edbSnapshotHashes: [edbTableHash(fact.pred, [fact])],
  })], undefined, profile, bound);
  assert.equal(run(RelationTable.of(fact.pred, 1, [fact])).verdict.kind, "accept");
  refusalSurvives(() => run(new RelationTable(fact.pred, 1, [fact, fact])), "cert_unsupported",
    RelationTable.prototype, "isCanonical", () => true);
});

for (const [label, target, method, replacement] of [
  ["domain membership", FiniteDomain.prototype, "contains", () => true],
  ["certificate domain lookup", ClosedModelCert.prototype, "domainContaining", () => FiniteDomain.of(domainTag, [b])],
]) {
  test("a shared " + label + " cannot hide an out-of-domain attested fact", () => {
    const row = GroundLiteral.of("allowed", [b]);
    const program = new MapProgram();
    const bound = boundTo(program);
    const profile = profileFor(leavesFor(row));
    const run = domain => checkClosedModelChain(program, [certificate(bound, {
      scope: StratumPrefix.of(0, [row.pred]), domains: [domain],
      extensions: [RelationTable.of(row.pred, 1, [row])],
      edbSnapshotHashes: [edbTableHash(row.pred, [row])],
    })], undefined, profile, bound);
    assert.equal(run(FiniteDomain.of(domainTag, [b])).verdict.kind, "accept");
    refusalSurvives(() => run(FiniteDomain.of(domainTag, [a])), "cert_out_of_domain",
      target, method, replacement);
  });
}

test("a shared table membership method cannot hide a missing derived fact", () => {
  const id = ClauseId.of("derived-fact");
  const claim = GroundLiteral.of("derived", [a]);
  const program = new MapProgram().with(id, Clause.fact(Goal.of("derived", [termA])));
  const bound = boundTo(program);
  const profile = profileFor();
  const run = complete => checkClosedModelChain(program, [certificate(bound, {
    scope: StratumPrefix.of(0, [claim.pred]), domains: [FiniteDomain.of(domainTag, [a])],
    extensions: [RelationTable.of(claim.pred, 1, complete ? [claim] : [])],
    supports: complete ? [new SupportEdge(claim, id, new Subst(), [], 0)] : [],
  })], undefined, profile, bound);
  assert.equal(run(true).verdict.kind, "accept");
  const expected = run(false);
  assert.equal(expected.verdict.kind, "reject");
  tryEdit(RelationTable.prototype, "contains", () => true,
    () => assert.deepEqual(run(false).verdict, expected.verdict));
});

test("an importer cannot supply an implicit certificate context through the default factory", () => {
  const id = ClauseId.of("negative");
  const absent = GroundLiteral.of("sealed", [a]);
  const claim = GroundLiteral.of("derived", [a]);
  const program = new MapProgram().with(id, Clause.withNeg(
    Goal.of("derived", [termA]), [], [Goal.of("sealed", [termA])],
  ));
  const profile = profileFor();
  const bound = boundTo(program);
  const seal = certificate(bound, {
    scope: StratumPrefix.of(0, [absent.pred]), domains: [FiniteDomain.of(domainTag, [a])],
    extensions: [RelationTable.of(absent.pred, 1, [])],
  });
  const proof = new Derivation([
    new RuleNode(claim, id, new Subst(), [new NegPremise(absent, 0)]),
  ], 0, [seal]);
  assert.equal(checkWithCertContext(program, claim, proof, undefined, profile, bound).verdict.kind, "accept");
  refusalSurvives(() => check(program, claim, proof, undefined, profile), "cert_context_unbound",
    CertContext, "zero", () => bound);
});

// A second independent LeafVerifier interprets a receipt under an application
// context instead of declaring a fixed fact. The checker knows neither policy.
test("independent receipt verification keeps its evidence and claim authority", () => {
  const receiptVerifier = {
    extensional: () => PredicateSet.from(["allowed"]),
    verify(literal, evidence, ctx) {
      const receipt = evidence.value();
      const token = receipt instanceof Atom ? receipt.bytes()[0] : undefined;
      const predicate = Buffer.from(literal.pred.bytes()).toString("utf8");
      return token !== undefined && ctx.receipts.get(token) === predicate &&
        literal.args.length === 1 && Buffer.from(literal.args[0].bytes()).equals(Buffer.from([97]))
        ? LeafOutcome.Admit : LeafOutcome.Reject("receipt_not_authorized");
    },
  };
  const context = { receipts: new Map([[7, "allowed"]]) };
  const profile = profileFor(receiptVerifier);
  const program = new MapProgram();
  const proof = token => new Derivation([new LeafNode(fact, Evidence.of(new Atom([token])))], 0);
  assert.equal(check(program, fact, proof(7), context, profile).verdict.kind, "accept");
  assert.equal(check(program, fact, proof(8), context, profile).verdict.code, "leaf_rejected");
  refusalSurvives(() => check(program, other, proof(7), context, profile), "root_conclusion_mismatch",
    GroundLiteral.prototype, "equals", () => true);
});


for (const [label, target, method, replacement] of [
  ["construction", ScopeGraph, "constructs", () => false],
  ["cycle reachability", ScopeGraph.prototype, "cycleThrough", () => undefined],
]) {
  test("a shared graph operation cannot change sealed " + label, () => {
    const x = Term.var("X");
    const q = Symbol.of("q");
    const r = Symbol.of("r");
    const run = constructing => {
      const qHead = Goal.of(q, [constructing ? Term.tuple([Term.atom([102]), x]) : x]);
      const program = new MapProgram()
        .with("q", new Clause(qHead, [Goal.of(r, [x])]))
        .with("r", new Clause(Goal.of(r, [x]), [Goal.of(q, [x])]));
      const bound = boundTo(program);
      const seal = certificate(bound, {
        scope: StratumPrefix.of(0, [q, r]),
        extensions: [RelationTable.of(q, 1, []), RelationTable.of(r, 1, [])],
      });
      return checkClosedModelChain(program, [seal], undefined, profileFor(), bound);
    };
    assert.equal(run(false).verdict.kind, "accept");
    const expected = run(true);
    assert.equal(expected.verdict.kind, "reject");
    tryEdit(target, method, replacement, () => assert.deepEqual(run(true).verdict, expected.verdict));
  });
}

test("a shared seal context cannot authorize an unresolved relation", () => {
  const x = Term.var("X");
  const q = Symbol.of("q");
  const r = Symbol.of("r");
  const program = new MapProgram().with("q", new Clause(Goal.of(q, [x]), [Goal.of(r, [x])]));
  const bound = boundTo(program);
  const run = complete => {
    const predicates = complete ? [q, r] : [q];
    const seal = certificate(bound, {
      scope: StratumPrefix.of(0, predicates),
      extensions: predicates.map(pred => RelationTable.of(pred, 1, [])),
    });
    return checkClosedModelChain(program, [seal], undefined, profileFor(), bound);
  };
  assert.equal(run(true).verdict.kind, "accept");
  const expected = run(false);
  assert.equal(expected.verdict.kind, "reject");
  tryEdit(SealContext.prototype, "seals", () => true, () => assert.deepEqual(run(false).verdict, expected.verdict));
});

test("checking a sealed relation selects its snapshot implementation once", () => {
  const program = new MapProgram();
  const bound = boundTo(program);
  const cert = certificate(bound, {
    scope: StratumPrefix.of(0, [fact.pred]), domains: [FiniteDomain.of(domainTag, [a])],
    extensions: [RelationTable.of(fact.pred, 1, [fact])],
    edbSnapshotHashes: [edbTableHash(fact.pred, [fact])],
  });
  const leaves = leavesFor();
  const attest = leaves.edbSnapshot;
  let selections = 0;
  let calls = 0;
  Object.defineProperty(leaves, "edbSnapshot", { get() {
    selections++;
    return function (pred, ctx) {
      assert.equal(this, leaves);
      calls++;
      return attest.call(this, pred, ctx);
    };
  } });
  const result = checkClosedModelChain(program, [cert], undefined, profileFor(leaves), bound);
  assert.equal(result.verdict.kind, "accept");
  assert.equal(selections, 1);
  assert.equal(calls, 1);
});
