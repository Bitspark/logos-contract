import assert from "node:assert/strict";
import { test } from "node:test";
import { Atom } from "@bitspark/ontos-core";
import {
  AlwaysAdmit, CertContext, Clause, ClauseId, ClosedModelCert, Derivation, FiniteDomain,
  Goal, LeafOutcome, PredicateSet, RelationTable, RuleNode, StratumPrefix, Symbol, Term,
  asCompleteProgram, check, checkClosedModelChain, defaultLimits, newCompoundTheory, programDigest, programDigestOf,
  Subst,
} from "@bitspark/logos-contract";

class Inventory {
  #entries;
  constructor(entries) { this.#entries = entries; }
  clause(id) { return this.#entries.find(([key]) => key.asStr() === id.asStr())?.[1]; }
  forEachClause(visit) { for (const [id, clause] of this.#entries) visit(id, clause); }
}

const pin = b => new Uint8Array(32).fill(b);
const profile = {
  theory: newCompoundTheory(), admit: new AlwaysAdmit(), limits: defaultLimits(),
  leaves: { extensional: () => PredicateSet.from([]), verify: () => LeafOutcome.Reject("no_evidence") },
};

test("a lookup-only program checks a cited positive clause", () => {
  const id = ClauseId.of("published");
  const goal = Goal.of("published", []);
  const inventory = new Inventory([[id, Clause.fact(goal)]]);
  const lookup = { clause: key => inventory.clause(key) };
  const claim = goal.asGround();
  const proof = new Derivation([new RuleNode(claim, id, new Subst(), [])], 0);
  assert.equal(check(lookup, claim, proof, undefined, profile).verdict.kind, "accept");
  assert.equal(asCompleteProgram(lookup), undefined);
  assert.throws(() => programDigestOf(lookup), TypeError);
});

test("selecting a complete view retains the store's operations and receiver", () => {
  const id = ClauseId.of("original");
  const clause = Clause.fact(Goal.of("published", []));
  const store = new Inventory([[id, clause]]);
  const selected = asCompleteProgram(store);
  store.clause = () => undefined;
  store.forEachClause = () => {};
  assert.equal(selected.clause(id), clause);
  assert.deepEqual(programDigestOf(selected), programDigest([clause]));
  assert.deepEqual(programDigestOf(asCompleteProgram(store)), programDigest([]));
});

function emptyCertificate(hash) {
  const pred = Symbol.of("sealed");
  const bound = CertContext.of(hash, pin(1), pin(2), pin(3));
  const cert = new ClosedModelCert({
    ...bound, scope: StratumPrefix.of(0, [pred]),
    domains: [FiniteDomain.of(Symbol.of("domain"), [new Atom([97])])],
    extensions: [RelationTable.of(pred, 1, [])], supports: [], edbSnapshotHashes: [],
    limitsDecl: { certFacts: 8, domainValues: 8, supportEdges: 8, ruleGroundings: 20, joinSteps: 20, certBytes: 4096 },
  });
  return { bound, cert };
}

test("closure distinguishes unavailable, complete empty and an uncited defining clause", () => {
  const empty = new Inventory([]);
  const withFact = new Inventory([[ClauseId.of("independent-definition"), Clause.fact(Goal.of("sealed", [Term.atom([97])]))]]);
  const outside = new Inventory([[ClauseId.of("outside-scope"),
    new Clause(Goal.of("sealed", [Term.atom([97])]), [Goal.of("outside", [])])]]);
  const emptyHash = programDigestOf(empty);
  assert.deepEqual(emptyHash, programDigest([]));
  for (const [program, hash, expected] of [
    [{ clause: key => empty.clause(key) }, emptyHash, "cert_scope_incomplete"],
    [empty, emptyHash, "accept"],
    [outside, programDigestOf(outside), "cert_scope_incomplete"],
    [withFact, emptyHash, "cert_context_mismatch"],
    [withFact, programDigestOf(withFact), "cert_not_closed"],
  ]) {
    const { bound, cert } = emptyCertificate(hash);
    const result = checkClosedModelChain(program, [cert], undefined, profile, bound).verdict;
    assert.equal(result.kind === "accept" ? result.kind : result.code, expected, result.detail);
  }
});

test("a complete program supplies one inventory to a certificate chain and a fresh one on the next call", () => {
  const inventory = new Inventory([]);
  let selections = 0;
  let visits = 0;
  Object.defineProperty(inventory, "forEachClause", {
    get() {
      selections++;
      return function (visit) {
        assert.equal(this, inventory);
        visits++;
        Inventory.prototype.forEachClause.call(this, visit);
      };
    },
  });
  const { cert, bound } = emptyCertificate(programDigest([]));
  for (let call = 1; call <= 2; call++) {
    const result = checkClosedModelChain(inventory, [cert, cert], undefined, profile, bound).verdict;
    assert.equal(result.kind, "accept", result.detail);
    assert.equal(selections, call);
    assert.equal(visits, call);
  }
});
