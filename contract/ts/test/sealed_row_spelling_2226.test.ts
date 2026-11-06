/*
 * #2226 step 0 (seat:caa, issuecomment-5812490508): can a certificate SEAL a table row spelled
 * list(a) while the leaves admit .(a,[])? If so, the now-EXACT negation lookup (#2227) finds the
 * body literal absent and certifies a false negation under the default reading. The same
 * witnesses are pinned in contract/rs and contract/go; see the rs file for the two routes.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import {
  AlwaysAdmit,
  CertContext,
  checkWithCertContext,
  Clause,
  ClauseId,
  ClosedModelCert,
  CompoundTheory,
  Derivation,
  edbTableHash,
  Evidence,
  FiniteDomain,
  Goal,
  GroundLiteral,
  type Hash,
  LeafOutcome,
  type LeafVerifier,
  MapProgram,
  NegPremise,
  NodeMeta,
  type Outcome,
  PredicateSet,
  programDigestOf,
  RelationTable,
  RuleNode,
  StratumPrefix,
  SupportEdge,
  SupportRef,
  Symbol,
  Term,
  type CheckProfile,
  defaultLimits,
} from "../src/index.js";

function av(s: string): Value {
  return valueAtom(new TextEncoder().encode(s));
}
const consA = valueTuple([av("."), av("a"), av("[]")]);
const listA = valueTuple([av("list"), av("a")]);

// test-double: consumer(a fixed EDB: admits exactly its rows and attests them)
class Leaves implements LeafVerifier<void> {
  readonly #extensional: PredicateSet;
  readonly #edb: readonly GroundLiteral[];
  constructor(extensional: string[], edb: readonly GroundLiteral[]) {
    this.#extensional = PredicateSet.from(extensional);
    this.#edb = edb;
  }
  extensional(): PredicateSet {
    return this.#extensional;
  }
  verify(atom: GroundLiteral, _evidence: Evidence, _ctx: void): LeafOutcome {
    return this.#edb.some((row) => row.equals(atom)) ? LeafOutcome.Admit : LeafOutcome.Reject("not_admitted");
  }
  edbSnapshot(pred: Symbol, _ctx: void): Hash | undefined {
    if (!this.#extensional.contains(pred)) return undefined;
    return edbTableHash(
      pred,
      this.#edb.filter((row) => row.pred.equals(pred)),
    );
  }
}

function verdict(o: Outcome): string {
  return o.kind === "accept" ? "ACCEPT" : o.code;
}

/** `r :- \+ seen(.(a,[]))` (plus `extra`) with a Neg premise seen(.(a,[])), EXACTLY the body literal. */
function negation(
  extra: [string, Clause][],
  extensional: string[],
  edb: GroundLiteral[],
  level: number,
  tables: RelationTable[],
  edbHashes: Hash[],
  edges: SupportEdge[],
): Outcome {
  let program = new MapProgram().with(
    "r_rule",
    Clause.withNeg(Goal.of("r", []), [], [Goal.of("seen", [Term.fromValue(consA)])]),
  );
  for (const [id, clause] of extra) program = program.with(id, clause);
  const pin: Hash = new Uint8Array(32).fill(1);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(
      level,
      tables.map((t) => t.pred),
    ),
    programHash: programDigestOf(program),
    profileHash: pin,
    ctxHash: pin,
    theoryConfigHash: pin,
    edbSnapshotHashes: edbHashes,
    domains: [FiniteDomain.of(Symbol.of("v"), [consA, listA])],
    extensions: tables,
    supports: edges,
    limitsDecl: {
      certFacts: tables.reduce((n, t) => n + t.rows.length, 0),
      domainValues: 2,
      supportEdges: edges.length,
      ruleGroundings: 1_000,
      joinSteps: 10_000,
      certBytes: 4_096,
    },
  });
  const claim = GroundLiteral.of("r", []);
  const deriv = new Derivation(
    [new RuleNode(claim, ClauseId.of("r_rule"), new Map(), [new NegPremise(GroundLiteral.of("seen", [consA]), 0)], NodeMeta.none())],
    0,
    [cert],
  );
  const profile: CheckProfile<void> = {
    theory: new CompoundTheory([]),
    leaves: new Leaves(extensional, edb),
    admit: new AlwaysAdmit<void>(),
    limits: defaultLimits(),
  };
  return checkWithCertContext(program, claim, deriv, undefined, profile, CertContext.of(programDigestOf(program), pin, pin, pin));
}

function routeE(sealed: Value): Outcome {
  const row = GroundLiteral.of("seen", [sealed]);
  const seen = Symbol.of("seen");
  return negation([], ["seen"], [GroundLiteral.of("seen", [consA])], 0, [RelationTable.of(seen, 1, [row])], [edbTableHash(seen, [row])], []);
}

test("#2226 step 0: an extensional row cannot be sealed in another spelling", () => {
  assert.equal(verdict(routeE(consA)), "neg_atom_present", "control");
  assert.equal(verdict(routeE(listA)), "cert_edb_mismatch", "E1 (extensional row respelled)");
});

function routeI(row: Value, supportX: Value): Outcome {
  const x = Term.var("X");
  const seenClause = new Clause(Goal.of("seen", [x]), [Goal.of("src", [x])]);
  const srcRow = GroundLiteral.of("src", [consA]);
  const src = Symbol.of("src");
  const seen = Symbol.of("seen");
  const edge = new SupportEdge(
    GroundLiteral.of("seen", [row]),
    ClauseId.of("seen_rule"),
    new Map([["X", Term.fromValue(supportX)]]),
    [SupportRef.lowerStratum(0, GroundLiteral.of("src", [supportX]))],
    1,
  );
  return negation(
    [["seen_rule", seenClause]],
    ["src"],
    [srcRow],
    1,
    [RelationTable.of(src, 1, [srcRow]), RelationTable.of(seen, 1, [GroundLiteral.of("seen", [row])])],
    [edbTableHash(src, [srcRow])],
    [edge],
  );
}

test("#2226 step 0: an intensional row cannot be sealed in another spelling", () => {
  assert.equal(verdict(routeI(consA, consA)), "neg_atom_present", "control");
  assert.equal(verdict(routeI(listA, listA)), "cert_unsupported", "I1 (support X = list(a))");
  assert.equal(verdict(routeI(listA, consA)), "cert_unsupported", "I2 (support X = .(a,[]))");
});
