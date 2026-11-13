// ADR 0029 D10 — the SLICE SEAL, ts arm.
//
// These are the ts twins of the six `d10_g5_*` tests in contract/rs/tests/negation.rs and the
// seven in contract/go/d10_slice_seal_test.go. They exist because of a hazard this language
// shares with Go and NOT with Rust: adding an OPTIONAL `decompositionWitness` to
// ClosedModelCert broke NOTHING — every existing construction site kept compiling and silently
// received `undefined`, where the identical change in rs surfaced 29 sites loudly. `tsc` and
// `npm test` passing therefore proved only that nothing REGRESSED; without this file the D10
// branch would ship unexercised. Silence is the alarm, not the all-clear.
//
// The public whole-chain check evaluates the slice context before its later obligations.
// These fixtures isolate that stage by inspecting the specific context-mismatch code.

import test from "node:test";
import assert from "node:assert/strict";

import { atom as valueAtom } from "@bitspark/ontos-core";

import {
  AlwaysAdmit,
  type CertContext as CertContextT,
  type CheckProfile,
  Clause,
  ClosedModelCert,
  CertContext,
  Derivation,
  Evidence,
  Goal,
  GroundLiteral,
  LeafNode,
  type Hash,
  type LeafOutcome,
  type LeafVerifier,
  MapProgram,
  PredicateSet,
  type CompleteProgram,
  StratumPrefix,
  Symbol as LogosSymbol,
  Term,
  TermTheory,
  defaultLimits,
  derivationAsValue,
  derivationFromValue,
  programDigestOf,
  checkClosedModelChain,
} from "../src/index.js";
import { programDigestOverScope } from "../src/cert_check.js";

// The two-clause program the rs and go twins use: `denied` is the sealed component, `permit` is
// the upper stratum and outside it. `revoked` is a pure EDB leaf and contributes no clause, so
// the SLICE of the ideal {denied, revoked} is exactly {denied_rule}.
function d10Program(): MapProgram {
  return new MapProgram()
    .with("denied_rule", new Clause(Goal.of("denied", [Term.var("S")]), [Goal.of("revoked", [Term.var("S")])]))
    .with("permit_rule", new Clause(Goal.of("permit", [Term.var("S")]), [Goal.of("granted", [Term.var("S")])]));
}

function d10Scope(): StratumPrefix {
  return StratumPrefix.of(1, [LogosSymbol.of("denied"), LogosSymbol.of("revoked")]);
}

function hashOf(b: number): Hash {
  const h = new Uint8Array(32);
  h[0] = b;
  return h;
}

const WITNESS_A = hashOf(0xd1);
const WITNESS_B = hashOf(0xd2);

/** Every clause of the program, via the same enumeration the checker uses. */
function clausesOf(program: CompleteProgram): Clause[] {
  const out: Clause[] = [];
  program.forEachClause((_id, clause) => out.push(clause));
  return out;
}

/** A cert whose four pins are honest for `program`, sealed over whichever clause set `sliced` says. */
function d10Cert(program: CompleteProgram, sliced: boolean, witness?: Hash): ClosedModelCert {
  const scope = d10Scope();
  const base = new ClosedModelCert({
    scope,
    programHash: programDigestOf(program),
    profileHash: hashOf(0x01),
    ctxHash: hashOf(0x02),
    theoryConfigHash: hashOf(0x03),
    edbSnapshotHashes: [],
    domains: [],
    extensions: [],
    supports: [],
    limitsDecl: { certFacts: 0, domainValues: 0, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 4096 },
  });
  const clauses = clausesOf(program);
  const programHash = sliced ? programDigestOverScope(clauses, base) : programDigestOf(program);
  return new ClosedModelCert({
    scope,
    programHash,
    profileHash: hashOf(0x01),
    ctxHash: hashOf(0x02),
    theoryConfigHash: hashOf(0x03),
    edbSnapshotHashes: [],
    domains: [],
    extensions: [],
    supports: [],
    limitsDecl: { certFacts: 0, domainValues: 0, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 4096 },
    ...(witness === undefined ? {} : { decompositionWitness: witness }),
  });
}

function d10Context(program: CompleteProgram, witness?: Hash): CertContextT {
  const base = CertContext.of(programDigestOf(program), hashOf(0x01), hashOf(0x02), hashOf(0x03));
  return witness === undefined ? base : CertContext.withDecomposition(base, witness);
}

// test-double: consumer(admits revoked and granted leaves)
const leaves: LeafVerifier<void> = {
  extensional: () => PredicateSet.from(["revoked", "granted"]),
  verify: (): LeafOutcome => ({ kind: "admit" }),
};

function d10Profile(): CheckProfile<void> {
  return { theory: new TermTheory(), leaves, admit: new AlwaysAdmit<void>(), limits: defaultLimits() };
}

/** The verdict of gate 2 only: `undefined` when the context gate passed, else its code. */
function contextVerdict(cert: ClosedModelCert, program: CompleteProgram, cx: CertContextT): string | undefined {
  const result = checkClosedModelChain(program, [cert], undefined, d10Profile(), cx).verdict;
  return result.kind === "reject" && result.code === "cert_context_mismatch" ? result.code : undefined;
}

// ANTI-VACUITY. Every case below is meaningless unless the slice and the complete program digest
// apart — if they collided, a checker that never read `decompositionWitness` would pass them all.
test("d10: the slice digest differs from the complete program digest", () => {
  const program = d10Program();
  const complete = programDigestOf(program);
  const clauses = clausesOf(program);
  const slice = programDigestOverScope(clauses, d10Cert(program, false));
  assert.ok(
    !Buffer.from(complete).equals(Buffer.from(slice)),
    "the D10 ts arm is vacuous unless the slice and the complete program digest apart",
  );
});

// THE GREEN TWIN: a slice seal replays under the decomposition that authorized it.
test("d10: a slice seal replays under its own decomposition", () => {
  const program = d10Program();
  assert.equal(
    contextVerdict(d10Cert(program, true, WITNESS_A), program, d10Context(program, WITNESS_A)),
    undefined,
    "a slice seal must get past the context gate under its own decomposition",
  );
});

// CONTROL: the pin is load-bearing. A DIFFERENT decomposition is refused.
test("d10: a slice seal under a different decomposition is refused", () => {
  const program = d10Program();
  assert.equal(
    contextVerdict(d10Cert(program, true, WITNESS_A), program, d10Context(program, WITNESS_B)),
    "cert_context_mismatch",
  );
});

// CONTROL: a slice seal cannot discharge in a run that declares no decomposition — this is what
// keeps a component's cert from leaking into a whole-program check.
test("d10: a slice seal cannot discharge in a whole-program run", () => {
  const program = d10Program();
  assert.equal(
    contextVerdict(d10Cert(program, true, WITNESS_A), program, d10Context(program)),
    "cert_context_mismatch",
  );
});

// CONTROL: D10 does not disturb the whole-program path. An ordinary cert is still admitted at the
// context gate even when the CALLER declares a decomposition — otherwise D10 would have made
// every existing cert conditional on the caller not decomposing.
test("d10: a whole-program cert is unaffected by a decomposed context", () => {
  const program = d10Program();
  assert.equal(
    contextVerdict(d10Cert(program, false), program, d10Context(program, WITNESS_A)),
    undefined,
    "a whole-program cert must be unaffected by the caller's decomposition",
  );
});

// CONTROL: the pre-D10 reading is untouched — and slicing ALONE never buys admission, which is
// exactly the assertion unit 1 (#1618) landed in rs and which stays red on purpose.
test("d10: pre-existing behaviour is unchanged, and slicing alone buys nothing", () => {
  const program = d10Program();
  assert.equal(
    contextVerdict(d10Cert(program, false), program, d10Context(program)),
    undefined,
    "an honest whole-program cert must still pass the context gate",
  );
  assert.equal(
    contextVerdict(d10Cert(program, true), program, d10Context(program)),
    "cert_context_mismatch",
    "slicing alone must never buy admission",
  );
});

// WIRE: the 11th element is TRAILING-OPTIONAL, so a cert that seals the complete program encodes
// to the same TEN-element tuple it always did — and a slice-sealed one round-trips its pin.
test("d10: the wire element is trailing-optional and round-trips", () => {
  const program = d10Program();

  // A one-node derivation, so the fixture is a real proof whose root names a node. (Since #2630
  // the decoder passes an out-of-range root through and check refuses it as root_out_of_range.)
  const node = () => [new LeafNode(GroundLiteral.of("revoked", [valueAtom(new TextEncoder().encode("s1"))]), Evidence.none())];

  const plain = new Derivation(node(), 0, [d10Cert(program, false)]);
  const backPlain = derivationFromValue(derivationAsValue(plain));
  assert.equal(backPlain.closedWorld[0]!.decompositionWitness, undefined, "a plain cert must carry no witness");

  const sealed = new Derivation(node(), 0, [d10Cert(program, true, WITNESS_A)]);
  const backSealed = derivationFromValue(derivationAsValue(sealed));
  const got = backSealed.closedWorld[0]!.decompositionWitness;
  assert.ok(got !== undefined, "a slice-sealed cert must round-trip its witness pin");
  assert.ok(Buffer.from(got).equals(Buffer.from(WITNESS_A)), "the round-tripped witness must be the one sealed");
});
