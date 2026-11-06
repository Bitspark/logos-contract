/**
 * The CONTRACT-TIER reachability test for the unidentified-component advisory (#815).
 *
 * It imports the **contract barrel and nothing else** — no kernel import anywhere in this
 * file. That is the point: it stands where a consumer of `@bitspark/logos-contract` stands.
 *
 * ADR 0026 **G2** asks each exposed consumer to self-measure. The advisory originally lived
 * in `kernel`, so a consumer binding only the contract package could not reach it — and
 * could not be given it, because `contract → kernel` is an **upward** edge the `arch` job
 * rejects. That wall was found only when a real consumer (thesmos) tried to follow the
 * instruction and had to submit a source-level audit instead (#791).
 *
 * The kernel forms are now re-exports of these. **A test that imports the kernel cannot
 * detect a regression of the placement** — it would keep passing if the definition moved
 * back up a tier, because a re-export looks identical from above. Only a test that refuses
 * the kernel dependency can.
 *
 * It replays the SAME `vectors/profile_identity_advisory.json` as the kernel arms, so
 * cross-tier agreement and tri-core agreement are one check rather than two.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";

import {
  AlwaysAdmit,
  type CheckProfile,
  type Clause,
  ComponentIdentity,
  type Evidence,
  type GroundLiteral,
  type LeafOutcome,
  type LeafVerifier,
  type NodeMeta,
  PredicateSet,
  type ProfileSlot,
  type RuleAdmissibility,
  RuleOutcome,
  type Symbol as LogosSymbol,
  type Theory,
  TheoryOutcome,
  defaultLimits,
  profileIsFullyIdentified,
  unidentifiedProfileSlots,
  unidentifiedProfileSlotsAllowing,
} from "../src/index.js";

function repoRoot(): string {
  let dir = process.cwd();
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "profile_identity_advisory.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate the advisory vector");
    dir = parent;
  }
}

interface VectorCase {
  name: string;
  theory: string;
  leaves: string;
  admit: string;
  allow_unidentified?: ProfileSlot[];
  unidentified_slots: string[];
}
interface Vectors {
  bindings: Record<string, { id: string; version: string; config_digest: string }>;
  cases: VectorCase[];
}

const vectors: Vectors = JSON.parse(
  fs.readFileSync(path.join(repoRoot(), "vectors", "profile_identity_advisory.json"), "utf8"),
) as Vectors;

function identityFor(name: string): ComponentIdentity | undefined {
  if (name === "anonymous") return undefined;
  const b = vectors.bindings[name];
  assert.ok(b, `unknown binding ${name}`);
  const digest = new Uint8Array(32);
  for (let i = 0; i < 32; i++) digest[i] = parseInt(b.config_digest.slice(i * 2, i * 2 + 2), 16);
  return ComponentIdentity.of(
    new TextEncoder().encode(b.id),
    new TextEncoder().encode(b.version),
    digest,
  );
}

function theoryFor(name: string): Theory {
  // test-double: consumer(a theory identified per vector case)
  const base: Theory = {
    owns: (_p: LogosSymbol) => false,
    decide: (_a: GroundLiteral) => TheoryOutcome.NotMine,
  };
  const id = identityFor(name);
  return id === undefined ? base : { ...base, identity: () => id };
}

function leavesFor(name: string): LeafVerifier<undefined> {
  const ext = PredicateSet.from(["p/1"]);
  // test-double: consumer(a leaf verifier identified per vector case)
  const base: LeafVerifier<undefined> = {
    extensional: () => ext,
    verify: (_a: GroundLiteral, _e: Evidence, _c: undefined): LeafOutcome => ({
      kind: "reject",
      code: "vector",
    }),
  };
  const id = identityFor(name);
  return id === undefined ? base : { ...base, identity: () => id };
}

// test-double: adversarial(no identity: the anonymous reading the advisory flags)
const anonAdmit: RuleAdmissibility<undefined> = {
  admissible: (_c: Clause, _m: NodeMeta, _x: undefined): RuleOutcome => RuleOutcome.Admit,
};

test("the advisory is reachable and correct from the contract barrel alone", () => {
  assert.ok(vectors.cases.length > 0, "vector must carry cases");

  for (const c of vectors.cases) {
    const profile: CheckProfile<undefined> = {
      theory: theoryFor(c.theory),
      leaves: leavesFor(c.leaves),
      admit: c.admit === "anonymous" ? anonAdmit : new AlwaysAdmit<undefined>(),
      limits: defaultLimits(),
    };
    const allowance = c.allow_unidentified ?? [];

    // ORDERED — a set comparison would pass under reordering.
    assert.deepEqual(
      unidentifiedProfileSlotsAllowing(profile, allowance),
      c.unidentified_slots,
      `case ${c.name}: the contract-tier advisory must match the shared vector, in fold order`,
    );

    if (allowance.length === 0) {
      assert.deepEqual(
        unidentifiedProfileSlots(profile),
        c.unidentified_slots,
        `case ${c.name}: the unallowed form must equal the empty allowance`,
      );
      assert.equal(
        profileIsFullyIdentified(profile),
        c.unidentified_slots.length === 0,
        `case ${c.name}: profileIsFullyIdentified must agree with the report`,
      );
    }
  }
});
