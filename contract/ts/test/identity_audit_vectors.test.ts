/*
 * TS replay of vectors/identity_audit.json (#767) — the identity-audit surface:
 * ComponentIdentity.equals/isUnidentified and the compoundIdentityOf baseline fold,
 * which this vector uses to FREEZE the CompoundTheory identity byte layout tri-core.
 *
 * Every case builds REAL member theories (fixture objects over the vector's invented
 * `mistfen` vocabulary, declared invented per ADR 0025 — a member named "unidentified"
 * is a theory WITHOUT an identity() method), constructs a live CompoundTheory, and
 * asserts three independently-falsifiable facts per case: the live identity() equals
 * the hand-authored pin; compoundIdentityOf over the triples equals the same pin; and
 * the distinguishability verdict (live vs the all-unidentified baseline of the same
 * member count) equals the pinned verdict. Plus the order pin: identified_first and
 * identified_second must carry DIFFERENT digests.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
  ComponentIdentity,
  CompoundTheory,
  compoundIdentityOf,
  type GroundLiteral,
  Symbol as LSymbol,
  type Theory,
  TheoryGround,
} from "../src/index.js";

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "identity_audit.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/identity_audit.json");
    dir = parent;
  }
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function loadFile(): any {
  return JSON.parse(
    fs.readFileSync(path.join(repoRoot(), "vectors", "identity_audit.json"), "utf8"),
  );
}

function hex32(s: string): Uint8Array {
  assert.equal(s.length, 64, "config_digest must be 64 hex chars");
  const out = new Uint8Array(32);
  for (let i = 0; i < 32; i += 1) {
    out[i] = Number.parseInt(s.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

const encoder = new TextEncoder();

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function identityFrom(spec: any): ComponentIdentity {
  return ComponentIdentity.of(
    encoder.encode(spec.id),
    encoder.encode(spec.version),
    hex32(spec.config_digest),
  );
}

/** A fixture member carrying an explicit identity. Owns nothing — the audit is about
 * identity, not routing. */
function pinnedTheory(identity: ComponentIdentity): Theory {
  return {
    owns: (_pred: LSymbol) => false,
    decideGround: (_atom: GroundLiteral) => TheoryGround.disowned(),
    identity: () => identity,
  };
}

/** A fixture member WITHOUT identity() — the defaulted (unidentified) reading the
 * audit exists to detect. */
function defaultedTheory(): Theory {
  return {
    owns: (_pred: LSymbol) => false,
    decideGround: (_atom: GroundLiteral) => TheoryGround.disowned(),
  };
}

test("identity_audit vectors replay (ts arm)", () => {
  const file = loadFile();
  assert.equal(file.cases.length, 8, "the pin file carries exactly 8 cases");

  // The plain-component audit primitive, against the vector's triples.
  assert.ok(identityFrom(file.unidentified).isUnidentified());
  for (const name of Object.keys(file.components)) {
    assert.ok(!identityFrom(file.components[name]).isUnidentified(), name);
  }
  // A live component without identity() resolves to unidentified.
  assert.ok(ComponentIdentity.resolve(defaultedTheory()).isUnidentified());

  const configByName = new Map<string, string>();
  for (const c of file.cases) {
    const pinned = ComponentIdentity.of(
      encoder.encode(file.compound_wrapper.id),
      encoder.encode(file.compound_wrapper.version),
      hex32(c.config_digest),
    );

    // (1) LIVE: real member theories -> CompoundTheory -> identity().
    const liveMembers: Theory[] = [];
    const triples: ComponentIdentity[] = [];
    const baseline: ComponentIdentity[] = [];
    for (const m of c.members) {
      baseline.push(ComponentIdentity.unidentified());
      if (m === "unidentified") {
        liveMembers.push(defaultedTheory());
        triples.push(ComponentIdentity.unidentified());
      } else {
        const id = identityFrom(file.components[m]);
        liveMembers.push(pinnedTheory(id));
        triples.push(id);
      }
    }
    const live = new CompoundTheory(liveMembers).identity();
    assert.ok(live.equals(pinned), `case ${c.name}: live identity vs hand-authored pin`);

    // (2) The public audit fn over the triples agrees with the same pin.
    assert.ok(
      compoundIdentityOf(triples).equals(pinned),
      `case ${c.name}: compoundIdentityOf vs hand-authored pin`,
    );

    // (3) The audit verdict: live vs the all-unidentified baseline of the same n.
    const distinguishable = !live.equals(compoundIdentityOf(baseline));
    assert.equal(distinguishable, c.distinguishable, `case ${c.name}: verdict`);

    configByName.set(c.name, c.config_digest);
  }

  // Order is identity-bearing: the same member multiset in two orders pins two digests.
  assert.notEqual(
    configByName.get("identified_first"),
    configByName.get("identified_second"),
    "member order must be identity-bearing",
  );
});
