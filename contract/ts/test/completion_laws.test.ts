/**
 * The completion algebra's laws, checked over EVERY ground outcome its vocabulary can form
 * (research 0031 row 15, #3164; seat:caa's ruling on #3179): the TypeScript twin of
 * contract/rs/tests/completion_laws.rs. The carrier is finite, so each law is checked over every
 * pair or triple, not a sample. The Kleene tables and the legal kind/scope pairs are written out
 * independently of the implementation.
 *
 * It also checks what only Go and TypeScript can express: a value outside the types (an unknown
 * kind, an invalid code, an illegal cause, null) is read as the fault malformed_outcome, and never
 * as an answer.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { completion } from "../src/index.js";

type Outcome = completion.GroundOutcome<string>;

const scopes: completion.CauseScope[] = ["literal", "branch", "enumeration", "dependency", "theory_snapshot", "request"];
const kinds: completion.NonCompletionKind[] = [
  "capacity",
  "work_cap",
  "instantiation",
  "host_refusal",
  "reply_unreadable",
  "inconsistent_theory",
  "malformed_outcome",
];

/** The ruling's table, written independently of `causeOf`. */
function legal(kind: string, scope: string | undefined): boolean {
  if (kind === "capacity" || kind === "work_cap" || kind === "instantiation") return scope !== undefined;
  if (kind === "host_refusal" || kind === "reply_unreadable") return scope === "request";
  if (kind === "inconsistent_theory" || kind === "malformed_outcome") return scope === undefined;
  return false;
}

const allScopes: (string | undefined)[] = [undefined, ...scopes];

const H: Outcome = completion.completed(completion.holds);
const F: Outcome = completion.completed(completion.fails("unsatisfied"));

function carrier(): Outcome[] {
  const all: Outcome[] = [H, F, completion.limitExceeded("limit_a"), completion.limitExceeded("limit_b")];
  for (const k of kinds) {
    for (const s of allScopes) {
      if (legal(k, s)) all.push(completion.notCompleted(completion.causeOf(k, s)));
    }
  }
  return all;
}

type Truth = "true" | "false" | "undecided";

function truth(o: Outcome): Truth {
  switch (o.kind) {
    case "completed":
      return o.value.kind === "holds" ? "true" : "false";
    case "limit_exceeded":
    case "not_completed":
      return "undecided";
    default:
      return "undecided";
  }
}

/** 0 decided or absorbable, 1 a dominant stop or a limit, 2 a fault. */
function tier(o: Outcome): number {
  switch (o.kind) {
    case "completed":
      return 0;
    case "limit_exceeded":
      return 1;
    case "not_completed": {
      const c = o.cause;
      if (completion.isFault(c.kind) || !("scope" in c)) return 2;
      return completion.isAbsorbable(c.scope) ? 0 : 1;
    }
    default:
      return 2;
  }
}

const cls = (o: Outcome): string => `${truth(o)}/${tier(o)}`;

const kNot = (a: Truth): Truth => (a === "true" ? "false" : a === "false" ? "true" : "undecided");
const kAnd = (a: Truth, b: Truth): Truth =>
  a === "false" || b === "false" ? "false" : a === "undecided" || b === "undecided" ? "undecided" : "true";
const kOr = (a: Truth, b: Truth): Truth =>
  a === "true" || b === "true" ? "true" : a === "undecided" || b === "undecided" ? "undecided" : "false";

const { not, and, or } = completion;
const ops: [string, (a: Outcome, b: Outcome) => Outcome][] = [
  ["and", and],
  ["or", or],
];
const show = (o: unknown): string => JSON.stringify(o);

test("completion causeOf builds exactly the legal pairs", () => {
  for (const k of kinds) {
    for (const s of allScopes) {
      if (legal(k, s)) {
        const c = completion.causeOf(k, s);
        assert.equal(c.kind, k);
        assert.equal("scope" in c ? c.scope : undefined, s);
      } else {
        assert.throws(() => completion.causeOf(k, s), completion.IllegalCauseError, `${k} at ${String(s)}`);
      }
    }
    assert.equal(completion.isFault(k), legal(k, undefined), `${k}: a fault is exactly a kind with no scope`);
  }
  assert.throws(() => completion.causeOf("gone", "literal"), completion.IllegalCauseError);
  assert.throws(() => completion.causeOf("capacity", "nowhere"), completion.IllegalCauseError);
  assert.deepStrictEqual(completion.requestStop("host_refusal"), { kind: "host_refusal", scope: "request" });
  assert.deepStrictEqual(completion.fault("inconsistent_theory"), { kind: "inconsistent_theory" });
});

test("completion carrier is the whole vocabulary", () => {
  assert.equal(carrier().length, 26);
});

test("completion negation is strong Kleene and an involution", () => {
  for (const a of carrier()) {
    assert.equal(truth(not(a)), kNot(truth(a)), `not ${show(a)}`);
    assert.deepStrictEqual(not(not(a)), a, `not not ${show(a)}`);
    if (truth(a) === "undecided") assert.deepStrictEqual(not(a), a, `not changed ${show(a)}`);
  }
});

test("completion idempotence", () => {
  for (const a of carrier()) {
    assert.deepStrictEqual(and(a, a), a);
    assert.deepStrictEqual(or(a, a), a);
  }
});

test("completion commutativity of the class, exact when classes differ", () => {
  for (const a of carrier()) {
    for (const b of carrier()) {
      for (const [name, f] of ops) {
        const ab = f(a, b);
        const ba = f(b, a);
        assert.equal(cls(ab), cls(ba), `${show(a)} ${name} ${show(b)}`);
        if (cls(a) !== cls(b)) assert.deepStrictEqual(ab, ba, `${show(a)} ${name} ${show(b)}`);
      }
    }
  }
});

test("completion associativity is exact", () => {
  const all = carrier();
  for (const a of all) {
    for (const b of all) {
      for (const c of all) {
        assert.deepStrictEqual(and(and(a, b), c), and(a, and(b, c)));
        assert.deepStrictEqual(or(or(a, b), c), or(a, or(b, c)));
      }
    }
  }
});

test("completion De Morgan is exact", () => {
  for (const a of carrier()) {
    for (const b of carrier()) {
      assert.deepStrictEqual(not(and(a, b)), or(not(a), not(b)));
      assert.deepStrictEqual(not(or(a, b)), and(not(a), not(b)));
    }
  }
});

test("completion without a dominant operand, the truth is strong Kleene", () => {
  const plain = carrier().filter((o) => tier(o) === 0);
  for (const a of plain) {
    for (const b of plain) {
      assert.equal(truth(and(a, b)), kAnd(truth(a), truth(b)), `${show(a)} and ${show(b)}`);
      assert.equal(truth(or(a, b)), kOr(truth(a), truth(b)), `${show(a)} or ${show(b)}`);
      assert.equal(truth(and(a, or(a, b))), truth(a));
      assert.equal(truth(or(a, and(a, b))), truth(a));
    }
  }
});

test("completion the highest tier is never absorbed, and the leftmost is reported", () => {
  for (const a of carrier()) {
    for (const b of carrier()) {
      const top = Math.max(tier(a), tier(b));
      if (top === 0) continue;
      const leftmost = tier(a) === top ? a : b;
      assert.deepStrictEqual(and(a, b), leftmost, `${show(a)} and ${show(b)}`);
      assert.deepStrictEqual(or(a, b), leftmost, `${show(a)} or ${show(b)}`);
    }
  }
});

test("completion a decided result does not depend on an undecided operand", () => {
  for (const a of carrier()) {
    for (const b of carrier()) {
      for (const [name, f] of ops) {
        const r = truth(f(a, b));
        if (r === "undecided") continue;
        for (const d of [H, F]) {
          if (truth(a) === "undecided") assert.equal(truth(f(d, b)), r, `${show(a)} ${name} ${show(b)}, left as ${show(d)}`);
          if (truth(b) === "undecided") assert.equal(truth(f(a, d)), r, `${show(a)} ${name} ${show(b)}, right as ${show(d)}`);
        }
      }
    }
  }
});

test("completion an invalid value is a malformed fault, never an answer", () => {
  const malformed: Outcome = completion.notCompleted(completion.fault("malformed_outcome"));
  const limit: Outcome = completion.limitExceeded("limit_a");
  // Values outside the types, as a host or a careless producer could hand them over.
  const invalid: Record<string, unknown> = {
    null: null,
    "an unknown kind": { kind: "maybe" },
    "a decision of unknown kind": { kind: "completed", value: { kind: "perhaps" } },
    "a fails with no code": { kind: "completed", value: { kind: "fails" } },
    "a fails with an unknown code": { kind: "completed", value: { kind: "fails", code: "nope" } },
    "a stop with no scope": { kind: "not_completed", cause: { kind: "work_cap" } },
    "a cause of unknown kind": { kind: "not_completed", cause: { kind: "gone", scope: "literal" } },
    "a fault with a local scope": { kind: "not_completed", cause: { kind: "inconsistent_theory", scope: "literal" } },
    "a host refusal at literal scope": { kind: "not_completed", cause: { kind: "host_refusal", scope: "literal" } },
    "a missing cause": { kind: "not_completed" },
  };
  for (const [name, raw] of Object.entries(invalid)) {
    const v = raw as Outcome;
    assert.deepStrictEqual(completion.normalize(v), malformed, name);
    for (const r of [not(v), and(F, v), and(v, F), or(H, v), or(v, H), and(limit, v), and(v, limit)]) {
      assert.deepStrictEqual(r, malformed, `${name}: a combinator returned ${show(r)}`);
    }
  }
});
