/**
 * TS replay of vectors/completion_algebra.json, the completion algebra's not/and/or (research 0031
 * row 15, #3164; seat:caa's ruling on #3179). The same file is replayed by Rust
 * (contract/rs/tests/completion_vectors.rs) and Go (contract/go/completion/completion_vectors_test.go).
 *
 * Each case is checked twice: the written operand order must give `expect` exactly, and every
 * reordering of every and/or node's operands must give an outcome of the same class. A case with
 * `construct` names a kind and scope `causeOf` must refuse; its `expr` holds a hand-built value of
 * that illegal pair, which must read as malformed_outcome. The replay is also run against three
 * deliberately wrong algebras (one that never absorbs, one that absorbs a request-scope stop, one
 * that ranks a fault with a limit) and must reject each: the broken counterparts design/0004 §7.7
 * asks for.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { completion } from "../src/index.js";

type Outcome = completion.GroundOutcome<string>;

interface Algebra {
  not: (a: Outcome) => Outcome;
  and: (a: Outcome, b: Outcome) => Outcome;
  or: (a: Outcome, b: Outcome) => Outcome;
}

const correct: Algebra = { not: completion.not, and: completion.and, or: completion.or };

interface Node {
  arm?: string;
  false_code?: string;
  kind?: string;
  scope?: string;
  limit?: string;
  op?: string;
  args?: Node[];
}

interface VectorFile {
  vocabulary: {
    false_codes: string[];
    kinds: string[];
    scopes: string[];
    absorbable_scopes: string[];
    scoped_stops: string[];
    request_stops: string[];
    faults: string[];
  };
  cases: { name: string; why: string; construct?: Node; refused?: boolean; expr: Node; expect: Node }[];
}

function loadVectors(): VectorFile {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "completion_algebra.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8")) as VectorFile;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/completion_algebra.json above ${dir}`);
    dir = parent;
  }
}

// The vocabulary, written out; the vocabulary test compares it with the vector's.
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
const falseCodes: completion.FalseCode[] = ["unsatisfied"];

function member<T extends string>(list: readonly T[], tag: string | undefined, what: string): T {
  const found = list.find((m) => m === tag);
  if (found === undefined) throw new Error(`unknown ${what} ${String(tag)}`);
  return found;
}

/** A leaf. A cause goes through `causeOf`; with `handBuilt`, an illegal pair is built by hand. */
function leaf(n: Node, handBuilt: boolean): Outcome {
  switch (n.arm) {
    case "holds":
      return completion.completed(completion.holds);
    case "fails":
      return completion.completed(completion.fails(member(falseCodes, n.false_code, "false code")));
    case "not_completed": {
      if (typeof n.kind !== "string") throw new Error("a cause without a kind");
      try {
        return completion.notCompleted(completion.causeOf(n.kind, n.scope));
      } catch (e) {
        if (!handBuilt || !(e instanceof completion.IllegalCauseError)) throw e;
        const raw = n.scope === undefined ? { kind: n.kind } : { kind: n.kind, scope: n.scope };
        return { kind: "not_completed", cause: raw } as unknown as Outcome;
      }
    }
    case "limit_exceeded":
      if (typeof n.limit !== "string") throw new Error("limit_exceeded without a limit");
      return completion.limitExceeded(n.limit);
    case undefined:
      throw new Error(`a leaf without an arm: ${JSON.stringify(n)}`);
    default:
      throw new Error(`unknown arm ${String(n.arm)}`);
  }
}

/** The outcome's class: the part of the result that must not depend on operand order. */
function classOf(o: Outcome): string {
  const x = completion.normalize(o);
  switch (x.kind) {
    case "completed":
      return x.value.kind;
    case "not_completed": {
      const c = x.cause;
      if (completion.isFault(c.kind) || !("scope" in c)) return "fault";
      return completion.isAbsorbable(c.scope) ? "absorbable" : "dominant";
    }
    case "limit_exceeded":
      return "dominant";
    default:
      return "fault";
  }
}

function args(n: Node): Node[] {
  if (!Array.isArray(n.args)) throw new Error(`expression without args: ${JSON.stringify(n)}`);
  return n.args;
}

function fold(alg: Algebra, op: string | undefined, operands: Outcome[]): Outcome {
  const combine = op === "and" ? alg.and : op === "or" ? alg.or : undefined;
  if (combine === undefined) throw new Error(`${String(op)} does not fold`);
  const [first, ...rest] = operands;
  if (first === undefined) throw new Error("a fold has at least one operand");
  return rest.reduce(combine, first);
}

function evaluate(alg: Algebra, e: Node, handBuilt: boolean): Outcome {
  if (e.arm !== undefined) return leaf(e, handBuilt);
  const operands = args(e).map((a) => evaluate(alg, a, handBuilt));
  if (e.op === "not") {
    const [only] = operands;
    if (only === undefined || operands.length !== 1) throw new Error("not takes one operand");
    return alg.not(only);
  }
  return fold(alg, e.op, operands);
}

function permutations(n: number): number[][] {
  if (n === 0) return [[]];
  const out: number[][] = [];
  for (const rest of permutations(n - 1)) {
    for (let at = 0; at <= rest.length; at++) out.push([...rest.slice(0, at), n - 1, ...rest.slice(at)]);
  }
  return out;
}

/** The expression under every reordering of every and/or node's operands. */
function evaluateEveryOrder(alg: Algebra, e: Node, handBuilt: boolean): Outcome[] {
  if (e.arm !== undefined) return [leaf(e, handBuilt)];
  const children = args(e).map((a) => evaluateEveryOrder(alg, a, handBuilt));
  if (e.op === "not") return (children[0] ?? []).map((o) => alg.not(o));
  const out: Outcome[] = [];
  for (const order of permutations(children.length)) {
    let combos: Outcome[][] = [[]];
    for (const i of order) {
      const next: Outcome[][] = [];
      for (const combo of combos) for (const o of children[i] ?? []) next.push([...combo, o]);
      combos = next;
    }
    for (const c of combos) out.push(fold(alg, e.op, c));
  }
  return out;
}

function replay(alg: Algebra): string[] {
  const failures: string[] = [];
  for (const raw of loadVectors().cases) {
    // Every failure carries the case's why, so the reader sees what the case pins.
    const c = { ...raw, name: `${raw.name} (${raw.why})` };
    const handBuilt = c.construct !== undefined;
    if (c.construct !== undefined) {
      assert.equal(c.refused, true, `${c.name}: a construct case must say refused: true`);
      const { kind, scope } = c.construct;
      if (typeof kind !== "string") throw new Error(`${c.name}: construct without a kind`);
      assert.throws(() => completion.causeOf(kind, scope), completion.IllegalCauseError, `${c.name}: causeOf built it`);
    }
    const expect = leaf(c.expect, false);
    const got = evaluate(alg, c.expr, handBuilt);
    try {
      assert.deepStrictEqual(got, expect);
    } catch {
      failures.push(`${c.name}: written order gave ${JSON.stringify(got)}, expected ${JSON.stringify(expect)}`);
      continue;
    }
    const off = evaluateEveryOrder(alg, c.expr, handBuilt).find((o) => classOf(o) !== classOf(expect));
    if (off !== undefined) {
      failures.push(`${c.name}: a reordering gave ${JSON.stringify(off)}, class ${classOf(off)} instead of ${classOf(expect)}`);
    }
  }
  return failures;
}

test("completion vectors replay", () => {
  const n = loadVectors().cases.length;
  assert.ok(n >= 55, `expected the full vector, loaded ${n} cases`);
  const failures = replay(correct);
  assert.deepStrictEqual(failures, [], `${failures.length} of ${n} cases fail:\n${failures.join("\n")}`);
});

test("completion vocabulary matches the vector", () => {
  const v = loadVectors().vocabulary;
  assert.deepStrictEqual(scopes, v.scopes);
  assert.deepStrictEqual(kinds, v.kinds);
  assert.deepStrictEqual(falseCodes, v.false_codes);
  assert.deepStrictEqual(
    scopes.filter((s) => completion.isAbsorbable(s)),
    v.absorbable_scopes,
  );
  const accepts = (k: string, s?: string): boolean => {
    try {
      completion.causeOf(k, s);
      return true;
    } catch {
      return false;
    }
  };
  assert.deepStrictEqual(
    kinds.filter((k) => accepts(k, "literal")),
    v.scoped_stops,
  );
  assert.deepStrictEqual(
    kinds.filter((k) => accepts(k, "request") && !accepts(k, "literal")),
    v.request_stops,
  );
  assert.deepStrictEqual(
    kinds.filter((k) => accepts(k)),
    v.faults,
  );
  assert.deepStrictEqual(
    kinds.filter((k) => completion.isFault(k)),
    v.faults,
  );
});

// ---- the broken counterparts ----

function mutant(rank: (o: Outcome) => number): (a: Outcome, b: Outcome) => Outcome {
  return (a, b) => (rank(b) > rank(a) ? b : a);
}

function rankBy(read: (o: Outcome) => string, order: string[]): (o: Outcome) => number {
  return (o) => {
    const i = order.indexOf(read(o));
    return i < 0 ? order.length : i;
  };
}

/** Ranks an undecided operand above a decided one in and and in or. */
const neverAbsorbs: Algebra = {
  not: completion.not,
  and: mutant(rankBy(classOf, ["holds", "fails", "absorbable", "dominant", "fault"])),
  or: mutant(rankBy(classOf, ["fails", "holds", "absorbable", "dominant", "fault"])),
};

/** Reads every stop as absorbable, wherever it reaches. */
function everyScope(o: Outcome): string {
  const c = classOf(o);
  return c === "dominant" && o.kind === "not_completed" ? "absorbable" : c;
}

const absorbsEveryScope: Algebra = {
  not: completion.not,
  and: mutant(rankBy(everyScope, ["holds", "absorbable", "fails", "dominant", "fault"])),
  or: mutant(rankBy(everyScope, ["fails", "absorbable", "holds", "dominant", "fault"])),
};

/** Ranks a fault with a limit, as before seat:caa's ruling on #3179. */
function faultAsDominant(o: Outcome): string {
  const c = classOf(o);
  return c === "fault" ? "dominant" : c;
}

const noFaultClass: Algebra = {
  not: completion.not,
  and: mutant(rankBy(faultAsDominant, ["holds", "absorbable", "fails", "dominant"])),
  or: mutant(rankBy(faultAsDominant, ["fails", "absorbable", "holds", "dominant"])),
};

function assertRejected(alg: Algebra, mutantName: string, mustFail: string): void {
  const failures = replay(alg);
  assert.ok(
    failures.some((f) => f.startsWith(`${mustFail} (`)),
    `the vector must reject the ${mutantName} mutant at ${mustFail}; it failed only:\n${failures.join("\n")}`,
  );
}

test("completion vectors reject an algebra that never absorbs", () => {
  assertRejected(neverAbsorbs, "never-absorbs", "and_fails_absorbs_literal_undecided");
  assertRejected(neverAbsorbs, "never-absorbs", "or_holds_absorbs_literal_undecided");
});

test("completion vectors reject an algebra that absorbs a request stop", () => {
  assertRejected(absorbsEveryScope, "absorbs-request-scope", "and_fails_keeps_request_undecided");
  assertRejected(absorbsEveryScope, "absorbs-request-scope", "or_holds_keeps_request_undecided");
});

test("completion vectors reject an algebra that ranks a fault with a limit", () => {
  assertRejected(noFaultClass, "no-fault-class", "and_limit_then_fault_reports_fault");
  assertRejected(noFaultClass, "no-fault-class", "and_fault_then_limit_reports_fault");
});
