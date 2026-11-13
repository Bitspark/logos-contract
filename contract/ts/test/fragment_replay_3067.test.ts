// #3067 (research 0028 row A15; seat:caa's rulings Q1 to Q3): vectors/fragment.json replayed through
// check's scope gate, as rs's check/fragment_replay.rs and go's fragment_replay_3067_test.go do. Each
// case states one sealed clause of a program and its context; the gate refuses the program by the
// case's `expect` (the first gate the clause fails, and that gate's subject), or admits it when
// `expect` is null.

import { test } from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import {
  BodyLit,
  Clause,
  ClosedModelCert,
  CountLit,
  Goal,
  type GroundLiteral,
  MapProgram,
  PredicateRef,
  ProjectSpec,
  StratumPrefix,
  Symbol,
  Term,
  TheoryGround,
  type Theory,
  zeroHash,
} from "../src/index.js";
import { CertView } from "../src/cert_stack.js";
import { checkScopeDownwardClosed } from "../src/cert_check.js";
import { classifySealedClause, type Outside, ScopeGraph, SealContext } from "../src/fragment.js";

interface FragmentExpect {
  readonly outside: string;
  readonly pred?: string;
  readonly same_scope?: boolean;
  readonly through?: string;
  readonly var?: string;
}

interface FragmentCase {
  readonly name: string;
  readonly program: readonly unknown[];
  readonly clause: number;
  readonly seals: readonly string[];
  readonly reads_lower: readonly string[];
  readonly owns: readonly string[];
  readonly expect: FragmentExpect | null;
}

function loadCases(): readonly FragmentCase[] {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const file = path.join(dir, "vectors", "fragment.json");
    if (fs.existsSync(file)) return (JSON.parse(fs.readFileSync(file, "utf8")) as { cases: FragmentCase[] }).cases;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/fragment.json above ${dir}`);
    dir = parent;
  }
}

/** The relations a case's theory owns: it decides nothing, and owning is all the gate reads. */
// test-double: consumer(owns the relations a fragment.json case lists, decides none)
class FragmentOwns implements Theory {
  readonly #owned: readonly Symbol[];
  constructor(owned: readonly Symbol[]) {
    this.#owned = owned;
  }
  owns(pred: Symbol): boolean {
    return this.#owned.some((s) => s.equals(pred));
  }
  decideGround(_atom: GroundLiteral): TheoryGround {
    return TheoryGround.disowned();
  }
}

const utf8 = new TextEncoder();

function term(v: unknown): Term {
  if (typeof v === "string") return /^[A-Z]/.test(v) ? Term.var(v) : Term.atom(utf8.encode(v));
  if (Array.isArray(v)) return Term.tuple([Term.atom(utf8.encode(String(v[0]))), ...v.slice(1).map(term)]);
  throw new Error(`not a term in fragment.json's notation: ${JSON.stringify(v)}`);
}

function goal(v: unknown): Goal {
  const items = v as readonly unknown[];
  return Goal.of(String(items[0]), items.slice(1).map(term));
}

function bodyLit(v: unknown): BodyLit {
  if (Array.isArray(v)) return BodyLit.pos(goal(v));
  const lit = v as { readonly neg?: unknown; readonly count?: Record<string, unknown> };
  if (lit.neg !== undefined) return BodyLit.neg(goal(lit.neg));
  const c = lit.count!;
  const filter = (c["filter"] as readonly (readonly [number, unknown])[]).map(([pos, t]) => ({ pos, term: term(t) }));
  return BodyLit.count(
    new CountLit(new PredicateRef(Symbol.of(String(c["pred"])), Number(c["arity"])), filter, ProjectSpec.rows(), term(c["result"])),
  );
}

function clause(v: unknown): Clause {
  const c = v as { readonly head: unknown; readonly body?: readonly unknown[] };
  return new Clause(goal(c.head), (c.body ?? []).map(bodyLit));
}

/** A certificate that seals `preds` and carries nothing else: the scope gate reads only its scope. */
function cert(preds: readonly Symbol[]): ClosedModelCert {
  return new ClosedModelCert({
    scope: StratumPrefix.of(1, preds),
    programHash: zeroHash(),
    profileHash: zeroHash(),
    ctxHash: zeroHash(),
    theoryConfigHash: zeroHash(),
    edbSnapshotHashes: [],
    domains: [],
    extensions: [],
    supports: [],
    limitsDecl: { certFacts: 0, domainValues: 0, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 0 },
  });
}

/** CertView keys a lower read by its symbol's bytes in hex, as cert_stack.ts does. */
function symKey(pred: Symbol): string {
  return Array.from(pred.bytes(), (b) => b.toString(16).padStart(2, "0")).join("");
}

/** The phrase check's refusal carries for `expect`: the gate, and its subject. */
function phrase(e: FragmentExpect): string {
  const q = (s: string | undefined): string => JSON.stringify(s ?? "");
  switch (e.outside) {
    case "count_not_lower":
      return e.same_scope === true
        ? `contains a count over predicate ${q(e.pred)}, which this same certificate seals`
        : `contains a count over predicate ${q(e.pred)}, which no unique, exact, Valid strictly lower certificate seals`;
    case "count_open_compound":
      return `count over predicate ${q(e.pred)} contains an open compound`;
    case "constructor_cycle":
      return `on a dependency cycle through ${q(e.through)}`;
    case "unserved":
      return `references predicate ${q(e.pred)} that is neither sealed`;
    case "intra_scope_negation":
      return `negates predicate ${q(e.pred)} sealed by this same prefix`;
    case "unbound_count_filter":
      return `count over predicate ${q(e.pred)} has filter variable ${q(e.var)} not bound`;
    case "unbound_variable":
      return `has unsafe variable ${q(e.var)}:`;
  }
  throw new Error(`fragment.json names an unknown gate: ${e.outside}`);
}

test("every fragment.json case is classified by its first gate in check (#3067)", () => {
  const cases = loadCases();
  assert.ok(cases.length >= 20, `fragment.json holds its cases: ${cases.length}`);
  const failures: string[] = [];
  for (const c of cases) {
    const program = new MapProgram();
    c.program.forEach((cl, i) => program.insert(`c${String(i).padStart(2, "0")}`, clause(cl)));
    const readsLower = c.reads_lower.map((n) => Symbol.of(n));
    const lower = cert(readsLower);
    const lowerMap = new Map<string, { readonly index: number; readonly cert: ClosedModelCert }>();
    for (const pred of readsLower) lowerMap.set(symKey(pred), { index: 0, cert: lower });
    const view = new CertView(
      cert(c.seals.map((n) => Symbol.of(n))),
      lowerMap,
    );
    const got = checkScopeDownwardClosed(view, program, new FragmentOwns(c.owns.map((n) => Symbol.of(n))));
    if (c.expect === null) {
      if (got !== undefined) failures.push(`${c.name}: inside the fragment, but refused: ${got[1]}`);
      continue;
    }
    if (got === undefined) {
      failures.push(`${c.name}: expected ${JSON.stringify(c.expect)}, admitted`);
      continue;
    }
    const want = phrase(c.expect);
    if (got[0] !== "cert_scope_incomplete" || !got[1].includes(want)) {
      failures.push(`${c.name}: expected ${JSON.stringify(want)}, got ${got[0]}: ${got[1]}`);
    }
  }
  assert.deepEqual(failures, [], `fragment.json through check's scope gate:\n${failures.join("\n")}`);
});

/** An `Outside` as one comparable string: its gate and its subject. */
function rendered(o: Outside | undefined): string {
  if (o === undefined) return "inside";
  const name = (sym: Symbol): string => new TextDecoder().decode(sym.bytes());
  switch (o.kind) {
    case "count_not_lower":
      return `${o.kind} ${name(o.pred)} same_scope=${String(o.sameScope)}`;
    case "count_open_compound":
    case "unserved":
    case "intra_scope_negation":
      return `${o.kind} ${name(o.pred)}`;
    case "constructor_cycle":
      return `${o.kind} ${name(o.through)}`;
    case "unbound_count_filter":
      return `${o.kind} ${name(o.pred)} ${o.var.asStr()}`;
    case "unbound_variable":
      return `${o.kind} ${o.var.asStr()}`;
    default: {
      const unhandled: never = o;
      throw new Error(`an Outside this replay cannot render: ${JSON.stringify(unhandled)}`);
    }
  }
}

/** The same rendering of a case's `expect`. */
function expected(e: FragmentExpect | null): string {
  if (e === null) return "inside";
  switch (e.outside) {
    case "count_not_lower":
      return `${e.outside} ${e.pred ?? ""} same_scope=${String(e.same_scope === true)}`;
    case "constructor_cycle":
      return `${e.outside} ${e.through ?? ""}`;
    case "unbound_count_filter":
      return `${e.outside} ${e.pred ?? ""} ${e.var ?? ""}`;
    case "unbound_variable":
      return `${e.outside} ${e.var ?? ""}`;
  }
  return `${e.outside} ${e.pred ?? ""}`;
}

test("every fragment.json case is classified by the contract tier's one function (#3067)", () => {
  const failures: string[] = [];
  for (const c of loadCases()) {
    const program = c.program.map(clause);
    const ctx = new SealContext(
      c.seals.map((n) => Symbol.of(n)),
      c.reads_lower.map((n) => Symbol.of(n)),
    );
    const graph = new ScopeGraph();
    for (const cl of program) graph.add(cl, (pred) => ctx.seals(pred));
    const owned = new FragmentOwns(c.owns.map((n) => Symbol.of(n)));
    const target = program[c.clause];
    assert.ok(target !== undefined, `${c.name}: its clause index names a clause of its program`);
    const owns = (pred: Symbol): boolean => owned.owns(pred);
    const got = rendered(classifySealedClause(target, ctx, graph, owns, owns));
    const want = expected(c.expect);
    if (got !== want) failures.push(`${c.name}: expected ${want}, got ${got}`);
  }
  assert.deepEqual(failures, [], `fragment.json through classifySealedClause:\n${failures.join("\n")}`);
});
