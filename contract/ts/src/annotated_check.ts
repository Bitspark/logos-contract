// ADR 0031 D5 (#1821 P9 I5a; rulings Q14 and Q15): checking an annotated closed-model certificate.
// [PROPOSED] TS binding of contract/rs/src/check/annotated.rs; go's CheckAnnotatedClosedModel is the
// third. vectors/annotated_closed_model.json is the hand-authored oracle all three replay.
//
// WHAT AN ACCEPT SAYS, AND WHAT IT DOES NOT.
//   - The certificate passes the EXISTING boolean closed-model check as a one-cert world, so its
//     tables are the exact least model of its scope.
//   - Every IDB row's claimed element is the least solution, in the semiring, of the system the
//     closure join's body-true groundings define: a(t) is the left fold from zero, with add, over
//     t's groundings in canonical order, of the left fold from one, with mul, over each grounding's
//     positive non-theory body literals in body order. It is computed by Jacobi rounds from zero,
//     bounded at (IDB rows + 1).
//   - The verdict is RELATIVE TO THE SEMIRING'S IDENTITY (semiringIdentity): the checker uses the
//     semiring it holds only after that identity equals the one the certificate names.
//   - It does NOT attest the elements of the EXTENSIONAL tables. They are premises the certificate
//     binds through its digest, and the accept names those tables as `unattested` (#1821 Q15
//     condition 1).
//   - It names the law it relied on: Kleene least-fixpoint iteration when the ground dependency
//     graph over IDB rows has a cycle, none otherwise.
//
// The groundings are the closure join's own (cert_check.ts joinGroundings, with a recorder): there is
// no second join. The boolean path is unchanged when no recorder is set.

import { encode } from "@bitspark/ontos-codec";
import { atom as valueAtom, bytesEqual, toHex, tuple as valueTuple, type Value } from "@bitspark/ontos-core";

import { type AnnotatedClosedModelCert } from "./annotated_cert.js";
import { groundKey, type RelationTable } from "./cert.js";
import { captureWorld } from "./capture.js";
import { type CertContext, checkClosedModelChain, joinGroundings, type JoinCounters } from "./cert_check.js";
import { CertView } from "./cert_stack.js";
import { captureCheckProfile, type CheckProfile, type RejectionCode } from "./check.js";
import { ClauseIdEncodingError, portableClauseIdBytes } from "./clause_id_encoding.js";
import { escapedName, type GroundLiteral, type Symbol } from "./literal.js";
import { captureClause, nativeClauseId } from "./native_copy.js";
import { type Clause, type ClauseId, type Program } from "./program.js";
import { quote } from "./reify.js";
import { type Semiring, semiringIdentity } from "./semiring.js";
import { type PredicateSet, type Theory } from "./spi.js";
import { Subst } from "./term.js";
import { encodeUtf8 } from "./utf8.js";

/** The law an accept relied on (ADR 0031 D5). Mirrors rs `AnnotationLaw::name()`. */
export type AnnotationLaw = "kleene_least_fixpoint";

/**
 * Why an annotated certificate was refused, when the boolean check accepted it or was never reached
 * (ADR 0031 D5). A separate vocabulary from the FIRM `RejectionCode`, which gains no variant. Mirrors
 * rs `AnnotationCode::code()`.
 */
export type AnnotationCode =
  | "annotation_identity_mismatch"
  | "annotation_unsupported"
  | "annotation_shape"
  | "annotation_not_converged"
  | "annotation_mismatch"
  | "semiring_not_an_element"
  | "semiring_stopped"
  | "annotation_budget_exceeded";

/** A row a refusal names: the sealed table's predicate and the row's index in it. */
export interface AnnotatedRow {
  readonly pred: Symbol;
  readonly index: number;
}

/**
 * The verdict of checkAnnotatedClosedModel. `accept` names the law it relied on (or none) and the
 * extensional tables whose elements are unattested premises; `reject_cert` is the boolean check's
 * own verdict, unchanged; `reject` is an annotation refusal, naming a row where one is at fault.
 */
export type AnnotatedOutcome =
  | { readonly kind: "accept"; readonly law: AnnotationLaw | undefined; readonly unattested: readonly Symbol[] }
  | { readonly kind: "reject_cert"; readonly code: RejectionCode; readonly detail: string }
  | {
      readonly kind: "reject";
      readonly code: AnnotationCode;
      readonly row: AnnotatedRow | undefined;
      readonly detail: string;
    };

/**
 * Check an annotated closed-model certificate (ADR 0031 D5; #1821 Q14, Q15), relative to the
 * identity of `semiring`. The parameters are checkClosedModelChain's, plus the semiring. The steps,
 * in order, the first failing one being the verdict:
 *
 *  1. identity: semiringIdentity(semiring) equals `annotated.semiring`, else annotation_identity_mismatch;
 *  2. the boolean check, checkClosedModelChain over the one-cert world; a rejection is `reject_cert`;
 *  3. a partial scope, or a negated or count body literal in a scope clause, is annotation_unsupported;
 *  4. shape: one annotated table per sealed table, same predicate, one element per row, each an
 *     element of the semiring (annotation_shape, naming the row for a non-element);
 *  5. the closure join's body-true groundings of every scope clause with an IDB head (an undecided
 *     body is annotation_unsupported), each keyed canonically;
 *  6. the least solution by Jacobi rounds from zero: each add or mul is one step against
 *     `maxJoinSteps` (annotation_budget_exceeded); an operation answering not-an-element or stopped
 *     names the IDB row being computed; no fixed point within (IDB rows + 1) rounds is
 *     annotation_not_converged;
 *  7. the first IDB row whose claim differs is annotation_mismatch;
 *  8. accept.
 *
 * The accept does not attest the elements of the extensional tables: it lists them as `unattested`,
 * premises bound by the certificate's digest (#1821 Q15 condition 1).
 */
export function checkAnnotatedClosedModel<C>(
  program: Program,
  annotated: AnnotatedClosedModelCert,
  ctx: C,
  profile: CheckProfile<C>,
  certContext: CertContext,
  semiring: Semiring,
): AnnotatedOutcome {
  // 1. IDENTITY, before the semiring is consulted for anything else.
  if (!semiringIdentity(semiring).equals(annotated.semiring)) {
    return reject("annotation_identity_mismatch", undefined, "the checker's semiring is named by another identity");
  }
  // 2. THE BOOLEAN CHECK, over a one-cert world, its verdict unchanged. The profile and the
  //    certificate are captured once, and the steps below read the captured copies.
  const bound = captureCheckProfile(profile);
  if (!bound.ok) return rejectCert("invalid_check_limits", bound.error.message);
  profile = bound.value;
  const world = captureWorld([annotated.cert], profile.limits);
  if (world.kind === "reject") return rejectCert(world.code, world.detail);
  const verdict = checkClosedModelChain(program, world.value, ctx, profile, certContext).verdict;
  if (verdict.kind === "reject") return rejectCert(verdict.code, verdict.detail);
  const cert = world.value[0]!;
  // 3. UNSUPPORTED: a lower bound has no least annotation, and a negation or a count is outside
  //    the positive system this check solves. (A one-cert world cannot negate its own seal, so the
  //    second is defensive.)
  if (cert.partialScope !== undefined) {
    return reject("annotation_unsupported", undefined, "the certificate seals a partial scope (ADR 0030), a lower bound");
  }
  const clauses = clauseInventory(program);
  if (clauses === undefined) return reject("annotation_unsupported", undefined, "the program does not enumerate its clauses");
  for (const [, clause] of clauses) {
    if (!cert.scope.seals(clause.head.pred)) continue;
    const other = clause.body.find((bl) => !bl.isPos());
    if (other !== undefined) {
      return reject("annotation_unsupported", undefined, `a scope clause for ${name(clause.head.pred)} has a ${other.polarity} body literal`);
    }
  }
  // 4. SHAPE, then each claimed element, in table order and row order.
  const tables = cert.extensions;
  const annotations = Array.from(annotated.annotations, (t) => ({ pred: t.pred, elements: Array.from(t.elements) }));
  if (annotations.length !== tables.length) {
    return reject("annotation_shape", undefined, `${annotations.length} annotated tables for ${tables.length} sealed tables`);
  }
  for (let i = 0; i < tables.length; i += 1) {
    const table = tables[i]!;
    const ann = annotations[i]!;
    if (!ann.pred.equals(table.pred)) {
      return reject("annotation_shape", undefined, `annotated table ${i} is ${name(ann.pred)}, sealed table ${i} is ${name(table.pred)}`);
    }
    if (ann.elements.length !== table.rows.length) {
      return reject("annotation_shape", undefined, `${name(table.pred)} has ${table.rows.length} rows and ${ann.elements.length} elements`);
    }
  }
  for (let i = 0; i < tables.length; i += 1) {
    const elements = annotations[i]!.elements;
    for (let j = 0; j < elements.length; j += 1) {
      if (!semiring.isElement(elements[j]!)) {
        return reject("annotation_shape", { pred: tables[i]!.pred, index: j }, "the claimed value is not an element of the semiring");
      }
    }
  }
  // 5. GROUNDINGS, from the closure join itself, recorded at the point it emits each one.
  const extensional = profile.leaves.extensional();
  const rows = indexRows(tables, annotations.map((t) => t.elements), extensional);
  const theory = profile.theory;
  const view = new CertView(cert);
  const counters: JoinCounters = { groundings: 0, joins: 0 };
  const groundings: Grounding[] = [];
  for (const [id, clause] of clauses) {
    if (!cert.scope.seals(clause.head.pred) || extensional.contains(clause.head.pred)) continue;
    const emitted: { readonly subst: Subst; readonly decided: boolean }[] = [];
    counters.record = (subst, decided) => {
      emitted.push({ subst: new Subst(subst), decided });
    };
    const err = joinGroundings(clause, view, theory, profile.limits, counters);
    if (err !== undefined) return rejectCert(err[0], err[1]);
    for (const e of emitted) {
      if (!e.decided) {
        return reject("annotation_unsupported", undefined, `a grounding of clause ${JSON.stringify(id.asStr())} has a body that is not decided`);
      }
      const g = groundingOf(id, clause, e.subst, rows, theory);
      if (typeof g === "string") return reject("annotation_unsupported", undefined, g);
      groundings.push(g);
    }
  }
  const idb: number[] = [];
  for (let t = 0; t < rows.idb.length; t += 1) if (rows.idb[t]) idb.push(t);
  const perRow: Grounding[][] = rows.idb.map(() => []);
  for (const g of groundings) perRow[g.head]!.push(g);
  for (const list of perRow) list.sort((a, b) => compareBytes(a.key, b.key));
  // 6. THE LEAST SOLUTION, by Jacobi rounds from zero.
  const solved = leastSolution(semiring, rows, idb, perRow, profile.limits.maxJoinSteps);
  if ("refused" in solved) return solved.refused;
  // 7. MISMATCH: the first IDB row whose claim is not the least solution.
  for (const t of idb) {
    if (!sameValue(solved.values[t]!, rows.claimed[t]!)) {
      return reject("annotation_mismatch", rows.rowOf(t), "the claimed element is not the least solution");
    }
  }
  // 8. ACCEPT, naming the law relied on and the unattested premises.
  const edges: number[][] = rows.idb.map(() => []);
  for (const g of groundings) {
    for (const f of g.factors) if (rows.idb[f]) edges[g.head]!.push(f);
  }
  const unattested = tables.filter((t) => extensional.contains(t.pred)).map((t) => t.pred);
  return accept(hasCycle(edges) ? "kleene_least_fixpoint" : undefined, unattested);
}

// ------------------------------------ the outcomes ------------------------------------

function accept(law: AnnotationLaw | undefined, unattested: readonly Symbol[]): AnnotatedOutcome {
  if (law !== undefined) {
    // A closed vocabulary: every law an accept relies on is one this check knows (research 0025).
    switch (law) {
      case "kleene_least_fixpoint":
        break;
      default: {
        const unknown: never = law;
        throw new Error(`checkAnnotatedClosedModel: a law with no meaning here: ${JSON.stringify(unknown)}`);
      }
    }
  }
  const out: AnnotatedOutcome = { kind: "accept", law, unattested: Object.freeze(Array.from(unattested)) };
  return Object.freeze(out);
}

function rejectCert(code: RejectionCode, detail: string): AnnotatedOutcome {
  const out: AnnotatedOutcome = { kind: "reject_cert", code, detail };
  return Object.freeze(out);
}

function reject(code: AnnotationCode, row: AnnotatedRow | undefined, detail: string): AnnotatedOutcome {
  const at: AnnotatedRow | undefined = row === undefined ? undefined : Object.freeze({ pred: row.pred, index: row.index });
  const out: AnnotatedOutcome = { kind: "reject", code, row: at, detail: `${summary(code)}: ${detail}` };
  return Object.freeze(out);
}

/** What each code means, the one total reading of the vocabulary (research 0025: a `never` arm). */
function summary(code: AnnotationCode): string {
  switch (code) {
    case "annotation_identity_mismatch":
      return "the certificate's semiring identity is not the checker's";
    case "annotation_unsupported":
      return "the certificate is outside the annotated fragment";
    case "annotation_shape":
      return "the annotations do not fit the sealed tables";
    case "annotation_not_converged":
      return "the iteration reached no fixed point within its bound";
    case "annotation_mismatch":
      return "a claimed element differs from the least solution";
    case "semiring_not_an_element":
      return "a semiring operation answered not an element";
    case "semiring_stopped":
      return "a semiring operation stopped";
    case "annotation_budget_exceeded":
      return "the semiring operations exceed the join-step budget";
    default: {
      const unknown: never = code;
      throw new Error(`checkAnnotatedClosedModel: a code with no meaning: ${JSON.stringify(unknown)}`);
    }
  }
}

// ------------------------------------- the rows ---------------------------------------

/** Every sealed row, flat in table order then row order, with its claim and its IDB-ness. */
interface Rows {
  readonly pred: readonly Symbol[];
  readonly index: readonly number[];
  readonly claimed: readonly Value[];
  readonly idb: readonly boolean[];
  /** A ground literal's flat row, keyed by its canonical key; the first table for a predicate wins. */
  readonly at: ReadonlyMap<string, number>;
  rowOf(t: number): AnnotatedRow;
}

function indexRows(tables: readonly RelationTable[], elements: readonly (readonly Value[])[], extensional: PredicateSet): Rows {
  const pred: Symbol[] = [];
  const index: number[] = [];
  const claimed: Value[] = [];
  const idb: boolean[] = [];
  const at = new Map<string, number>();
  tables.forEach((table, i) => {
    const isIdb = !extensional.contains(table.pred);
    table.rows.forEach((row, j) => {
      const key = rowKey(row);
      if (!at.has(key)) at.set(key, pred.length);
      pred.push(table.pred);
      index.push(j);
      claimed.push(elements[i]![j]!);
      idb.push(isIdb);
    });
  });
  return { pred, index, claimed, idb, at, rowOf: (t) => ({ pred: pred[t]!, index: index[t]! }) };
}

function rowKey(lit: GroundLiteral): string {
  return toHex(groundKey(lit));
}

// ---------------------------------- the groundings -----------------------------------

/** One body-true grounding of a scope clause with an IDB head. */
interface Grounding {
  /** The canonical key: codec bytes of Tuple[Atom(clause id), Tuple[Tuple[Atom(var), quote(image)], ...]]. */
  readonly key: Uint8Array;
  /** The head's flat row. */
  readonly head: number;
  /** The flat rows of the positive non-theory body literals, in body order. */
  readonly factors: readonly number[];
}

/** The grounding's head and factors located among the rows, or why they cannot be. */
function groundingOf(id: ClauseId, clause: Clause, subst: Subst, rows: Rows, theory: Theory): Grounding | string {
  const head = clause.head.substitute(subst).asGround();
  const at = head === undefined ? undefined : rows.at.get(rowKey(head));
  if (at === undefined || !rows.idb[at]) return `a grounding of ${name(clause.head.pred)} has no IDB row for its head`;
  const factors: number[] = [];
  for (const bl of clause.body) {
    if (!bl.isPos() || theory.owns(bl.lit.pred)) continue;
    const lit = bl.lit.substitute(subst).asGround();
    const f = lit === undefined ? undefined : rows.at.get(rowKey(lit));
    if (f === undefined) return `a grounding of ${name(clause.head.pred)} reads ${name(bl.lit.pred)} outside the sealed rows`;
    factors.push(f);
  }
  let clauseBytes: Uint8Array;
  try {
    clauseBytes = portableClauseIdBytes(id.asStr());
  } catch (error) {
    if (!(error instanceof ClauseIdEncodingError)) throw error;
    return "a scope clause id has no UTF-8 spelling, so its groundings have no canonical order";
  }
  const vars = Array.from(subst.entries(), ([v, term]) => ({ name: encodeUtf8(v.asStr()), term }));
  vars.sort((a, b) => compareBytes(a.name, b.name));
  const key = encode(
    valueTuple([valueAtom(clauseBytes), valueTuple(vars.map((v) => valueTuple([valueAtom(v.name), quote(v.term)])))]),
  );
  return { key, head: at, factors };
}

/** The program's clauses with their ids, each captured, from its complete enumeration. */
function clauseInventory(program: Program): (readonly [ClauseId, Clause])[] | undefined {
  const enumerate = program.forEachClause;
  if (typeof enumerate !== "function") return undefined;
  const out: (readonly [ClauseId, Clause])[] = [];
  const visit = (id: ClauseId, clause: Clause): void => {
    out.push([nativeClauseId(id), captureClause(clause)]);
  };
  Reflect.apply(enumerate, program, [visit]);
  return out;
}

// --------------------------------- the least solution ---------------------------------

type Solved = { readonly values: readonly Value[] } | { readonly refused: AnnotatedOutcome };

/**
 * Jacobi rounds from zero over the IDB rows `idb` (table order, row order), at most idb.length + 1
 * of them. An extensional factor reads its claimed element, an IDB factor the previous round's
 * value. Every add and mul is one step against `maxSteps`, summed over all rounds.
 */
function leastSolution(
  semiring: Semiring,
  rows: Rows,
  idb: readonly number[],
  perRow: readonly (readonly Grounding[])[],
  maxSteps: number,
): Solved {
  const zero = semiring.zero();
  const one = semiring.one();
  let steps = 0;
  const op = (which: "add" | "mul", a: Value, b: Value, t: number): { readonly value: Value } | { readonly refused: AnnotatedOutcome } => {
    steps += 1;
    if (steps > maxSteps) {
      return { refused: reject("annotation_budget_exceeded", undefined, `counted operations ${steps} exceed budget ${maxSteps}`) };
    }
    const answer = which === "add" ? semiring.add(a, b) : semiring.mul(a, b);
    switch (answer.kind) {
      case "element":
        return { value: answer.value };
      case "not_an_element":
        return { refused: reject("semiring_not_an_element", rows.rowOf(t), `${which} while computing this row`) };
      case "stopped":
        return { refused: reject("semiring_stopped", rows.rowOf(t), `${which} while computing this row (${answer.cause.kind})`) };
      default: {
        const unknown: never = answer;
        throw new Error(`checkAnnotatedClosedModel: a semiring answer of no known kind: ${JSON.stringify(unknown)}`);
      }
    }
  };
  let prev: Value[] = rows.claimed.map(() => zero);
  const bound = idb.length + 1;
  for (let round = 1; round <= bound; round += 1) {
    const next = prev.slice();
    for (const t of idb) {
      let acc = zero;
      for (const g of perRow[t]!) {
        let p = one;
        for (const f of g.factors) {
          const product = op("mul", p, rows.idb[f] ? prev[f]! : rows.claimed[f]!, t);
          if ("refused" in product) return product;
          p = product.value;
        }
        const sum = op("add", acc, p, t);
        if ("refused" in sum) return sum;
        acc = sum.value;
      }
      next[t] = acc;
    }
    const fixed = idb.every((t) => sameValue(next[t]!, prev[t]!));
    prev = next;
    if (fixed) return { values: prev };
  }
  return { refused: reject("annotation_not_converged", undefined, `no fixed point within ${bound} rounds`) };
}

/** Whether the dependency graph (an edge from each head row to each IDB factor row) has a cycle. */
function hasCycle(edges: readonly (readonly number[])[]): boolean {
  // 0 unvisited, 1 on the current path, 2 finished. Iterative, so depth is not the call stack's.
  const state = edges.map(() => 0);
  for (let start = 0; start < edges.length; start += 1) {
    if (state[start] !== 0) continue;
    state[start] = 1;
    const path: { node: number; next: number }[] = [{ node: start, next: 0 }];
    while (path.length > 0) {
      const top = path[path.length - 1]!;
      const out = edges[top.node]!;
      if (top.next < out.length) {
        const w = out[top.next]!;
        top.next += 1;
        if (state[w] === 1) return true;
        if (state[w] === 0) {
          state[w] = 1;
          path.push({ node: w, next: 0 });
        }
      } else {
        state[top.node] = 2;
        path.pop();
      }
    }
  }
  return false;
}

// ------------------------------------ small helpers ------------------------------------

/** Value equality, by the canonical codec bytes. */
function sameValue(a: Value, b: Value): boolean {
  return bytesEqual(encode(a), encode(b));
}

/** Lexicographic byte order (rs slice `Ord`, go `bytes.Compare`). */
function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) if (a[i] !== b[i]) return a[i]! - b[i]!;
  return a.length - b.length;
}

/** A name for a detail string, through the one injective rendering. */
function name(pred: Symbol): string {
  return JSON.stringify(escapedName(pred.bytes()));
}
