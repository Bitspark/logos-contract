/**
 * G4, the completeness gate's set comparison, as one contract operation (design 0008 section 1.4.4;
 * research 0028 row A16, seat:caa's ruling on #3023). Each kernel's gate calls it after G2 and G3,
 * and `vectors/exact_answer_set.json` replays it in all three cores. rs `answer_set.rs`.
 *
 * The emitted answers must be exactly the sealed rows that are instances of the goal. A row is an
 * instance when one binding of the goal's variables makes the goal structurally equal to it, where a
 * repeated variable binds one value. Two answers are one answer exactly when they are structurally
 * equal (`groundKey`).
 *
 * The precedence is normative: the first emitted answer that is not a sealed instance, in claim
 * order; otherwise the first sealed instance that was not emitted, in `groundKey` order.
 */

import { equals as valueEquals, Tuple as ValueTuple, type Value } from "@bitspark/ontos-core";

import { groundKey } from "./cert.js";
import { type Goal, type GroundLiteral } from "./literal.js";
import { Term } from "./term.js";

/**
 * How an answer set fails G4, with the literal that shows it. These are exactly the two ways a set
 * comparison fails (seat:caa's ruling on #3023): a third kind would be a contract v2 item.
 * - `extra`: an emitted answer that is not a sealed row matching the goal, the first in claim order.
 * - `missing`: a sealed row matching the goal that was not emitted, the first in `groundKey` order.
 */
export type AnswerSetMismatch =
  | { readonly kind: "extra"; readonly literal: GroundLiteral }
  | { readonly kind: "missing"; readonly literal: GroundLiteral };

/**
 * G4: `undefined` when `claims` is exactly the set of `sealed` rows that are instances of `goal`, and
 * otherwise the first difference by the normative precedence.
 */
export function checkAnswerSet(
  goal: Goal,
  sealed: readonly GroundLiteral[],
  claims: readonly GroundLiteral[],
): AnswerSetMismatch | undefined {
  const instances = new Map<string, GroundLiteral>();
  for (const row of sealed) {
    if (isInstance(goal, row)) instances.set(answerKey(row), row);
  }
  const emitted = new Set<string>();
  for (const claim of claims) {
    const key = answerKey(claim);
    if (!instances.has(key)) return { kind: "extra", literal: claim };
    emitted.add(key);
  }
  // Byte order: the keys are fixed-width hex, so their string order is the bytes' order.
  for (const key of [...instances.keys()].sort()) {
    if (!emitted.has(key)) return { kind: "missing", literal: instances.get(key) as GroundLiteral };
  }
  return undefined;
}

/** An answer's key: hex of its canonical codec bytes (`groundKey`), so it orders as the bytes do. */
function answerKey(lit: GroundLiteral): string {
  return Array.from(groundKey(lit), (b) => b.toString(16).padStart(2, "0")).join("");
}

/**
 * Whether `row` is an instance of `goal`: the same predicate and arity, and one binding of the goal's
 * variables under which every argument matches. The walk is an explicit stack of pairs, never one
 * native frame per nesting level (#3036).
 */
function isInstance(goal: Goal, row: GroundLiteral): boolean {
  if (!goal.pred.equals(row.pred) || goal.args.length !== row.args.length) return false;
  const work: Array<[Term, Value]> = [];
  for (let i = goal.args.length - 1; i >= 0; i--) {
    work.push([goal.args[i] as Term, row.args[i] as Value]);
  }
  const bound = new Map<string, Value>();
  for (let pair = work.pop(); pair !== undefined; pair = work.pop()) {
    const [term, value] = pair;
    switch (term.kind) {
      case "var": {
        const name = term.id().asStr();
        const prior = bound.get(name);
        if (prior === undefined) bound.set(name, value);
        else if (!valueEquals(prior, value)) return false;
        break;
      }
      case "atom": {
        const ground = Term.eraseGround(term);
        if (ground === undefined || !valueEquals(ground, value)) return false;
        break;
      }
      case "tuple": {
        if (!(value instanceof ValueTuple)) return false;
        const children = term.children();
        const items = value.items();
        if (children.length !== items.length) return false;
        for (let i = children.length - 1; i >= 0; i--) {
          work.push([children[i] as Term, items[i] as Value]);
        }
        break;
      }
      default: {
        // The goal is the caller's query, never untrusted input (#3074): an unknown kind is a defect.
        const unhandled: never = term;
        throw new Error(`contract: checkAnswerSet: unknown term kind ${String(unhandled)}`);
      }
    }
  }
  return true;
}
