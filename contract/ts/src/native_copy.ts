import { Atom, Tuple, type Value } from "@bitspark/ontos-core";
import { Goal, GroundLiteral, Symbol as PredicateSymbol } from "./literal.js";
import { BodyLit, Clause, ClauseId, CountLit, PredicateRef } from "./program.js";
import { TermAtom, TermTuple, TermVar, VarId, type Subst, type Term } from "./term.js";

/** Model sequences are arrays. Read their captured length by index, so a
 * producer cannot substitute a different sequence through its iterator. */
export function copyArray<T, U>(items: readonly T[], read: (item: T) => U, count = items.length): U[] {
  if (!Array.isArray(items)) throw new TypeError("an account sequence must be an array");
  const result = new Array<U>(count);
  for (let i = 0; i < count; i++) result[i] = read(items[i]!);
  return result;
}

/** Capture native record fields without dispatching on producer-provided methods. */
export function nativeSymbol(source: PredicateSymbol): PredicateSymbol {
  if (source instanceof PredicateSymbol && Object.getPrototypeOf(source) === PredicateSymbol.prototype) return source;
  return PredicateSymbol.of(PredicateSymbol.prototype.bytes.call(source));
}

const atomLength = Object.getOwnPropertyDescriptor(Atom.prototype, "length")!.get!;
const tupleItems = Tuple.prototype.items;

/** Only Ontos' immutable values can be shared with the producer. A tuple may
 * contain a prototype imitation even when the outer tuple is genuine. */
export function nativeValue(value: Value, max: number): Value {
  const work = [{ value, depth: 1 }];
  while (work.length > 0) {
    const item = work.pop()!;
    // The checker's iterative depth pass refuses at this same depth before
    // inspecting the child, preserving its normal rejection and detail.
    if (item.depth > max) continue;
    const prototype = Object.getPrototypeOf(item.value);
    if (prototype === Atom.prototype) {
      atomLength.call(item.value);
    } else if (prototype === Tuple.prototype) {
      for (const child of tupleItems.call(item.value as Tuple)) work.push({ value: child, depth: item.depth + 1 });
    } else {
      throw new TypeError("a ground value must be a native Ontos atom or tuple");
    }
  }
  return value;
}

export function nativeLiteral(source: GroundLiteral, max: number): GroundLiteral {
  return new GroundLiteral(nativeSymbol(source.pred), copyArray(source.args, arg => nativeValue(arg, max)));
}

/** Capture one persistent native fact independently of a checker's resource policy. */
export function captureGroundLiteral(source: GroundLiteral): GroundLiteral {
  return nativeLiteral(source, Infinity);
}

/** Recognize the immutable native term algebra. A checking budget can stop
 * before children that will be refused for their depth. */
export function hasNativeTermShape(term: Term, max: number): boolean {
  const work = [{ term, depth: 1 }];
  while (work.length > 0) {
    const { term: current, depth } = work.pop()!;
    if (depth > max) continue;
    if (current instanceof TermAtom && Object.getPrototypeOf(current) === TermAtom.prototype) continue;
    if (current instanceof TermVar && Object.getPrototypeOf(current) === TermVar.prototype) {
      const id = current.id();
      if (id instanceof VarId && Object.getPrototypeOf(id) === VarId.prototype) continue;
    }
    if (current instanceof TermTuple && Object.getPrototypeOf(current) === TermTuple.prototype) {
      for (const child of current.children()) work.push({ term: child, depth: depth + 1 });
      continue;
    }
    return false;
  }
  return true;
}

function nativeTerm(term: Term): Term {
  if (!hasNativeTermShape(term, Infinity)) throw new TypeError("a native clause requires immutable account terms");
  return term;
}

function nativeGoal(goal: Goal): Goal {
  return new Goal(nativeSymbol(goal.pred), copyArray(goal.args, nativeTerm));
}

/** Capture a native clause without encoding or changing its opaque program handle. */
export function captureClause(clause: Clause): Clause {
  const head = nativeGoal(clause.head);
  const body = copyArray(clause.body, lit => {
    const polarity = lit.polarity;
    if (polarity === "pos") return BodyLit.pos(nativeGoal(lit.lit));
    if (polarity === "neg") return BodyLit.neg(nativeGoal(lit.lit));
    const count = lit.countLit;
    if (polarity !== "count" || count === undefined) throw new TypeError("unrecognized native body literal");
    return BodyLit.count(new CountLit(nativePredicateRef(count.pred),
      copyArray(count.filter, entry => ({ pos: entry.pos, term: nativeTerm(entry.term) })),
      count.project, nativeTerm(count.count)));
  });
  return new Clause(head, body);
}

export function nativeClauseId(source: ClauseId): ClauseId {
  return ClauseId.of(ClauseId.prototype.asStr.call(source));
}

export function nativePredicateRef(source: PredicateRef): PredicateRef {
  return new PredicateRef(nativeSymbol(source.pred), source.arity);
}

export function nativeSubst(source: Subst): Subst {
  return new Map(Map.prototype.entries.call(source) as IterableIterator<[string, Term]>);
}
