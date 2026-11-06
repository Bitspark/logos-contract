// §2a Reification — quote / reify. [STABLE v1 shape · byte form FROZEN v1]
// TS sibling of contract/rs/src/reify.rs.
//
// The tag bytes below are FROZEN v1 (§9 settled: VarId syntactic, no
// alpha-normalization) and byte-identical to the Rust and Go bindings — quote is
// the canonical encoding the account codec (account.ts) hashes. Changing a tag is a
// breaking change shipped as a new version, never an edit.

import { UTF8_STRICT } from "./utf8.js";
import { Atom, Tuple, atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { type Term, TermAtom, TermTuple, TermVar, VarId } from "./term.js";

const TAG_ATOM = 0x00;
const TAG_TUPLE = 0x01;
const TAG_VAR = 0x02;

/**
 * Total: maps `Atom`/`Tuple`/`Var` → a ground ontos value (§2a).
 *
 * Iterative, with an explicit work stack (#3036): how deep a term it quotes is never a property of
 * the JS call stack, which moves with the V8 tier and the runner (#3014). Each open tuple is a frame
 * collecting its children's quoted values; a frame closes into `[0x01, [children…]]` and hands that to
 * its parent. The output is byte-identical to the recursive form.
 */
export function quote(term: Term): Value {
  const leaf = quoteLeaf(term);
  if (!(leaf instanceof TermTuple)) return leaf;
  const stack: { kids: readonly Term[]; next: number; out: Value[] }[] = [
    { kids: leaf.children(), next: 0, out: [] },
  ];
  for (;;) {
    const top = stack[stack.length - 1]!;
    if (top.next < top.kids.length) {
      const child = top.kids[top.next]!;
      top.next += 1;
      const v = quoteLeaf(child);
      if (v instanceof TermTuple) stack.push({ kids: v.children(), next: 0, out: [] });
      else top.out.push(v);
      continue;
    }
    const done = valueTuple([valueAtom([TAG_TUPLE]), valueTuple(top.out)]);
    stack.pop();
    if (stack.length === 0) return done;
    stack[stack.length - 1]!.out.push(done);
  }
}

/**
 * An atom's or variable's quoted value, or the tuple itself, which the caller opens. A distinct
 * marker, never `undefined`, and a `never` default (research 0025 A4, seat:caa on #3053): a Term
 * kind added later is a compile error here, never a value that falls through and reads as a tuple.
 */
function quoteLeaf(term: Term): Value | TermTuple {
  switch (term.kind) {
    case "atom":
      return valueTuple([valueAtom([TAG_ATOM]), valueAtom(term.bytes())]);
    case "var":
      return valueTuple([
        valueAtom([TAG_VAR]),
        valueAtom(new TextEncoder().encode(term.id().asStr())),
      ]);
    case "tuple":
      return term;
    default: {
      const unhandled: never = term;
      throw new Error(`reify: quote: unknown Term kind ${String(unhandled)}`);
    }
  }
}

/**
 * Partial inverse of `quote`: a `Term` iff `value` is in the image of `quote`,
 * else `undefined` (§2a).
 *
 * Iterative, like `quote` (#3036): an explicit stack of open tuples, each collecting its reified
 * children, so a deep value is never a JS-stack property.
 */
export function reify(value: Value): Term | undefined {
  const first = reifyStep(value);
  if (first === undefined) return undefined;
  if (!isKids(first)) return first;
  const stack: { kids: readonly Value[]; next: number; out: Term[] }[] = [{ kids: first, next: 0, out: [] }];
  for (;;) {
    const top = stack[stack.length - 1]!;
    if (top.next < top.kids.length) {
      const step = reifyStep(top.kids[top.next]!);
      top.next += 1;
      if (step === undefined) return undefined;
      if (isKids(step)) stack.push({ kids: step, next: 0, out: [] });
      else top.out.push(step);
      continue;
    }
    const done = new TermTuple(top.out);
    stack.pop();
    if (stack.length === 0) return done;
    stack[stack.length - 1]!.out.push(done);
  }
}

/** A tuple's quoted children, as `reifyStep` returns them (a Term is never an array). */
function isKids(x: Term | readonly Value[]): x is readonly Value[] {
  return Array.isArray(x);
}

/**
 * One level of `reify`: the term for an atom or a variable, the tuple's quoted children for a tuple
 * (which the caller opens), or `undefined` when `value` is not in `quote`'s image.
 */
function reifyStep(value: Value): Term | readonly Value[] | undefined {
  if (!(value instanceof Tuple)) return undefined;
  const items = value.items();
  if (items.length !== 2) return undefined;
  const tagItem = items[0];
  const payload = items[1];
  if (tagItem === undefined || payload === undefined) return undefined;
  if (!(tagItem instanceof Atom)) return undefined;
  const tag = tagItem.bytes();
  if (tag.length !== 1) return undefined;
  // The tag byte's domain is open (any byte), so `default` is a real case here; only the
  // index's `undefined` is narrowed away first (#2893).
  const byte = tag[0];
  if (byte === undefined) return undefined;
  switch (byte) {
    case TAG_ATOM: {
      if (!(payload instanceof Atom)) return undefined;
      return new TermAtom(payload.bytes());
    }
    case TAG_VAR: {
      if (!(payload instanceof Atom)) return undefined;
      const name = decodeUtf8(payload.bytes());
      if (name === undefined) return undefined;
      return new TermVar(new VarId(name));
    }
    case TAG_TUPLE: {
      if (!(payload instanceof Tuple)) return undefined;
      return payload.items();
    }
    default:
      return undefined;
  }
}

function decodeUtf8(bytes: Uint8Array): string | undefined {
  try {
    return UTF8_STRICT.decode(bytes);
  } catch {
    return undefined;
  }
}
