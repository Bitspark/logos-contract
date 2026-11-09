// §1 Term — an ontos value, with holes. [FIRM]
// TS sibling of contract/rs/src/term.rs.
//
//   Term = Atom(Bytes) | Tuple(Term*) | Var(VarId)
//
// A ground term (no Var) corresponds exactly to an ontos Value, witnessed by
// eraseGround / fromValue. Identity is structural and extends ontos identity with
// Var(a) == Var(b) iff a == b.

import {
  Atom,
  Tuple as ValueTupleClass,
  atom as valueAtom,
  tuple as valueTuple,
  bytesEqual,
  type Value,
} from "@bitspark/ontos-core";
import { copyOctets, type OctetSource } from "./octets.js";
import { wellFormedUtf16 } from "./utf8.js";

/**
 * Default cap on single-term nesting depth in the trusted check/decode path (issue
 * #253). A pathologically deep term — `f(f(f(…)))` nested tens of thousands deep, or a
 * deep cons-chain — would otherwise overflow the JS call stack during the recursive
 * term traversals (`substitute` / `eraseGround` / structural `equals` / the account
 * `quote`), aborting the trusted checker (a DoS / RangeError).
 *
 * Distinct from `CheckLimits.maxDepth`, which bounds DAG/premise-chain depth: a single
 * node's term can be arbitrarily deep within one node, so the node/depth caps do not
 * bound it. Tri-core-consistent with contract/{rs,go} (256).
 */
export const MAX_TERM_DEPTH_DEFAULT = 256;

/**
 * The deepest term the ts core represents (#2366, `seat:caa`'s ruling). It had an rs twin,
 * `VALUE_STACK_DEPTH_LIMIT`, until ontos v0.10.0 made rs's `Value` iterative (#3596). Depth is
 * `Term.depthLe`'s: an atom or variable counts 1, a tuple 1 + its deepest child.
 *
 * A **safety bound named for the JS stack, not a caller's budget.** The ts term walks are
 * iterative (#2393), but `quote` and `@bitspark/ontos-codec`'s `encode` (in ontos, the floor)
 * recursed once per level when it was measured. The codec's `encode` is iterative from ontos
 * v0.10.0, so the bound is re-measured against that pin (#3608). The resolver runs both when it digests a program, before any
 * provider is probed, and a guest-backed host runs both when it encodes a request. Past this
 * depth the resolver refuses the program as `Unsupported` on the representation axis
 * (`VALUE_TOO_DEEP`), and the wasm host declines a request by the same name before encoding it.
 *
 * Set at 0.8 × (the lowest throw depth measured over the Nodes that matter, minus the largest
 * same-row spread measured between runs) (`seat:caa`'s ruling on #2472), in the UNOPTIMIZED tier
 * (#3014): 0.8 × (2,378 − 9) = 1,895. The throw depth depends on V8's execution tier: interpreter
 * and baseline frames are the largest V8 builds, so a process that meets a deep term while its code
 * is still cold runs out of stack ~570 levels sooner than one whose code is optimized, and the bound
 * must hold there. `kernel/ts/test/value_depth_calibration_2366.test.ts` re-measures on every run,
 * in process and in a child with `--no-opt --no-maglev`, including from inside Resolver.resolve's
 * own call chain, and reds if this exceeds 0.8 × the lowest it finds over both tiers.
 *
 *   lowest     2,378   Node v24.1.0 (V8 13.6.233.10-node.16), Windows, unoptimized, the in-resolver
 *                      count-filter row (#3014, five runs on 2026-09-26: lowest 2,378 to 2,387)
 *   spread         9   those five runs, max − min of every unoptimized row (8 or 9 for each)
 *   linux      2,397   Node v24.21.0 (V8 13.6.233.17-node.53), Linux CI, unoptimized, the same row
 *                      (#3021's red-first run, job 108436172225). 0.8 × (2,397 − 9) = 1,910 ≥ 1,895,
 *                      so the row CONFIRMS this constant.
 *   optimized  2,953+  both platforms in process (2,953 to 2,968 Windows, 2,975 Linux): never binding
 *
 * History: #2472 set 2,240 from in-process rows alone, where a "spread" of 150 was the tier mix read
 * as noise. One CI run whose first bisection ran cold measured 2,546 and went red (#3014).
 *
 * Re-derivation rule: a run whose lowest falls below lowest − spread (2,369) means re-measure and
 * re-derive this constant from the new figures. Never loosen the calibration's assert.
 *
 * Since ontos 0.13.0 the codec's `encode` no longer recurses (Bitspark/ontos#343). On that bump no
 * row of the calibration threw by 100,000 levels in either tier, so nothing it measures binds this
 * constant any more. The value is kept as the declared bound; raising it is a separate decision.
 * `analyze` refuses past this bound as its first act (`value_too_deep`, the ts twin of #2447's rs
 * entry check), so a direct caller of that public function is covered as well as the resolver.
 */
export const TS_VALUE_STACK_DEPTH_LIMIT = 1_895;

/**
 * The one name for "a term nests deeper than this build can represent" (#2425): contract/rs's
 * `VALUE_TOO_DEEP`. A representation refusal's reason begins with it, whichever bound applied.
 */
export const VALUE_TOO_DEEP = "value_too_deep";

/**
 * The named refusal of a name that is not a variable's (#3115): §2a makes a `VarId`'s name UTF-8
 * text, and a JS string with a lone surrogate is not (`TextEncoder` would write U+FFFD, so
 * `VarId("\ud800")` and `VarId("�")` would quote to one byte string: two variables, one
 * account).
 */
export class VarIdError extends Error {
  /** The refused name, as given. */
  readonly varName: string;

  constructor(varName: string) {
    super(`VarId name ${JSON.stringify(varName)} is not UTF-8 text: it holds a lone UTF-16 surrogate (§2a)`);
    this.name = "VarIdError";
    this.varName = varName;
  }
}

/**
 * An opaque variable identity (§1): a name. Its only contract is equality and
 * freshness. logos imposes no numeric/quotient equality.
 *
 * The name is UTF-8 text (§2a, #3115), the domain rs's `String` holds by type: the constructor
 * refuses a lone surrogate with a `VarIdError`, through `wellFormedUtf16`, the one ts test of that
 * domain. `VarId.of` and `Term.var` construct through here, and so does `reify`.
 */
export class VarId {
  readonly #name: string;

  static [Symbol.hasInstance](value: unknown): boolean {
    return typeof value === "object" && value !== null && #name in value;
  }

  constructor(name: string) {
    if (!wellFormedUtf16(name)) throw new VarIdError(name);
    this.#name = name;
    Object.freeze(this);
  }

  static of(name: string): VarId {
    return new VarId(name);
  }

  asStr(): string {
    return this.#name;
  }

  equals(other: VarId): boolean {
    return this.#name === other.#name;
  }
}

/** A term: an ontos value with holes (§1). Discriminated by `kind`. */
export type Term = TermAtom | TermTuple | TermVar;

/** The same bytes as an ontos `Atom`. */
export class TermAtom {
  readonly kind = "atom" as const;
  readonly #bytes: Uint8Array;

  static [Symbol.hasInstance](value: unknown): boolean {
    return typeof value === "object" && value !== null && #bytes in value;
  }

  constructor(bytes: OctetSource) {
    this.#bytes = copyOctets(bytes);
    Object.freeze(this);
  }

  bytes(): Uint8Array {
    return this.#bytes.slice();
  }

  equals(other: Term): boolean {
    return other.kind === "atom" && bytesEqual(this.#bytes, other.#bytes);
  }
}

/** The same ordered shape as an ontos `Tuple`, but children may contain `Var`. */
export class TermTuple {
  readonly kind = "tuple" as const;
  readonly #children: readonly Term[];

  static [Symbol.hasInstance](value: unknown): boolean {
    return typeof value === "object" && value !== null && #children in value;
  }

  constructor(children: readonly Term[]) {
    this.#children = Object.freeze(Array.from(children));
    Object.freeze(this);
  }

  children(): readonly Term[] {
    return this.#children;
  }

  /**
   * Structural equality, walked with an explicit work stack (#2366) so a term nested
   * thousands of levels deep (a long surface list is one level per element) cannot
   * overflow the JS call stack. Atom and Var equality is not recursive, so only tuple
   * pairs are expanded.
   */
  equals(other: Term): boolean {
    const work: Array<readonly [Term, Term]> = [[this, other]];
    while (work.length > 0) {
      const [left, right] = work.pop()!;
      if (left.kind !== "tuple") {
        if (!left.equals(right)) return false;
        continue;
      }
      if (right.kind !== "tuple") return false;
      const a = left.children();
      const b = right.children();
      if (a.length !== b.length) return false;
      for (let i = a.length - 1; i >= 0; i -= 1) {
        work.push([a[i]!, b[i]!]);
      }
    }
    return true;
  }
}

/** The unknown — logos's sole addition. */
export class TermVar {
  readonly kind = "var" as const;
  readonly #id: VarId;

  static [Symbol.hasInstance](value: unknown): boolean {
    return typeof value === "object" && value !== null && #id in value;
  }

  constructor(id: VarId) {
    this.#id = id;
    Object.freeze(this);
  }

  id(): VarId {
    return this.#id;
  }

  equals(other: Term): boolean {
    return other.kind === "var" && this.#id.equals(other.id());
  }
}

Object.freeze(VarId.prototype);
Object.freeze(VarId);
Object.freeze(TermAtom.prototype);
Object.freeze(TermAtom);
Object.freeze(TermTuple.prototype);
Object.freeze(TermTuple);
Object.freeze(TermVar.prototype);
Object.freeze(TermVar);

export const Term = {
  atom(bytes: OctetSource): Term {
    return new TermAtom(bytes);
  },
  tuple(children: Iterable<Term>): Term {
    return new TermTuple(Array.from(children));
  },
  var(id: VarId | string): Term {
    return new TermVar(typeof id === "string" ? new VarId(id) : id);
  },

  /**
   * `ground(t)` ⟺ `t` contains no `Var` (normative, §1).
   *
   * Non-recursive (#2366), like `fromValue` (#253): it used to recurse once per nesting
   * level and threw a RangeError at about 2,464 list elements, which rs answers.
   */
  isGround(t: Term): boolean {
    const work: Term[] = [t];
    while (work.length > 0) {
      const term = work.pop()!;
      if (term.kind === "var") return false;
      if (term.kind === "tuple") {
        for (const child of term.children()) work.push(child);
      }
    }
    return true;
  },

  /**
   * Whether `t` is an OPEN compound: a tuple containing a variable at any depth (#2294, ruled
   * seat:caa). THE classification of "compound" the function-free fragment excludes. A GROUND
   * term, compound or not, is a constant: a string, an int, a ground list and `f(a)` all are.
   * Mirrors rs `Term::is_open_compound` and go `IsOpenCompound`.
   */
  isOpenCompound(t: Term): boolean {
    return t.kind === "tuple" && !Term.isGround(t);
  },

  /**
   * `eraseGround(t)` — the corresponding ontos `Value`, defined iff `ground(t)`
   * (normative, §1). Returns `undefined` for a non-ground term.
   *
   * Non-recursive (#2366): the same explicit post-order assembly as `fromValue`, so a
   * deep term cannot overflow the JS call stack here.
   */
  eraseGround(t: Term): Value | undefined {
    type Frame = { enter: Term } | { assemble: number };
    const work: Frame[] = [{ enter: t }];
    const out: Value[] = [];
    while (work.length > 0) {
      const frame = work.pop()!;
      if ("assemble" in frame) {
        const start = out.length - frame.assemble;
        out.push(valueTuple(out.splice(start, frame.assemble)));
        continue;
      }
      const term = frame.enter;
      switch (term.kind) {
        case "atom":
          out.push(valueAtom(term.bytes()));
          break;
        case "var":
          return undefined;
        case "tuple": {
          const children = term.children();
          // The assemble first, then the children in reverse: LIFO processes the
          // children in order and leaves exactly `arity` values for the assemble.
          work.push({ assemble: children.length });
          for (let i = children.length - 1; i >= 0; i -= 1) {
            work.push({ enter: children[i]! });
          }
          break;
        }
      }
    }
    return out[out.length - 1];
  },

  /**
   * Inverse of `eraseGround` on ground terms: lift an ontos `Value` into a Term.
   *
   * Non-recursive (issue #253). Built with an explicit work stack so a pathologically
   * deep `Value` cannot overflow the JS call stack here at the decode boundary — this
   * is the one term traversal that must remain total even for an over-deep input (the
   * depth guard runs after a term is in hand, so constructing it must not itself
   * throw a RangeError). The post-order assembly reproduces the recursive shape.
   */
  fromValue(value: Value): Term {
    type Frame = { enter: Value } | { assemble: number };
    const work: Frame[] = [{ enter: value }];
    const out: Term[] = [];
    while (work.length > 0) {
      const frame = work.pop()!;
      if ("assemble" in frame) {
        const start = out.length - frame.assemble;
        const children = out.splice(start, frame.assemble);
        out.push(new TermTuple(children));
        continue;
      }
      const v = frame.enter;
      if (v instanceof Atom) {
        out.push(new TermAtom(v.bytes()));
      } else {
        const items = (v as { items(): readonly Value[] }).items();
        // Schedule the assemble first, then the children (LIFO → children are
        // processed before the assemble, leaving exactly `arity` built terms).
        work.push({ assemble: items.length });
        for (let i = items.length - 1; i >= 0; i -= 1) {
          work.push({ enter: items[i]! });
        }
      }
    }
    return out[out.length - 1]!;
  },

  /**
   * `depthLe(t, max)` — `true` iff `t` nests no deeper than `max` levels, measured
   * ITERATIVELY with an early cutoff (issue #253), so checking a pathologically deep
   * term's depth does NOT itself overflow the stack (a recursive depth-measure would
   * defeat the purpose). An Atom/Var has depth 1; a Tuple has depth `1 + max(child
   * depth)`. Returns `false` as soon as a path exceeds `max`.
   */
  depthLe(t: Term, max: number): boolean {
    const work: Array<{ term: Term; level: number }> = [{ term: t, level: 1 }];
    while (work.length > 0) {
      const { term, level } = work.pop()!;
      if (level > max) return false;
      if (term.kind === "tuple") {
        for (const c of term.children()) {
          work.push({ term: c, level: level + 1 });
        }
      }
    }
    return true;
  },

  /**
   * Apply a grounding substitution (one pass). A `Var` with no binding is left in
   * place (so the result is non-ground and a subsequent ground check fails).
   *
   * Non-recursive (#2366): the same explicit post-order assembly as `fromValue`.
   */
  substitute(t: Term, subst: Subst): Term {
    type Frame = { enter: Term } | { assemble: number };
    const work: Frame[] = [{ enter: t }];
    const out: Term[] = [];
    while (work.length > 0) {
      const frame = work.pop()!;
      if ("assemble" in frame) {
        const start = out.length - frame.assemble;
        out.push(new TermTuple(out.splice(start, frame.assemble)));
        continue;
      }
      const term = frame.enter;
      switch (term.kind) {
        case "atom":
          out.push(term);
          break;
        case "var":
          out.push(subst.get(term.id().asStr()) ?? term);
          break;
        case "tuple": {
          const children = term.children();
          work.push({ assemble: children.length });
          for (let i = children.length - 1; i >= 0; i -= 1) {
            work.push({ enter: children[i]! });
          }
          break;
        }
      }
    }
    return out[out.length - 1]!;
  },
};

Object.freeze(Term);

// ===========================================================================
// account-v2 list canonicalization (cons ↔ `list`) — the BIJECTION on ground proper
// lists used by the reify-aware account-equality (#277). [FIRM]
//
// TS sibling of contract/rs/src/term.rs::canonicalize_lists. The logos surface lowers
// list syntax to Prolog-style cons cells (`[]` = Atom("[]"), `[H|T]` = Tuple[Atom("."),
// H, T]); the ontos/data L2 profile carries a sequence as the flat `list` embedding
// Tuple[Atom("list"), e0, …] (ontos-data §5.5). These are two spellings of the SAME
// datum; the opt-in account-emit reification (rust-only reifyLists, #159) rewrites cons
// → `list`. #277 made `check` treat the two spellings as account-equal; #3022 withdrew
// that: every certified literal claim is exact, `check` compares structurally, and this
// canonicalization is the PRESENTATION equivalence, never a certification equivalence.
//
// `canonicalizeLists` is the single canonical retraction `check` applies to BOTH sides
// of a comparison: it maps every ground PROPER cons-list to its `list` embedding (and
// leaves the `list` embedding fixed), so a cons-form clause head and a reified `list()`
// conclusion canonicalize to the same value and compare equal — while NEVER conflating
// two terms that denote different data.
//
// THE BIJECTION. On ground proper lists, cons-form `[e0,…,e_{n-1}]` and the `list`
// embedding `list(e0,…,e_{n-1})` are in one-to-one correspondence (a proper cons-chain
// has a unique element sequence; `list(…)` a unique child sequence). `canonicalizeLists`
// picks the `list` embedding as the canonical representative and is the IDENTITY on every
// other value; it is idempotent (a retraction), conflates two values ONLY when they are
// the cons and `list` spellings of the SAME sequence (the intended account equality), and
// leaves a non-list value untouched (so distinct sequences / non-list terms never
// collapse).
//
// EDGE CASES (each kept distinct): a bare nil Atom("[]") is an ATOM, not a `.`/2 cell, so
// it is LEFT as Atom("[]") (never rewritten to list()); the empty `list` embedding
// Tuple[Atom("list")] is likewise fixed — so `[]` and `list()` are DISTINCT. An improper
// `.(a, b)` (tail not []) is NOT a proper list → kept as the cons tuple. A partial `[a|X]`
// cannot occur (a Value has no Var). An existing Tuple[Atom("list"), …] is headed by
// `list`, not `.`, so it is never a cons cell (children canonicalized, no double-wrap).
// ===========================================================================

/** The cons functor "." (a `[H|T]` cell head), as bytes. */
const CONS_LABEL = new TextEncoder().encode(".");
/** The nil atom "[]" (the cons-chain terminator), as bytes. */
const NIL_LABEL = new TextEncoder().encode("[]");
/** The ontos/data `list` embedding label (Tuple[Atom("list"), …]), as bytes. */
const LIST_LABEL = new TextEncoder().encode("list");

/**
 * Canonicalize every ground PROPER cons-list anywhere inside `value` to the ontos/data
 * flat `list` embedding (`Tuple[Atom("list"), e0, …]`), bottom-up — the single canonical
 * retraction of the presentation equivalence (#277; since #3022 `check` never applies
 * it). The IDENTITY on every non-(proper-cons-list) value. See the block note above
 * for the bijection / no-conflation argument and the edge cases. Total and deterministic;
 * the spine walk is iterative (no per-cell recursion), and element/child recursion is
 * bounded by the term-nesting depth the trusted path already gated (`maxTermDepth`).
 */
export function canonicalizeLists(value: Value): Value {
  // A proper cons-list anywhere is canonicalized to the flat `list` embedding. The test
  // runs on the RAW value (before any child rewrite): the spine threads through `.`/`[]`
  // cells, so canonicalizing a child first would dissolve the spine the top of the chain
  // must walk. We collect the raw element values off the intact spine, then canonicalize
  // EACH element (so nested lists are normalized too).
  const elems = collectProperConsList(value);
  if (elems !== undefined) {
    return valueTuple([valueAtom(LIST_LABEL), ...elems.map(canonicalizeLists)]);
  }
  if (value instanceof ValueTupleClass) {
    // A non-list tuple (an ordinary compound, an existing list(…) embedding): keep the
    // shape, canonicalize each child.
    return valueTuple(value.items().map(canonicalizeLists));
  }
  // An Atom (including the bare nil "[]"): identity.
  return value;
}

/**
 * If `value` is a cons cell `Tuple[Atom("."), H, T]` whose spine is a PROPER list (ends
 * in the nil atom "[]"), return the RAW (un-canonicalized) element values in order;
 * otherwise `undefined`. Iterative over the tail (no spine recursion) so a long list does
 * not grow the stack.
 */
function collectProperConsList(value: Value): Value[] | undefined {
  // A standalone nil atom "[]" is NOT a list — only an actual `.`/2 cons cell starts a
  // list. (Canonicalizing a bare "[]" to list() would re-encode a legitimate atom and
  // break the empty-list edge case.)
  if (!(value instanceof ValueTupleClass) || !isConsCell(value.items())) {
    return undefined;
  }
  let cursor: Value = value;
  const elems: Value[] = [];
  for (;;) {
    if (cursor instanceof Atom) {
      // Proper terminator: the spine ends in the nil atom "[]".
      if (bytesEqual(cursor.bytes(), NIL_LABEL)) return elems;
      // A non-"[]" atom before reaching "[]": improper.
      return undefined;
    }
    if (cursor instanceof ValueTupleClass && isConsCell(cursor.items())) {
      const items = cursor.items();
      elems.push(items[1]!);
      cursor = items[2]!;
      continue;
    }
    // A non-cons tuple before reaching "[]": improper / not a list.
    return undefined;
  }
}

/** Whether `items` are exactly the items of a cons cell: arity 3, headed by Atom("."). */
function isConsCell(items: readonly Value[]): boolean {
  return items.length === 3 && items[0] instanceof Atom && bytesEqual(items[0].bytes(), CONS_LABEL);
}

/**
 * `valueDepthLe(value, max)` — `true` iff the ontos `value` nests no deeper than `max`
 * levels: the `Term.depthLe` analogue for a ground `Value` (a `GroundLiteral`'s args
 * are `Value`s, not `Term`s). Iterative with an early cutoff (issue #253): the
 * recursive `Value` traversals on the trusted path (structural `equals` against the
 * claim, the canonical codec encode) would overflow on a pathologically deep value, so
 * the trusted checker measures depth without recursing and rejects an over-deep value.
 */
export function valueDepthLe(value: Value, max: number): boolean {
  const work: Array<{ value: Value; level: number }> = [{ value, level: 1 }];
  while (work.length > 0) {
    const { value: v, level } = work.pop()!;
    if (level > max) return false;
    if (v instanceof ValueTupleClass) {
      for (const c of v.items()) {
        work.push({ value: c, level: level + 1 });
      }
    }
  }
  return true;
}

/**
 * A grounding substitution (§3): a map from variable identity to a replacement
 * term. Keyed by the `VarId` string (the Rust `BTreeMap<VarId, Term>`).
 */
export type Subst = Map<string, Term>;
