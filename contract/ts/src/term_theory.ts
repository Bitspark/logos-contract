// TermTheory — the TS binding of logos-core's term-algebra Theory, a
// judgment-for-judgment mirror of the Rust TermTheory in contract/rs/src/term_theory.rs
// and the Go TermTheory in contract/go/term_theory.go (ADR 0016, Shelf A0).
// [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the term
// recognizers and standard order: a program that uses atom/1, atomic/1, compound/1,
// is_list/1, number/1, ==/2, \==/2, @</2, @>/2, @=</2, @>=/2 can now be CHECKED in TS,
// because the same decision the Rust core makes is reproduced here byte-for-byte. All
// three cores agree on EVERY ground term atom — the §7 dual-conformance law, pinned by
// vectors/term.json.
//
// # The home (why contract/ts)
//
// Rust's TermTheory lives in the contract tier (contract/rs), beside the Theory SPI, per
// ADR 0014 / ADR 0016: a pure, total, deterministic function of a resolved ground term is
// a shared certifiable artifact, not a search-only Rust builtin. TS has no core tier; the
// checker SPI is tri-core in contract/ts, and the reusable Theory impls a consumer binds
// (e.g. AlwaysAdmit, ArithmeticTheory, TextTheory) live HERE, beside the SPI. So this is
// where a TS consumer binds the term recognizers + standard order.
//
// # The standard order (ground restriction: Atom < Tuple)
//
// Ground terms are an ontos Value = Atom(bytes) | Tuple(items) — there is NO Var. The full
// standard order is Var < Atom < Tuple; restricted to ground terms it is Atom < Tuple,
// ties by atom bytes / tuple arity-then-elementwise. A number is the int embedding
// Tuple(Atom("int"), Atom(payload)) — structurally a Tuple — so it sorts with the compound
// rank, NOT before atoms (matching the search-side compare_terms). number/1 still
// distinguishes a number from a bare atom via the embedding shape (readInt).
//
// # Judgments (mirroring Rust/Go exactly)
//
// owns(pred): by NAME only (any arity) — the five recognizers, six comparisons, univ, and
// (since 1.1.0, #1611) unification + the control constants.
// decideGround(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{term_unknown_predicate}   (defensive)
//   - recognizer not at arity 1
//     OR comparison not at arity 2
//     OR control constant not at 0   -> Fails{term_bad_arity}
//   - the relation is true           -> Holds
//   - the relation is false          -> Fails{term_does_not_hold}
//
// # Unification and the control constants (1.1.0, #1611 — seat:caa's ruling)
//
// =/2, \=/2, true/0, fail/0 and false/0 are served by the rs engine's Stage-A registry but
// dispatched only behind theory.owns, and the checker's Builtin arm accepts a node only if a
// bound theory owns its predicate — so until a theory owned them, `X = a` in a body yielded
// a SILENT empty answer and no Builtin node could certify. On ground terms syntactic
// unification is structural equality, so `t = u` holds iff compareValues(t, u) === 0 and
// `t \= u` iff it differs; `true` holds; `fail`/`false` never hold. Mirrors Rust/Go exactly.

import { decodeUtf8 } from "./utf8.js";
import { Atom, Tuple, type Value } from "@bitspark/ontos-core";
import { readInt } from "@bitspark/ontos-data";

import { BigDecimal } from "./decval.js";
import { TheoryGround } from "./completion.js";
import { Symbol, type GroundLiteral } from "./literal.js";
import { ComponentIdentity, DecisionCompletion, type Theory } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** Lower-case hex of a byte string — a byte-exact, UTF-8-agnostic map/set key. */
function hexKey(bytes: Uint8Array): string {
  let s = "";
  for (const b of bytes) s += b.toString(16).padStart(2, "0");
  return s;
}

// The list-cons functor `.`/2 ([H|T] = Tuple(Atom("."), H, T)) and nil `[]` bytes —
// mirror the Rust CONS_FUNCTOR / NIL_ATOM.
const CONS_FUNCTOR = utf8Encoder.encode(".");
const NIL_ATOM = utf8Encoder.encode("[]");

// The arity-1 recognizers and arity-2 comparisons TermTheory owns, mirroring Rust's
// RECOGNIZER_PREDICATES / COMPARISON_PREDICATES. Keyed by byte-exact hex so an
// unregistered arity (or a non-UTF-8 predicate) routes correctly — never throws.
const TERM_PREDICATE_KEYS: ReadonlySet<string> = new Set(
  // The five recognizers, six comparisons, `=..` (univ, #658), and — since 1.1.0 (#1611) —
  // unification (`=` `\\=`) and the control constants (`true` `fail` `false`). Owned by name.
  [
    "atom", "atomic", "compound", "is_list", "number",
    "==", "\\==", "@<", "@>", "@=<", "@>=",
    "=..",
    "=", "\\=",
    "true", "fail", "false",
  ].map((name) => hexKey(utf8Encoder.encode(name))),
);

/**
 * The config-pinned §5 Theory that owns the A0 term recognizers (atom atomic compound
 * is_list number) and the standard-order comparisons (== \== @< @> @=< @>=) and decides a
 * GROUND term atom by a constant-time structural match (no search, no trail). Pure /
 * total / deterministic / config-free — a faithful mirror of Rust's
 * contract::term_theory::TermTheory and the Go TermTheory.
 */
export class TermTheory implements Theory {
  /**
   * Owns reports whether `pred` names an owned term relation. Mirrors Rust's
   * TermTheory::owns / owns_name and Go's Owns — by name, at any arity.
   */
  owns(pred: Symbol): boolean {
    return TERM_PREDICATE_KEYS.has(hexKey(pred.bytes()));
  }

  /**
   * Decides an owned GROUND term atom, byte-identically to the Rust/Go TermTheory.decide_ground.
   * A ground term relation binds nothing, so it either Holds (the relation is true) or
   * Fails with a pinned host-band sub-code.
   */
  decideGround(atom: GroundLiteral): TheoryGround {
    // Not one of ours: a routing safety net (check routes by owns, so this is
    // unreachable on a correctly-routed call — but stay total). Mirrors Rust/Go.
    if (!this.owns(atom.pred)) {
      return TheoryGround.disowned();
    }
    let name: string;
    try {
      name = decodeUtf8(atom.pred.bytes());
    } catch {
      return TheoryGround.fails("term_unknown_predicate");
    }

    switch (name) {
      // A0 recognizers (arity 1).
      case "atom":
        return decideRecognizer(atom.args, isAtomValue);
      // In the ground term world the only atomic terms are Atoms (no Var, a number is the
      // int Tuple embedding), so atomic coincides with atom.
      case "atomic":
        return decideRecognizer(atom.args, isAtomValue);
      case "compound":
        return decideRecognizer(atom.args, isTupleValue);
      case "is_list":
        return decideRecognizer(atom.args, isProperList);
      case "number":
        return decideRecognizer(atom.args, isNumber);
      // A0 standard-order comparisons (arity 2).
      case "==":
        return decideComparison(atom.args, (c) => c === 0);
      case "\\==":
        return decideComparison(atom.args, (c) => c !== 0);
      case "@<":
        return decideComparison(atom.args, (c) => c < 0);
      case "@>":
        return decideComparison(atom.args, (c) => c > 0);
      case "@=<":
        return decideComparison(atom.args, (c) => c <= 0);
      case "@>=":
        return decideComparison(atom.args, (c) => c >= 0);
      // A0 structural decomposition (arity 2): univ.
      case "=..":
        return decideUniv(atom.args);
      // Unification over GROUND terms (arity 2, #1611): structural equality.
      case "=":
        return decideComparison(atom.args, (c) => c === 0);
      case "\\=":
        return decideComparison(atom.args, (c) => c !== 0);
      // Control constants (arity 0, #1611).
      case "true":
        return decideControl(atom.args, true);
      case "fail":
      case "false":
        return decideControl(atom.args, false);
      default:
        // Owned name routed here but not handled above — unreachable (the name set is
        // exactly the switch arms), but stay total.
        return TheoryGround.fails("term_does_not_hold");
    }
  }

  /**
   * The theory's canonical component identity, logos-core/term-theory@1.1.0 with a zero
   * config digest — byte-identical to the Rust/Go theory's identity, so a CheckProfile
   * binding it derives the same theory binding (and thus the same stamped digest)
   * tri-core. The logos-core/ namespace is a STABLE IDENTITY, not a path (ADR 0014/0016).
   * 1.0.0 -> 1.1.0 with #1611 (the owned set grew by = \\= true fail false).
   */
  identity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/term-theory"),
      utf8Encoder.encode("1.1.0"),
      new Uint8Array(32),
    );
  }

  /** #3142: every term decision completes (the recognizers, univ, and the standard order, an explicit-stack walk since #2275). */
  completion(_pred: Symbol): DecisionCompletion {
    return DecisionCompletion.StopsAreTyped;
  }
}

/** Builds the standard term Theory (no configuration). */
export function newTermTheory(): TermTheory {
  return new TermTheory();
}

/** Whether a ground value is a bare Atom. */
function isAtomValue(v: Value): boolean {
  return v instanceof Atom;
}

/** Whether a ground value is a compound Tuple. */
function isTupleValue(v: Value): boolean {
  return v instanceof Tuple;
}

/** Byte-equality of two Uint8Arrays. */
function bytesEq(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

/** Whether a ground value is the nil atom `[]`. */
function isNil(v: Value): boolean {
  return v instanceof Atom && bytesEq(v.bytes(), NIL_ATOM);
}

/**
 * Matches a [H|T] cons cell over a GROUND value (a 3-element tuple headed by the `.`
 * atom), returning [head, tail], or undefined. Mirrors Rust's as_cons.
 */
function asCons(v: Value): [Value, Value] | undefined {
  if (!(v instanceof Tuple)) return undefined;
  const items = v.items();
  if (items.length !== 3) return undefined;
  const head = items[0]!;
  if (!(head instanceof Atom) || !bytesEq(head.bytes(), CONS_FUNCTOR)) return undefined;
  return [items[1]!, items[2]!];
}

/**
 * Whether a GROUND value is a proper list (a []-terminated chain of `.`/2 cons cells). A
 * ground value can never be partial (no Var), so only the improper-tail case fails.
 * Mirrors Rust's is_proper_list.
 */
function isProperList(v: Value): boolean {
  let current = v;
  for (;;) {
    if (isNil(current)) return true;
    const cons = asCons(current);
    if (cons === undefined) return false;
    current = cons[1];
  }
}

/**
 * Whether a GROUND value is a (canonical) exact-integer int embedding OR a (canonical)
 * exact-decimal decimal embedding (#331). Unlike atom, a number-shaped bare atom ("3.14"
 * or Atom("42")) does NOT count — only the genuine embeddings do. Shares the recognizers
 * with the search-side number/1, so the two agree byte-for-byte. readInt throws on any
 * non-int; BigDecimal.fromTerm returns undefined on any non-decimal.
 */
function isNumber(v: Value): boolean {
  try {
    readInt(v);
    return true;
  } catch {
    return BigDecimal.fromTerm(v) !== undefined;
  }
}

/**
 * Decides an arity-1 recognizer: arity must be 1; then test(arg0). A non-1 arity has no
 * such relation (term_bad_arity); a false test is term_does_not_hold.
 */
function decideRecognizer(args: readonly Value[], test: (v: Value) => boolean): TheoryGround {
  if (args.length !== 1) {
    return TheoryGround.fails("term_bad_arity");
  }
  return test(args[0]!) ? TheoryGround.holds() : TheoryGround.fails("term_does_not_hold");
}

/**
 * Decides an arity-2 standard-order comparison: arity must be 2; then accept iff
 * accept(compareValues(arg0, arg1)). A non-2 arity has no such relation (term_bad_arity);
 * a false comparison is term_does_not_hold.
 */
function decideComparison(
  args: readonly Value[],
  accept: (c: number) => boolean,
): TheoryGround {
  if (args.length !== 2) {
    return TheoryGround.fails("term_bad_arity");
  }
  return accept(compareValues(args[0]!, args[1]!))
    ? TheoryGround.holds()
    : TheoryGround.fails("term_does_not_hold");
}

/**
 * Decides an arity-0 control constant (#1611): arity must be 0 (term_bad_arity otherwise);
 * then `true` holds and `fail`/`false` are term_does_not_hold. Mirrors Rust's decide_control.
 */
function decideControl(args: readonly Value[], holds: boolean): TheoryGround {
  if (args.length !== 0) {
    return TheoryGround.fails("term_bad_arity");
  }
  return holds ? TheoryGround.holds() : TheoryGround.fails("term_does_not_hold");
}

/**
 * Builds the cons-list [e0, … en] as a ground Value — the frozen `.`/2 cons form
 * ([]-terminated). Mirrors Rust's value_cons_list / Go's valueConsList.
 */
function valueConsList(elements: readonly Value[]): Value {
  let acc: Value = new Atom(NIL_ATOM);
  for (let i = elements.length - 1; i >= 0; i--) {
    acc = new Tuple([new Atom(CONS_FUNCTOR), elements[i]!, acc]);
  }
  return acc;
}

/**
 * The univ image of a ground term: the [Functor | Args] cons-list a `T =.. L` relation holds
 * for. A labeled compound Tuple(Atom(f), a1 … an) -> [f, a1, … an]; a bare Atom(a) -> [a]. An
 * empty tuple or a non-Atom-headed tuple is outside the labeled-compound image (undefined).
 * Mirrors Rust's univ_list_of / Go's univListOf.
 */
function univListOf(v: Value): Value | undefined {
  if (v instanceof Atom) {
    return valueConsList([v]);
  }
  if (v instanceof Tuple) {
    const items = v.items();
    if (items.length === 0 || !(items[0] instanceof Atom)) {
      return undefined;
    }
    return valueConsList(items);
  }
  return undefined;
}

/**
 * Decides the arity-2 univ relation `T =.. L`: arity must be 2; then Holds iff L equals the
 * univ image of T. A T that is not a labeled compound / atom -> univ_not_callable; a
 * mismatched L -> univ_mismatch. Mirrors Rust's decide_univ / Go's decideUniv.
 */
function decideUniv(args: readonly Value[]): TheoryGround {
  if (args.length !== 2) {
    return TheoryGround.fails("term_bad_arity");
  }
  const expected = univListOf(args[0]!);
  if (expected === undefined) {
    return TheoryGround.fails("univ_not_callable");
  }
  return compareValues(args[1]!, expected) === 0
    ? TheoryGround.holds()
    : TheoryGround.fails("univ_mismatch");
}

/**
 * Compares two GROUND terms by the standard order of terms — a total order consistent with
 * structural equality (compareValues(a, b) === 0 iff a == b). Ground terms are ranked
 * Atom < Tuple; within a rank, Atoms order by raw bytes and Tuples first by arity then
 * element-wise. Returns a three-way result (-1 / 0 / +1). Mirrors Rust's
 * contract::term_theory::compare_values byte-for-byte (and the search-side compare_terms
 * over ground terms).
 */
export function compareValues(a: Value, b: Value): number {
  const aIsAtom = a instanceof Atom;
  const bIsAtom = b instanceof Atom;
  if (aIsAtom && bIsAtom) {
    return compareBytes(a.bytes(), b.bytes());
  }
  if (aIsAtom && !bIsAtom) {
    // Atom (rank 0) before Tuple (rank 1).
    return -1;
  }
  if (!aIsAtom && bIsAtom) {
    return 1;
  }
  // Both Tuples: by arity, then element-wise.
  const aItems = (a as Tuple).items();
  const bItems = (b as Tuple).items();
  if (aItems.length !== bItems.length) {
    return aItems.length < bItems.length ? -1 : 1;
  }
  for (let i = 0; i < aItems.length; i += 1) {
    const c = compareValues(aItems[i]!, bItems[i]!);
    if (c !== 0) return c;
  }
  return 0;
}

/** Lexicographic byte comparison (shorter-is-prefix-first), like Rust's slice cmp. */
function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    if (a[i]! !== b[i]!) return a[i]! < b[i]! ? -1 : 1;
  }
  if (a.length === b.length) return 0;
  return a.length < b.length ? -1 : 1;
}
