// ListTheory — the TS binding of logos-core's reified list-relation Theory, a
// judgment-for-judgment mirror of the Rust ListTheory in contract/rs/src/list_theory.rs
// and the Go ListTheory in contract/go/list_theory.go (ADR 0016, Shelf A1).
// [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the list
// relations length/2, nth0/3, last/2 over the ontos/data REIFIED list embedding
// list(e0..e_{n-1}) = Tuple(Atom("list"), e0, ..., e_{n-1}): a program that uses them on
// the list() embedding can now be CHECKED in TS, because the same decision the Rust
// core makes is reproduced here byte-for-byte. All three cores agree on EVERY ground atom —
// the §7 dual-conformance law, pinned by vectors/list.json.
//
// # The home (why contract/ts)
//
// Rust's ListTheory lives in the contract tier (contract/rs), beside the Theory SPI, per
// ADR 0014 / ADR 0016: a pure, total, deterministic function of a resolved ground term is
// a shared certifiable artifact, not a search-only Rust builtin. TS has no core tier; the
// reusable Theory impls a consumer binds (ArithmeticTheory, TextTheory, TermTheory) live
// HERE, beside the SPI. So this is where a TS consumer binds the list relations.
//
// # The A1 fast-path complement (NOT a duplicate)
//
// The Shelf-B lists@1.1.0 prelude ships length/2, nth0/3, last/2 as Rule clauses over
// CONS cells ([H|T] = Tuple(Atom("."), H, T)); the existing check() verifies them. This
// theory is the native A1 reading over the list() embedding instead — the SAME relations,
// a DIFFERENT representation. The two share predicate names but own structurally disjoint
// argument shapes, so a profile binds exactly one of them per predicate (the §4.4 builtin
// partition forbids a theory-owned name from also being a rule head).
//
// # Judgments (mirroring Rust/Go exactly)
//
// owns(pred): by NAME only (any arity) — length, nth0, last.
// decideGround(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{list_unknown_predicate}   (defensive)
//   - wrong arity                    -> Fails{list_bad_arity}
//   - the relation is true           -> Holds
//   - the relation is false          -> Fails{list_does_not_hold}
//     (non-list argument, out-of-range index, count/element mismatch, empty list for last)

import { decodeUtf8 } from "./utf8.js";
import { equals, type Value } from "@bitspark/ontos-core";
import { encodeInt, readInt, readList } from "@bitspark/ontos-data";

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

// The predicate names ListTheory owns, mirroring Rust's LIST_PREDICATES / Go's
// listPredicates. Keyed by byte-exact hex so an unregistered arity (or a non-UTF-8
// predicate) routes correctly — never throws.
const LIST_PREDICATE_KEYS: ReadonlySet<string> = new Set(
  ["length", "nth0", "last"].map((name) => hexKey(utf8Encoder.encode(name))),
);

/**
 * The config-pinned §5 Theory that owns the A1 list relations (length nth0 last) over the
 * ontos/data list embedding and decides a GROUND atom by a direct structural match against
 * list(…) (constant/linear, no search, no trail). Pure / total / deterministic /
 * config-free — a faithful mirror of Rust's contract::list_theory::ListTheory and the Go
 * ListTheory.
 */
export class ListTheory implements Theory {
  /**
   * owns reports whether `pred` names an owned list relation. Mirrors Rust's
   * ListTheory::owns / owns_name and Go's Owns — by name, at any arity.
   */
  owns(pred: Symbol): boolean {
    return LIST_PREDICATE_KEYS.has(hexKey(pred.bytes()));
  }

  /**
   * Decides an owned GROUND atom, byte-identically to the Rust/Go ListTheory.decide_ground. A
   * ground list relation binds nothing, so it either Holds (the relation is true) or Fails
   * with a pinned host-band sub-code.
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
      return TheoryGround.fails("list_unknown_predicate");
    }

    switch (name) {
      case "length":
        return decideLength(atom.args);
      case "nth0":
        return decideNth0(atom.args);
      case "last":
        return decideLast(atom.args);
      default:
        // Owned name routed here but not handled above — unreachable (the name set is
        // exactly the switch arms), but stay total.
        return TheoryGround.fails("list_does_not_hold");
    }
  }

  /**
   * The theory's canonical component identity, logos-core/list-theory@1.0.0 with a zero
   * config digest — byte-identical to the Rust/Go theory's identity, so a CheckProfile
   * binding it derives the same theory binding (and thus the same stamped digest)
   * tri-core. The logos-core/ namespace is a STABLE IDENTITY, not a path (ADR 0014/0016).
   */
  identity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/list-theory"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  /** #3142: every list decision completes (a direct destructuring of the list embedding). */
  completion(_pred: Symbol): DecisionCompletion {
    return DecisionCompletion.StopsAreTyped;
  }
}

/** Builds the standard list Theory (no configuration). */
export function newListTheory(): ListTheory {
  return new ListTheory();
}

/**
 * Reads the elements of a GROUND list embedding Tuple(Atom("list"), e0, …), or undefined
 * if `v` is not a canonical list embedding. Thin wrapper over the frozen readList (which
 * throws on a non-list) — the SAME recognizer the producer's reify emits through, so
 * producer and checker agree by construction. Mirrors Rust's list_elements.
 */
function listElements(v: Value): Value[] | undefined {
  try {
    return readList(v);
  } catch {
    return undefined;
  }
}

/** Reads a canonical int embedding as a bigint, or undefined for any non-int. */
function readIntOrUndefined(v: Value): bigint | undefined {
  try {
    return readInt(v);
  } catch {
    return undefined;
  }
}

/**
 * Decides length(list(e0..e_{n-1}), int(n)): arity must be 2; then arg0 must be a list
 * embedding of n elements AND arg1 must be the canonical int embedding of that same n. A
 * non-list arg0, a non-int arg1, or a count mismatch is list_does_not_hold. Mirrors Rust's
 * decide_length.
 */
function decideLength(args: readonly Value[]): TheoryGround {
  if (args.length !== 2) {
    return TheoryGround.fails("list_bad_arity");
  }
  const elems = listElements(args[0]!);
  if (elems === undefined) {
    return TheoryGround.fails("list_does_not_hold");
  }
  // Build the canonical int embedding of the length and compare structurally — so arg1
  // must be the SAME canonical int the Shelf-B length clauses (is/2 over the int
  // embedding) accumulate. A non-int or a wrong-int arg1 simply fails to equal it.
  const want = encodeInt(BigInt(elems.length));
  return equals(args[1]!, want)
    ? TheoryGround.holds()
    : TheoryGround.fails("list_does_not_hold");
}

/**
 * Decides nth0(int(i), list(e0..e_{n-1}), e_i): arity must be 3; then arg0 must be a
 * non-negative int index i, arg1 a list embedding, i in range 0 <= i < n, and arg2
 * structurally equal to the i-th element. A non-int index, a non-list, an out-of-range
 * index, or an element mismatch is list_does_not_hold. (Prolog/SWI argument order: index,
 * list, element.) Mirrors Rust's decide_nth0.
 */
function decideNth0(args: readonly Value[]): TheoryGround {
  if (args.length !== 3) {
    return TheoryGround.fails("list_bad_arity");
  }
  // Index must be the canonical int embedding. A non-int / negative / out-of-range index
  // is simply a false relation (the element does not exist at that position).
  const index = readIntOrUndefined(args[0]!);
  if (index === undefined) {
    return TheoryGround.fails("list_does_not_hold");
  }
  const elems = listElements(args[1]!);
  if (elems === undefined) {
    return TheoryGround.fails("list_does_not_hold");
  }
  if (index < 0n || index >= BigInt(elems.length)) {
    return TheoryGround.fails("list_does_not_hold");
  }
  const elem = elems[Number(index)]!;
  return equals(elem, args[2]!)
    ? TheoryGround.holds()
    : TheoryGround.fails("list_does_not_hold");
}

/**
 * Decides last(list(e0..e_{n-1}), e_{n-1}): arity must be 2; then arg0 must be a NON-EMPTY
 * list embedding and arg1 structurally equal to its last element. A non-list, an empty
 * list, or a mismatch is list_does_not_hold. Mirrors Rust's decide_last.
 */
function decideLast(args: readonly Value[]): TheoryGround {
  if (args.length !== 2) {
    return TheoryGround.fails("list_bad_arity");
  }
  const elems = listElements(args[0]!);
  if (elems === undefined || elems.length === 0) {
    return TheoryGround.fails("list_does_not_hold");
  }
  const last = elems[elems.length - 1]!;
  return equals(last, args[1]!)
    ? TheoryGround.holds()
    : TheoryGround.fails("list_does_not_hold");
}
