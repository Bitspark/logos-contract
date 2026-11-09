// TextTheory — the TS binding of logos-core's byte-string Theory, a
// judgment-for-judgment mirror of the Rust TextTheory in contract/rs/src/text.rs and
// the Go TextTheory in contract/go/text.go (ADR 0016, Shelf A). [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the text
// relations: a program that uses contains/2, starts_with/2, ends_with/2 can now be
// CHECKED in TS, because the same decide() that the Rust core uses is reproduced here
// byte-for-byte. All three cores agree on EVERY ground text atom — the §7
// dual-conformance law, pinned by vectors/text.json.
//
// # The home (why contract/ts)
//
// Rust's TextTheory lives in the contract tier (contract/rs), beside the Theory SPI,
// per ADR 0014 / ADR 0016: a pure, total, deterministic function of ground args is a
// shared certifiable artifact, not a search-only Rust builtin. TS has no core tier; the
// checker SPI is tri-core in contract/ts, and the reusable Theory impls a consumer
// binds (e.g. AlwaysAdmit, ArithmeticTheory) live HERE, beside the SPI. So this is
// where a TS consumer binds the text relations.
//
// # The operand domain (raw Atom bytes, NOT the utf8-text embedding)
//
// Operands are RAW Atom bytes — exactly what the search builtins read and what the Rust
// TextTheory decides over. The utf8-text *embedding* is a Tuple, so it is NOT a bare
// Atom and therefore does not hold (text_does_not_hold). Matching is byte-level over
// the UTF-8 encoding, not codepoint-level.
//
// # Judgments (mirroring Rust/Go exactly)
//
// owns(pred): by NAME only (any arity) — contains, starts_with, ends_with. There is no
// nested expression grammar (unlike arithmetic operators), so nothing else to exclude.
// decide(atom) on a ground atom:
//   - non-UTF-8 predicate             -> Fails{text_unknown_predicate}  (defensive)
//   - owned name, arity != 2          -> Fails{text_bad_arity}
//   - both args bare Atoms, test true -> Holds
//   - false test OR a non-Atom arg
//     (a compound, or the utf8-text
//     embedding, which is a Tuple)    -> Fails{text_does_not_hold}
//
// An empty needle / prefix / suffix HOLDS (every byte-slice contains/starts with/ends
// with the empty slice) — these byte helpers agree with Rust's contains_subslice /
// slice::starts_with / slice::ends_with and Go's bytes.Contains/HasPrefix/HasSuffix.

import { decodeUtf8 } from "./utf8.js";
import { Atom, type Value } from "@bitspark/ontos-core";

import { Symbol, type GroundLiteral } from "./literal.js";
import { ComponentIdentity, DecisionCompletion, type Theory, TheoryOutcome } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** Lower-case hex of a byte string — a byte-exact, UTF-8-agnostic map/set key. */
function hexKey(bytes: Uint8Array): string {
  let s = "";
  for (const b of bytes) s += b.toString(16).padStart(2, "0");
  return s;
}

// The set of relation names TextTheory owns, mirroring Rust's TEXT_PREDICATES / Go's
// textPredicates. Keyed by byte-exact hex so an unregistered arity (or a non-UTF-8
// predicate) routes correctly — never throws.
const TEXT_PREDICATE_KEYS: ReadonlySet<string> = new Set(
  ["contains", "starts_with", "ends_with"].map((name) => hexKey(utf8Encoder.encode(name))),
);

/**
 * The config-pinned §5 Theory that owns the byte-string relations (contains/2,
 * starts_with/2, ends_with/2) and decides a GROUND text atom by a byte-level test over
 * the raw Atom operands. Pure / total / deterministic / config-free — a faithful mirror
 * of Rust's contract::text::TextTheory and the Go TextTheory.
 */
export class TextTheory implements Theory {
  /**
   * Owns reports whether `pred` names an owned text relation. Mirrors Rust's
   * TextTheory::owns / owns_name and Go's Owns — by name, at any arity.
   */
  owns(pred: Symbol): boolean {
    return TEXT_PREDICATE_KEYS.has(hexKey(pred.bytes()));
  }

  /**
   * Decides an owned GROUND text atom, byte-identically to the Rust/Go
   * TextTheory.decide. A ground text relation binds nothing, so it either Holds (the
   * byte test is true) or Fails with a pinned host-band sub-code.
   */
  decide(atom: GroundLiteral): TheoryOutcome {
    // Not one of ours: a routing safety net (check routes by owns, so this is
    // unreachable on a correctly-routed call — but stay total). Mirrors Rust/Go.
    if (!this.owns(atom.pred)) {
      return TheoryOutcome.NotMine;
    }
    // An owned name is always valid UTF-8 (the names are ASCII), but mirror Rust's
    // from_utf8 / Go's utf8.Valid guard so the non-UTF-8 defensive arm carries the
    // identical code on every path.
    let name: string;
    try {
      name = decodeUtf8(atom.pred.bytes());
    } catch {
      return TheoryOutcome.Fails("text_unknown_predicate");
    }

    switch (name) {
      case "contains":
        return decideTextRelation(atom.args, bytesContains);
      case "starts_with":
        return decideTextRelation(atom.args, bytesStartsWith);
      case "ends_with":
        return decideTextRelation(atom.args, bytesEndsWith);
      default:
        // Owned name routed here but not handled above — unreachable (the name set is
        // exactly the switch arms), but stay total.
        return TheoryOutcome.Fails("text_does_not_hold");
    }
  }

  /**
   * The theory's canonical component identity, logos-core/text-theory@1.0.0 with a zero
   * config digest — byte-identical to the Rust/Go theory's identity, so a CheckProfile
   * binding it derives the same theory binding (and thus the same stamped digest)
   * tri-core. The logos-core/ namespace is a STABLE IDENTITY, not a path (ADR 0014/0016).
   */
  identity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/text-theory"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  /** #3142: every text decision completes (a byte comparison of two ground atoms). */
  completion(_pred: Symbol): DecisionCompletion {
    return DecisionCompletion.StopsAreTyped;
  }
}

/** Builds the standard text Theory (no configuration). */
export function newTextTheory(): TextTheory {
  return new TextTheory();
}

/**
 * The bytes of a bare Atom, or `undefined` for any non-atom value (a compound Tuple —
 * including the utf8-text embedding — which a binary text test cannot run over). Mirrors
 * the Rust atom_bytes accessor (and the search builtins).
 */
function atomBytes(v: Value): Uint8Array | undefined {
  return v instanceof Atom ? v.bytes() : undefined;
}

/**
 * Decides a binary byte-string relation: arity must be 2; both args must be bare Atoms;
 * then `test(arg0Bytes, arg1Bytes)`. Mirrors Rust's decide_relation (and the search-side
 * builtins): a non-atom arg or a false test is text_does_not_hold; a non-2 arity has no
 * such relation (text_bad_arity).
 */
function decideTextRelation(
  args: readonly Value[],
  test: (text: Uint8Array, sub: Uint8Array) => boolean,
): TheoryOutcome {
  if (args.length !== 2) {
    return TheoryOutcome.Fails("text_bad_arity");
  }
  const lhs = atomBytes(args[0]!);
  const rhs = atomBytes(args[1]!);
  if (lhs !== undefined && rhs !== undefined && test(lhs, rhs)) {
    return TheoryOutcome.Holds;
  }
  return TheoryOutcome.Fails("text_does_not_hold");
}

/**
 * Whether `haystack` contains `needle` as a contiguous byte subslice. An empty needle is
 * contained in everything. Byte-for-byte identical to Rust's contains_subslice and Go's
 * bytes.Contains — the search/check shared semantics.
 */
function bytesContains(haystack: Uint8Array, needle: Uint8Array): boolean {
  if (needle.length === 0) {
    return true;
  }
  if (needle.length > haystack.length) {
    return false;
  }
  outer: for (let i = 0; i + needle.length <= haystack.length; i += 1) {
    for (let j = 0; j < needle.length; j += 1) {
      if (haystack[i + j] !== needle[j]) {
        continue outer;
      }
    }
    return true;
  }
  return false;
}

/** Whether `text` begins with `prefix` (byte-level). The empty prefix always matches. */
function bytesStartsWith(text: Uint8Array, prefix: Uint8Array): boolean {
  if (prefix.length > text.length) {
    return false;
  }
  for (let i = 0; i < prefix.length; i += 1) {
    if (text[i] !== prefix[i]) {
      return false;
    }
  }
  return true;
}

/** Whether `text` ends with `suffix` (byte-level). The empty suffix always matches. */
function bytesEndsWith(text: Uint8Array, suffix: Uint8Array): boolean {
  if (suffix.length > text.length) {
    return false;
  }
  const offset = text.length - suffix.length;
  for (let i = 0; i < suffix.length; i += 1) {
    if (text[offset + i] !== suffix[i]) {
      return false;
    }
  }
  return true;
}
