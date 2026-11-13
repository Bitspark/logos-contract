// ArithmeticTheory — the TS binding of logos-core's exact-integer arithmetic
// Theory, a judgment-for-judgment mirror of the Rust ArithmeticTheory in
// core/rs/src/builtins.rs and the Go ArithmeticTheory in contract/go/arithmetic.go.
// [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification: a program
// that uses the arithmetic relations (is / =:= / =\= / < / > / >= / =<) can now be
// CHECKED in TS, because the same decision the Rust core makes is reproduced
// here byte-for-byte. All three cores agree on EVERY ground arithmetic atom — the §7
// dual-conformance law and the issue-#95 byte-parity requirement (TS sibling, #154).
//
// # The home (why contract/ts)
//
// Rust's ArithmeticTheory lives in logos-core (core/rs). TS has no core tier; the
// checker SPI is tri-core in contract/ts, and the reusable Theory/RuleAdmissibility
// impls a consumer binds (e.g. AlwaysAdmit) live HERE, beside the SPI. So this is
// where a TS consumer binds arithmetic — alongside AlwaysAdmit — exactly as a Rust
// consumer binds logos_core::builtins::ArithmeticTheory and a Go consumer binds
// contract.NewArithmeticTheory beside the contract.
//
// # The numeric domain (frozen ontos-data int, NOT a re-invented parse)
//
// Every integer is the FROZEN ontos-data §5.1 `int` embedding
// Tuple(Atom("int"), Atom(sign‖big-endian-minimal-magnitude)). This file reads and
// builds those values through @bitspark/ontos-data's readInt / encodeInt over the
// native `bigint` — the SAME canonical bytes the Rust intval module delegates to
// (ontos_data::read_int / encode_int) and Go reads via ontos/data. The domain is
// unbounded (bigint), matching Rust's hand-rolled unbounded BigInt and Go's math/big:
// no fixed-width overflow, no float.
//
// # Judgments (mirroring Rust/Go exactly)
//
// owns(pred): by NAME only (any arity, byte-exact) for the seven arithmetic
// relations. The expression operators (+ - * / // mod abs min max) are never goals,
// so they are NOT owned. decideGround(atom) on a ground atom:
//   - not owned                      -> disowned                    (routed away by check)
//   - owned name, unregistered arity -> Fails{arith_bad_arity}      (e.g. is/3, </1)
//   - registered, evaluates to true  -> Holds
//   - registered, evaluates to false
//     OR an unevaluable expression
//     (unbound never occurs in a ground
//     atom; non-int atom / unknown op /
//     div-by-zero make the goal FAIL) -> Fails{arith_does_not_hold}
//
// (The Rust/Go arm Fails{arith_unknown_predicate} is reachable only on a non-UTF-8
// predicate; since `owns` already gated by byte-exact match against the ASCII
// relation names, it is unreachable on a routed call but preserved here for a
// byte-identical code on that defensive path.)

import { decodeUtf8 } from "./utf8.js";
import { Atom, Tuple, equals, type Value } from "@bitspark/ontos-core";
import { encodeInt, readInt } from "@bitspark/ontos-data";

import {
  completed,
  notCompleted,
  stop,
  theoryFails,
  theoryHolds,
  type NonCompletion,
  TheoryGround,
} from "./completion.js";
import { BigDecimal, type DecimalResult } from "./decval.js";
import { Symbol, type GroundLiteral } from "./literal.js";
import { ComponentIdentity, DecisionCompletion, type Theory } from "./spi.js";

// A numeric value the arithmetic evaluator produces and applyOperator combines: an exact
// integer OR an exact decimal (#331), mirroring Rust's arithmetic::Num and Go's num. The
// two are DISTINCT sorts — int(5) and decimal(5,0) are different terms, so `5 is 2+3.0`
// FAILS while `5.0 is 2+3.0` HOLDS (numToTerm keeps the sort). But the comparisons order
// by VALUE across sorts (numCmpValue), so `2 =:= 2.0` HOLDS. An all-integer expression
// stays integer (byte-identical to the pre-decimal path); a decimal operand promotes it.
type Num = { dec: false; i: bigint } | { dec: true; d: BigDecimal };

const numInt = (i: bigint): Num => ({ dec: false, i });
const numDec = (d: BigDecimal): Num => ({ dec: true, d });

/** Lower to the canonical embedding of the value's sort — int(…) or decimal(…). */
function numToTerm(n: Num): Value {
  return n.dec ? n.d.toTerm() : encodeInt(n.i);
}

/** Total VALUE order across sorts (so `2 =:= 2.0`): a mixed pair promotes the integer. */
function numCmpValue(a: Num, b: Num): number {
  if (!a.dec && !b.dec) return cmpBig(a.i, b.i);
  if (a.dec && b.dec) return a.d.cmp(b.d);
  if (!a.dec && b.dec) return BigDecimal.fromBigInt(a.i).cmp(b.d);
  if (a.dec && !b.dec) return a.d.cmp(BigDecimal.fromBigInt(b.i));
  return 0; // unreachable (all four sort combinations are covered above)
}

/** Promote to the decimal domain (for a mixed-sort binary operator). */
function numToDecimal(n: Num): BigDecimal {
  return n.dec ? n.d : BigDecimal.fromBigInt(n.i);
}

function numNegate(n: Num): Num {
  return n.dec ? numDec(n.d.negate()) : numInt(-n.i);
}

function numAbs(n: Num): Num {
  return n.dec ? numDec(n.d.abs()) : numInt(n.i < 0n ? -n.i : n.i);
}

const utf8Encoder = new TextEncoder();

/** Lower-case hex of a byte string — a byte-exact, UTF-8-agnostic map/set key. */
function hexKey(bytes: Uint8Array): string {
  let s = "";
  for (const b of bytes) s += b.toString(16).padStart(2, "0");
  return s;
}

// The set of relation names ArithmeticTheory owns, mirroring Rust's
// ARITHMETIC_PREDICATES / Go's arithmeticPredicates. Keyed by byte-exact hex so an
// unregistered arity (or a non-UTF-8 predicate) routes correctly — never throws.
const ARITHMETIC_PREDICATE_KEYS: ReadonlySet<string> = new Set(
  ["is", "=:=", "=\\=", "<", ">", ">=", "=<"].map((name) => hexKey(utf8Encoder.encode(name))),
);

/**
 * The config-pinned §5 Theory that owns the arithmetic relations (is/2, =:= =\= < >
 * >= =<) and decides a GROUND arithmetic atom by exact-integer evaluation over the
 * frozen ontos-data int embedding. Pure / total / deterministic / config-free — a
 * faithful mirror of Rust's logos_core::builtins::ArithmeticTheory and the Go
 * ArithmeticTheory.
 */
export class ArithmeticTheory implements Theory {
  /**
   * Owns reports whether `pred` names an owned arithmetic relation. Mirrors Rust's
   * ArithmeticTheory::owns / owns_name and Go's Owns — by name, at any arity.
   */
  owns(pred: Symbol): boolean {
    return ARITHMETIC_PREDICATE_KEYS.has(hexKey(pred.bytes()));
  }


  /**
   * Decides an owned GROUND arithmetic atom, byte-identically to the Rust/Go
   * ArithmeticTheory.decide_ground (#3126). A ground arithmetic relation binds nothing, so it
   * Holds, Fails with a pinned host-band sub-code (a domain error is the language's false), or is
   * not decided (an evaluation past a work cap, never a false).
   */
  decideGround(atom: GroundLiteral): TheoryGround {
    // Not one of ours: check routes by owns, so this is the theory contradicting its own routing,
    // the inconsistent_theory fault. Stay total. Mirrors Rust/Go.
    if (!this.owns(atom.pred)) {
      return TheoryGround.disowned();
    }
    // An owned name is always valid UTF-8 (the names are ASCII), but mirror Rust's
    // from_utf8 / Go's utf8.Valid guard so the non-UTF-8 defensive arm carries the
    // identical code on every path.
    let name: string;
    try {
      name = decodeUtf8(atom.pred.bytes());
    } catch {
      return arithFails("arith_unknown_predicate");
    }

    switch (name) {
      case "is":
        return decideIs(atom.args);
      case "=:=":
        return decideCompare(atom.args, (c) => c === 0);
      case "=\\=":
        return decideCompare(atom.args, (c) => c !== 0);
      case "<":
        return decideCompare(atom.args, (c) => c < 0);
      case ">":
        return decideCompare(atom.args, (c) => c > 0);
      case ">=":
        return decideCompare(atom.args, (c) => c >= 0);
      case "=<":
        return decideCompare(atom.args, (c) => c <= 0);
      default:
        // Owned name routed here but not handled above — unreachable (the name set
        // is exactly the switch arms), but stay total.
        return arithFails(ARITH_DOES_NOT_HOLD);
    }
  }

  /**
   * The theory's canonical component identity, logos-core/arithmetic-theory@1.0.0
   * with a zero config digest — byte-identical to the Rust/Go theory's identity, so a
   * CheckProfile binding it derives the same theory binding (and thus the same
   * stamped digest) tri-core.
   */
  identity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/arithmetic-theory"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  /**
   * #3142, PER THEORY (seat:caa's rulings on #3142 and on #3189, Q3): every arithmetic stop is typed.
   * Its one stop, decimal alignment past MAX_DECIMAL_SCALE_SHIFT (#3126; #3123 removed the depth
   * capacity), is `decideGround`'s `not_completed(work_cap)`, never `Fails` (#3313), and `check`
   * refuses it by name. Arithmetic still stops, so it is not "complete".
   */
  completion(_pred: Symbol): DecisionCompletion {
    return DecisionCompletion.StopsAreTyped;
  }
}

/** Builds the standard arithmetic Theory (no configuration). */
export function newArithmeticTheory(): ArithmeticTheory {
  return new ArithmeticTheory();
}

/** The code a false arithmetic relation names: a relation over values that does not hold, or an expression with no value. */
const ARITH_DOES_NOT_HOLD = "arith_does_not_hold";

/** The false arm with `code`. */
function arithFails(code: string): TheoryGround {
  return completed(theoryFails(code));
}

/** Holds when `holds`, else the relation's false. */
function arithHoldsIf(holds: boolean): TheoryGround {
  return holds ? completed(theoryHolds) : arithFails(ARITH_DOES_NOT_HOLD);
}

/**
 * Why an arithmetic expression has no value in the language (#3161), Rust's `DomainError`: every
 * failure ADR 0022 defines. The goal over it is false, a decided answer. A work cap is not here: it
 * is an {@link Evaluation}'s stop, because the value exists and was not computed.
 */
export type DomainError =
  | "not_a_number"
  | "unknown_operator"
  | "division_by_zero"
  | "inexact_division"
  | "non_terminating"
  | "outside_domain";

/**
 * The false code a domain failure names in `decideGround` (seat:caa's condition on #3126): the ONE
 * function a domain failure's code comes from. Every domain failure names `arith_does_not_hold`, the
 * code a false arithmetic relation has always named in vectors/arithmetic.json. Rust's
 * `DomainError::code`.
 */
export function domainErrorCode(e: DomainError): string {
  switch (e) {
    case "not_a_number":
    case "unknown_operator":
    case "division_by_zero":
    case "inexact_division":
    case "non_terminating":
    case "outside_domain":
      return ARITH_DOES_NOT_HOLD;
    default: {
      const never: never = e;
      throw new Error(`arithmetic: ${JSON.stringify(never)} is not a domain error`);
    }
  }
}

/**
 * What evaluating an arithmetic expression establishes (#3161, research 0031 row 3), Rust's
 * `Evaluation`: a value; the language's answer that it has none (a {@link DomainError}, so a goal
 * over it is false); or a stop (the work cap, #3126), so a goal over it is not decided. No path
 * converts a stop into a domain error.
 */
type Evaluation =
  | { readonly kind: "value"; readonly value: Num }
  | { readonly kind: "no_value"; readonly error: DomainError }
  | { readonly kind: "stopped"; readonly cause: NonCompletion };

function valueOf(value: Num): Evaluation {
  return { kind: "value", value };
}

function noValue(error: DomainError): Evaluation {
  return { kind: "no_value", error };
}

/**
 * A decimal operation's result as an {@link Evaluation}: the ONE place a `DecimalError` is sorted
 * into the language's failure or the implementation's stop. The alignment cap is the only stop.
 */
function decimalStep<T>(result: DecimalResult<T>, wrap: (v: T) => Num): Evaluation {
  if (result.ok) return valueOf(wrap(result.value));
  switch (result.error) {
    case "division_by_zero":
      return noValue("division_by_zero");
    case "non_terminating":
      return noValue("non_terminating");
    case "outside_domain":
      return noValue("outside_domain");
    case "alignment_cap":
      return { kind: "stopped", cause: stop("work_cap", "literal") };
    default: {
      const never: never = result.error;
      throw new Error(`arithmetic: ${JSON.stringify(never)} is not a decimal error`);
    }
  }
}

/**
 * An operand's value, or the decision its evaluation already settles: a domain error is the
 * relation's false, named by its code; a stop is not decided.
 */
function settle(e: Evaluation): { readonly value: Num } | { readonly settled: TheoryGround } {
  switch (e.kind) {
    case "value":
      return { value: e.value };
    case "no_value":
      return { settled: arithFails(domainErrorCode(e.error)) };
    case "stopped":
      return { settled: notCompleted(e.cause) };
    default: {
      const never: never = e;
      throw new Error(`arithmetic: an evaluation nobody built: ${JSON.stringify(never)}`);
    }
  }
}

/**
 * Decides `is/2`: evaluate the RHS expression and compare the LHS (a ground value) to the canonical
 * embedding of its value. Mirrors Rust's decide_is.
 *
 *   - wrong arity (not 2)    -> Fails{arith_bad_arity}    (no is/N builtin)
 *   - RHS has no value       -> the domain error's code, arith_does_not_hold (the goal fails)
 *   - RHS past a work cap    -> not decided (#3126)
 *   - LHS != its value       -> arith_does_not_hold
 *   - LHS == its value       -> Holds
 */
function decideIs(args: readonly Value[]): TheoryGround {
  if (args.length !== 2) {
    return arithFails("arith_bad_arity");
  }
  const rhs = settle(evalArith(args[1]!));
  if ("settled" in rhs) return rhs.settled;
  // `is` unifies arg0 with the embedding of the result's SORT (int(…) or decimal(…),
  // #331). The atom is ground, so "unify" is structural equality against the canonical
  // embedding: a decimal result lowers to decimal(…), so `5 is 2+3.0` fails and
  // `5.0 is 2+3.0` holds.
  return arithHoldsIf(equals(args[0]!, numToTerm(rhs.value)));
}

/**
 * Decides one of the six arithmetic comparisons: evaluate both operands and accept iff
 * `accept(cmp(a, b))`. A non-2 arity has no relation (arith_bad_arity). The operands are evaluated
 * left to right and the first that gives no value settles the comparison, as a stop inside one
 * expression does: a domain error makes it false (its code), a work cap leaves it not decided
 * (#3126). Mirrors Rust's decide_compare.
 */
function decideCompare(args: readonly Value[], accept: (c: number) => boolean): TheoryGround {
  if (args.length !== 2) {
    return arithFails("arith_bad_arity");
  }
  const a = settle(evalArith(args[0]!));
  if ("settled" in a) return a.settled;
  const b = settle(evalArith(args[1]!));
  if ("settled" in b) return b.settled;
  // Compare by VALUE across the int/decimal sorts (#331), so `2 =:= 2.0` holds.
  return arithHoldsIf(accept(numCmpValue(a.value, b.value)));
}

/** Three-way compare of two bigints to {-1, 0, 1} — the sign of a − b (Rust BigInt::cmp). */
function cmpBig(a: bigint, b: bigint): number {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

/**
 * Evaluates an arithmetic-expression value to an exact bigint, mirroring Rust's
 * eval_arith and Go's evalArith. The grammar (over a ground value — there are no Vars
 * in a ground atom, so the unbound-variable arm of Rust's eval is statically absent):
 *   - an int embedding Tuple(Atom("int"), Atom(payload)) -> its integer value;
 *   - an operator compound Tuple(Atom(op), arg…) for a known op/arity -> combine;
 *   - anything else (a bare/decimal atom, an unknown operator, the wrong arity for an
 *     operator) -> a {@link DomainError}, the language's answer that it has no value;
 *   - an exceeded decimal scale alignment -> a stop (#3126), not decided.
 *
 * Never a throw on an input. There is no depth at which it stops (#3123): the walk keeps its place on an explicit heap stack of
 * {@link ArithFrame}s, so a deep expression evaluates like a shallow one and no JS-stack
 * property enters the answer. Until #3123 a recursive walk stopped at 256 levels and the stop
 * was read as a failure, so a capacity became a decided false that a negation or a closure read
 * as knowledge. Operands are evaluated left to right and each compound is applied after its
 * operands, the order the recursion used.
 */
function evalArith(root: Value): Evaluation {
  const work: ArithFrame[] = [{ op: "eval", value: root }];
  const vals: Num[] = [];
  for (let frame = work.pop(); frame !== undefined; frame = work.pop()) {
    switch (frame.op) {
      case "eval": {
        const v = frame.value;
        // A number leaf: the frozen ontos-data int embedding, then the decimal embedding (#331).
        // readInt throws on any non-int; BigDecimal.fromTerm returns undefined on any non-decimal.
        // Each is tried only on a tuple headed by its own label, a necessary condition of both
        // embeddings, so an operator node costs no thrown exception (the readers' throw made a
        // deep expression's walk cost tens of microseconds a level).
        const label = headLabel(v);
        if (label === "int") {
          let int: bigint | undefined;
          try {
            int = readInt(v);
          } catch {
            // not a canonical int embedding — the operator grammar decides it below.
          }
          if (int !== undefined) {
            vals.push(numInt(int));
            break;
          }
        } else if (label === "decimal") {
          const dec = BigDecimal.fromTerm(v);
          if (dec !== undefined) {
            vals.push(numDec(dec));
            break;
          }
        }
        if (!(v instanceof Tuple)) {
          // A bare or number-shaped atom is not an evaluable number.
          return noValue("not_a_number");
        }
        const items = v.items();
        if (items.length === 0) {
          return noValue("not_a_number");
        }
        const head = items[0]!;
        if (!(head instanceof Atom)) {
          // Head child is not an operator atom.
          return noValue("not_a_number");
        }
        let operator: string;
        try {
          operator = decodeUtf8(head.bytes());
        } catch {
          // A non-UTF-8 operator atom is an unknown operator (Go: string(bytes) never
          // matches a known op; Rust: from_utf8 err -> unknown).
          return noValue("unknown_operator");
        }
        // The apply runs after every operand: it is pushed first (LIFO), and the operands in
        // reverse, so the leftmost is evaluated first.
        work.push({ op: "apply", operator, base: vals.length, arity: items.length - 1 });
        for (let i = items.length - 1; i >= 1; i -= 1) {
          work.push({ op: "eval", value: items[i]! });
        }
        break;
      }
      case "apply": {
        if (vals.length - frame.base !== frame.arity) {
          throw new Error(
            `arithmetic walk: an apply step found ${vals.length - frame.base} values above its base, want its arity ${frame.arity}`,
          );
        }
        const result = applyOperator(frame.operator, vals.splice(frame.base, frame.arity));
        if (result.kind !== "value") {
          return result;
        }
        vals.push(result.value);
        break;
      }
      default: {
        const never: never = frame;
        throw new Error(`arithmetic walk: a frame with no step: ${JSON.stringify(never)}`);
      }
    }
  }
  // Every compound consumed its operands and pushed one value, so the root's is the only one.
  if (vals.length !== 1) {
    throw new Error(`arithmetic walk: the root left ${vals.length} values`);
  }
  return valueOf(vals[0]!);
}

/**
 * One step of {@link evalArith}'s walk. The walk's control lives in the explicit `op` tag, never in
 * the value stack or the input (research 0030: no input value can be read as a control marker).
 *   - `eval`: evaluate `value` and push its number onto the value stack;
 *   - `apply`: the `arity` values from `base` up are `operator`'s operands, in order; replace them
 *     with the result.
 */
type ArithFrame =
  | { readonly op: "eval"; readonly value: Value }
  | { readonly op: "apply"; readonly operator: string; readonly base: number; readonly arity: number };

const INT_LABEL = utf8Encoder.encode("int");
const DECIMAL_LABEL = utf8Encoder.encode("decimal");

/** Whether `bytes` equals `label`, byte for byte. */
function bytesEqual(bytes: Uint8Array, label: Uint8Array): boolean {
  if (bytes.length !== label.length) return false;
  for (let i = 0; i < bytes.length; i += 1) {
    if (bytes[i] !== label[i]) return false;
  }
  return true;
}

/**
 * "int" or "decimal" when `v` is a tuple whose head is that label's atom, the shape both number
 * embeddings require; otherwise undefined. Only a necessary condition: the embedding's reader
 * still decides the rest.
 */
function headLabel(v: Value): "int" | "decimal" | undefined {
  if (!(v instanceof Tuple)) return undefined;
  const head = v.items()[0];
  if (!(head instanceof Atom)) return undefined;
  const bytes = head.bytes();
  if (bytesEqual(bytes, INT_LABEL)) return "int";
  if (bytesEqual(bytes, DECIMAL_LABEL)) return "decimal";
  return undefined;
}

/**
 * Applies an arithmetic operator to its already-evaluated operands, mirroring Rust's
 * apply_operator EXACTLY: same operator/arity set, same exact-/truncating-division
 * split, same floored mod, same domain error on an unknown operator or a zero divisor, and
 * the same stop past the decimal work cap (#3126). The /-operator is EXACT division: a
 * non-even quotient has no value (no fractional integer, never a float — Rust's div_exact).
 */
function applyOperator(op: string, vals: readonly Num[]): Evaluation {
  switch (op) {
    case "+":
      if (vals.length === 2) return numAdd(vals[0]!, vals[1]!);
      break;
    case "-":
      if (vals.length === 2) return numSub(vals[0]!, vals[1]!);
      if (vals.length === 1) return valueOf(numNegate(vals[0]!)); // unary minus
      break;
    case "*":
      if (vals.length === 2) return numMul(vals[0]!, vals[1]!);
      break;
    case "abs":
      if (vals.length === 1) return valueOf(numAbs(vals[0]!));
      break;
    case "min":
      // Order by value across sorts; return the chosen operand in its OWN sort (ties
      // keep the left operand).
      if (vals.length === 2) return valueOf(numCmpValue(vals[0]!, vals[1]!) > 0 ? vals[1]! : vals[0]!);
      break;
    case "max":
      if (vals.length === 2) return valueOf(numCmpValue(vals[0]!, vals[1]!) < 0 ? vals[1]! : vals[0]!);
      break;
    case "/":
      // Exact division in BOTH domains: integer (even quotient only) / decimal
      // (terminating-in-base-10 only). Fail loud otherwise — never a float (#331).
      if (vals.length === 2) return numDiv(vals[0]!, vals[1]!);
      break;
    case "//":
      // Truncating integer division (toward zero), same convention in both domains;
      // always an integer result. Fail loud on /0 (ADR 0022 Amendment).
      if (vals.length === 2) return numFloorDiv(vals[0]!, vals[1]!);
      break;
    case "mod":
      // ISO floored modulo (sign of the divisor), same convention in both domains;
      // result int for two ints, decimal when an operand is decimal. Fail loud on /0.
      if (vals.length === 2) return numMod(vals[0]!, vals[1]!);
      break;
  }
  // Unknown operator/arity.
  return noValue("unknown_operator");
}

/**
 * a + b: integer-closed when both are integers (byte-identical to the pre-#331 path),
 * else promoted to the decimal domain.
 */
function numAdd(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) return valueOf(numInt(a.i + b.i));
  return decimalStep(numToDecimal(a).add(numToDecimal(b)), numDec);
}

function numSub(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) return valueOf(numInt(a.i - b.i));
  return decimalStep(numToDecimal(a).sub(numToDecimal(b)), numDec);
}

function numMul(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) return valueOf(numInt(a.i * b.i));
  return decimalStep(numToDecimal(a).mul(numToDecimal(b)), numDec);
}

/** a / b: exact integer division (even quotient) or exact terminating decimal division. */
function numDiv(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) {
    if (b.i === 0n) return noValue("division_by_zero");
    const q = divExact(a.i, b.i);
    return q === undefined ? noValue("inexact_division") : valueOf(numInt(q));
  }
  return decimalStep(numToDecimal(a).divTerminating(numToDecimal(b)), numDec);
}

/**
 * a // b — TRUNCATING integer division (toward zero), the same rounding convention in both
 * domains (ADR 0022 Amendment). Integer: the truncated quotient (byte-identical to the
 * pre-decimal path). Decimal (any operand a decimal, the integers promoted): the exact
 * quotient of the scaled mantissas truncated toward zero (divTruncInt) — e.g. -7.5 // 2 =
 * -3 (NOT floor -4). The result is always an INTEGER in both domains. division_by_zero on /0.
 */
function numFloorDiv(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) {
    const q = divTrunc(a.i, b.i);
    return q === undefined ? noValue("division_by_zero") : valueOf(numInt(q));
  }
  return decimalStep(numToDecimal(a).divTruncInt(numToDecimal(b)), numInt);
}

/**
 * a mod b — ISO FLOORED modulo (sign of the divisor), the same sign convention in both
 * domains (ADR 0022 Amendment). Integer: the floored remainder (byte-identical to the
 * pre-decimal path), result INTEGER. Decimal (any operand a decimal, the integers
 * promoted): a − floor(a/b)·b (moduloFloored) — always exact, result DECIMAL — e.g.
 * 7.5 mod 0.25 = 0.0, -7.5 mod 2 = 0.5 (sign follows the divisor). division_by_zero on /0.
 */
function numMod(a: Num, b: Num): Evaluation {
  if (!a.dec && !b.dec) {
    const r = modFloored(a.i, b.i);
    return r === undefined ? noValue("division_by_zero") : valueOf(numInt(r));
  }
  return decimalStep(numToDecimal(a).moduloFloored(numToDecimal(b)), numDec);
}

/**
 * Returns a/b iff b divides a evenly; undefined on a zero divisor or a non-zero
 * remainder. Mirrors Rust's BigInt::div_exact: there is no fractional integer, so an
 * inexact division is a domain error (the goal fails), never a truncation and never a
 * float. `bigint` division truncates toward zero and `%` is the truncated remainder.
 */
function divExact(a: bigint, b: bigint): bigint | undefined {
  if (b === 0n) {
    return undefined;
  }
  if (a % b !== 0n) {
    return undefined; // inexact: operands do not divide evenly
  }
  return a / b;
}

/**
 * Returns the truncating quotient a // b (toward zero); undefined on /0. Mirrors
 * Rust's // (div_rem_trunc quotient). `bigint` division truncates toward zero, like
 * Go's Quo.
 */
function divTrunc(a: bigint, b: bigint): bigint | undefined {
  if (b === 0n) {
    return undefined;
  }
  return a / b;
}

/**
 * Returns the ISO floored modulo `a mod b` (result takes the sign of the divisor b);
 * undefined on /0. Mirrors Rust's BigInt::modulo_floored and Go's modFloored.
 *
 * `bigint`'s `%` is the TRUNCATED remainder (sign of the dividend a), which differs
 * from ISO floored mod when the divisor is negative. So correct it onto the divisor's
 * side: floored mod differs from the truncated remainder exactly when r is non-zero
 * and its sign differs from the divisor's — then add the divisor.
 */
function modFloored(a: bigint, b: bigint): bigint | undefined {
  if (b === 0n) {
    return undefined;
  }
  let r = a % b; // truncated remainder: sign of the dividend a
  if (r !== 0n && r < 0n !== b < 0n) {
    r += b;
  }
  return r;
}
