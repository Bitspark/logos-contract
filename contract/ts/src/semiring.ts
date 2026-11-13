// The Semiring SPI and its registration audit (ADR 0031 D1, G3; v2 §14.3). [PROPOSED]
// (ADR 0035 D7: a new extension seam enters at [PROPOSED]; its vector parity is not a tier.)
// The TS binding of contract/rs/src/semiring.rs; contract/go/semiring.go is the third.
//
// A semiring is the algebra an annotated evaluation combines values in: add (⊕) joins
// alternative derivations, mul (⊗) joins the premises of one derivation, zero is the value
// of no derivation and one the value of an empty conjunction. ADR 0031 puts it on the path
// checkable theories already took: the checker may consult a semiring it did not link,
// because the verdict NAMES it by identity and what it names is pure.
//
// The obligations of an implementation:
//   - Pure, total over its carrier up to its declared capacity bounds, deterministic. add and
//     mul answer `not_an_element` exactly when an operand is not an element (isElement). On
//     elements they answer an element, the same one every time, or, for a result past a bound
//     the carrier declares, `stopped` with a capacity non-completion (ADR 0031 D1 as clarified
//     on #1821): not decided, never "no such element".
//   - Laws declared, never inferred. laws() declares the five optional laws of v2 §14.3. The
//     semiring axioms are not declarable: ⊕ is associative and commutative with identity
//     zero, ⊗ is associative with identity one, zero annihilates, and ⊗ distributes over ⊕.
//     LawDeclaration.commutative names ⊗; ⊕ is always commutative.
//   - Identity computed by the contract. semiringIdentity folds the declared laws into the
//     declared (id, version, configDigest), so changing a declared law changes the identity a
//     verdict names (ADR 0031 D1).
//
// What the audit can and cannot say: auditSemiring evaluates every axiom and every declared
// law over a finite sample set, in one pinned order (SEMIRING_AUDIT_ORDER), and reports the
// first counterexample. A finite sample can only refute a law, never prove one, so a passing
// audit is "no_counterexample": no counterexample in these samples, not "verified". A tuple on
// which an operation stopped is undecided, and a law no tuple decided is VACUOUS (verdict
// "vacuous"), which is a state, never a pass.

import { sha256 } from "@noble/hashes/sha2.js";
import { equals, type Value } from "@bitspark/ontos-core";
import { encodeInt, readInt } from "@bitspark/ontos-data";

import { type NonCompletion, stop } from "./completion.js";
import { ComponentIdentity } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** The domain separator of a semiring's computed identity digest ({@link semiringIdentityOf}). */
export function semiringIdentityPrefix(): Uint8Array {
  return utf8Encoder.encode("logos-core/semiring-identity/v1\n");
}

/**
 * The most caller samples {@link auditSemiring} evaluates. The audit is cubic in the sample
 * count, so a larger set is refused by name (`sample_limit`).
 */
export const SEMIRING_AUDIT_SAMPLE_LIMIT = 16;

/**
 * The five optional laws a semiring declares (v2 §14.3; ADR 0031 D1). Each is a CLAIM the
 * audit tests on samples, never a fact it proves.
 */
export interface LawDeclaration {
  /** `a ⊕ a = a`. */
  readonly idempotent: boolean;
  /** `one ⊕ a = one` (absorptive): the law a fixpoint argument over recursion relies on. */
  readonly bounded: boolean;
  /** The natural order (`a ≤ b` iff `a ⊕ c = b` for some `c`) is antisymmetric. */
  readonly monotone: boolean;
  /** `a ⊗ b = b ⊗ a` (a commutative semiring; ⊕ is commutative by axiom). */
  readonly commutative: boolean;
  /** ⊕ is cancellative (`a ⊕ b = a ⊕ c` implies `b = c`), so a contribution can be retracted. */
  readonly supportsRetraction: boolean;
}

/** The bit of each declarable law in {@link lawBits}. */
export const LAW_BITS = Object.freeze({
  idempotent: 1,
  bounded: 2,
  monotone: 4,
  commutative: 8,
  supportsRetraction: 16,
});

/** The declaration as one byte, the form {@link semiringIdentityOf} hashes. */
export function lawBits(laws: LawDeclaration): number {
  let bits = 0;
  if (laws.idempotent === true) bits |= LAW_BITS.idempotent;
  if (laws.bounded === true) bits |= LAW_BITS.bounded;
  if (laws.monotone === true) bits |= LAW_BITS.monotone;
  if (laws.commutative === true) bits |= LAW_BITS.commutative;
  if (laws.supportsRetraction === true) bits |= LAW_BITS.supportsRetraction;
  return bits;
}

/**
 * A law {@link auditSemiring} tests, by its wire name (the spelling vectors/semiring.json
 * pins): the ten axioms of a semiring over a carrier, then the five declarable laws.
 */
export type SemiringLaw =
  | "carrier"
  | "add_closed"
  | "mul_closed"
  | "add_associative"
  | "add_commutative"
  | "add_identity"
  | "mul_associative"
  | "mul_identity"
  | "annihilation"
  | "distributive"
  | "idempotent"
  | "bounded"
  | "monotone"
  | "commutative"
  | "supports_retraction";

/** The order {@link auditSemiring} tests the laws in; its first counterexample is the one it reports. */
export const SEMIRING_AUDIT_ORDER: readonly SemiringLaw[] = Object.freeze([
  "carrier",
  "add_closed",
  "mul_closed",
  "add_associative",
  "add_commutative",
  "add_identity",
  "mul_associative",
  "mul_identity",
  "annihilation",
  "distributive",
  "idempotent",
  "bounded",
  "monotone",
  "commutative",
  "supports_retraction",
] as const);

/**
 * Whether the audit tests `law` for a semiring with this declaration: every axiom always, a
 * declarable law only when it is declared.
 */
export function lawObliged(laws: LawDeclaration, law: SemiringLaw): boolean {
  switch (law) {
    case "carrier":
    case "add_closed":
    case "mul_closed":
    case "add_associative":
    case "add_commutative":
    case "add_identity":
    case "mul_associative":
    case "mul_identity":
    case "annihilation":
    case "distributive":
      return true;
    case "idempotent":
      return laws.idempotent === true;
    case "bounded":
      return laws.bounded === true;
    case "monotone":
      return laws.monotone === true;
    case "commutative":
      return laws.commutative === true;
    case "supports_retraction":
      return laws.supportsRetraction === true;
  }
  const unknown: never = law;
  throw new Error(`unknown semiring law ${String(unknown)}`);
}

/**
 * What a semiring operation answered (ADR 0031 D1, as clarified on #1821).
 *
 * An operation is total over its carrier up to the carrier's declared capacity bounds: on
 * elements it answers an element or, for a result past a bound the carrier declares,
 * `stopped` with a capacity non-completion. A stop is "not decided", never "no such element",
 * so a consumer reports it as a non-completion and never as a rejection.
 */
export type SemiringAnswer =
  | { readonly kind: "element"; readonly value: Value }
  | { readonly kind: "not_an_element" }
  | { readonly kind: "stopped"; readonly cause: NonCompletion };

/** The constructors of {@link SemiringAnswer}. */
export const SemiringAnswer = Object.freeze({
  /** The result, an element of the carrier. */
  element(value: Value): SemiringAnswer {
    return Object.freeze({ kind: "element", value } as const);
  },
  /** An operand is not an element of the carrier. */
  notAnElement(): SemiringAnswer {
    return NOT_AN_ELEMENT;
  },
  /**
   * The stop a carrier answers for a result past its declared capacity bound: a capacity
   * non-completion of this one operation (literal scope).
   */
  capacity(): SemiringAnswer {
    return Object.freeze({ kind: "stopped", cause: stop("capacity", "literal") } as const);
  },
});

const NOT_AN_ELEMENT: SemiringAnswer = Object.freeze({ kind: "not_an_element" } as const);

/**
 * A semiring the checker may consult (ADR 0031 D1). [PROPOSED]
 *
 * Elements are ontos values, so one interface carries every carrier. See the file comment
 * for the obligations an implementation takes on.
 */
export interface Semiring {
  /**
   * The (id, version, configDigest) the implementation declares. The identity a verdict
   * names is {@link semiringIdentity}, which folds {@link Semiring.laws} into it.
   */
  declaredIdentity(): ComponentIdentity;
  /** The optional laws this semiring claims (v2 §14.3). */
  laws(): LawDeclaration;
  /** The identity of ⊕: the value of no derivation. */
  zero(): Value;
  /** The identity of ⊗: the value of an empty conjunction. */
  one(): Value;
  /** Whether `value` is an element of the carrier. */
  isElement(value: Value): boolean;
  /** `a ⊕ b`; `not_an_element` exactly when an operand is not an element. */
  add(a: Value, b: Value): SemiringAnswer;
  /** `a ⊗ b`; `not_an_element` exactly when an operand is not an element. */
  mul(a: Value, b: Value): SemiringAnswer;
}

/**
 * The identity a semiring with this declared identity and these laws is named by:
 * (id, version, SHA-256(prefix ‖ len(id) ‖ id ‖ len(version) ‖ version ‖ configDigest ‖
 * laws)), each length a big-endian u64 and the laws {@link lawBits}. The id and version are
 * kept; the digest commits to the configuration AND the declared laws (ADR 0031 D1).
 */
export function semiringIdentityOf(declared: ComponentIdentity, laws: LawDeclaration): ComponentIdentity {
  const id = declared.id;
  const version = declared.version;
  const config = declared.configDigest;
  const digest = sha256(
    concatBytes([
      semiringIdentityPrefix(),
      u64be(id.length),
      id,
      u64be(version.length),
      version,
      config,
      Uint8Array.of(lawBits(laws)),
    ]),
  );
  return ComponentIdentity.of(id, version, digest);
}

/**
 * The identity `semiring` is named by: {@link semiringIdentityOf} over its declared identity
 * and its declared laws, each read once.
 */
export function semiringIdentity(semiring: Semiring): ComponentIdentity {
  const declared = semiring.declaredIdentity();
  return semiringIdentityOf(
    ComponentIdentity.of(declared.id, declared.version, declared.configDigest),
    captureLaws(semiring.laws()),
  );
}

/**
 * How many tuples of the evaluated set decided a law, and how many were undecided because an
 * operation the law names stopped. A law with no decided tuple is VACUOUS: the samples never
 * exercised it, which is a state of the audit, never a pass (design/0004).
 */
export interface LawTally {
  readonly law: SemiringLaw;
  /** Tuples on which every operation the law names answered, and the law held. */
  readonly decided: number;
  /** Tuples on which an operation the law names stopped. */
  readonly undecided: number;
}

/** No decided tuple exercised the law. */
export function lawIsVacuous(tally: LawTally): boolean {
  return tally.decided === 0;
}

/** The verdict of {@link auditSemiring}. */
export type SemiringAudit =
  /** No counterexample in the samples, and every law tested was decided on some tuple. NOT a proof. */
  | { readonly kind: "no_counterexample"; readonly laws: readonly LawTally[] }
  /** No counterexample, but a law tested is vacuous (no tuple decided it). Not a pass. */
  | { readonly kind: "vacuous"; readonly laws: readonly LawTally[] }
  /** The first law a decided tuple refutes, with the elements that refute it. Registration is rejected. */
  | { readonly kind: "counterexample"; readonly law: SemiringLaw; readonly witness: readonly Value[] }
  /** More samples than {@link SEMIRING_AUDIT_SAMPLE_LIMIT}; nothing was evaluated. */
  | { readonly kind: "sample_limit"; readonly given: number; readonly limit: number };

/**
 * Audit `semiring` over `samples` (v2 §14.3 `audit_semiring`; ADR 0031 G3).
 *
 * The evaluated set is [zero, one, samples…] in that order. The laws are tested in
 * {@link SEMIRING_AUDIT_ORDER}, every axiom and each law `laws()` declares; within a law the
 * elements are enumerated in set order, the first operand outermost. Each tuple is read in
 * three values: the law holds, fails, or is undecided because an operation it names stopped
 * (strong Kleene: a failing conjunct fails the tuple even beside a stop). An operation
 * answering `not_an_element` on elements fails the law it was evaluated for. The first failing
 * tuple is the verdict; otherwise a law no tuple decided makes the verdict `vacuous`. The
 * declared laws are read once, the samples are copied before any call, and each answer is read
 * once.
 */
export function auditSemiring(semiring: Semiring, samples: readonly Value[]): SemiringAudit {
  const given = [...samples];
  if (given.length > SEMIRING_AUDIT_SAMPLE_LIMIT) {
    const refused: SemiringAudit = { kind: "sample_limit", given: given.length, limit: SEMIRING_AUDIT_SAMPLE_LIMIT };
    return Object.freeze(refused);
  }
  const declared = captureLaws(semiring.laws());
  const zero = semiring.zero();
  const one = semiring.one();
  const audit = new Audit(semiring, [zero, one, ...given], zero, one);
  const laws: LawTally[] = [];
  for (const law of SEMIRING_AUDIT_ORDER) {
    if (!lawObliged(declared, law)) continue;
    const tally = { law, decided: 0, undecided: 0 };
    const witness = audit.counterexample(law, tally);
    if (witness !== undefined) {
      const refuted: SemiringAudit = { kind: "counterexample", law, witness: Object.freeze(witness) };
      return Object.freeze(refuted);
    }
    laws.push(Object.freeze(tally));
  }
  const frozen = Object.freeze(laws);
  const verdict: SemiringAudit = laws.some(lawIsVacuous)
    ? { kind: "vacuous", laws: frozen }
    : { kind: "no_counterexample", laws: frozen };
  return Object.freeze(verdict);
}

/** A declaration read once, as plain booleans. */
function captureLaws(declared: LawDeclaration): LawDeclaration {
  return Object.freeze({
    idempotent: declared.idempotent === true,
    bounded: declared.bounded === true,
    monotone: declared.monotone === true,
    commutative: declared.commutative === true,
    supportsRetraction: declared.supportsRetraction === true,
  });
}

/** An answer read once: the element, or which non-answer it is. */
type Reading = Value | "not_an_element" | "stopped";

function read(answer: SemiringAnswer): Reading {
  const kind = answer.kind;
  if (kind === "element") return answer.value;
  return kind === "stopped" ? "stopped" : "not_an_element";
}

/** A law's reading on one tuple: strong Kleene over the operations' answers. */
type Truth = "holds" | "fails" | "undecided";

function truthOf(holds: boolean): Truth {
  return holds ? "holds" : "fails";
}

function both(left: Truth, right: Truth): Truth {
  if (left === "fails" || right === "fails") return "fails";
  return left === "holds" && right === "holds" ? "holds" : "undecided";
}

function either(left: Truth, right: Truth): Truth {
  if (left === "holds" || right === "holds") return "holds";
  return left === "fails" && right === "fails" ? "fails" : "undecided";
}

function not(truth: Truth): Truth {
  return truth === "holds" ? "fails" : truth === "fails" ? "holds" : "undecided";
}

/** Both readings are the same element. A non-element fails; otherwise a stop is undecided. */
function same(left: Reading, right: Reading): Truth {
  if (left === "not_an_element" || right === "not_an_element") return "fails";
  if (left === "stopped" || right === "stopped") return "undecided";
  return truthOf(equals(left, right));
}

/** The reading is the element `expected`. */
function gives(answer: Reading, expected: Value): Truth {
  if (answer === "not_an_element") return "fails";
  if (answer === "stopped") return "undecided";
  return truthOf(equals(answer, expected));
}

/** Count one tuple's reading; `true` when it refutes the law. */
function count(tally: { decided: number; undecided: number }, truth: Truth): boolean {
  if (truth === "holds") tally.decided += 1;
  else if (truth === "undecided") tally.undecided += 1;
  return truth === "fails";
}

/** One audit run: the semiring and the evaluated set. */
class Audit {
  constructor(
    private readonly semiring: Semiring,
    private readonly set: readonly Value[],
    private readonly zero: Value,
    private readonly one: Value,
  ) {}

  /** `a ⊕ b` over readings; a non-element or a stop is carried unchanged. */
  private add(a: Reading, b: Reading): Reading {
    if (a === "not_an_element" || b === "not_an_element") return "not_an_element";
    if (a === "stopped" || b === "stopped") return "stopped";
    return read(this.semiring.add(a, b));
  }

  /** `a ⊗ b` over readings; a non-element or a stop is carried unchanged. */
  private mul(a: Reading, b: Reading): Reading {
    if (a === "not_an_element" || b === "not_an_element") return "not_an_element";
    if (a === "stopped" || b === "stopped") return "stopped";
    return read(this.semiring.mul(a, b));
  }

  /** `a ≤ b` in the natural order, witnessed inside the set (`a ⊕ c = b` for a sample `c`). */
  private below(a: Value, b: Value): Truth {
    let found: Truth = "fails";
    for (const c of this.set) found = either(found, gives(this.add(a, c), b));
    return found;
  }

  /** An operation's answer is an element, and the same one when asked again. */
  private closed(first: Reading, again: Reading): Truth {
    if (first === "not_an_element") return "fails";
    if (first === "stopped") return "undecided";
    return both(truthOf(this.semiring.isElement(first)), gives(again, first));
  }

  /** The first tuple of the set on which `law` fails, or `undefined`; `tally` counts the rest. */
  counterexample(law: SemiringLaw, tally: { decided: number; undecided: number }): Value[] | undefined {
    const each = (holds: (a: Value) => Truth): Value[] | undefined => {
      for (const a of this.set) if (count(tally, holds(a))) return [a];
      return undefined;
    };
    const pairs = (holds: (a: Value, b: Value) => Truth): Value[] | undefined => {
      for (const a of this.set) for (const b of this.set) if (count(tally, holds(a, b))) return [a, b];
      return undefined;
    };
    const triples = (holds: (a: Value, b: Value, c: Value) => Truth): Value[] | undefined => {
      for (const a of this.set)
        for (const b of this.set) for (const c of this.set) if (count(tally, holds(a, b, c))) return [a, b, c];
      return undefined;
    };
    switch (law) {
      case "carrier":
        return each((a) => truthOf(this.semiring.isElement(a)));
      case "add_closed":
        return pairs((a, b) => this.closed(this.add(a, b), this.add(a, b)));
      case "mul_closed":
        return pairs((a, b) => this.closed(this.mul(a, b), this.mul(a, b)));
      case "add_associative":
        return triples((a, b, c) => same(this.add(this.add(a, b), c), this.add(a, this.add(b, c))));
      case "add_commutative":
        return pairs((a, b) => same(this.add(a, b), this.add(b, a)));
      case "add_identity":
        return each((a) => both(gives(this.add(this.zero, a), a), gives(this.add(a, this.zero), a)));
      case "mul_associative":
        return triples((a, b, c) => same(this.mul(this.mul(a, b), c), this.mul(a, this.mul(b, c))));
      case "mul_identity":
        return each((a) => both(gives(this.mul(this.one, a), a), gives(this.mul(a, this.one), a)));
      case "annihilation":
        return each((a) => both(gives(this.mul(this.zero, a), this.zero), gives(this.mul(a, this.zero), this.zero)));
      case "distributive":
        return triples((a, b, c) =>
          both(
            same(this.mul(a, this.add(b, c)), this.add(this.mul(a, b), this.mul(a, c))),
            same(this.mul(this.add(a, b), c), this.add(this.mul(a, c), this.mul(b, c))),
          ),
        );
      case "idempotent":
        return each((a) => gives(this.add(a, a), a));
      case "bounded":
        return each((a) => gives(this.add(this.one, a), this.one));
      case "monotone":
        return pairs((a, b) => either(truthOf(equals(a, b)), either(not(this.below(a, b)), not(this.below(b, a)))));
      case "commutative":
        return pairs((a, b) => same(this.mul(a, b), this.mul(b, a)));
      case "supports_retraction":
        return triples((a, b, c) => either(truthOf(equals(b, c)), not(same(this.add(a, b), this.add(a, c)))));
    }
    const unknown: never = law;
    throw new Error(`unknown semiring law ${String(unknown)}`);
  }
}

/**
 * The counting semiring (ℕ, +, ×, 0, 1) (v2 §8.3 `Counting`; ADR 0031 D2), a core semiring.
 *
 * Its carrier is the non-negative integers in the frozen ontos-data int embedding,
 * unbounded (bigint), so add and mul are exact and total on elements. It declares monotone,
 * commutative and supportsRetraction; it is neither idempotent nor bounded. Identity
 * logos-core/counting-semiring@1.0.0, zero configuration.
 */
export function newCountingSemiring(): Semiring {
  return new CountingSemiring();
}

const COUNTING_LAWS: LawDeclaration = Object.freeze({
  idempotent: false,
  bounded: false,
  monotone: true,
  commutative: true,
  supportsRetraction: true,
});

class CountingSemiring implements Semiring {
  constructor() {
    Object.freeze(this);
  }

  declaredIdentity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/counting-semiring"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  laws(): LawDeclaration {
    return COUNTING_LAWS;
  }

  zero(): Value {
    return encodeInt(0n);
  }

  one(): Value {
    return encodeInt(1n);
  }

  isElement(value: Value): boolean {
    return natural(value) !== undefined;
  }

  add(a: Value, b: Value): SemiringAnswer {
    const x = natural(a);
    const y = natural(b);
    return x === undefined || y === undefined ? NOT_AN_ELEMENT : SemiringAnswer.element(encodeInt(x + y));
  }

  mul(a: Value, b: Value): SemiringAnswer {
    const x = natural(a);
    const y = natural(b);
    return x === undefined || y === undefined ? NOT_AN_ELEMENT : SemiringAnswer.element(encodeInt(x * y));
  }
}
Object.freeze(CountingSemiring.prototype);

/** The non-negative integer `value` embeds, or `undefined` when it is not one. */
function natural(value: Value): bigint | undefined {
  let n: bigint;
  try {
    n = readInt(value);
  } catch {
    return undefined;
  }
  return n < 0n ? undefined : n;
}

/** The 8-byte big-endian encoding of `n` (the u64 length prefix). */
function u64be(n: number): Uint8Array {
  const buf = new Uint8Array(8);
  new DataView(buf.buffer).setBigUint64(0, BigInt(n), false);
  return buf;
}

/** Concatenate byte slices into one buffer. */
function concatBytes(parts: readonly Uint8Array[]): Uint8Array {
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let offset = 0;
  for (const p of parts) {
    out.set(p, offset);
    offset += p.length;
  }
  return out;
}
