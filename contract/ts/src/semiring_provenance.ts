// The provenance core semiring ℕ[X] (v2 §8.3 Provenance; ADR 0031 D2): polynomials with natural
// coefficients over fact identities. [PROPOSED] The TS binding of
// contract/rs/src/semiring_provenance.rs.
//
// Its carrier was ruled on #1821 (2026-11-11): one canonical sorted encoding with integer
// coefficients. A polynomial is a Tuple of terms; a term is Tuple[int c, Tuple[x…]], its
// coefficient c >= 1 in the frozen ontos-data int embedding and its monomial the multiset of its
// variables, each any ground ontos value (a fact identity), in non-decreasing order of their
// ontos-codec bytes. The terms are in strictly increasing order of their monomials' codec bytes,
// so no monomial repeats. Zero is the empty Tuple; one is the single term 1·(). Coefficients are
// unbounded, so the operations never stop.

import { Tuple, tuple, type Value } from "@bitspark/ontos-core";
import { encode } from "@bitspark/ontos-codec";
import { encodeInt, readInt } from "@bitspark/ontos-data";

import { type LawDeclaration, type Semiring, SemiringAnswer } from "./semiring.js";
import { ComponentIdentity } from "./spi.js";

const utf8Encoder = new TextEncoder();

/** One term of a polynomial: its monomial's variables and its coefficient. */
interface PolyTerm {
  readonly key: Uint8Array;
  readonly variables: readonly Value[];
  readonly coefficient: bigint;
}

/** Unsigned lexicographic byte order. */
function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a[i] !== b[i]) return a[i]! - b[i]!;
  }
  return a.length - b.length;
}

function hexKey(bytes: Uint8Array): string {
  return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

/** The canonical polynomial `value` encodes, keyed by its monomials' codec bytes, or `undefined`. */
function polynomial(value: Value): Map<string, PolyTerm> | undefined {
  if (!(value instanceof Tuple)) return undefined;
  const terms = new Map<string, PolyTerm>();
  let last: Uint8Array | undefined;
  for (const term of value.items()) {
    if (!(term instanceof Tuple)) return undefined;
    const pair = term.items();
    if (pair.length !== 2) return undefined;
    let coefficient: bigint;
    try {
      coefficient = readInt(pair[0]!);
    } catch {
      return undefined;
    }
    if (coefficient <= 0n) return undefined;
    const monomial = pair[1]!;
    if (!(monomial instanceof Tuple)) return undefined;
    const variables = [...monomial.items()];
    for (let j = 1; j < variables.length; j++) {
      if (compareBytes(encode(variables[j - 1]!), encode(variables[j]!)) > 0) return undefined;
    }
    const key = encode(monomial);
    if (last !== undefined && compareBytes(last, key) >= 0) return undefined;
    last = key;
    terms.set(hexKey(key), { key, variables, coefficient });
  }
  return terms;
}

/** The canonical encoding of `terms`. */
function polynomialValue(terms: Map<string, PolyTerm>): Value {
  const ordered = [...terms.values()].sort((a, b) => compareBytes(a.key, b.key));
  return tuple(ordered.map((t) => tuple([encodeInt(t.coefficient), tuple([...t.variables])])));
}

/** Add `coefficient · variables` into `terms`. */
function accumulate(terms: Map<string, PolyTerm>, variables: readonly Value[], coefficient: bigint): void {
  const key = encode(tuple([...variables]));
  const name = hexKey(key);
  const existing = terms.get(name);
  terms.set(
    name,
    existing === undefined
      ? { key, variables, coefficient }
      : { key, variables: existing.variables, coefficient: existing.coefficient + coefficient },
  );
}

const NOT_AN_ELEMENT = SemiringAnswer.notAnElement();

const PROVENANCE_LAWS: LawDeclaration = Object.freeze({
  idempotent: false,
  bounded: false,
  monotone: true,
  commutative: true,
  supportsRetraction: true,
});

class ProvenanceSemiring implements Semiring {
  constructor() {
    Object.freeze(this);
  }

  declaredIdentity(): ComponentIdentity {
    return ComponentIdentity.of(
      utf8Encoder.encode("logos-core/provenance-semiring"),
      utf8Encoder.encode("1.0.0"),
      new Uint8Array(32),
    );
  }

  laws(): LawDeclaration {
    return PROVENANCE_LAWS;
  }

  zero(): Value {
    return polynomialValue(new Map());
  }

  one(): Value {
    const terms = new Map<string, PolyTerm>();
    accumulate(terms, [], 1n);
    return polynomialValue(terms);
  }

  isElement(value: Value): boolean {
    return polynomial(value) !== undefined;
  }

  add(a: Value, b: Value): SemiringAnswer {
    const x = polynomial(a);
    const y = polynomial(b);
    if (x === undefined || y === undefined) return NOT_AN_ELEMENT;
    for (const t of y.values()) accumulate(x, t.variables, t.coefficient);
    return SemiringAnswer.element(polynomialValue(x));
  }

  mul(a: Value, b: Value): SemiringAnswer {
    const x = polynomial(a);
    const y = polynomial(b);
    if (x === undefined || y === undefined) return NOT_AN_ELEMENT;
    const product = new Map<string, PolyTerm>();
    for (const p of x.values()) {
      for (const q of y.values()) {
        const variables = [...p.variables, ...q.variables]
          .map((v) => ({ v, bytes: encode(v) }))
          .sort((l, r) => compareBytes(l.bytes, r.bytes))
          .map((e) => e.v);
        accumulate(product, variables, p.coefficient * q.coefficient);
      }
    }
    return SemiringAnswer.element(polynomialValue(product));
  }
}
Object.freeze(ProvenanceSemiring.prototype);

/**
 * The provenance semiring ℕ[X] (v2 §8.3 `Provenance`; ADR 0031 D2), a core semiring: an
 * annotation records which facts, how many times and in which combinations, an answer was
 * derived from. It declares monotone, commutative and supportsRetraction; it is neither
 * idempotent nor bounded. Identity logos-core/provenance-semiring@1.0.0.
 */
export function newProvenanceSemiring(): Semiring {
  return new ProvenanceSemiring();
}
