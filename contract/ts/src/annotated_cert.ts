// ADR 0031 D5 (#1821 P9 I5a; rulings Q14 and Q15): the annotated closed-model certificate.
// [PROPOSED] TS binding of contract/rs/src/annotated_cert.rs; contract/go/annotated_cert.go is the
// third.
//
// An annotated certificate is a ClosedModelCert, unchanged (its wire, its digest and the boolean
// check that verifies it are byte-identical), plus the identity of the semiring its annotations are
// elements of, plus one element per row of each sealed table: `annotations[i]` annotates
// `cert.extensions[i]`, in the cert's table order, one element per row in row order.
//
// The elements of an EXTENSIONAL table are premises. The certificate binds them through its digest,
// and checkAnnotatedClosedModel never attests them: its verdict names those tables as unattested
// (#1821 Q15 condition 1). The check is relative to the semiring's identity (semiringIdentity).

import { Atom, Tuple, atom as valueAtom, bytesEqual, tuple as valueTuple, type Value } from "@bitspark/ontos-core";

import { digestAtom } from "./atoms.js";
import { type ClosedModelCert, parseHashHex } from "./cert.js";
import {
  arityRefusal,
  closedModelCertAsValue,
  closedModelCertFromValue,
  DecodeError,
  renderTag,
} from "./derivation_wire.js";
import { Symbol } from "./literal.js";
import { ComponentIdentity } from "./spi.js";
import { encodeUtf8 } from "./utf8.js";

/** The wire tag of an annotated closed-model certificate. */
const TAG = "annotated_closed_model_cert";

/**
 * The claimed semiring elements of one sealed table (ADR 0031 D5): `elements[j]` annotates row `j`
 * of the certificate's table for `pred`. Mirrors rs `AnnotatedTable` and go `AnnotatedTable`.
 */
export class AnnotatedTable {
  /** The sealed table's predicate. */
  readonly pred: Symbol;
  /** One element per row of that table, in row order. */
  readonly elements: readonly Value[];

  constructor(pred: Symbol, elements: readonly Value[]) {
    this.pred = pred;
    this.elements = Object.freeze(Array.from(elements));
    Object.freeze(this);
  }
}
Object.freeze(AnnotatedTable.prototype);
Object.freeze(AnnotatedTable);

/**
 * A closed-model certificate annotated in a semiring (ADR 0031 D5). `cert` is the boolean
 * certificate, unchanged; `semiring` the identity (semiringIdentity) of the semiring its
 * annotations are elements of; `annotations[i]` annotates `cert.extensions[i]`. An extensional
 * table's elements are premises the certificate binds, never facts the check attests (#1821 Q15).
 * Mirrors rs `AnnotatedClosedModelCert` and go `AnnotatedClosedModelCert`.
 */
export class AnnotatedClosedModelCert {
  /** The boolean closed-model certificate, byte-identical to an unannotated one. */
  readonly cert: ClosedModelCert;
  /** The identity of the semiring the annotations are elements of. */
  readonly semiring: ComponentIdentity;
  /** One annotated table per sealed table, in the certificate's table order. */
  readonly annotations: readonly AnnotatedTable[];

  constructor(cert: ClosedModelCert, semiring: ComponentIdentity, annotations: readonly AnnotatedTable[]) {
    this.cert = cert;
    this.semiring = semiring;
    this.annotations = Object.freeze(Array.from(annotations));
    Object.freeze(this);
  }
}
Object.freeze(AnnotatedClosedModelCert.prototype);
Object.freeze(AnnotatedClosedModelCert);

/**
 * An annotated certificate as a value (ADR 0031 D5):
 *
 *     Tuple[ Atom("annotated_closed_model_cert"),
 *            <the ClosedModelCert wire, closedModelCertAsValue>,
 *            Tuple[Atom(id), Atom(version), digestAtom(config_digest)],
 *            Tuple[ Tuple[Atom(pred), Tuple[element, ...]], ... ] ]
 *
 * The identity record is byte-equal to the kernel's ComponentBinding record (id, version,
 * config_digest), the digest a lowercase-hex atom like every digest on the certificate wire. Mirrors rs
 * `annotated_closed_model_cert_as_value` and go `AnnotatedClosedModelCertAsValue`.
 */
export function annotatedClosedModelCertAsValue(annotated: AnnotatedClosedModelCert): Value {
  const identity = annotated.semiring;
  return valueTuple([
    valueAtom(encodeUtf8(TAG)),
    closedModelCertAsValue(annotated.cert),
    valueTuple([valueAtom(identity.id), valueAtom(identity.version), digestAtom(identity.configDigest)]),
    valueTuple(
      annotated.annotations.map((t) => valueTuple([valueAtom(t.pred.bytes()), valueTuple(Array.from(t.elements))])),
    ),
  ]);
}

/**
 * The CLOSED inverse of annotatedClosedModelCertAsValue. It accepts exactly that shape and refuses
 * everything else with a `DecodeError` (`decode <path>: <defect>`): a wrong tag, a wrong arity at
 * any level, a config digest that is not 64 lowercase-hex characters, an annotated table that is not a pair, a
 * predicate that is not an atom. The inner certificate goes through closedModelCertFromValue, the
 * one certificate decoder. Mirrors rs `annotated_closed_model_cert_from_value` and go
 * `AnnotatedClosedModelCertFromValue`.
 */
export function annotatedClosedModelCertFromValue(v: Value): AnnotatedClosedModelCert {
  const its = itemsN(v, "annotated_cert", 4);
  const tag = atomBytes(its[0]!, "annotated_cert.tag");
  if (!bytesEqual(tag, encodeUtf8(TAG))) throw new DecodeError(`decode annotated_cert: unknown tag ${renderTag(tag)}`);
  const cert = closedModelCertFromValue(its[1]!);
  const identity = itemsN(its[2]!, "annotated_cert.semiring", 3);
  const id = atomBytes(identity[0]!, "annotated_cert.semiring.id");
  const version = atomBytes(identity[1]!, "annotated_cert.semiring.version");
  const digest = parseHashHex(atomBytes(identity[2]!, "annotated_cert.semiring.config_digest"));
  if (digest === undefined) {
    throw new DecodeError("decode annotated_cert.semiring.config_digest: expected 64 lowercase-hex characters");
  }
  const annotations = items(its[3]!, "annotated_cert.annotations").map((t) => {
    const pair = itemsN(t, "annotated_cert.annotation", 2);
    const pred = new Symbol(atomBytes(pair[0]!, "annotated_cert.annotation.pred"));
    return new AnnotatedTable(pred, items(pair[1]!, "annotated_cert.annotation.elements"));
  });
  return new AnnotatedClosedModelCert(cert, ComponentIdentity.of(id, version, digest), annotations);
}

function items(v: Value, ctx: string): readonly Value[] {
  if (!(v instanceof Tuple)) throw new DecodeError(`decode ${ctx}: expected a different value shape`);
  return v.items();
}

function itemsN(v: Value, ctx: string, n: number): readonly Value[] {
  const its = items(v, ctx);
  if (its.length !== n) throw new DecodeError(arityRefusal(ctx, [n], its.length));
  return its;
}

function atomBytes(v: Value, ctx: string): Uint8Array {
  if (!(v instanceof Atom)) throw new DecodeError(`decode ${ctx}: expected a different value shape`);
  return v.bytes();
}
