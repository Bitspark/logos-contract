/**
 * #2605, the ts rung of #2602 (`seat:caa`'s lever A): a closed-model certificate's canonical wire
 * SHAPE, written ONCE as a pre-order walk over a {@link WireSink}, with two readings. The value
 * reading builds exactly the ontos value `closedModelCertAsValue` returns; the length reading counts
 * the bytes of that value's canonical encoding without building anything. The walk emits each node
 * before its children, in encoding order, as rs `wire_sink` and go `wire_sink.go` do.
 *
 * Why: `certEncodedBytes`, the measure behind `max_cert_bytes` (#2524), built the whole value tree
 * and then its encoded buffer only to count the bytes. On the rs path that transient was 41% of a
 * certified-set run's peak heap (#2602); the ts host pays the same when it checks a decoded
 * certificate. Measured through the length reading, the budget check refuses an oversized
 * certificate in bounded memory.
 *
 * What the length reading RESTATES, both frozen formats, and pinned against `encode(..)` by
 * `test/wire_sink_2605.test.ts` including the uvarint width boundaries:
 *   - the ontos codec's framing: Atom = 0x00 ‖ uvarint(len) ‖ bytes, Tuple = 0x01 ‖ uvarint(arity) ‖ children;
 *   - the frozen quote reading (`reify.ts`): an atom b is Tuple[Atom([0x00]), Atom(b)], a variable
 *     Tuple[Atom([0x02]), Atom(name)], a tuple Tuple[Atom([0x01]), Tuple[quote(child)…]].
 *
 * It takes its scalar readings (`intAtom`, `digestAtom`) from `derivation_wire.ts`, which takes its
 * builders from here: a cycle of hoisted function declarations only, used at call time, as rs
 * `wire_sink` reaches back for `derivation_wire::to_hex`.
 */

import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import type {
  CertSizeDecl,
  ClosedModelCert,
  FiniteDomain,
  RelationTable,
  StratumPrefix,
  SupportEdge,
  SupportRef,
} from "./cert.js";
import { hashFromBytes, nativeOctetLength } from "./octets.js";
import { digestAtom, intAtom } from "./atoms.js";
import type { GroundLiteral, Symbol } from "./literal.js";
import { quote } from "./reify.js";
import { Term, type Subst } from "./term.js";
import { portableClauseIdBytes } from "./clause_id_encoding.js";

const enc = new TextEncoder();

/** One reading of the wire shape, fed in pre-order: every node before its children. */
export interface WireSink {
  /**
   * Whether the walk must emit a sorted map's entries in codec order. `false` is legal ONLY for a
   * reading whose result does not depend on that order, which today means the length (a sum); any
   * reading of the bytes or of the value must say `true`.
   */
  readonly ordered: boolean;
  /** An Atom of a string's UTF-8 bytes. */
  atomStr(s: string): void;
  /** Read a native clause handle under this sink's identity or size contract. */
  clauseId(handle: string): void;
  /** An Atom of bytes the sink must not keep or mutate. */
  atomBytes(b: Uint8Array): void;
  /** A digest's lowercase-hex Atom. */
  digest(d: Uint8Array): void;
  /** Opens a Tuple of `arity` children; exactly `arity` nodes follow, then `tupleEnd`. */
  tupleBegin(arity: number): void;
  tupleEnd(): void;
  /** An ontos value carried verbatim. */
  value(v: Value): void;
  /** A ground value through the frozen quote reading. */
  quotedValue(v: Value): void;
  /** A term through the frozen quote reading. */
  quotedTerm(t: Term): void;
  /** A non-negative integer as the ontos-data `int` embedding. */
  int(n: number): void;
}

/** The value reading: exactly the tree `closedModelCertAsValue` has always built. */
class ValueSink implements WireSink {
  readonly ordered = true;
  // The open tuples' children so far, innermost last; frame 0 holds the result.
  readonly #frames: Value[][] = [[]];

  constructor(private readonly clauseBytes: (handle: string) => Uint8Array = portableClauseIdBytes) {}

  #push(v: Value): void {
    this.#frames[this.#frames.length - 1]!.push(v);
  }
  atomStr(s: string): void {
    this.#push(valueAtom(enc.encode(s)));
  }
  clauseId(handle: string): void {
    this.#push(valueAtom(this.clauseBytes(handle)));
  }
  atomBytes(b: Uint8Array): void {
    this.#push(valueAtom(b));
  }
  digest(d: Uint8Array): void {
    this.#push(digestAtom(d));
  }
  tupleBegin(_arity: number): void {
    this.#frames.push([]);
  }
  tupleEnd(): void {
    const items = this.#frames.pop()!;
    this.#push(valueTuple(items));
  }
  value(v: Value): void {
    this.#push(v);
  }
  quotedValue(v: Value): void {
    this.#push(quote(Term.fromValue(v)));
  }
  quotedTerm(t: Term): void {
    this.#push(quote(t));
  }
  int(n: number): void {
    this.#push(intAtom(n));
  }
  result(): Value {
    const top = this.#frames[0]!;
    if (this.#frames.length !== 1 || top.length !== 1) {
      throw new Error("contract: wire walk left an open tuple or emitted other than one value");
    }
    return top[0]!;
  }
}

/** The value `emit` walks. */
export function buildValue(emit: (s: WireSink) => void): Value {
  const s = new ValueSink();
  emit(s);
  return s.result();
}

/** Exact JavaScript code units, including unpaired surrogates. Used only for native memo equality. */
function nativeHandleBytes(handle: string): Uint8Array {
  const bytes = new Uint8Array(handle.length * 2);
  for (let i = 0; i < handle.length; i++) {
    const unit = handle.charCodeAt(i);
    bytes[2 * i] = unit >>> 8;
    bytes[2 * i + 1] = unit & 0xff;
  }
  return bytes;
}

export function nativeCertificateKey(cert: ClosedModelCert): Value {
  const sink = new ValueSink(nativeHandleBytes);
  writeClosedModelCert(sink, cert, cert.limitsDecl);
  return sink.result();
}

/** The width of `n` as a shortest-form LEB128 uvarint. */
function uvarintLen(n: number): number {
  let w = 1;
  while (n >= 128) {
    n = Math.floor(n / 128);
    w += 1;
  }
  return w;
}

/** An Atom of `n` bytes: tag, length, bytes. */
function atomLen(n: number): number {
  return 1 + uvarintLen(n) + n;
}

/** A Tuple of `arity` children whose encodings sum to `children`. */
function tupleLen(arity: number, children: number): number {
  return 1 + uvarintLen(arity) + children;
}

/** A quote node's one-byte tag atom. */
const QUOTE_TAG = 3;

/**
 * The UTF-8 byte length of `s` as `TextEncoder` writes it, without encoding it: a lone surrogate
 * becomes U+FFFD (three bytes), as the encoder's replacement does.
 */
export function utf8Len(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i += 1) {
    const c = s.charCodeAt(i);
    if (c < 0x80) {
      n += 1;
    } else if (c < 0x800) {
      n += 2;
    } else if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
      const d = s.charCodeAt(i + 1);
      if (d >= 0xdc00 && d <= 0xdfff) {
        n += 4;
        i += 1;
      } else {
        n += 3;
      }
    } else {
      n += 3;
    }
  }
  return n;
}

/** The encoded length of `v`, without encoding it. */
function encodedLen(v: Value): number {
  if (v.kind === "atom") return atomLen(v.length);
  let sum = 0;
  for (const child of v.items()) sum += encodedLen(child);
  return tupleLen(v.length, sum);
}

/** The encoded length of `quote(Term.fromValue(v))`, without building either. */
function quotedLen(v: Value): number {
  let payload: number;
  if (v.kind === "atom") {
    payload = atomLen(v.length);
  } else {
    let sum = 0;
    for (const child of v.items()) sum += quotedLen(child);
    payload = tupleLen(v.length, sum);
  }
  return tupleLen(2, QUOTE_TAG + payload);
}

/** The encoded length of `quote(t)`, without building it. */
function quotedTermLen(t: Term): number {
  return tupleLen(2, QUOTE_TAG + quotedPayloadLen(t));
}

/** The encoded length of a quote node's payload: the atom, the name, or the quoted children. */
function quotedPayloadLen(t: Term): number {
  switch (t.kind) {
    case "atom":
      return atomLen(t.bytes().length);
    case "var":
      return atomLen(utf8Len(t.id().asStr()));
    case "tuple": {
      let sum = 0;
      for (const child of t.children()) sum += quotedTermLen(child);
      return tupleLen(t.children().length, sum);
    }
  }
}

/** The length reading: the canonical encoding's byte count, with no tree and no buffer. */
class LenSink implements WireSink {
  readonly ordered = false;
  total = 0;

  atomStr(s: string): void {
    this.total += atomLen(utf8Len(s));
  }
  clauseId(handle: string): void {
    this.total += atomLen(utf8Len(handle));
  }
  atomBytes(b: Uint8Array): void {
    this.total += atomLen(b.length);
  }
  digest(d: Uint8Array): void {
    // The native Hash reading only needs its width. Explicit numeric input,
    // like the value sink's, first has to establish each of the 32 octets.
    if (nativeOctetLength(d) !== 32) hashFromBytes(d);
    this.total += atomLen(64);
  }
  tupleBegin(arity: number): void {
    this.total += 1 + uvarintLen(arity);
  }
  tupleEnd(): void {}
  value(v: Value): void {
    this.total += encodedLen(v);
  }
  quotedValue(v: Value): void {
    this.total += quotedLen(v);
  }
  quotedTerm(t: Term): void {
    this.total += quotedTermLen(t);
  }
  int(n: number): void {
    // The int embedding is ontos-data's to define; measuring its (three-node) value keeps that
    // definition in one place, at a constant transient per integer, as rs and go do.
    this.total += encodedLen(intAtom(n));
  }
}

/** The encoded length of the value `emit` walks. */
export function measureLen(emit: (s: WireSink) => void): number {
  const s = new LenSink();
  emit(s);
  return s.total;
}

/** `uvarint(n)`'s bytes, shortest-form LEB128. */
function uvarintBytes(n: number): number[] {
  const out: number[] = [];
  for (;;) {
    const low = n % 128;
    n = Math.floor(n / 128);
    out.push(n !== 0 ? low | 0x80 : low);
    if (n === 0) return out;
  }
}

/**
 * The codec order of two atoms (§0.3.3's sorted-map order) without encoding them: 0x00, then
 * uvarint(len), then the bytes. LEB128 is prefix-free, so comparing the length prefixes first and
 * the bytes second is the order of the whole encodings.
 */
function atomCodecCmp(a: Uint8Array, b: Uint8Array): number {
  const la = uvarintBytes(a.length);
  const lb = uvarintBytes(b.length);
  for (let i = 0; i < la.length && i < lb.length; i += 1) {
    if (la[i] !== lb[i]) return la[i]! < lb[i]! ? -1 : 1;
  }
  if (la.length !== lb.length) return la.length < lb.length ? -1 : 1;
  for (let i = 0; i < a.length; i += 1) {
    if (a[i] !== b[i]) return a[i]! < b[i]! ? -1 : 1;
  }
  return 0;
}

// ------------------------------ the shape, once ------------------------------

function wireTuple(s: WireSink, arity: number, children: () => void): void {
  s.tupleBegin(arity);
  children();
  s.tupleEnd();
}

function writeSymbol(s: WireSink, sym: Symbol): void {
  s.atomBytes(sym.bytes());
}

/** A ground literal `p(a…)` as `Tuple[Atom(p), quote(a)…]`. */
export function writeGroundLiteral(s: WireSink, lit: GroundLiteral): void {
  wireTuple(s, 1 + lit.args.length, () => {
    writeSymbol(s, lit.pred);
    for (const arg of lit.args) s.quotedValue(arg);
  });
}

/**
 * A substitution as `Tuple[Tuple[Atom(var), quote(term)], …]`, sorted by the key's codec bytes
 * (§0.3.3): shorter names first, so Z precedes AB. Every key is a `VarId` (#3288), so its name has
 * passed the constructor's §2a test and encodes as the UTF-8 text it is: no check is made here.
 */
export function writeSubst(s: WireSink, subst: Subst): void {
  if (!s.ordered) {
    wireTuple(s, subst.size, () => {
      for (const [id, term] of subst) {
        wireTuple(s, 2, () => {
          s.atomStr(id.asStr());
          s.quotedTerm(term);
        });
      }
    });
    return;
  }
  const keyed = Array.from(subst, ([id, term]) => ({ key: enc.encode(id.asStr()), term }));
  keyed.sort((p, q) => atomCodecCmp(p.key, q.key));
  wireTuple(s, keyed.length, () => {
    for (const { key, term } of keyed) {
      wireTuple(s, 2, () => {
        s.atomBytes(key);
        s.quotedTerm(term);
      });
    }
  });
}

/**
 * A closed-model certificate with `decl` in its size-declaration slot. The trailing-optional
 * elements follow ADR 0029 D10 (the 11th, a slice-seal pin) and ADR 0030 D4 (the 12th, a partial
 * scope; with no pin the 11th is the `opt` none marker Tuple[Atom("none")]).
 */
export function writeClosedModelCert(s: WireSink, cert: ClosedModelCert, decl: CertSizeDecl): void {
  const trailing = cert.partialScope !== undefined ? 2 : cert.decompositionWitness !== undefined ? 1 : 0;
  wireTuple(s, 10 + trailing, () => {
    writeStratumPrefix(s, cert.scope);
    s.digest(cert.programHash);
    s.digest(cert.profileHash);
    s.digest(cert.ctxHash);
    s.digest(cert.theoryConfigHash);
    wireTuple(s, cert.edbSnapshotHashes.length, () => {
      for (const h of cert.edbSnapshotHashes) s.digest(h);
    });
    wireTuple(s, cert.domains.length, () => {
      for (const d of cert.domains) writeFiniteDomain(s, d);
    });
    wireTuple(s, cert.extensions.length, () => {
      for (const t of cert.extensions) writeRelationTable(s, t);
    });
    wireTuple(s, cert.supports.length, () => {
      for (const e of cert.supports) writeSupportEdge(s, e);
    });
    writeCertSizeDecl(s, decl);
    if (cert.partialScope !== undefined) {
      if (cert.decompositionWitness !== undefined) {
        s.digest(cert.decompositionWitness);
      } else {
        wireTuple(s, 1, () => s.atomStr("none"));
      }
      writeStratumPrefix(s, cert.partialScope);
    } else if (cert.decompositionWitness !== undefined) {
      s.digest(cert.decompositionWitness);
    }
  });
}

function writeStratumPrefix(s: WireSink, scope: StratumPrefix): void {
  wireTuple(s, 2, () => {
    s.int(scope.level);
    wireTuple(s, scope.predicates.length, () => {
      for (const p of scope.predicates) writeSymbol(s, p);
    });
  });
}

function writeFiniteDomain(s: WireSink, domain: FiniteDomain): void {
  wireTuple(s, 2, () => {
    writeSymbol(s, domain.typeTag);
    wireTuple(s, domain.values.length, () => {
      for (const v of domain.values) s.value(v);
    });
  });
}

function writeRelationTable(s: WireSink, table: RelationTable): void {
  wireTuple(s, 3, () => {
    writeSymbol(s, table.pred);
    s.int(table.arity);
    wireTuple(s, table.rows.length, () => {
      for (const r of table.rows) writeGroundLiteral(s, r);
    });
  });
}

function writeSupportEdge(s: WireSink, edge: SupportEdge): void {
  wireTuple(s, 5, () => {
    writeGroundLiteral(s, edge.fact);
    s.clauseId(edge.clause.asStr());
    writeSubst(s, edge.subst);
    wireTuple(s, edge.bodyRefs.length, () => {
      for (const r of edge.bodyRefs) writeSupportRef(s, r);
    });
    s.int(edge.rank);
  });
}

function writeSupportRef(s: WireSink, ref: SupportRef): void {
  switch (ref.kind) {
    case "same_stratum":
      return wireTuple(s, 3, () => {
        s.atomStr("same_stratum");
        writeGroundLiteral(s, ref.fact);
        s.int(ref.rank);
      });
    case "lower_stratum":
      return wireTuple(s, 3, () => {
        s.atomStr("lower_stratum");
        s.int(ref.cert);
        writeGroundLiteral(s, ref.atom);
      });
    case "builtin":
      return wireTuple(s, 2, () => {
        s.atomStr("builtin");
        writeGroundLiteral(s, ref.atom);
      });
    case "neg_lower":
      return wireTuple(s, 3, () => {
        s.atomStr("neg_lower");
        s.int(ref.cert);
        writeGroundLiteral(s, ref.atom);
      });
    case "count_lower":
      // #2258 L3.3b: additive on the wire, a fifth tag.
      return wireTuple(s, 2, () => {
        s.atomStr("count_lower");
        s.int(ref.cert);
      });
  }
}

function writeCertSizeDecl(s: WireSink, decl: CertSizeDecl): void {
  wireTuple(s, 6, () => {
    s.int(decl.certFacts);
    s.int(decl.domainValues);
    s.int(decl.supportEdges);
    s.int(decl.ruleGroundings);
    s.int(decl.joinSteps);
    s.int(decl.certBytes);
  });
}
