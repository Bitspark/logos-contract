// §3 (ADR 0007) Closed-model certificate — the sealed, finite, exact relation a
// negated premise `\+ r(a)` discharges against. [FIRM amendment · additive]
// TS sibling of contract/rs/src/cert.rs.
//
// A `\+ r(a)` is sound only if the checker can verify that *all* of `r` has been
// enumerated and that the enumeration is *exact* (no junk, no missing heads) under
// this program / EDB / profile / stratification. That argument is a `ClosedModelCert`:
// a sealed finite model of a STRATUM PREFIX, carrying its scope, the pins it is sealed
// against (program / profile / context / theory-config / EDB-snapshot hashes), the
// finite domains every value must stay within, the exact extensions (relation tables)
// of the sealed predicates, a support witness (E ⊆ least model) and a closure witness
// (least model ⊆ E), and a declared-size budget the checker validates before any scan.

import { encode } from "@bitspark/ontos-codec";
import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";

import { GroundLiteral, Symbol } from "./literal.js";
import { type Subst } from "./term.js";

/**
 * A 32-byte pin (e.g. a SHA-256 digest). The contract carries the raw bytes; how a
 * hash is computed is a consumer/kernel concern (the contract never learns the
 * scheme — it only compares pins for equality). Mirrors Rust's `Hash = [u8; 32]`.
 */
export type Hash = Uint8Array;

/** The all-zero 32-byte hash (a fresh, never-aliased buffer per call). */
export function zeroHash(): Hash {
  return new Uint8Array(32);
}

/** Byte-equality on two `Hash`es (32-byte pins). */
export function hashEquals(a: Hash, b: Hash): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) if (a[i] !== b[i]) return false;
  return true;
}

/**
 * An index into `Derivation.closedWorld`. A thin newtype over a non-negative integer
 * (mirrors Rust's `CertId(usize)`); kept as a number for ergonomics.
 */
export type CertId = number;

/**
 * How a `\+ r(a)` premise's non-membership is witnessed against the cited cert. In v1
 * the only form is `"direct_lookup"` — the checker scans the sealed relation table
 * directly. Kept as an enum so a future compression scheme is an additive variant.
 */
export type NonMemberProof = "direct_lookup";

/**
 * The scope a `ClosedModelCert` seals: a STRATUM PREFIX — all predicates up to (and
 * including) stratification `level`. A prefix (not a single predicate) is needed
 * because mutually-recursive positive SCCs must be sealed together.
 *
 * `predicates` is kept SORTED + DEDUPED (by `Symbol` byte order) so membership and
 * scope-equality are canonical; build one via `StratumPrefix.of`.
 */
export class StratumPrefix {
  /** The stratification level this prefix seals (predicates at levels `0..=level`). */
  readonly level: number;
  /** The sealed predicate symbols, sorted + deduped. */
  readonly predicates: readonly Symbol[];

  private constructor(level: number, predicates: readonly Symbol[]) {
    this.level = level;
    this.predicates = Object.freeze(Array.from(predicates));
    Object.freeze(this);
  }

  /** Build a prefix, sorting + deduping the predicate set canonically (by symbol bytes). */
  static of(level: number, predicates: Iterable<Symbol>): StratumPrefix {
    const sorted = Array.from(predicates).sort((a, b) => compareBytes(a.bytes(), b.bytes()));
    const deduped: Symbol[] = [];
    for (const p of sorted) {
      const last = deduped[deduped.length - 1];
      if (last === undefined || !last.equals(p)) deduped.push(p);
    }
    return new StratumPrefix(level, deduped);
  }

  /**
   * Is `predicates` actually sorted + deduped (strictly increasing by symbol bytes)?
   * ts scans linearly so an unsorted prefix would still *evaluate* correctly here —
   * but the invariant is normative cross-core (#839): rs/go binary-search this
   * collection, so a non-canonical cert is ill-formed everywhere and `verifyCert`
   * rejects it identically in all three cores.
   */
  isCanonical(): boolean {
    for (let i = 1; i < this.predicates.length; i++) {
      if (compareBytes(this.predicates[i - 1]!.bytes(), this.predicates[i]!.bytes()) >= 0) return false;
    }
    return true;
  }

  /** Is `pred` sealed by this prefix? (linear scan over the small sorted predicate set) */
  seals(pred: Symbol): boolean {
    for (const p of this.predicates) {
      if (p.equals(pred)) return true;
    }
    return false;
  }
}

/**
 * A finite, typed value domain — the set of values an argument of a sealed predicate
 * may take. The closure join never enumerates them (#1829); a satisfied grounding whose
 * head value escapes every domain is `cert_out_of_domain`.
 *
 * `values` is kept SORTED + DEDUPED by canonical codec bytes (ontos `Value` has no
 * total order), so domain membership is a canonical lookup.
 */
export class FiniteDomain {
  /** An opaque type tag naming this domain (e.g. `subject`, `action`). */
  readonly typeTag: Symbol;
  /** The domain's values, sorted + deduped by canonical codec bytes. */
  readonly values: readonly Value[];

  private constructor(typeTag: Symbol, values: readonly Value[]) {
    this.typeTag = typeTag;
    this.values = Object.freeze(Array.from(values));
    Object.freeze(this);
  }

  /** Build a domain, sorting + deduping its values by canonical codec bytes. */
  static of(typeTag: Symbol, values: Iterable<Value>): FiniteDomain {
    const keyed = Array.from(values).map((v) => ({ v, key: encode(v) }));
    keyed.sort((a, b) => compareBytes(a.key, b.key));
    const deduped: Value[] = [];
    let prevKey: Uint8Array | undefined;
    for (const { v, key } of keyed) {
      if (prevKey === undefined || compareBytes(prevKey, key) !== 0) deduped.push(v);
      prevKey = key;
    }
    return new FiniteDomain(typeTag, deduped);
  }

  /**
   * Is `values` actually sorted + deduped (strictly increasing by canonical codec
   * bytes)? Normative cross-core (#839; see `StratumPrefix.isCanonical`).
   */
  isCanonical(): boolean {
    for (let i = 1; i < this.values.length; i++) {
      if (compareBytes(encode(this.values[i - 1]!), encode(this.values[i]!)) >= 0) return false;
    }
    return true;
  }

  /** Does this domain contain `v`? (canonical lookup by codec bytes) */
  contains(v: Value): boolean {
    const key = encode(v);
    for (const x of this.values) {
      if (compareBytes(encode(x), key) === 0) return true;
    }
    return false;
  }
}

/**
 * The exact extension (relation table) of one sealed predicate: every ground fact the
 * sealed least model assigns to `pred`. Membership and absence are decided against
 * this table (the rows are kept sorted + deduped by canonical codec bytes).
 */
export class RelationTable {
  readonly pred: Symbol;
  readonly arity: number;
  /** The exact rows, sorted + deduped by canonical codec bytes. */
  readonly rows: readonly GroundLiteral[];

  private constructor(pred: Symbol, arity: number, rows: readonly GroundLiteral[]) {
    this.pred = pred;
    this.arity = arity;
    this.rows = Object.freeze(Array.from(rows));
    Object.freeze(this);
  }

  /** Build a table, sorting + deduping its rows by canonical codec bytes. */
  static of(pred: Symbol, arity: number, rows: Iterable<GroundLiteral>): RelationTable {
    return new RelationTable(pred, arity, sortDedupByGroundKey(rows));
  }

  /**
   * Is `rows` actually sorted + deduped (strictly increasing by `groundKey`)?
   * Normative cross-core (#839; see `StratumPrefix.isCanonical`).
   */
  isCanonical(): boolean {
    for (let i = 1; i < this.rows.length; i++) {
      if (compareBytes(groundKey(this.rows[i - 1]!), groundKey(this.rows[i]!)) >= 0) return false;
    }
    return true;
  }

  /** Does this table contain `fact`? (canonical lookup) */
  contains(fact: GroundLiteral): boolean {
    const key = groundKey(fact);
    for (const x of this.rows) {
      if (compareBytes(groundKey(x), key) === 0) return true;
    }
    return false;
  }
}

/**
 * Canonical sort/compare key for a `GroundLiteral`: the codec bytes of its labeled-
 * compound value `Tuple[Atom(pred), args…]`. Total + deterministic; byte-identical to
 * Rust's `ground_key`.
 */
/**
 * `rows` sorted by `groundKey` with one row per key: the canonical SET order (#2279).
 * `RelationTable.of` and `edbTableHash` both use it, so a sealed table and an EDB snapshot
 * built from the same rows agree by construction.
 */
export function sortDedupByGroundKey(rows: Iterable<GroundLiteral>): GroundLiteral[] {
  const keyed = Array.from(rows).map((g) => ({ g, key: groundKey(g) }));
  keyed.sort((a, b) => compareBytes(a.key, b.key));
  const deduped: GroundLiteral[] = [];
  let prevKey: Uint8Array | undefined;
  for (const { g, key } of keyed) {
    if (prevKey === undefined || compareBytes(prevKey, key) !== 0) deduped.push(g);
    prevKey = key;
  }
  return deduped;
}

export function groundKey(g: GroundLiteral): Uint8Array {
  const items: Value[] = [valueAtom(g.pred.bytes())];
  for (const a of g.args) items.push(a);
  return encode(valueTuple(items));
}

/**
 * A reference inside a `SupportEdge`'s body — how one body literal of the cited rule
 * is satisfied, with the rank discipline that prevents self-justification. A tagged
 * union mirroring Rust's `SupportRef` enum.
 */
export type SupportRef =
  /**
   * A positive dependency on a fact in the SAME sealed stratum. Its `rank` MUST be
   * STRICTLY SMALLER than the supported fact's rank — the semi-naive discipline that
   * rejects the `p :- p` self-justification.
   */
  | { readonly kind: "same_stratum"; readonly fact: GroundLiteral; readonly rank: number }
  /**
   * A positive dependency on a fact in a STRICTLY LOWER sealed stratum; it must be
   * present in the cited lower cert's table.
   */
  | { readonly kind: "lower_stratum"; readonly cert: CertId; readonly atom: GroundLiteral }
  /** A builtin/theory atom, decided `Holds` by the pinned Theory. */
  | { readonly kind: "builtin"; readonly atom: GroundLiteral }
  /**
   * A NEGATED dependency on a fact in a strictly lower sealed stratum; it must be
   * absent from the cited lower cert's table.
   */
  | { readonly kind: "neg_lower"; readonly cert: CertId; readonly atom: GroundLiteral }
  /**
   * #2258 L3.3b: a COUNT body literal, recomputed over the relation the strictly lower
   * certificate `cert` seals. It carries no atom: the count's filter and result are the edge's
   * grounded `subst`, and the checker re-folds the cited table and requires the result.
   */
  | { readonly kind: "count_lower"; readonly cert: CertId };

export const SupportRef = {
  sameStratum(fact: GroundLiteral, rank: number): SupportRef {
    return { kind: "same_stratum", fact, rank };
  },
  lowerStratum(cert: CertId, atom: GroundLiteral): SupportRef {
    return { kind: "lower_stratum", cert, atom };
  },
  builtin(atom: GroundLiteral): SupportRef {
    return { kind: "builtin", atom };
  },
  negLower(cert: CertId, atom: GroundLiteral): SupportRef {
    return { kind: "neg_lower", cert, atom };
  },
  countLower(cert: CertId): SupportRef {
    return { kind: "count_lower", cert };
  },
  /**
   * The single atom/fact a ref points at (used by depth + domain coverage gates), or
   * `undefined` for a `count_lower` ref, which carries none (#2258 L3.3b).
   */
  atom(ref: SupportRef): GroundLiteral | undefined {
    if (ref.kind === "count_lower") return undefined;
    return ref.kind === "same_stratum" ? ref.fact : ref.atom;
  },
};

/**
 * One support edge: a witness that a single sealed fact is in the least model — the
 * cited clause, grounded by `subst`, with head equal to `fact`, whose body literals
 * each resolve via a `SupportRef`, at semi-naive `rank`.
 */
export class SupportEdge {
  /** The sealed fact this edge justifies (must equal the grounded clause head). */
  readonly fact: GroundLiteral;
  /** The clause whose grounding produced `fact`. */
  readonly clause: import("./program.js").ClauseId;
  /** The grounding substitution applied to the clause. */
  readonly subst: Subst;
  /** One reference per clause body literal, in body order. */
  readonly bodyRefs: readonly SupportRef[];
  /**
   * The semi-naive rank assigned to `fact` (must strictly dominate every same-stratum
   * body ref's rank).
   */
  readonly rank: number;

  constructor(
    fact: GroundLiteral,
    clause: import("./program.js").ClauseId,
    subst: Subst,
    bodyRefs: readonly SupportRef[],
    rank: number,
  ) {
    this.fact = fact;
    this.clause = clause;
    this.subst = subst;
    this.bodyRefs = Object.freeze(Array.from(bodyRefs));
    this.rank = rank;
    Object.freeze(this);
  }
}

/**
 * The declared sizes of a certificate — every field validated against the `CheckLimits` cert
 * budgets BEFORE any scan, and every counted field against its ACTUAL value, so a lying
 * declaration is caught (`cert_decl_mismatch`, #2335) whichever field lies. The comparison point
 * differs by field: `certFacts`, `domainValues` and `supportEdges` are read off the artifact
 * and compared BEFORE the scan; `ruleGroundings` and `joinSteps` are the closure scan's own
 * counters and are compared AS IT RUNS (#1852), tripping the moment the count exceeds the
 * declaration — so a checked certificate's scan cost is bounded by min(declared, budget),
 * never by the budget alone. `certBytes` is compared BEFORE the scan too, and since #2524 it is
 * also MEASURED: the certificate's canonical encoded size (`certEncodedBytes`) must not exceed
 * it, so `maxCertBytes` bounds what a certificate is, not only what it declares. Bounding the
 * bytes a host READS before decoding is the transport's (#2528). Mirrors Rust's `CertSizeDecl`.
 */
export interface CertSizeDecl {
  /** Declared total number of sealed facts (rows across all `extensions`). */
  readonly certFacts: number;
  /** Declared total number of domain values (across all `domains`). */
  readonly domainValues: number;
  /** Declared total number of support edges. */
  readonly supportEdges: number;
  /**
   * Declared number of rule groundings the closure join will emit — one per body-true tuple
   * of a sealed-scope clause (#1829; before it, the groundings of `|∪domains|^vars` the
   * self-enumeration would visit, an upper bound on this figure).
   */
  readonly ruleGroundings: number;
  /**
   * Declared number of join steps the closure join will perform — one per candidate examined
   * at one body literal: a sealed-table row offered to a binder, or the current tuple offered
   * to a filter (#1829).
   */
  readonly joinSteps: number;
  /** Declared serialized size of the certificate, in bytes: `certEncodedBytes`, the canonical encoding with this field zeroed (#2524). */
  readonly certBytes: number;
}

/**
 * A sealed finite-model certificate for a STRATUM PREFIX (ADR 0007). Verified once per
 * citing derivation; a `\+ r(a)` premise reuses the verified result. TS sibling of
 * Rust's `ClosedModelCert`.
 */
export class ClosedModelCert {
  /** The stratum prefix this cert seals. */
  readonly scope: StratumPrefix;
  /** Pin of the program the cert was computed against. */
  readonly programHash: Hash;
  /** Pin of the check profile (leaves/admit identities). */
  readonly profileHash: Hash;
  /** Pin of the verification context snapshot. */
  readonly ctxHash: Hash;
  /** Pin of the theory configuration (so `not` means the same builtin semantics). */
  readonly theoryConfigHash: Hash;
  /** Pins of the complete EDB snapshots the sealed extensions were drawn from. */
  readonly edbSnapshotHashes: readonly Hash[];
  /** The finite, typed value domains every sealed value must stay within. */
  readonly domains: readonly FiniteDomain[];
  /** The exact extensions (relation tables) of the sealed predicates. */
  readonly extensions: readonly RelationTable[];
  /** The support witness (`E ⊆ least model`, no junk) — one edge per sealed IDB fact. */
  readonly supports: readonly SupportEdge[];
  /** Declared sizes, validated against the cert budgets before any scan. */
  readonly limitsDecl: CertSizeDecl;
  /**
   * ADR 0029 D10's SLICE SEAL. `undefined` (the default, and every pre-D10 cert) means
   * `programHash` pins the COMPLETE live clause set, ADR 0007 §3.1. Defined means this cert
   * was minted for ONE COMPONENT, so `programHash` pins only that component's downward-closed
   * slice, and the value is the digest of the `DecompositionWitness` that authorized it —
   * which the bound `CertContext` must carry identically.
   *
   * OPTIONAL on purpose, and read the hazard: TypeScript absorbs a new optional field as
   * silently as Go's zero value does, so every existing construction site keeps compiling and
   * receives `undefined` — where the identical change in rs surfaced 29 sites loudly. A green
   * ts suite is therefore NOT parity evidence; only a test that constructs a slice-sealed cert
   * exercises this at all.
   *
   * The contract tier never interprets it: 32 opaque bytes compared for equality. It cannot be
   * richer — `DecompositionWitness` lives above this package in the kernel (ADR 0004).
   */
  readonly decompositionWitness?: Hash | undefined;

  /**
   * ADR 0030 D1: the sub-scope of `scope` whose tables are LOWER BOUNDS of the least model
   * rather than exact — the tripping stratum of a truncated evaluation, sealed for its
   * positive rows only. `undefined` for every exact seal (the wire form is the same TEN or
   * ELEVEN element tuple it always was); present only as the twelfth trailing-optional
   * element. Invariants, verified by `verifyCert` step 1c BEFORE any table is consulted:
   * canonical, a non-empty subset of `scope` at the prefix's own level, upward-closed within
   * the sealed prefix (a complete sealed table never reads a partial one), and never an
   * extensional table. Closure is NOT verified over a partial table; a `Neg` premise over one
   * is `neg_atom_partial`, a `Count` premise `count_over_partial`. Mirrors rs `partial_scope`.
   *
   * OPTIONAL — the same absorption hazard as `decompositionWitness`: every existing
   * construction site keeps compiling and receives `undefined`.
   */
  readonly partialScope?: StratumPrefix | undefined;

  constructor(params: {
    scope: StratumPrefix;
    programHash: Hash;
    profileHash: Hash;
    ctxHash: Hash;
    theoryConfigHash: Hash;
    edbSnapshotHashes: readonly Hash[];
    domains: readonly FiniteDomain[];
    extensions: readonly RelationTable[];
    supports: readonly SupportEdge[];
    limitsDecl: CertSizeDecl;
    decompositionWitness?: Hash | undefined;
    partialScope?: StratumPrefix | undefined;
  }) {
    this.scope = params.scope;
    this.programHash = params.programHash;
    this.profileHash = params.profileHash;
    this.ctxHash = params.ctxHash;
    this.theoryConfigHash = params.theoryConfigHash;
    this.edbSnapshotHashes = Object.freeze(Array.from(params.edbSnapshotHashes));
    this.domains = Object.freeze(Array.from(params.domains));
    this.extensions = Object.freeze(Array.from(params.extensions));
    this.supports = Object.freeze(Array.from(params.supports));
    this.limitsDecl = params.limitsDecl;
    this.decompositionWitness = params.decompositionWitness;
    this.partialScope = params.partialScope;
    Object.freeze(this);
  }

  /** ADR 0030: is `pred`'s sealed table a LOWER BOUND (in `partialScope`) rather than exact? */
  isPartial(pred: Symbol): boolean {
    return this.partialScope !== undefined && this.partialScope.seals(pred);
  }

  /** Look the exact table for `pred` up among this cert's extensions, if sealed. */
  table(pred: Symbol): RelationTable | undefined {
    for (const t of this.extensions) {
      if (t.pred.equals(pred)) return t;
    }
    return undefined;
  }

  /**
   * Find the domain whose values contain `v` (used for the negated-atom typing check);
   * `undefined` if no supplied domain contains it.
   */
  domainContaining(v: Value): FiniteDomain | undefined {
    for (const d of this.domains) {
      if (d.contains(v)) return d;
    }
    return undefined;
  }
}

/** Lexicographic byte ordering — the total order Rust's slice `Ord` uses. */
function compareBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const ai = a[i]!;
    const bi = b[i]!;
    if (ai !== bi) return ai < bi ? -1 : 1;
  }
  return a.length - b.length;
}
