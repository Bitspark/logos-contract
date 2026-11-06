// §5 / §5a / §6 — the checker-facing extension points (SPI). [STABLE v1]
// TS sibling of contract/rs/src/spi.rs.

import { encode } from "@bitspark/ontos-codec";
import { atom as valueAtom, tuple as valueTuple, type Value } from "@bitspark/ontos-core";
import { sha256 } from "@noble/hashes/sha2.js";

import { sortDedupByGroundKey, type Hash } from "./cert.js";
import { Symbol, type GroundLiteral } from "./literal.js";
import { type Evidence, type NodeMeta } from "./derivation.js";
import { type Clause } from "./program.js";
import {
  completed,
  fault,
  notCompleted,
  theoryFails,
  theoryHolds,
  type TheoryGround,
} from "./completion.js";

/**
 * Domain separator for the canonical EDB-table snapshot hash (ADR 0007 §3.6), so an
 * EDB-snapshot digest can never collide with a clause id or any other hash. Mirrors
 * Rust's `EDB_PREFIX`.
 */
export const EDB_PREFIX: Uint8Array = new TextEncoder().encode("logos/account/edb-snapshot/v1\n");

/**
 * The canonical snapshot hash of one extensional predicate's table, read as a SET —
 * `SHA-256(EDB_PREFIX ‖ pred-bytes ‖ ontos-codec(Tuple[rows…]))`, with the rows sorted by
 * `groundKey` and a repeated row ignored (#2279): order and multiplicity never change the
 * hash. This is the value a `LeafVerifier.edbSnapshot` returns for `pred` over its trusted
 * EDB, and the value `check` recomputes over a cert's sealed extension table to bind that
 * table to the live EDB (the `cert_edb_mismatch` obligation). The sealed table is itself a
 * set (`RelationTable.of` dedups by the same key), so a snapshot provider need not
 * deduplicate its rows first. Byte-identical to Rust's `edb_table_hash`.
 */
export function edbTableHash(pred: Symbol, rows: readonly GroundLiteral[]): Hash {
  const sorted = sortDedupByGroundKey(rows);
  const rowValues: Value[] = sorted.map((g) => {
    const items: Value[] = [valueAtom(g.pred.bytes())];
    for (const a of g.args) items.push(a);
    return valueTuple(items);
  });
  const body = encode(valueTuple(rowValues));
  const predBytes = pred.bytes();
  const input = new Uint8Array(EDB_PREFIX.length + predBytes.length + body.length);
  input.set(EDB_PREFIX, 0);
  input.set(predBytes, EDB_PREFIX.length);
  input.set(body, EDB_PREFIX.length + predBytes.length);
  return sha256(input);
}

/** The verdict of a `Theory` on a ground atom (§5). Discriminated by `kind`. */
export type TheoryOutcome =
  | { readonly kind: "holds" }
  | { readonly kind: "fails"; readonly code: string }
  | { readonly kind: "not_mine" };

export const TheoryOutcome = {
  Holds: { kind: "holds" } as const satisfies TheoryOutcome,
  Fails(code: string): TheoryOutcome {
    return { kind: "fails", code };
  },
  NotMine: { kind: "not_mine" } as const satisfies TheoryOutcome,
};

/**
 * §5 Theory SPI — builtins / decidable atoms.
 *
 * STABLE-v1 realization (erratum, §5): the seam is object-safe — `decide(atom)`
 * only, with config closed over at construction (NO live ctx). A verdict MUST be a
 * pure, total, deterministic function of the ground arguments alone.
 *
 * spi-role: consumer. A consumer implements this extension point in its own domain; a test
 * double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
 */
export interface Theory {
  /** Does this theory own (decide) the given predicate? */
  owns(pred: Symbol): boolean;
  /**
   * Decide an owned ground atom. Pure / total / deterministic / config-pinned. The v1 form, kept
   * for external readers: logos's own readers call {@link decideGround}, which can also say "not
   * decided".
   */
  decide(atom: GroundLiteral): TheoryOutcome;
  /**
   * **Decide an owned ground atom, or say it was NOT DECIDED (#3126; seat:caa's rulings of
   * 2026-09-27).** A decider that stops before it establishes a fact (a work cap, a capacity)
   * returns `not_completed(cause)`, never a false: under negation or in the closure check a stop
   * read as `fails` becomes a false positive (research 0031). OPTIONAL (ADR 0003): absent, the
   * default is derived from `decide` ({@link groundFromLegacy}), so a theory that never stops needs
   * no change. A theory that can stop implements it, and its `decide` then answers the stopped case
   * with `not_mine`, never `fails`, so a legacy reader fails CLOSED. A composite theory implements
   * it by FORWARDING to its members. ADR 0036 D8's checker SPI v2 makes it required.
   */
  decideGround?(atom: GroundLiteral): TheoryGround;
  /**
   * The component's inherent identity (ADR 0004 D4 · parity with the Rust binding's
   * defaulted `identity()`). OPTIONAL: TS optional members are non-breaking, so
   * existing impls without it still satisfy the interface. ABSENT = unidentified —
   * a consumer reads it as {@link ComponentIdentity.unidentified}.
   */
  identity?(): ComponentIdentity;
  /**
   * #3142 (research 0031 row 13): whether this theory's `Fails` on the owned predicate `pred` is
   * always a decided false (parity with the Rust binding's defaulted `completion()` and Go's optional
   * `CompletionDeclared`). OPTIONAL: an impl without it reads {@link DecisionCompletion.undeclared}
   * naming it ({@link completionOf}), which admission treats as may-not-complete (fail closed,
   * seat:caa on #3142). A decision that stops early can surface as `Fails`, and a sealed closure
   * reads that false as knowledge, so the certifying kernel refuses a seal whose clauses reach a
   * decider that does not declare `stops_are_typed` (#3313 typed the stop; retires at v2, ADR 0036 D8).
   */
  completion?(pred: Symbol): DecisionCompletion;
}

/**
 * A decider's declaration about its own decisions on an owned predicate (#3142), the TS binding of
 * Rust's `DecisionCompletion` and Go's sealed `DecisionCompletion`.
 */
export type DecisionCompletion =
  | { readonly kind: "stops_are_typed" }
  | { readonly kind: "may_not_complete"; readonly decider: ComponentIdentity; readonly cause: string }
  | { readonly kind: "undeclared"; readonly decider: ComponentIdentity };

export const DecisionCompletion = {
  /**
   * Every non-decision on the predicate reaches readers as `decideGround`'s typed `not_completed`,
   * so a `Fails` is always a decided false. A decider that never stops satisfies it trivially; one
   * that stops satisfies it when every stop is typed (arithmetic's work cap, #3313). Named for the
   * claim the guard needs, never "completes": a decider here may stop.
   */
  StopsAreTyped: { kind: "stops_are_typed" } as const satisfies DecisionCompletion,
  /** A decision may stop without deciding and still answer `Fails`; `cause` says why. */
  mayNotComplete(decider: ComponentIdentity, cause: string): DecisionCompletion {
    return { kind: "may_not_complete", decider, cause };
  },
  /** The decider declared nothing: read as may-not-complete (fail closed). */
  undeclared(decider: ComponentIdentity): DecisionCompletion {
    return { kind: "undeclared", decider };
  },
  /** Whether admission may rest a certified claim on the declaration: only `stops_are_typed`. */
  stopsAreTyped(d: DecisionCompletion): boolean {
    switch (d.kind) {
      case "stops_are_typed":
        return true;
      case "may_not_complete":
      case "undeclared":
        return false;
      default: {
        const unreachable: never = d;
        throw new Error(`DecisionCompletion.stopsAreTyped over an unknown declaration ${JSON.stringify(unreachable)}`);
      }
    }
  },
};

/**
 * `t`'s declaration for `pred`: its own when it implements the optional `completion`, otherwise
 * {@link DecisionCompletion.undeclared} naming it (fail closed, never a borrowed `stops_are_typed`).
 */
export function completionOf(t: Theory, pred: Symbol): DecisionCompletion {
  return t.completion?.(pred) ?? DecisionCompletion.undeclared(t.identity?.() ?? ComponentIdentity.unidentified());
}

/**
 * The ONE reader of a theory's ground verdict (#3126): the theory's own `decideGround` when it has
 * one, else the default derived from `decide`. Every logos reader calls it, never `decide`.
 */
export function decideGround(theory: Theory, atom: GroundLiteral): TheoryGround {
  return theory.decideGround !== undefined ? theory.decideGround(atom) : groundFromLegacy(theory.decide(atom));
}

/**
 * The mapping `decideGround`'s default applies to a v1 answer (#3126): `holds` and `fails` are the
 * decision, and `not_mine` is the named `inconsistent_theory` fault. A wrapper whose own answers
 * come from `decide` (a host builtin) uses it for them, and forwards the rest. An outcome outside
 * the type is the fault `malformed_outcome`. Rust's `ground_from_legacy`.
 */
export function groundFromLegacy(o: TheoryOutcome): TheoryGround {
  if (o === null || o === undefined) return notCompleted(fault("malformed_outcome"));
  switch (o.kind) {
    case "holds":
      return completed(theoryHolds);
    case "fails":
      return completed(theoryFails(o.code));
    case "not_mine":
      return notCompleted(fault("inconsistent_theory"));
    default:
      return notCompleted(fault("malformed_outcome"));
  }
}

/**
 * The one legacy adapter (#3126): the v1 `TheoryOutcome` of a `decideGround` answer, for a theory
 * that implements `decideGround` and derives its `decide` from it. A not-completed answer becomes
 * `not_mine`, never `fails`: v1 has no "not decided" arm, and every reader refuses an owned atom's
 * `not_mine` by name, so a legacy reader fails CLOSED. The wrong category (a stop reported as a
 * routing fault), never a wrong answer; ADR 0036 D8's v2 deletes it with `decide`. Rust's
 * `legacy_outcome`.
 */
export function legacyOutcome(g: TheoryGround): TheoryOutcome {
  if (g.kind === "completed") {
    return g.value.kind === "holds" ? TheoryOutcome.Holds : TheoryOutcome.Fails(g.value.code);
  }
  return TheoryOutcome.NotMine;
}

/** The verdict of a `LeafVerifier` (§6). */
export type LeafOutcome =
  | { readonly kind: "admit" }
  | { readonly kind: "reject"; readonly code: string };

export const LeafOutcome = {
  Admit: { kind: "admit" } as const satisfies LeafOutcome,
  Reject(code: string): LeafOutcome {
    return { kind: "reject", code };
  },
};

/**
 * §6 Leaf SPI — attestation / extensional admission, generic over the verification
 * context `C`. Leaf verification is fully delegated here (v1). `verify` MUST be
 * total and deterministic over `(atom, evidence, ctx)`.
 *
 * spi-role: consumer. A consumer implements this extension point in its own domain; a test
 * double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
 */
export interface LeafVerifier<C> {
  /** Declares the extensional (sealed/leaf) predicate set (§4.2). */
  extensional(): PredicateSet;
  verify(atom: GroundLiteral, evidence: Evidence, ctx: C): LeafOutcome;
  /**
   * The canonical `edbTableHash` of `pred`'s COMPLETE extensional table in this
   * verifier's trusted EDB-of-record, or `undefined` if the verifier does not attest a
   * snapshot for `pred` (ADR 0007 §3.6).
   *
   * OPTIONAL — absent is read as `undefined` (fail-closed). A certifying check binds a
   * cert's sealed extension table for an extensional predicate `p` to the live EDB by
   * requiring `edbTableHash(p, cert.table(p).rows) == leaves.edbSnapshot(p, ctx)`. When
   * this returns `undefined`, the cert cannot bind `p` to a live snapshot, so a cert
   * sealing an extensional `p` is REJECTED (`cert_edb_mismatch`) rather than trusted on
   * the prover's word. A consumer that wants certifiable negation over extensional
   * inputs MUST implement this to return the real snapshot hash. Mirrors Rust's
   * `LeafVerifier::edb_snapshot` (defaults to `None`).
   */
  edbSnapshot?(pred: Symbol, ctx: C): Hash | undefined;
  /**
   * The component's inherent identity. OPTIONAL (non-breaking); ABSENT =
   * {@link ComponentIdentity.unidentified}. See {@link Theory.identity}.
   */
  identity?(): ComponentIdentity;
}

/** The verdict of a `RuleAdmissibility` check (§5a). */
export type RuleOutcome =
  | { readonly kind: "admit" }
  | { readonly kind: "reject"; readonly code: string };

export const RuleOutcome = {
  Admit: { kind: "admit" } as const satisfies RuleOutcome,
  Reject(code: string): RuleOutcome {
    return { kind: "reject", code };
  },
};

/**
 * §5a RuleAdmissibility SPI — validates a `Rule` node's metadata after the core has
 * validated its logical shape. Generic over the context `C`. MUST be total and
 * deterministic over `(clause, meta, ctx)`.
 *
 * spi-role: consumer. A consumer implements this extension point in its own domain; a test
 * double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
 */
export interface RuleAdmissibility<C> {
  admissible(clause: Clause, meta: NodeMeta, ctx: C): RuleOutcome;
  /**
   * The component's inherent identity. OPTIONAL (non-breaking); ABSENT =
   * {@link ComponentIdentity.unidentified}. See {@link Theory.identity}.
   */
  identity?(): ComponentIdentity;
}

/** The no-op `RuleAdmissibility`: admits every rule node (§5a). */
export class AlwaysAdmit<C> implements RuleAdmissibility<C> {
  admissible(_clause: Clause, _meta: NodeMeta, _ctx: C): RuleOutcome {
    return RuleOutcome.Admit;
  }
  /** Canonical identity: core/always-admit@1.0.0, zero config digest (parity with Rust). */
  identity(): ComponentIdentity {
    return ComponentIdentity.of(
      new TextEncoder().encode("core/always-admit"),
      new TextEncoder().encode("1.0.0"),
      new Uint8Array(32),
    );
  }
}

/**
 * A component's inherent identity — the (id, version, configDigest) triple a
 * certificate's meaning depends on (ADR 0004 D4 · parity with the Rust binding's
 * `ComponentIdentity`).
 *
 * A check-only consumer EXPOSES this identity so it can be attested. There is NO
 * check-profile-digest derivation in the go/ts bindings — that lives only in the
 * Rust kernel/seam; these bindings carry the identity, nothing more.
 *
 * The seam is the optional `identity?()` method on {@link Theory},
 * {@link LeafVerifier}, and {@link RuleAdmissibility}: ABSENT = `unidentified()`.
 */
export class ComponentIdentity {
  /** The component's identifier (e.g. utf8 "core/always-admit"). */
  readonly id: Uint8Array;
  /** The component's version (e.g. utf8 "1.0.0"); may be empty. */
  readonly version: Uint8Array;
  /** A 32-byte digest pinning the config; all-zero when there is none (not computed here). */
  readonly configDigest: Uint8Array;

  private constructor(id: Uint8Array, version: Uint8Array, configDigest: Uint8Array) {
    if (configDigest.length !== 32) {
      throw new RangeError(`configDigest must be 32 bytes, got ${configDigest.length}`);
    }
    this.id = id;
    this.version = version;
    this.configDigest = configDigest;
  }

  /** Build a ComponentIdentity from its parts. `configDigest` must be exactly 32 bytes. */
  static of(id: Uint8Array, version: Uint8Array, configDigest: Uint8Array): ComponentIdentity {
    return new ComponentIdentity(id, version, configDigest);
  }

  /**
   * The canonical placeholder identity: id "unidentified", empty version, zero
   * config digest. The reading of an absent `identity?()` (mirrors the Rust
   * `ComponentIdentity::unidentified()` default).
   */
  static unidentified(): ComponentIdentity {
    return new ComponentIdentity(
      new TextEncoder().encode("unidentified"),
      new Uint8Array(0),
      new Uint8Array(32),
    );
  }

  /**
   * Resolve a component's identity under the "absent = unidentified" convention:
   * returns the component's `identity()` if it implements one, else
   * {@link ComponentIdentity.unidentified}. The TS analogue of the go `Identified`
   * type-assertion.
   */
  static resolve(component: {
    identity?(): ComponentIdentity;
  }): ComponentIdentity {
    return component.identity ? component.identity() : ComponentIdentity.unidentified();
  }

  /**
   * Structural identity of two component identities (id bytes, version bytes, config
   * digest). Supported v1 surface (#767, additive per ADR 0003) — the comparison the
   * identity audit rests on; mirrors Rust's derived `PartialEq` and go's `Equal`.
   */
  equals(other: ComponentIdentity): boolean {
    return (
      bytesEq(this.id, other.id) &&
      bytesEq(this.version, other.version) &&
      bytesEq(this.configDigest, other.configDigest)
    );
  }

  /**
   * True iff this is the {@link ComponentIdentity.unidentified} placeholder — the
   * identity-audit primitive for a PLAIN component (#767, supported v1 surface,
   * additive per ADR 0003): an unidentified component contributes only a constant to
   * any derived profile digest, so the digest attests nothing about it. For a
   * `CompoundTheory`, whose identity is a real-looking COMPUTED digest even over
   * all-unidentified members, compare against `compoundIdentityOf` instead — this
   * method alone cannot see through the composition, and the members are deliberately
   * not enumerable (#708).
   */
  isUnidentified(): boolean {
    return this.equals(ComponentIdentity.unidentified());
  }
}

/** Byte-wise equality of two buffers. */
function bytesEq(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) {
    if (a[i] !== b[i]) return false;
  }
  return true;
}

/** A set of predicate `Symbol`s — the extensional predicates a `LeafVerifier` declares. */
export class PredicateSet {
  readonly #preds = new Set<string>();

  static from(preds: Iterable<Symbol | string>): PredicateSet {
    const set = new PredicateSet();
    for (const p of preds) set.insert(p);
    return set;
  }

  /** Membership is by exact predicate bytes (hex-keyed internally). */
  contains(pred: Symbol): boolean {
    return this.#preds.has(symbolKey(pred));
  }

  insert(pred: Symbol | string): void {
    const sym = typeof pred === "string" ? Symbol.of(pred) : pred;
    this.#preds.add(symbolKey(sym));
  }
}

function symbolKey(pred: Symbol): string {
  return Array.from(pred.bytes(), (b) => b.toString(16).padStart(2, "0")).join("");
}
