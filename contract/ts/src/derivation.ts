// §3 Derivation — the shared DTO, the heart. [FIRM]
// TS sibling of contract/rs/src/derivation.rs.
//
// A finite DAG of nodes; each node concludes a ground literal; premises reference
// earlier nodes (acyclic). The node set is closed and positive: Rule | Builtin |
// Leaf.

import { type Value } from "@bitspark/ontos-core";
import { type CertId, type ClosedModelCert, type NonMemberProof } from "./cert.js";
import { type GroundLiteral } from "./literal.js";
import { type ClauseId, type PredicateRef, type ProjectSpec } from "./program.js";
import { type Subst } from "./term.js";

/**
 * Provenance / placement metadata attached to a `Rule` node. Opaque to the core —
 * only a `RuleAdmissibility` verifier interprets it. Modelled as an optional ontos
 * value the kernel never inspects.
 */
export class NodeMeta {
  readonly #value: Value | undefined;

  private constructor(value: Value | undefined) {
    this.#value = value;
    Object.freeze(this);
  }

  /** Empty metadata (the common case). */
  static none(): NodeMeta {
    return new NodeMeta(undefined);
  }

  /** Pack a consumer value as rule metadata. */
  static of(value: Value): NodeMeta {
    return new NodeMeta(value);
  }

  /** The packed value, for a consumer's `RuleAdmissibility` to interpret. */
  value(): Value | undefined {
    return this.#value;
  }
}

/**
 * Attestation / admission evidence attached to a `Leaf` node. Opaque to the core —
 * only a `LeafVerifier` interprets it.
 */
export class Evidence {
  readonly #value: Value | undefined;

  private constructor(value: Value | undefined) {
    this.#value = value;
    Object.freeze(this);
  }

  /** No evidence (e.g. a trusted axiom leaf). */
  static none(): Evidence {
    return new Evidence(undefined);
  }

  /** Pack consumer evidence for a `LeafVerifier` to interpret. */
  static of(value: Value): Evidence {
    return new Evidence(value);
  }

  /** The packed value, for a consumer's `LeafVerifier` to interpret. */
  value(): Value | undefined {
    return this.#value;
  }
}

/**
 * A negated `Rule` premise `\+ atom` (ADR 0007) — discharged NOT by an earlier node
 * but as a checked side-condition: the negated atom `r(a)` must be ABSENT from a
 * cited, already-verified `ClosedModelCert`. This is what makes absence sound rather
 * than an upper bound — the cert proves the sealed relation is exact. TS sibling of
 * Rust's `Premise::Neg` variant.
 */
export class NegPremise {
  readonly kind = "neg" as const;
  /** The grounded negated atom that must be absent from the sealed relation. */
  readonly atom: GroundLiteral;
  /** Index into `Derivation.closedWorld` of the certificate to consult. */
  readonly cert: CertId;
  /** How non-membership is witnessed (a direct table lookup in v1). */
  readonly nonmember: NonMemberProof;

  constructor(atom: GroundLiteral, cert: CertId, nonmember: NonMemberProof = "direct_lookup") {
    this.atom = atom;
    this.cert = cert;
    this.nonmember = nonmember;
    Object.freeze(this);
  }
}

/** One `(position, value)` of a `CountPremise`'s GROUND filter (ADR 0023). */
export interface GroundFilterEntry {
  readonly pos: number;
  readonly value: Value;
}

/**
 * A certifiable `count` / `count_distinct` `Rule` premise (ADR 0023) — discharged NOT by
 * an earlier node but as a checked side-condition: the checker recomputes the cardinality
 * over `closedWorld[cert].table(pred)` — a relation it has independently proven exact — and
 * accepts only if it equals the claimed `k`. TS sibling of Rust's `Premise::Count` variant.
 */
export class CountPremise {
  readonly kind = "count" as const;
  /** The sealed relation being counted — matched by name AND arity (#581). */
  readonly pred: PredicateRef;
  /** The ground bound-position filter selecting the counted rows. */
  readonly filter: readonly GroundFilterEntry[];
  /** `rows` (count) or `distinct{attr}` (count_distinct). */
  readonly project: ProjectSpec;
  /** The CLAIMED cardinality, as the canonical ontos/data int ground value. */
  readonly k: Value;
  /** Index into `Derivation.closedWorld` of the certificate to consult. */
  readonly cert: CertId;

  constructor(
    pred: PredicateRef,
    filter: readonly GroundFilterEntry[],
    project: ProjectSpec,
    k: Value,
    cert: CertId,
  ) {
    this.pred = pred;
    this.filter = Object.freeze(Array.from(filter));
    this.project = project;
    this.k = k;
    this.cert = cert;
    Object.freeze(this);
  }
}

/**
 * A `Rule` premise — one per clause body literal, with polarity (ADR 0007 / ADR 0023).
 *
 * - A bare `number` discharges a POSITIVE body literal by an earlier derivation node
 *   (the same backward edge today's account carried as a bare index — so existing
 *   all-positive `premises: [0, 2]` lists keep constructing unchanged: a bare index
 *   lifts to `Premise::Pos`, mirroring Rust's `From<usize> for Premise`).
 * - A `NegPremise` discharges a NEGATED body literal `\+ r(a)` against a cited cert.
 * - A `CountPremise` discharges a `count`/`count_distinct` body literal against a cited cert.
 */
export type Premise = number | NegPremise | CountPremise;

/** True iff `p` is a negated premise (a checked cert side-condition). */
export function isNegPremise(p: Premise): p is NegPremise {
  return typeof p !== "number" && p.kind === "neg";
}

/** True iff `p` is a count premise (a checked cert side-condition). */
export function isCountPremise(p: Premise): p is CountPremise {
  return typeof p !== "number" && p.kind === "count";
}

/** The positive node index of a `Premise`, or `undefined` if it is a checked side-condition. */
export function premiseNode(p: Premise): number | undefined {
  return typeof p === "number" ? p : undefined;
}

/** A derivation node. Every kind concludes a `GroundLiteral`. Discriminated by `kind`. */
export type Node = RuleNode | BuiltinNode | LeafNode;

/** Intensional step: instantiate a cited clause. */
export class RuleNode {
  readonly kind = "rule" as const;
  readonly conclusion: GroundLiteral;
  readonly clause: ClauseId;
  /** Grounding substitution applied to the clause. */
  readonly subst: Subst;
  /**
   * One premise per body literal, in body order. A bare `number` is a positive
   * premise (node index `< this node's index`); a `NegPremise` is a checked cert
   * side-condition (ADR 0007). A bare-index list is exactly the pre-amendment shape.
   */
  readonly premises: readonly Premise[];
  /** Opaque to core (provenance / projection binding / …). */
  readonly meta: NodeMeta;

  constructor(
    conclusion: GroundLiteral,
    clause: ClauseId,
    subst: Subst,
    premises: readonly Premise[],
    meta: NodeMeta = NodeMeta.none(),
  ) {
    this.conclusion = conclusion;
    this.clause = clause;
    this.subst = subst;
    this.premises = Object.freeze(Array.from(premises));
    this.meta = meta;
    Object.freeze(this);
  }
}

/**
 * A theory/builtin atom, decided by the `Theory` SPI (§5). Carries no `TheoryId` —
 * dispatch is by predicate ownership.
 */
export class BuiltinNode {
  readonly kind = "builtin" as const;
  readonly conclusion: GroundLiteral;

  constructor(conclusion: GroundLiteral) {
    this.conclusion = conclusion;
    Object.freeze(this);
  }
}

/** An extensional leaf, admitted by the `LeafVerifier` SPI (§6), not derived. */
export class LeafNode {
  readonly kind = "leaf" as const;
  readonly conclusion: GroundLiteral;
  readonly evidence: Evidence;

  constructor(conclusion: GroundLiteral, evidence: Evidence = Evidence.none()) {
    this.conclusion = conclusion;
    this.evidence = evidence;
    Object.freeze(this);
  }
}

/** The ground literal a node concludes (every kind has one). */
export function nodeConclusion(node: Node): GroundLiteral {
  return node.conclusion;
}

/**
 * A finite DAG of nodes with a distinguished `root` (an index into `nodes`), plus the
 * `ClosedModelCert`s the derivation's `Neg` premises cite (ADR 0007).
 *
 * Additive: `closedWorld` defaults to empty; an all-positive, empty-`closedWorld`
 * derivation is exactly today's account, and `check` over it behaves byte-identically
 * — the certificate machinery is only consulted when a `NegPremise` (and hence a
 * non-empty `closedWorld`) is present. Mirrors Rust's `Derivation.closed_world`.
 */
/**
 * **This class IS the account.**
 *
 * `Account` is not a separate type and never has been — it is the name the v2 design and
 * ADR 0003 give to *this* artifact:
 *
 * - ADR 0003's layer table: **"A. Account / proof artifact"** → `Derivation`
 *   (`Rule|Theory|Leaf`), **FIRM / invariant** per ADR 0001.
 * - `docs/spec/logos-contract.md`: *"the account grammar — the `Derivation` node set"*.
 * - v2 §0 glossary: *"**Account** — a derivation in the core evidence language (§8.3)"*.
 *
 * So a plan item written `Account::foo()` is a method on `Derivation` — e.g. v2 §8.2's
 * `Account::is_self_contained()` ships as `Derivation.isSelfContained`.
 *
 * ⚠ Stated because a **declaration-shaped** search (`class|interface|type Account`) returns
 * zero and reads as *"unbuilt"*. Two agents concluded exactly that on 2026-08-29; the
 * mapping was already in the three documents above and neither looked, because a code-shaped
 * question invites a code-shaped search. **This note cannot make that query succeed** — only
 * a public alias could, and adding a public name to FIRM layer A is outside ADR 0003's
 * additive permission and is not a documentation change. What it does is make a plain search
 * for `account` state the identity outright instead of only alluding to it.
 */
export class Derivation {
  readonly nodes: readonly Node[];
  readonly root: number;
  /**
   * The closed-model certificates this derivation CARRIES, indexed by `CertId`: every
   * certificate its `Neg` and `Count` premises cite, at the index they cite it by. The in-tree
   * producer carries the prefix up to the highest cited certificate, and none when nothing is
   * cited (#2533), so a carried certificate is not by itself a dependency: read the citations.
   */
  readonly closedWorld: readonly ClosedModelCert[];

  constructor(nodes: Iterable<Node>, root: number, closedWorld: Iterable<ClosedModelCert> = []) {
    this.nodes = Object.freeze(Array.from(nodes));
    this.root = root;
    this.closedWorld = Object.freeze(Array.from(closedWorld));
    Object.freeze(this);
  }

  /**
   * Whether this account can be checked against a **trivial** context — no closure
   * certificates to resolve against.
   *
   * §8.2 of the v2 design: *"an account is portable iff it is either fully
   * self-contained or carries authenticated …"*. This is the **first arm**, and it is the
   * account-side mirror of the kernel seam's `CheckContext.isTrivial` (named in prose, not
   * imported: `contract` is the bottom tier and does not depend on `kernel` — ADR 0004).
   *
   * The polarity it reads is already load-bearing in `check`: a non-empty `closedWorld` is
   * a *certifying* check that needs a bound cert context, and for an all-positive
   * derivation the context is never consulted.
   *
   * ⚠ **Deliberately HALF of its mirror, and that asymmetry is the point.**
   * `CheckContext.isTrivial` is two-half (base commitments AND certificates); this is the
   * **closure half only** — the base-facts half has no account-side carrier, because
   * contract's `check` reads `base_commitments` **nowhere** (0 references). Widen this when
   * base facts become context-dependent. An `&&` over a field nothing reads would be
   * **vacuously true** and would read as coverage it does not provide (ruled 2026-08-29,
   * `seat:cca`).
   */
  isSelfContained(): boolean {
    return this.closedWorld.length === 0;
  }
}
