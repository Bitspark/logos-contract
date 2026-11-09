// CompoundTheory — the TS binding of the Rust CompoundTheory in contract/rs/src/spi.rs
// and the Go CompoundTheory in contract/go/compound.go. [STABLE-v1 Theory combinator]
//
// A Theory that delegates to an ORDERED list of member theories, routing each predicate
// to the first member that owns it. This is how a TS consumer binds MORE THAN ONE
// standard theory (e.g. arithmetic + text) behind the single Theory a CheckProfile holds
// — and, because the engine emits a Builtin node only for a predicate its bound theory
// owns (dual-conformance), binding a compound is exactly what makes a standard theory's
// relations reachable in search AND checkable.
//
// # Partition discipline (§4.4)
//
// check requires exactly one theory to own each builtin predicate. The members a compound
// holds MUST own DISJOINT predicate sets; if two members claim the same predicate,
// decide routes it to the FIRST owner (deterministic, but a mis-binding) — keep the
// member predicate sets disjoint, as the standard theories (arithmetic vs text) are by
// construction.
//
// # Identity
//
// logos-core/compound-theory@1.0.0 with a config digest that commits to the ORDERED
// member identities: a length-prefixed (u64 big-endian) SHA-256 over each member's
// (id, version, configDigest), domain-separated by "logos-core/compound-theory/v1\n".
// Byte-identical to the Rust/Go bindings (pinned by vectors/compound.json) so a profile
// binding a compound derives the same digest tri-core.

import { sha256 } from "@noble/hashes/sha2.js";
import { copyOctets } from "./octets.js";
import { hashFromBytes } from "./cert.js";

import { newArithmeticTheory } from "./arithmetic.js";
import { type GroundLiteral, Symbol } from "./literal.js";
import { newListTheory } from "./list_theory.js";
import { fault, notCompleted, type TheoryGround } from "./completion.js";
import { ComponentIdentity, completionOf, decideGround, DecisionCompletion, type Theory, TheoryOutcome } from "./spi.js";
import { newTermTheory } from "./term_theory.js";
import { newTextTheory } from "./text.js";

const utf8Encoder = new TextEncoder();

// Domain separator for the CompoundTheory identity digest — mirrors Rust's
// COMPOUND_THEORY_PREFIX / Go's compoundTheoryPrefix byte-for-byte.
const COMPOUND_THEORY_PREFIX = utf8Encoder.encode("logos-core/compound-theory/v1\n");

/**
 * A {@link Theory} that delegates to an ORDERED list of member theories, routing each
 * predicate to the first member that owns it. Pure / total / deterministic — a faithful
 * mirror of Rust's `contract::spi::CompoundTheory` and the Go `CompoundTheory`.
 */
export class CompoundTheory implements Theory {
  private readonly theories: readonly Theory[];

  /**
   * Build a compound over `theories`, routed in order. The members SHOULD own disjoint
   * predicate sets (the §4.4 builtin partition extends to the composition).
   */
  constructor(theories: readonly Theory[]) {
    this.theories = theories;
  }

  /** owns reports whether ANY member owns `pred` (the union of the members' predicates). */
  owns(pred: Symbol): boolean {
    return this.theories.some((t) => t.owns(pred));
  }

  /**
   * Routes the atom to the FIRST member that owns its predicate (members own disjoint
   * sets, so "first" is "the" owner). No member owns it → NotMine — a routing safety net;
   * check routes by owns, so a correctly-routed call always finds an owner.
   */
  decide(atom: GroundLiteral): TheoryOutcome {
    for (const t of this.theories) {
      if (t.owns(atom.pred)) {
        return t.decide(atom);
      }
    }
    return TheoryOutcome.NotMine;
  }

  /**
   * Forwarded to the FIRST member that owns the atom's predicate (#3126), through that member's
   * own ground verdict, never the default: the default would read a member's `not_mine` (the
   * answer a stopping member gives its legacy `decide`) as a fault instead of the member's own
   * non-completion. No member owns it: the `inconsistent_theory` fault. Mirrors Rust/Go.
   */
  decideGround(atom: GroundLiteral): TheoryGround {
    for (const t of this.theories) {
      if (t.owns(atom.pred)) {
        return decideGround(t, atom);
      }
    }
    return notCompleted(fault("inconsistent_theory"));
  }

  /**
   * #3142: the declaration of the member that decides `pred`, routed as {@link decide} routes (the
   * first owner). A predicate no member owns reads undeclared naming the compound.
   */
  completion(pred: Symbol): DecisionCompletion {
    for (const t of this.theories) {
      if (t.owns(pred)) {
        return completionOf(t, pred);
      }
    }
    return DecisionCompletion.undeclared(this.identity());
  }

  /**
   * logos-core/compound-theory@1.0.0 with a config digest committing to the ordered
   * member identities — a length-prefixed (u64 big-endian) SHA-256, mirroring the Rust/Go
   * scheme byte-for-byte (pinned by vectors/compound.json). A member that does not
   * implement the optional `identity()` reads as {@link ComponentIdentity.unidentified}.
   */
  identity(): ComponentIdentity {
    // Delegates to compoundIdentityOf so the identity-audit baseline and the live
    // identity share ONE code path and cannot drift (#767).
    return compoundIdentityOf(
      this.theories.map((t) => ComponentIdentity.resolve(t)),
    );
  }
}

/**
 * The {@link ComponentIdentity} a {@link CompoundTheory} over members with exactly
 * these identities reports — the same fold `identity()` delegates to.
 *
 * **Supported v1 surface (#767, additive per ADR 0003).** This is the identity-audit
 * primitive for a COMPOUND: a compound's `identity()` is a computed digest that reads
 * as evidence even when every member is unidentified, and its members are deliberately
 * not enumerable (the #708 hazard). The audit therefore never inspects members — the
 * party that CONSTRUCTED the compound knows its member count `n`, and compares:
 *
 * ```ts
 * const baseline = compoundIdentityOf(
 *   Array.from({ length: n }, () => ComponentIdentity.unidentified()),
 * );
 * const distinguishable = !liveIdentity.equals(baseline);
 * ```
 *
 * Equality with the baseline means no member contributes anything distinguishable —
 * the digest computes but attests nothing. Member ORDER and COUNT are identity-bearing
 * (the fold commits to both), so the baseline must be built for the same `n` the live
 * compound was constructed with.
 *
 * Inequality proves at least ONE member is distinguishable — not that all are. A
 * compound with one identified member among unidentified ones reads distinguishable
 * while the others contribute constants (the vector's `identified_first` case pins
 * exactly this). A constructor who needs "every member attested" has a stronger check
 * available from the same helper: compare the live identity against
 * `compoundIdentityOf` over the member identities they INTENDED to bind — equality
 * there proves exact membership, in order. (The `identity_audit_vectors` replays
 * exercise that comparison for every case.)
 */
export function compoundIdentityOf(
  memberIdentities: readonly ComponentIdentity[],
): ComponentIdentity {
  const parts: Uint8Array[] = [COMPOUND_THEORY_PREFIX];
  for (const report of memberIdentities) {
    const id = copyOctets(report.id);
    const version = copyOctets(report.version);
    const config = hashFromBytes(report.configDigest);
    parts.push(u64be(id.length), id, u64be(version.length), version, config);
  }
  const digest = sha256(concatBytes(parts));
  return ComponentIdentity.of(
    utf8Encoder.encode("logos-core/compound-theory"),
    utf8Encoder.encode("1.0.0"),
    digest,
  );
}

/** Build a compound over `theories`, routed in order. */
export function newCompoundTheory(...theories: Theory[]): CompoundTheory {
  return new CompoundTheory(theories);
}

/**
 * The consumer-facing STANDARD gate Theory — a CompoundTheory over the four standard
 * checkable theories, in the SAME order the wasm guest binds them (app/wasm/rs/src/lib.rs
 * standard_theory()): ArithmeticTheory · TextTheory · TermTheory · ListTheory.
 *
 * This is the helper a CHECK-side TS consumer binds into its CheckProfile to certify a
 * search that uses the guest's builtins. A consumer that hand-assembles a CompoundTheory
 * member-by-member must keep it byte-identical to the guest's standard_theory() (same
 * members, same order) AND derive its advertised CheckProfileDigest from the same components
 * (deriveCheckProfileDigest) — getting either wrong silently fails to certify a
 * perfectly-formed Builtin node (issue #574). Binding newStandardTheory() removes that
 * footgun: it owns EXACTLY the predicate set the guest evaluates in search
 * (is =:= =\= < > >= =< · contains starts_with ends_with · atom atomic compound is_list
 * number == \== @< @> @=< @>= =.. = \= true fail false · length nth0 last), so every Builtin node the guest can emit
 * routes to an owner under check, and its identity() is the stable CompoundTheory digest the
 * kernel's deriveCheckProfileDigest folds in. A sync-guard test pins this owned set tri-core.
 */
export function newStandardTheory(): CompoundTheory {
  return newCompoundTheory(newArithmeticTheory(), newTextTheory(), newTermTheory(), newListTheory());
}

/** The 8-byte big-endian encoding of `n` (the u64 length prefix; mirrors Rust's to_be_bytes). */
function u64be(n: number): Uint8Array {
  const buf = new Uint8Array(8);
  new DataView(buf.buffer).setBigUint64(0, BigInt(n), false); // false = big-endian
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
