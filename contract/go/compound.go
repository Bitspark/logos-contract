// CompoundTheory — the Go binding of the Rust CompoundTheory in contract/rs/src/spi.rs.
// [STABLE-v1 Theory combinator]
//
// A Theory that delegates to an ORDERED list of member theories, routing each predicate
// to the first member that Owns it. This is how a Go consumer binds MORE THAN ONE
// standard theory (e.g. arithmetic + text) behind the single Theory a CheckProfile holds
// — and, because the engine emits a Builtin node only for a predicate its bound theory
// owns (dual-conformance), binding a compound is exactly what makes a standard theory's
// relations reachable in search AND checkable.
//
// # Partition discipline (§4.4)
//
// check requires exactly one theory to own each builtin predicate. The members a compound
// holds MUST own DISJOINT predicate sets; if two members claim the same predicate, Decide
// routes it to the FIRST owner (deterministic, but a mis-binding) — keep the member
// predicate sets disjoint, as the standard theories (arithmetic vs text) are by
// construction.
//
// # Identity
//
// logos-core/compound-theory@1.0.0 with a config digest that commits to the ORDERED
// member identities: a length-prefixed (u64 big-endian) SHA-256 over each member's
// (Id, Version, ConfigDigest), domain-separated by "logos-core/compound-theory/v1\n".
// Byte-identical to the Rust binding (pinned by vectors/compound.json) so a profile
// binding a compound derives the same digest tri-core.
package contract

import (
	"crypto/sha256"
	"encoding/binary"

	"github.com/Bitspark/logos-contract/contract/go/completion"
)

// compoundTheoryPrefix domain-separates the CompoundTheory identity digest, so a
// compound's config digest can never collide with another hash band. Mirrors Rust's
// COMPOUND_THEORY_PREFIX byte-for-byte.
var compoundTheoryPrefix = []byte("logos-core/compound-theory/v1\n")

// CompoundTheory delegates to an ordered list of member theories. Pure / total /
// deterministic — a faithful mirror of Rust's contract::spi::CompoundTheory.
type CompoundTheory struct {
	theories []Theory
}

// NewCompoundTheory builds a compound over theories, routed in order. The members SHOULD
// own disjoint predicate sets (the §4.4 builtin partition extends to the composition).
func NewCompoundTheory(theories ...Theory) CompoundTheory {
	return CompoundTheory{theories: theories}
}

// NewStandardTheory builds the consumer-facing STANDARD gate Theory — a CompoundTheory over
// the four standard checkable theories, in the SAME order the wasm guest binds them
// (app/wasm/rs/src/lib.rs standard_theory()): ArithmeticTheory · TextTheory · TermTheory ·
// ListTheory.
//
// This is the helper a CHECK-side Go consumer binds into its CheckProfile to certify a
// search that uses the guest's builtins. A consumer that hand-assembles a CompoundTheory
// member-by-member must keep it byte-identical to the guest's standard_theory() (same
// members, same order) AND derive its advertised CheckProfileDigest from the same
// components (certify.DeriveCheckProfileDigest) — getting either wrong silently fails to
// certify a perfectly-formed Builtin node (issue #574). Binding NewStandardTheory() removes
// that footgun: it owns EXACTLY the predicate set the guest evaluates in search
// (is =:= =\= < > >= =< · contains starts_with ends_with · atom atomic compound is_list
// number == \== @< @> @=< @>= =.. = \= true fail false · length nth0 last), so every Builtin node the guest can emit
// routes to an owner under check, and its Identity() is the stable CompoundTheory digest the
// kernel's DeriveCheckProfileDigest folds in. A sync-guard test pins this owned set tri-core.
func NewStandardTheory() CompoundTheory {
	return NewCompoundTheory(
		NewArithmeticTheory(),
		NewTextTheory(),
		NewTermTheory(),
		NewListTheory(),
	)
}

// compile-time proofs that the compound satisfies the SPI seam (Theory + Identified).
var (
	_ Theory     = CompoundTheory{}
	_ Identified = CompoundTheory{}
)

// Owns reports whether ANY member owns pred (the union of the members' predicates).
func (c CompoundTheory) Owns(pred Symbol) bool {
	for _, t := range c.theories {
		if t.Owns(pred) {
			return true
		}
	}
	return false
}

// Decide routes the atom to the FIRST member that owns its predicate (members own
// disjoint sets, so "first" is "the" owner). No member owns it → TheoryNotMine — a
// routing safety net; check routes by Owns, so a correctly-routed call always finds an
// owner. Mirrors Rust's CompoundTheory::decide.
func (c CompoundTheory) Decide(atom GroundLiteral) TheoryOutcome {
	for _, t := range c.theories {
		if t.Owns(atom.Pred) {
			return t.Decide(atom)
		}
	}
	return TheoryNotMine{}
}

// compile-time proof that the compound forwards the #3126 ground verdict.
var _ GroundDecider = CompoundTheory{}

// DecideGround forwards to the FIRST member that owns the atom's predicate (#3126), through that
// member's own ground verdict, never the default: the default would read a member's TheoryNotMine
// (the answer a stopping member gives its legacy Decide) as a fault instead of the member's own
// non-completion. No member owns it: the inconsistent_theory fault. Mirrors Rust's
// CompoundTheory::decide_ground.
func (c CompoundTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	for _, t := range c.theories {
		if t.Owns(atom.Pred) {
			return DecideGround(t, atom)
		}
	}
	return completion.NotCompleted[completion.TheoryDecision, completion.NoCallerLimit](completion.InconsistentTheory())
}

// Identity reports logos-core/compound-theory@1.0.0 with a config digest that commits to
// the ordered member identities — a length-prefixed (u64 big-endian) SHA-256, mirroring
// the Rust scheme byte-for-byte (pinned by vectors/compound.json). Delegates to
// CompoundIdentityOf so the identity-audit baseline and the live identity share ONE
// code path and cannot drift (#767).
func (c CompoundTheory) Identity() ComponentIdentity {
	memberIdentities := make([]ComponentIdentity, len(c.theories))
	for i, t := range c.theories {
		id := identityOf(t)
		memberIdentities[i] = NewComponentIdentity(id.Id, id.Version, id.ConfigDigest)
	}
	return CompoundIdentityOf(memberIdentities)
}

// CompoundIdentityOf reports the ComponentIdentity a CompoundTheory over members with
// exactly these identities reports — the same fold Identity delegates to.
//
// Supported v1 surface (#767, additive per ADR 0003). This is the identity-audit
// primitive for a COMPOUND: a compound's Identity() is a computed digest that reads as
// evidence even when every member is unidentified, and its members are deliberately
// not enumerable (the #708 hazard). The audit therefore never inspects members — the
// party that CONSTRUCTED the compound knows its member count n, and compares:
//
//	unids := make([]ComponentIdentity, n)
//	for i := range unids {
//		unids[i] = UnidentifiedComponent()
//	}
//	distinguishable := !live.Equal(CompoundIdentityOf(unids))
//
// Equality with the baseline means no member contributes anything distinguishable —
// the digest computes but attests nothing. Member ORDER and COUNT are identity-bearing
// (the fold commits to both), so the baseline must be built for the same n the live
// compound was constructed with.
//
// Inequality proves at least ONE member is distinguishable — not that all are. A
// compound with one identified member among unidentified ones reads distinguishable
// while the others contribute constants (the vector's identified_first case pins
// exactly this). A constructor who needs "every member attested" has a stronger check
// available from the same helper: compare the live identity against CompoundIdentityOf
// over the member identities they INTENDED to bind — equality there proves exact
// membership, in order. (The identity_audit_vectors replays exercise that comparison
// for every case.)
func CompoundIdentityOf(memberIdentities []ComponentIdentity) ComponentIdentity {
	h := sha256.New()
	h.Write(compoundTheoryPrefix)
	lenBuf := make([]byte, 8)
	for _, id := range memberIdentities {
		binary.BigEndian.PutUint64(lenBuf, uint64(len(id.Id)))
		h.Write(lenBuf)
		h.Write(id.Id)
		binary.BigEndian.PutUint64(lenBuf, uint64(len(id.Version)))
		h.Write(lenBuf)
		h.Write(id.Version)
		h.Write(id.ConfigDigest[:])
	}
	var digest [32]byte
	copy(digest[:], h.Sum(nil))
	return NewComponentIdentity([]byte("logos-core/compound-theory"), []byte("1.0.0"), digest)
}

// identityOf reports a member's identity, mirroring Rust's defaulted Theory::identity():
// a member that implements the optional Identified seam reports its own identity; one
// that does not is the unidentified placeholder.
func identityOf(t Theory) ComponentIdentity {
	if ident, ok := t.(Identified); ok {
		return ident.Identity()
	}
	return UnidentifiedComponent()
}
