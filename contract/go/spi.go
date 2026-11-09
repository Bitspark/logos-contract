// The checker-facing extension points — Theory (§5), RuleAdmissibility (§5a),
// LeafVerifier (§6). [STABLE v1] (logos-checker-spi v1).
//
// These are the seams through which everything consumer-specific enters; the core
// check stays consumer-agnostic and merely routes to them.
package contract

import (
	"bytes"
	"crypto/sha256"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// EDBSnapshotHashPrefix is the domain separator for the canonical EDB-table snapshot hash (ADR
// 0007 §3.6), so an EDB-snapshot digest can never collide with a clause id or any
// other hash. Mirrors Rust's EDB_PREFIX.
func EDBSnapshotHashPrefix() []byte { return []byte("logos/account/edb-snapshot/v1\n") }

// EdbTableHash is the canonical snapshot hash of one extensional predicate's table,
// read as a SET — SHA-256(EDBSnapshotHashPrefix ‖ pred-bytes ‖ ontos-codec(Tuple[rows…])), with the
// rows sorted by GroundKey and a repeated row ignored (#2279): order and multiplicity
// never change the hash. This is the value an EdbSnapshotProvider returns for pred over
// its trusted EDB, and the value Check recomputes over a cert's sealed extension table
// to bind that table to the live EDB (the cert_edb_mismatch obligation). The sealed
// table is itself a set (NewRelationTable dedups by the same key), so a snapshot
// provider need not deduplicate its rows first. Byte-identical to Rust's edb_table_hash.
func EdbTableHash(pred Symbol, rows []GroundLiteral) Hash {
	sorted := sortDedupByGroundKey(rows)
	// Reuse each row's labeled-compound value Tuple[Atom(pred), args…] (matching
	// GroundKey's reading) so the canonical bytes are stable + cross-language.
	rowValues := make([]core.Value, len(sorted))
	for i, g := range sorted {
		items := make([]core.Value, 0, len(g.Args)+1)
		items = append(items, core.NewAtom(g.Pred.Bytes()))
		items = append(items, g.Args...)
		rowValues[i] = core.NewTuple(items...)
	}
	h := sha256.New()
	h.Write(EDBSnapshotHashPrefix())
	h.Write(pred.Bytes())
	h.Write(codec.Encode(core.NewTuple(rowValues...)))
	var out Hash
	copy(out[:], h.Sum(nil))
	return out
}

// TheoryOutcome is the verdict of a Theory on a ground atom (§5). It is a closed
// sum type via an unexported marker method (mirroring Rust's enum).
type TheoryOutcome interface {
	isTheoryOutcome()
}

// TheoryHolds is the verdict that the atom holds.
type TheoryHolds struct{}

// TheoryFails is the verdict that the atom is owned by this theory but does not
// hold; Code is a host-band sub-code surfaced under builtin_failed.
type TheoryFails struct {
	Code string
}

// TheoryNotMine is the verdict "not this theory's predicate" (a routing safety
// net; check routes by Theory.Owns, so a correctly-routed call never returns this).
type TheoryNotMine struct{}

func (TheoryHolds) isTheoryOutcome()   {}
func (TheoryFails) isTheoryOutcome()   {}
func (TheoryNotMine) isTheoryOutcome() {}

// Theory is the §5 Theory SPI — builtins / decidable atoms.
//
// Purity is load-bearing (§5). A verdict MUST be a pure, total, deterministic
// function of the ground arguments alone, reproducible from configuration, with no
// I/O, clock, or ledger access — a *parameterized fact*, re-derivable by anyone.
//
// Realization of "config-pinned" (§5, STABLE-v1 erratum). The spec writes
// type Config + decide(atom, cfg). To keep check's signature stable via an
// interface (object-safe — no live ctx), the config is held *inside* the
// implementing value (closed over at construction) rather than threaded as a type
// parameter. Decide therefore takes only the atom; the theory is still config-
// pinned and pure by construction.
//
// spi-role: consumer. A consumer implements this extension point in its own domain; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type Theory interface {
	// Owns reports whether this theory owns (decides) the given predicate. (§4
	// obligation 3 routes Builtin nodes by this; exactly one theory must own each
	// builtin predicate.)
	Owns(pred Symbol) bool

	// Decide decides an owned ground atom. Pure / total / deterministic /
	// config-pinned.
	//
	// The v1 form, kept for external readers: logos's own readers call DecideGround, which can
	// also say "not decided".
	Decide(atom GroundLiteral) TheoryOutcome
}

// GroundDecider is the optional #3126 method of a Theory (seat:caa's rulings of 2026-09-27): decide
// an owned ground atom, or say it was NOT DECIDED. A decider that stops before it establishes a fact
// (a work cap, a capacity) returns NotCompleted(cause), never a false: under negation or in the
// closure check a stop read as Fails becomes a false positive (research 0031). A theory that can
// stop implements it, and its Decide then answers the stopped case with TheoryNotMine, never
// TheoryFails, so a legacy reader fails CLOSED. A composite theory implements it by FORWARDING to
// its members. Additive (ADR 0003): a theory that never stops needs no change. Rust's
// Theory::decide_ground; ADR 0036 D8's checker SPI v2 makes it required.
type GroundDecider interface {
	DecideGround(atom GroundLiteral) completion.TheoryGround
}

// DecideGround is the ONE reader of a theory's ground verdict (#3126): the theory's own
// DecideGround when it implements GroundDecider, else the default derived from Decide
// (GroundFromLegacy). Every logos reader calls it, never Decide.
func DecideGround(t Theory, atom GroundLiteral) completion.TheoryGround {
	atom = atom.detached()
	if g, ok := t.(GroundDecider); ok {
		return g.DecideGround(atom)
	}
	return GroundFromLegacy(t.Decide(atom))
}

// GroundFromLegacy is the mapping DecideGround's default applies to a v1 answer (#3126): Holds and
// Fails are the decision, and TheoryNotMine is the named inconsistent_theory fault. A wrapper whose
// own answers come from Decide uses it for them, and forwards the rest. An outcome no TheoryOutcome
// type names (nil, an unknown type) is the fault malformed_outcome. Rust's ground_from_legacy.
func GroundFromLegacy(o TheoryOutcome) completion.TheoryGround {
	switch out := o.(type) {
	case TheoryHolds:
		return completion.Completed[completion.TheoryDecision, completion.NoCallerLimit](completion.TheoryHolds())
	case TheoryFails:
		return completion.Completed[completion.TheoryDecision, completion.NoCallerLimit](completion.TheoryFails(out.Code))
	case TheoryNotMine:
		return completion.NotCompleted[completion.TheoryDecision, completion.NoCallerLimit](completion.InconsistentTheory())
	default:
		return completion.NotCompleted[completion.TheoryDecision, completion.NoCallerLimit](completion.MalformedOutcome())
	}
}

// LegacyOutcome is the one legacy adapter (#3126): the v1 TheoryOutcome of a DecideGround answer,
// for a theory that implements GroundDecider and derives its Decide from it. A not-completed answer
// becomes TheoryNotMine, never TheoryFails: v1 has no "not decided" arm, and every reader refuses an
// owned atom's NotMine by name, so a legacy reader fails CLOSED. The wrong category (a stop reported
// as a routing fault), never a wrong answer; ADR 0036 D8's v2 deletes it with Decide. Rust's
// legacy_outcome.
func LegacyOutcome(g completion.TheoryGround) TheoryOutcome {
	return completion.MatchTheory[completion.NoCallerLimit, TheoryOutcome](g, legacyCases{})
}

type legacyCases struct{}

func (legacyCases) Holds() TheoryOutcome                                 { return TheoryHolds{} }
func (legacyCases) Fails(code string) TheoryOutcome                      { return TheoryFails{Code: code} }
func (legacyCases) LimitExceeded(completion.NoCallerLimit) TheoryOutcome { return TheoryNotMine{} }
func (legacyCases) NotCompleted(completion.NonCompletion) TheoryOutcome  { return TheoryNotMine{} }

// groundArm is which of a ground verdict's three answers a reader holds.
type groundArm uint8

const (
	groundInvalid groundArm = iota
	groundHolds
	groundFails
	groundNotDecided
)

// groundReading is a ground verdict read once, so each reader switches on three arms: the theory's
// code for a false, the cause for a verdict it did not decide. A LimitExceeded (no caller's limit
// reaches a theory) reads as the fault malformed_outcome.
type groundReading struct {
	arm   groundArm
	code  string
	cause completion.NonCompletion
}

// readGround reads a ground verdict.
func readGround(g completion.TheoryGround) groundReading {
	return completion.MatchTheory[completion.NoCallerLimit, groundReading](g, readCases{})
}

type readCases struct{}

func (readCases) Holds() groundReading { return groundReading{arm: groundHolds} }
func (readCases) Fails(code string) groundReading {
	return groundReading{arm: groundFails, code: code}
}
func (readCases) LimitExceeded(completion.NoCallerLimit) groundReading {
	return groundReading{arm: groundNotDecided, cause: completion.MalformedOutcome()}
}
func (readCases) NotCompleted(cause completion.NonCompletion) groundReading {
	return groundReading{arm: groundNotDecided, cause: cause}
}

// disowned reports whether a not-decided reading is the fault the default reports for a
// TheoryNotMine (#3126): each reader keeps the refusal it gave NotMine for it.
func (r groundReading) disowned() bool {
	return r.arm == groundNotDecided && r.cause.Kind() == completion.KindInconsistentTheory
}

// LeafOutcome is the verdict of a LeafVerifier (§6). Closed sum type.
type LeafOutcome interface {
	isLeafOutcome()
}

// LeafAdmit is the verdict that the leaf is admitted.
type LeafAdmit struct{}

// LeafReject is the verdict that the leaf is rejected; Code is a host-band sub-code
// surfaced under leaf_rejected.
type LeafReject struct {
	Code string
}

func (LeafAdmit) isLeafOutcome()  {}
func (LeafReject) isLeafOutcome() {}

// LeafVerifier is the §6 Leaf SPI — attestation / extensional admission, generic
// over the verification context C.
//
// Leaf verification is *fully delegated* here (v1 decision, §6): the kernel
// verifies no signatures itself — a signature is an arche-style evidence mechanism,
// not a universal property of an extensional leaf. Verify MUST be total and
// deterministic over (atom, evidence, ctx); ctx is an immutable snapshot (no I/O,
// clock, mutable state, or unbounded search) — §6 / G14.
//
// spi-role: consumer. A consumer implements this extension point in its own domain; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type LeafVerifier[C any] interface {
	// Extensional declares the extensional (sealed/leaf) predicate set (§4.2). A
	// Leaf may conclude *only* a predicate in this set.
	Extensional() *PredicateSet

	Verify(atom GroundLiteral, evidence Evidence, ctx C) LeafOutcome
}

// EdbSnapshotProvider is the OPTIONAL EDB-of-record seam (ADR 0007 §3.6). Go
// interfaces carry no default methods, so edb_snapshot is NOT a member of
// LeafVerifier (adding it would break every existing impl). Instead a LeafVerifier
// MAY ALSO implement EdbSnapshotProvider; the certifying Check type-asserts it.
//
// A certifying check binds a cert's sealed extension table for an extensional
// predicate p to the live EDB by requiring EdbTableHash(p, cert.Table(p).Rows) ==
// EdbSnapshot(p, ctx). When a verifier does NOT implement this (or returns ok=false),
// the cert cannot bind p to a live snapshot, so a cert sealing an extensional p is
// rejected (cert_edb_mismatch) rather than trusted on the prover's word — fail-closed.
// A consumer that wants certifiable negation over extensional inputs MUST implement
// this to return the real snapshot hash. This is the non-breaking go form of the Rust
// binding's defaulted LeafVerifier::edb_snapshot method.
//
// spi-role: consumer. The optional go form of a consumer component's defaulted method; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type EdbSnapshotProvider[C any] interface {
	// EdbSnapshot returns the canonical EdbTableHash of pred's *complete* extensional
	// table in this verifier's trusted EDB-of-record, with ok=true; ok=false if the
	// verifier does not attest a snapshot for pred (the fail-closed default).
	EdbSnapshot(pred Symbol, ctx C) (Hash, bool)
}

// RuleOutcome is the verdict of a RuleAdmissibility check (§5a). Closed sum type.
type RuleOutcome interface {
	isRuleOutcome()
}

// RuleAdmit is the verdict that the rule node is admitted.
type RuleAdmit struct{}

// RuleReject is the verdict that the rule node is rejected; Code is a host-band
// sub-code surfaced under rule_inadmissible (e.g. "placement_mismatch").
type RuleReject struct {
	Code string
}

func (RuleAdmit) isRuleOutcome()  {}
func (RuleReject) isRuleOutcome() {}

// RuleAdmissibility is the §5a RuleAdmissibility SPI — validates a Rule node's
// *metadata* after the core has validated its *logical shape*. Generic over the
// context C.
//
// NodeMeta stays opaque to core; only this verifier interprets it. Most consumers
// bind the no-op AlwaysAdmit — a plain engine or any consumer whose clauses are
// fixed/bootstrap needs nothing here. MUST be total and deterministic over
// (clause, meta, ctx); ctx is an immutable snapshot (§5a / G14).
//
// spi-role: consumer. A consumer implements this extension point in its own domain; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type RuleAdmissibility[C any] interface {
	Admissible(clause Clause, meta NodeMeta, ctx C) RuleOutcome
}

// AlwaysAdmit is the no-op RuleAdmissibility: admits every rule node. The default
// for any consumer without provenance-bound clauses (§5a) — costs non-arche
// consumers nothing.
type AlwaysAdmit[C any] struct{}

// Admissible always admits.
func (AlwaysAdmit[C]) Admissible(_ Clause, _ NodeMeta, _ C) RuleOutcome {
	return RuleAdmit{}
}

// Identity reports AlwaysAdmit's canonical component identity (core/always-admit@1.0.0,
// zero config digest). AlwaysAdmit thus implements Identified, paralleling the Rust
// binding's override on the defaulted identity() method.
func (AlwaysAdmit[C]) Identity() ComponentIdentity {
	return NewComponentIdentity([]byte("core/always-admit"), []byte("1.0.0"), [32]byte{})
}

// ComponentIdentity is a component's inherent identity — the (Id, Version,
// ConfigDigest) triple a certificate's meaning depends on (ADR 0004 D4 · parity with
// the Rust binding's ComponentIdentity).
//
// A check-only consumer exposes its component's identity through this contract.
// The kernel derives a negotiated profile and its digest from the live components.
type ComponentIdentity struct {
	// Id is the component's identifier (e.g. []byte("core/always-admit")).
	Id []byte
	// Version is the component's version (e.g. []byte("1.0.0")); may be empty.
	Version []byte
	// ConfigDigest is a 32-byte digest pinning the component's configuration; zero
	// when there is none (the bindings do not compute it).
	ConfigDigest [32]byte
}

// NewComponentIdentity builds a ComponentIdentity from its parts.
func NewComponentIdentity(id, version []byte, configDigest [32]byte) ComponentIdentity {
	return ComponentIdentity{Id: bytes.Clone(id), Version: bytes.Clone(version), ConfigDigest: configDigest}
}

// UnidentifiedComponent is the canonical placeholder identity: Id "unidentified",
// empty version, zero config digest. A component that does not implement Identified
// is treated as this (mirrors the Rust ComponentIdentity::unidentified() default).
func UnidentifiedComponent() ComponentIdentity {
	return NewComponentIdentity([]byte("unidentified"), []byte{}, [32]byte{})
}

// Equal reports structural identity of two component identities (id bytes, version
// bytes, config digest). Supported v1 surface (#767, additive per ADR 0003) — the
// comparison the identity audit rests on; mirrors Rust's derived PartialEq.
func (c ComponentIdentity) Equal(other ComponentIdentity) bool {
	return bytes.Equal(c.Id, other.Id) &&
		bytes.Equal(c.Version, other.Version) &&
		c.ConfigDigest == other.ConfigDigest
}

// IsUnidentified reports whether this is the UnidentifiedComponent placeholder — the
// identity-audit primitive for a PLAIN component (#767, supported v1 surface, additive
// per ADR 0003): an unidentified component contributes only a constant to any derived
// profile digest, so the digest attests nothing about it. For a CompoundTheory, whose
// identity is a real-looking COMPUTED digest even over all-unidentified members,
// compare against CompoundIdentityOf instead — this method alone cannot see through
// the composition, and the members are deliberately not enumerable (#708).
func (c ComponentIdentity) IsUnidentified() bool {
	return c.Equal(UnidentifiedComponent())
}

// Identified is the OPTIONAL identity seam. Go interfaces carry no default methods,
// so identity is NOT a member of Theory / LeafVerifier / RuleAdmissibility (adding it
// would break every existing impl). Instead a component MAY implement Identified; a
// kernel-side consumer type-asserts:
//
//	id := UnidentifiedComponent()
//	if c, ok := component.(Identified); ok {
//		id = c.Identity()
//	}
//
// A component that does NOT implement Identified is treated as UnidentifiedComponent().
// This is the non-breaking go form of the Rust binding's defaulted identity() method.
//
// spi-role: consumer. The optional go form of a consumer component's defaulted method; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type Identified interface {
	// Identity reports the component's inherent (Id, Version, ConfigDigest) identity.
	Identity() ComponentIdentity
}

// CompletionDeclared is the OPTIONAL declaration of a Theory's completion (#3142, research 0031
// row 13), the go form of Rust's defaulted Theory::completion: go interfaces carry no default
// methods, so a theory MAY implement it, and one that does not reads DecisionUndeclared
// (CompletionOf, completion.go), which admission treats as may-not-complete (fail closed). A
// composite routes the question to the member that owns pred.
//
// spi-role: consumer. The optional go form of a consumer component's defaulted method; a test
// double of it may declare consumer(<what it models>) (#2720, scripts/test_doubles_inventory.py).
type CompletionDeclared interface {
	// Completion reports whether the theory's decisions on the owned predicate pred complete.
	Completion(pred Symbol) DecisionCompletion
}

// PredicateSet is a set of predicate Symbols — the extensional predicates a
// LeafVerifier declares (§4.2).
type PredicateSet struct {
	set map[Symbol]struct{}
}

// NewPredicateSet builds an empty PredicateSet.
func NewPredicateSet() *PredicateSet {
	return &PredicateSet{set: make(map[Symbol]struct{})}
}

// PredicateSetOf builds a PredicateSet from predicate strings.
func PredicateSetOf(preds ...string) *PredicateSet {
	ps := NewPredicateSet()
	for _, p := range preds {
		ps.Insert(SymbolFromString(p))
	}
	return ps
}

// Contains reports membership.
func (p *PredicateSet) Contains(pred Symbol) bool {
	_, ok := p.set[pred]
	return ok
}

// Insert adds a predicate to the set.
func (p *PredicateSet) Insert(pred Symbol) {
	p.set[pred] = struct{}{}
}
