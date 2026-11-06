// §3 (ADR 0007) Closed-model certificate — the sealed, finite, exact relation a
// negated premise \+ r(a) discharges against. [FIRM amendment · additive]
//
// A \+ r(a) is sound only if the checker can verify that *all* of r has been
// enumerated and that the enumeration is *exact* (no junk, no missing heads) under
// this program / EDB / profile / stratification. That argument is a ClosedModelCert:
// a sealed finite model of a stratum prefix, carrying
//
//   - the scope it seals (StratumPrefix),
//   - the pins it is sealed against (program / profile / context / theory-config
//     hashes, EDB snapshot hashes),
//   - the finite domains every value must stay within (FiniteDomain),
//   - the exact extensions (relation tables) of the sealed predicates (RelationTable),
//   - a support witness (every sealed fact has a witness ⇒ E ⊆ least model) and a
//     closure witness (every satisfied rule grounding has its head present ⇒ least
//     model ⊆ E); together E is exact, so a ∉ E ⇒ a is false — absence is sound, not
//     merely an upper bound,
//   - a CertSizeDecl of declared sizes the checker validates against its budgets
//     *before* any scan.
//
// Go sibling of contract/rs/src/cert.rs; the canonical-ordering (sort+dedup)
// constructors keep membership/scope/domain decisions a canonical binary search,
// byte-identical across {rs,go}.
package contract

import (
	"bytes"
	"sort"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// Hash is a 32-byte pin (e.g. a SHA-256 digest). The contract carries the raw bytes;
// how a hash is *computed* is a consumer/kernel concern (the contract never learns
// the scheme — it only compares pins for equality). Mirrors Rust's Hash = [u8; 32].
type Hash = [32]byte

// IndexOffset turns a protocol index into a host offset into a collection of length n, and is the
// ONLY place one becomes the other (#2735): ok only when i < n. A protocol index is an integer in
// 0..=IndexMax, held as uint64 on every platform; an index past the collection is never an offset,
// so check refuses it by name (root_out_of_range, cert_out_of_range) instead of any decode limit.
func IndexOffset(i uint64, n int) (int, bool) {
	if n <= 0 || i >= uint64(n) {
		return 0, false
	}
	return int(i), true
}

// CertId is an index into Derivation.ClosedWorld, a protocol integer (#2735).
type CertId struct {
	idx uint64
}

// NewCertId builds a CertId from an index.
func NewCertId(i uint64) CertId { return CertId{idx: i} }

// Index returns the cert's index into Derivation.ClosedWorld.
func (c CertId) Index() uint64 { return c.idx }

// Offset is the cert's host offset into a ClosedWorld of length n, ok only when it is in range.
func (c CertId) Offset(n int) (int, bool) { return IndexOffset(c.idx, n) }

// NonMemberProof is how a \+ r(a) premise's non-membership is witnessed against the
// cited cert. In v1 the only form is DirectLookup — the checker scans the sealed
// RelationTable directly. The type exists so a future compression scheme (e.g. a
// sorted-run / Merkle non-membership proof) is an *additive* variant.
type NonMemberProof int

const (
	// DirectLookup is a direct membership scan of the sealed relation table.
	DirectLookup NonMemberProof = iota
)

// StratumPrefix is the scope a ClosedModelCert seals: a stratum prefix — all
// predicates up to (and including) stratification Level. A prefix (not a single
// predicate) is needed because mutually-recursive positive SCCs must be sealed
// together. Predicates is kept sorted + deduped (by Symbol byte order) so membership
// and scope-equality are canonical; build one via NewStratumPrefix.
type StratumPrefix struct {
	// Level is the stratification level this prefix seals (predicates at levels 0..=Level).
	Level uint32
	// Predicates is the sealed predicate symbols, sorted + deduped. Invariant, not
	// a hint (#839): Seals is a binary search, so a struct literal built with
	// unsorted predicates compiles fine and then fails membership lookups
	// arbitrarily. Build via NewStratumPrefix; verifyCert rejects a non-canonical
	// prefix up front.
	Predicates []Symbol
}

// NewStratumPrefix builds a prefix, sorting + deduping the predicate set canonically.
func NewStratumPrefix(level uint32, predicates []Symbol) StratumPrefix {
	preds := append([]Symbol(nil), predicates...)
	sort.Slice(preds, func(i, j int) bool { return lessBytes(preds[i].Bytes(), preds[j].Bytes()) })
	preds = dedupSymbols(preds)
	return StratumPrefix{Level: level, Predicates: preds}
}

// IsCanonical reports whether Predicates is actually sorted + deduped (strictly
// increasing by Symbol byte order) — the invariant Seals relies on. A struct
// literal can violate it; NewStratumPrefix cannot.
func (s StratumPrefix) IsCanonical() bool {
	for i := 1; i < len(s.Predicates); i++ {
		if !lessBytes(s.Predicates[i-1].Bytes(), s.Predicates[i].Bytes()) {
			return false
		}
	}
	return true
}

// Seals reports whether pred is sealed by this prefix (canonical binary search).
func (s StratumPrefix) Seals(pred Symbol) bool {
	target := pred.Bytes()
	i := sort.Search(len(s.Predicates), func(i int) bool {
		return !lessBytes(s.Predicates[i].Bytes(), target)
	})
	return i < len(s.Predicates) && s.Predicates[i].Equal(pred)
}

// dedupSymbols removes adjacent duplicate symbols from a sorted slice.
func dedupSymbols(sorted []Symbol) []Symbol {
	if len(sorted) == 0 {
		return sorted
	}
	out := sorted[:1]
	for _, s := range sorted[1:] {
		if !out[len(out)-1].Equal(s) {
			out = append(out, s)
		}
	}
	return out
}

// FiniteDomain is a finite, typed value domain — the set of values an argument of a
// sealed predicate may take. The closure join never enumerates them (#1829); a satisfied
// grounding whose head value escapes every domain is cert_out_of_domain. Values is
// kept sorted + deduped by canonical ontos-codec bytes (ontos Value has no Ord), so
// domain membership is a canonical binary search.
type FiniteDomain struct {
	// TypeTag is an opaque type tag naming this domain (e.g. subject, action).
	TypeTag Symbol
	// Values is the domain's values, sorted + deduped by canonical codec bytes.
	// Invariant, not a hint (#839): Contains is a binary search, so a struct
	// literal built with unsorted values compiles fine and then reports present
	// values absent, arbitrarily per lookup. Build via NewFiniteDomain; verifyCert
	// rejects a non-canonical domain up front.
	Values []core.Value
}

// NewFiniteDomain builds a domain, sorting + deduping its values by canonical codec
// bytes.
func NewFiniteDomain(typeTag Symbol, values []core.Value) FiniteDomain {
	vs := append([]core.Value(nil), values...)
	sortValuesByCodec(vs)
	vs = dedupValues(vs)
	return FiniteDomain{TypeTag: typeTag, Values: vs}
}

// IsCanonical reports whether Values is actually sorted + deduped (strictly
// increasing by canonical codec bytes) — the invariant Contains relies on. A
// struct literal can violate it; NewFiniteDomain cannot.
func (d FiniteDomain) IsCanonical() bool {
	for i := 1; i < len(d.Values); i++ {
		if !lessBytes(codec.Encode(d.Values[i-1]), codec.Encode(d.Values[i])) {
			return false
		}
	}
	return true
}

// Contains reports whether this domain contains v (canonical binary search by codec
// bytes).
func (d FiniteDomain) Contains(v core.Value) bool {
	key := codec.Encode(v)
	i := sort.Search(len(d.Values), func(i int) bool {
		return !lessBytes(codec.Encode(d.Values[i]), key)
	})
	return i < len(d.Values) && d.Values[i].Equal(v)
}

// RelationTable is the exact extension (relation table) of one sealed predicate:
// every ground fact the sealed least model assigns to Pred. Membership and absence
// are decided against this table (the rows are kept sorted + deduped by canonical
// codec bytes).
type RelationTable struct {
	Pred  Symbol
	Arity uint32
	// Rows is the exact rows, sorted + deduped by canonical codec bytes (GroundKey).
	// Invariant, not a hint (#839): Contains is a binary search, so a struct
	// literal built with unsorted rows compiles fine and then reports present rows
	// absent, arbitrarily per lookup. Build via NewRelationTable; verifyCert
	// rejects a non-canonical table up front.
	Rows []GroundLiteral
}

// NewRelationTable builds a table, sorting + deduping its rows by canonical codec
// bytes.
func NewRelationTable(pred Symbol, arity uint32, rows []GroundLiteral) RelationTable {
	return RelationTable{Pred: pred, Arity: arity, Rows: sortDedupByGroundKey(rows)}
}

// IsCanonical reports whether Rows is actually sorted + deduped (strictly
// increasing by GroundKey) — the invariant Contains relies on. A struct literal
// can violate it; NewRelationTable cannot.
func (t RelationTable) IsCanonical() bool {
	for i := 1; i < len(t.Rows); i++ {
		if !lessBytes(GroundKey(t.Rows[i-1]), GroundKey(t.Rows[i])) {
			return false
		}
	}
	return true
}

// Contains reports whether this table contains fact (canonical binary search).
func (t RelationTable) Contains(fact GroundLiteral) bool {
	key := GroundKey(fact)
	i := sort.Search(len(t.Rows), func(i int) bool {
		return !lessBytes(GroundKey(t.Rows[i]), key)
	})
	return i < len(t.Rows) && t.Rows[i].Equal(fact)
}

// GroundKey is the canonical sort/compare key for a GroundLiteral: the codec bytes of
// its labeled-compound value Tuple[Atom(pred), args…]. Total + deterministic, and
// byte-identical to Rust's ground_key.
func GroundKey(g GroundLiteral) []byte {
	items := make([]core.Value, 0, len(g.Args)+1)
	items = append(items, core.NewAtom(g.Pred.Bytes()))
	items = append(items, g.Args...)
	return codec.Encode(core.NewTuple(items...))
}

// sortValuesByCodec sorts values in place by canonical codec bytes.
func sortValuesByCodec(vs []core.Value) {
	sort.Slice(vs, func(i, j int) bool { return lessBytes(codec.Encode(vs[i]), codec.Encode(vs[j])) })
}

// dedupValues removes adjacent codec-equal values from a sorted slice.
func dedupValues(sorted []core.Value) []core.Value {
	if len(sorted) == 0 {
		return sorted
	}
	out := sorted[:1]
	for _, v := range sorted[1:] {
		if !out[len(out)-1].Equal(v) {
			out = append(out, v)
		}
	}
	return out
}

// sortDedupByGroundKey returns rows sorted by GroundKey with one row per key: the
// canonical SET order (#2279). NewRelationTable and EdbTableHash both use it, so a
// sealed table and an EDB snapshot built from the same rows agree by construction. Two
// rows are equal exactly when their keys are, which is also how Contains decides
// membership; this replaces a structural Equal dedup that could disagree with the key.
// The input slice is not modified.
func sortDedupByGroundKey(rows []GroundLiteral) []GroundLiteral {
	type keyed struct {
		g   GroundLiteral
		key []byte
	}
	ks := make([]keyed, len(rows))
	for i, g := range rows {
		ks[i] = keyed{g: g, key: GroundKey(g)}
	}
	sort.Slice(ks, func(i, j int) bool { return lessBytes(ks[i].key, ks[j].key) })
	out := make([]GroundLiteral, 0, len(ks))
	for i, x := range ks {
		if i > 0 && bytes.Equal(ks[i-1].key, x.key) {
			continue
		}
		out = append(out, x.g)
	}
	return out
}

// SupportRef is a reference inside a SupportEdge's body — how one body literal of the
// cited rule is satisfied, with the rank discipline that prevents self-justification.
// The unexported marker method keeps the sum type closed (mirroring Rust's enum).
type SupportRef interface {
	isSupportRef()
}

// SameStratumRef is a positive dependency on a fact in the *same* sealed stratum. Its
// Rank MUST be strictly smaller than the supported fact's rank — the semi-naive
// discipline that rejects the p :- p self-justification (a fact cannot derive itself
// at equal or higher rank).
type SameStratumRef struct {
	Fact GroundLiteral
	Rank uint32
}

// LowerStratumRef is a positive dependency on a fact in a *strictly lower* sealed
// stratum; it must be present in the cited lower cert's table.
type LowerStratumRef struct {
	Cert CertId
	Atom GroundLiteral
}

// BuiltinRef is a builtin/theory atom, decided Holds by the pinned Theory.
type BuiltinRef struct {
	Atom GroundLiteral
}

// NegLowerRef is a negated dependency on a fact in a strictly lower sealed stratum; it
// must be absent from the cited lower cert's table.
type NegLowerRef struct {
	Cert CertId
	Atom GroundLiteral
}

// CountLowerRef is a count (ADR 0023) over a relation in a strictly lower sealed stratum (#2258
// L3.3b): the edge's Subst fixes the count's filter and its claimed result, and the checker
// recomputes the aggregate over the cited lower cert's exact table and requires equality. It
// carries no copy of the result (seat:caa's Q3: one source per fact) and adds no rank.
type CountLowerRef struct {
	Cert CertId
}

func (SameStratumRef) isSupportRef()  {}
func (LowerStratumRef) isSupportRef() {}
func (BuiltinRef) isSupportRef()      {}
func (NegLowerRef) isSupportRef()     {}
func (CountLowerRef) isSupportRef()   {}

// supportRefAtom returns the ground atom/fact carried by a SupportRef (for domain coverage /
// depth checks); false for a CountLowerRef, which carries none (its values are the Subst's).
func supportRefAtom(r SupportRef) (GroundLiteral, bool) {
	switch ref := r.(type) {
	case SameStratumRef:
		return ref.Fact, true
	case LowerStratumRef:
		return ref.Atom, true
	case BuiltinRef:
		return ref.Atom, true
	case NegLowerRef:
		return ref.Atom, true
	case CountLowerRef:
		return GroundLiteral{}, false
	default:
		panic("contract: supportRefAtom: unknown SupportRef")
	}
}

// SupportEdge is one support edge: a witness that a single sealed fact is in the least
// model — the cited clause, grounded by Subst, with head equal to Fact, whose body
// literals each resolve via a SupportRef, at semi-naive Rank.
type SupportEdge struct {
	// Fact is the sealed fact this edge justifies (must equal the grounded clause head).
	Fact GroundLiteral
	// Clause is the clause whose grounding produced Fact.
	Clause ClauseId
	// Subst is the grounding substitution applied to the clause.
	Subst Subst
	// BodyRefs is one reference per clause body literal, in body order.
	BodyRefs []SupportRef
	// Rank is the semi-naive rank assigned to Fact (must strictly dominate every
	// SameStratumRef body ref's rank).
	Rank uint32
}

// SupportWitness is the support witness: one SupportEdge per sealed IDB fact
// (E ⊆ least model). Every fact in the sealed extensions must have at least one edge
// here — no junk.
type SupportWitness struct {
	Edges []SupportEdge
}

// ClosureWitness is the closure witness (least model ⊆ E). In v1 it is an empty marker
// (closure carries no engine-supplied data): the checker joins every scope clause's
// positive sealed literals over the sealed tables (#1829) and demands a body-true
// grounding's head be present in the table. It is kept as a named field so a future scheme is an
// *additive* change, not a shape break.
type ClosureWitness struct{}

// CertSizeDecl is the declared sizes of a certificate — every field validated against the
// CheckLimits cert budgets *before* any scan, and every counted field against its ACTUAL
// value, so a lying declaration is caught (cert_decl_mismatch, #2335) whichever field lies.
// The comparison point differs by field: CertFacts, DomainValues and SupportEdges are
// read off the artifact and compared BEFORE the scan; RuleGroundings and JoinSteps are
// the closure scan's own counters and are compared AS IT RUNS (#1852), tripping the
// moment the count exceeds the declaration — so a checked certificate's scan cost is
// bounded by min(declared, budget), never by the budget alone. CertBytes is compared BEFORE
// the scan too, and since #2524 it is also MEASURED: the certificate's canonical encoded size
// (CertEncodedBytes) must not exceed it, so MaxCertBytes bounds what a certificate is, not only
// what it declares. Bounding the bytes a host READS before decoding is the transport's (#2528).
type CertSizeDecl struct {
	// CertFacts is the declared total number of sealed facts (rows across all extensions).
	CertFacts uint64
	// DomainValues is the declared total number of domain values (across all domains).
	DomainValues uint64
	// SupportEdges is the declared total number of support edges.
	SupportEdges uint64
	// RuleGroundings is the declared number of rule groundings the closure join will
	// emit — one per body-true tuple of a sealed-scope clause (#1829; before it, the
	// groundings of |∪domains|^vars the self-enumeration would visit, an upper bound on
	// this figure).
	RuleGroundings uint64
	// JoinSteps is the declared number of join steps the closure join will perform — one
	// per candidate examined at one body literal: a sealed-table row offered to a binder,
	// or the current tuple offered to a filter (#1829).
	JoinSteps uint64
	// CertBytes is the declared serialized size of the certificate, in bytes: CertEncodedBytes,
	// the canonical encoding with this field zeroed (#2524).
	CertBytes uint64
}

// ClosedModelCert is a sealed finite-model certificate for a stratum prefix (ADR
// 0007). Verified once per citing derivation; a \+ r(a) premise reuses the verified
// result.
type ClosedModelCert struct {
	// Scope is the stratum prefix this cert seals.
	Scope StratumPrefix
	// ProgramHash pins the program the cert was computed against.
	ProgramHash Hash
	// ProfileHash pins the check profile (leaves/admit identities).
	ProfileHash Hash
	// CtxHash pins the verification context snapshot.
	CtxHash Hash
	// TheoryConfigHash pins the theory configuration (so `not` means the same builtin
	// semantics).
	TheoryConfigHash Hash
	// EdbSnapshotHashes pins the complete EDB snapshots the sealed extensions were drawn
	// from.
	EdbSnapshotHashes []Hash
	// Domains is the finite, typed value domains every sealed value must stay within.
	Domains []FiniteDomain
	// Extensions is the exact extensions (relation tables) of the sealed predicates.
	Extensions []RelationTable
	// Supports is the support witness (E ⊆ least model, no junk).
	Supports SupportWitness
	// Closure is the closure witness (least model ⊆ E, no missing heads) — checked by the join.
	Closure ClosureWitness
	// LimitsDecl is the declared sizes, validated against the CheckLimits cert budgets
	// before any scan.
	LimitsDecl CertSizeDecl
	// DecompositionWitness is ADR 0029 D10's SLICE SEAL. nil (the default, and every pre-D10
	// cert) means ProgramHash pins the COMPLETE live clause set, ADR 0007 3.1. Non-nil means
	// this cert was minted for ONE COMPONENT, so ProgramHash pins only that component's
	// downward-closed slice, and the value is the digest of the DecompositionWitness that
	// authorized it — which the bound CertContext must carry identically.
	//
	// A POINTER on purpose: Go's zero value absorbs a new field silently, so every existing
	// literal keeps compiling and gets nil, which is exactly the pre-D10 reading. That is the
	// safe direction here, but it means the compiler enumerates nothing — unlike rs, where the
	// same change surfaced 29 sites loudly.
	//
	// The contract tier never interprets it: 32 opaque bytes compared for equality. It cannot
	// be richer — DecompositionWitness lives above this package in the kernel (ADR 0004).
	DecompositionWitness *Hash
	// PartialScope is ADR 0030 D1's PARTIAL sub-scope. nil (the default, and every pre-0030
	// cert) means every sealed table is exact. Non-nil names the sealed predicates whose
	// extension tables are LOWER BOUNDS of their least-model relations — sealed at a
	// round-budget trip, not at a fixpoint. The checker verifies three invariants before any
	// table is consulted (cert_partial_scope_invalid): a canonical sub-scope of Scope at the
	// prefix's own level; upward-closed within the sealed prefix (a complete table may depend
	// only on complete tables); never an extensional table. Closure is NOT verified for a
	// partial table; support still is; a Neg premise citing one is neg_atom_partial and a
	// Count premise count_over_partial. The 12th trailing-optional element of the certificate
	// tuple (D4). A POINTER for the same reason DecompositionWitness is: every existing
	// literal keeps compiling and reads nil, the pre-0030 meaning — mirrors rs partial_scope.
	PartialScope *StratumPrefix
}

// IsPartial reports whether pred's sealed table is a LOWER BOUND (ADR 0030 D1) — false for
// every predicate of a cert with no PartialScope, i.e. every pre-0030 cert.
func (c ClosedModelCert) IsPartial(pred Symbol) bool {
	return c.PartialScope != nil && c.PartialScope.Seals(pred)
}

// Table looks the exact table for pred up among this cert's extensions, if sealed; the
// second result is false if pred is not sealed.
func (c ClosedModelCert) Table(pred Symbol) (RelationTable, bool) {
	for _, t := range c.Extensions {
		if t.Pred.Equal(pred) {
			return t, true
		}
	}
	return RelationTable{}, false
}

// DomainContaining finds the domain whose values contain v (used for the negated-atom
// typing check); the second result is false if no supplied domain contains it.
func (c ClosedModelCert) DomainContaining(v core.Value) (FiniteDomain, bool) {
	for _, d := range c.Domains {
		if d.Contains(v) {
			return d, true
		}
	}
	return FiniteDomain{}, false
}
