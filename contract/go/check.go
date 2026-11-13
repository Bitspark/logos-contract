// §4 Checker SPI — the P0 deliverable. [FIRM core obligations · STABLE v1 seam params]
//
// check is *total* and performs *no search*. In one forward pass over the DAG it
// verifies every node is locally valid and that the root concludes the claim.
// Consumer-specific decisions enter only through the bound profile (Theory /
// LeafVerifier / RuleAdmissibility), so the *signature* is stable while the
// *bindings* are consumer-supplied.
package contract

import (
	"fmt"
	"slices"
)

// RejectionCode identifies a checker refusal (§4).
//
//   - structural band (FIRM, closed, frozen tri-core) — the codes the kernel itself
//     emits. Branch on these, not on detail.
//   - host-extension band (STABLE v1 *mechanism*; sub-code set open) — the three
//     wrappers a delegated extension point raises; the seam's own sub-code is
//     carried in Verdict.Detail.
//   - configuration: the supplied profile cannot run a check.
type RejectionCode int

const (
	// ---- structural band (FIRM) ----

	EmptyDerivation RejectionCode = iota
	TooManyNodes
	TooDeep
	// TermTooDeep: a single term nests deeper than CheckLimits.MaxTermDepth (issue
	// #253) — a pathologically deep term that would overflow the goroutine stack in
	// the recursive term traversals. Distinct from TooDeep (DAG/premise-chain depth).
	TermTooDeep
	RootOutOfRange
	NonGroundConclusion
	UnknownClause
	InstantiationMismatch
	BadDependencyOrder
	RootConclusionMismatch
	SealedViolation
	PredicatePartitionViolation
	// UnknownNodeKind: a derivation component (a node, premise, term, value or support ref, in a
	// node or a certificate) of unknown or absent kind (#3088). The detail names the component.
	// Such a component is outside the account grammar (ADR 0035 D2) and has no encoding, so its
	// refusal is not a narrowing under ADR 0035 D1 and moves no stored verdict (seat:caa's ruling
	// on #3088; wellformed_3088_test.go checks that every refused shape fails to encode).
	UnknownNodeKind

	// ---- closed-model certificate band (ADR 0007, structural / FIRM) ----

	// CertOutOfRange: a Neg premise cites a ClosedWorld index out of range.
	CertOutOfRange
	// CertBudgetExceeded: the certificate's CLOSURE work exceeds the caller's CheckLimits
	// closure budget: its declared RuleGroundings / JoinSteps, or the count the closure scan
	// reaches live, is over MaxRuleGroundings / MaxJoinSteps. The caller's verify budget, not
	// an engine fault (#2335). Until CHECKER_VERSION 10 this code ALSO covered the four size
	// budgets (now cert_size_exceeded) and a lying declaration (now cert_decl_mismatch), so a
	// verdict stored under an older version meant something wider.
	CertBudgetExceeded
	// CertSizeExceeded: the certificate's declared SIZE exceeds the caller's CheckLimits size
	// budget: its CertBytes / CertFacts / DomainValues / SupportEdges is over the matching
	// Max*. The caller's verify budget, not an engine fault (#2335).
	CertSizeExceeded
	// CertDeclMismatch: the certificate's ACTUAL size or closure work exceeds its OWN
	// declaration (LimitsDecl): the producer under-declared, so an engine fault. Split from
	// cert_budget_exceeded by #2335, which until then named both parties.
	CertDeclMismatch
	// CertContextMismatch: a certificate's pinned hashes do not match the check context.
	CertContextMismatch
	// NegAtomNotSealed: a \+ atom's predicate is not sealed by the cited certificate.
	NegAtomNotSealed
	// NegStratumNotLower: the negated predicate is not in a strictly-lower stratum than
	// the rule head.
	NegStratumNotLower
	// NegAtomIllTyped: the negated atom is not ground / well-typed within the cert's
	// finite domain.
	NegAtomIllTyped
	// NegAtomPresent: the negated atom IS present in the sealed relation (so \+ fails).
	NegAtomPresent
	// CertUnsupported: a sealed fact lacks a valid support edge (E not ⊆ least model).
	CertUnsupported
	// CertNotClosed: a satisfied rule grounding's head is absent from the table (not
	// closed).
	CertNotClosed
	// CertOutOfDomain: a satisfied grounding produces a value outside the sealed finite
	// domain.
	CertOutOfDomain
	// CertScopeIncomplete: the sealed stratum prefix is not downward-closed.
	CertScopeIncomplete
	// CertContextUnbound: a Neg-bearing derivation supplied an all-zero (unbound) cert
	// context.
	CertContextUnbound
	// CertEdbMismatch: a sealed extensional table does not match the live EDB snapshot.
	CertEdbMismatch
	// CertPartialScopeInvalid: a cert's PartialScope (ADR 0030 D1) breaks one of its three
	// invariants — not canonical or not a sub-scope of Scope at its level; marks an
	// extensional table; or is not upward-closed within the sealed prefix (a complete table's
	// defining clause reads a predicate marked partial).
	CertPartialScopeInvalid
	// NegAtomPartial: a \+ atom's predicate is sealed but marked PARTIAL (ADR 0030 D2) — its
	// table is a lower bound, so absence from it proves nothing.
	NegAtomPartial

	// ---- certifiable aggregation band (ADR 0023, structural / FIRM) ----

	// CountStratumNotLower: a Count premise's counted predicate is not in a strictly-lower
	// stratum than the rule head (a count is non-monotone, so it must read a sealed lower
	// stratum).
	CountStratumNotLower
	// CountAttrOutOfRange: a Count premise's filter position, count_distinct projection
	// attribute, or predicate arity is outside the counted predicate's arity.
	CountAttrOutOfRange
	// CountMismatch: a Count premise's claimed cardinality k does not equal the count
	// recomputed over the proven-exact sealed relation (the core dual-conformance guarantee).
	CountMismatch
	// AggEmptyUndefined: a min/max aggregate (ADR 0023 #587) folds ZERO matching rows —
	// the minimum/maximum of an empty set is undefined. Sits right after CountMismatch in
	// the certifiable-aggregation band.
	AggEmptyUndefined
	// CountOverPartial: a Count premise's counted predicate is sealed but marked PARTIAL
	// (ADR 0030 D2) — a cardinality over a lower bound is a lower bound, never the claimed k.
	// The count twin of NegAtomPartial.
	CountOverPartial

	// ---- host-extension band (STABLE v1 mechanism; sub-code in detail) ----

	BuiltinFailed
	LeafRejected
	RuleInadmissible
	// BuiltinNotDecided (#3126): the theory did not DECIDE a builtin literal the derivation relies
	// on (its DecideGround stopped: a work cap, a capacity). Check refuses rather than reading the
	// stop as a decision, in every position: a positive Builtin node, a support edge's builtin,
	// and a closure rule instance whose body is not decided and whose head is absent. The sub-code
	// in detail is the stop's kind tag (work_cap, ...), as builtin_failed carries the theory's own
	// code. Listed last so the numbering of the codes before it does not move.
	BuiltinNotDecided

	// InvalidCheckLimits is a caller configuration failure before proof checking.
	InvalidCheckLimits
)

// Code returns the stable, cross-language rejection-code string — the *normative*
// artifact (the detail text is diagnostic only). These strings are byte-identical
// across the {rs,go} bindings and equal the code field in the shared conformance
// vectors.
func (c RejectionCode) Code() string {
	switch c {
	case EmptyDerivation:
		return "empty_derivation"
	case TooManyNodes:
		return "too_many_nodes"
	case TooDeep:
		return "too_deep"
	case TermTooDeep:
		return "term_too_deep"
	case RootOutOfRange:
		return "root_out_of_range"
	case NonGroundConclusion:
		return "non_ground_conclusion"
	case UnknownClause:
		return "unknown_clause"
	case InstantiationMismatch:
		return "instantiation_mismatch"
	case BadDependencyOrder:
		return "bad_dependency_order"
	case RootConclusionMismatch:
		return "root_conclusion_mismatch"
	case SealedViolation:
		return "sealed_violation"
	case PredicatePartitionViolation:
		return "predicate_partition_violation"
	case UnknownNodeKind:
		return "unknown_node_kind"
	case CertOutOfRange:
		return "cert_out_of_range"
	case CertBudgetExceeded:
		return "cert_budget_exceeded"
	case CertSizeExceeded:
		return "cert_size_exceeded"
	case CertDeclMismatch:
		return "cert_decl_mismatch"
	case CertContextMismatch:
		return "cert_context_mismatch"
	case NegAtomNotSealed:
		return "neg_atom_not_sealed"
	case NegStratumNotLower:
		return "neg_stratum_not_lower"
	case NegAtomIllTyped:
		return "neg_atom_ill_typed"
	case NegAtomPresent:
		return "neg_atom_present"
	case CertUnsupported:
		return "cert_unsupported"
	case CertNotClosed:
		return "cert_not_closed"
	case CertOutOfDomain:
		return "cert_out_of_domain"
	case CertScopeIncomplete:
		return "cert_scope_incomplete"
	case CertContextUnbound:
		return "cert_context_unbound"
	case CertEdbMismatch:
		return "cert_edb_mismatch"
	case CertPartialScopeInvalid:
		return "cert_partial_scope_invalid"
	case NegAtomPartial:
		return "neg_atom_partial"
	case CountStratumNotLower:
		return "count_stratum_not_lower"
	case CountAttrOutOfRange:
		return "count_attr_out_of_range"
	case CountMismatch:
		return "count_mismatch"
	case AggEmptyUndefined:
		return "agg_empty_undefined"
	case CountOverPartial:
		return "count_over_partial"
	case BuiltinFailed:
		return "builtin_failed"
	case LeafRejected:
		return "leaf_rejected"
	case RuleInadmissible:
		return "rule_inadmissible"
	case BuiltinNotDecided:
		return "builtin_not_decided"
	case InvalidCheckLimits:
		return "invalid_check_limits"
	default:
		panic(fmt.Sprintf("contract: unknown RejectionCode %d", int(c)))
	}
}

// IsStructural reports true for the closed FIRM structural band — the codes a check
// over well-typed input may itself emit. (non_ground_conclusion is in the band but is
// *decoder*-emitted: a well-typed Node always concludes a ground literal. unknown_node_kind
// is emitted by a decoder, and by check for a node, premise or support ref that is none of
// the known kinds: nil, or a foreign type embedding the interface, #3074.)
//
// Every code is named (#3074, seat:caa's ruling): the band is a decision per code, so a new
// code must be placed here, and one this switch does not know panics by name.
func (c RejectionCode) IsStructural() bool {
	switch c {
	case InvalidCheckLimits, BuiltinFailed, BuiltinNotDecided, LeafRejected, RuleInadmissible:
		return false
	case EmptyDerivation, TooManyNodes, TooDeep, TermTooDeep, RootOutOfRange, NonGroundConclusion,
		UnknownClause, InstantiationMismatch, BadDependencyOrder, RootConclusionMismatch, SealedViolation,
		PredicatePartitionViolation, UnknownNodeKind, CertOutOfRange, CertBudgetExceeded, CertSizeExceeded,
		CertDeclMismatch, CertContextMismatch, NegAtomNotSealed, NegStratumNotLower, NegAtomIllTyped,
		NegAtomPresent, CertUnsupported, CertNotClosed, CertOutOfDomain, CertScopeIncomplete,
		CertContextUnbound, CertEdbMismatch, CertPartialScopeInvalid, NegAtomPartial, CountStratumNotLower,
		CountAttrOutOfRange, CountMismatch, AggEmptyUndefined, CountOverPartial:
		return true
	default:
		panic(fmt.Sprintf("contract: IsStructural: unknown RejectionCode %d", int(c)))
	}
}

// Verdict is what check decided: accept, or reject with a code and its diagnostic detail. A closed
// sum modelled as a struct (not an interface), so it is a plain comparable value: two verdicts are
// == exactly when they are the same decision. IsAccept distinguishes the two arms. Rust's
// check::Verdict.
type Verdict struct {
	accept bool
	code   RejectionCode
	detail string
}

// Accept is the accepting verdict.
func Accept() Verdict { return Verdict{accept: true} }

// reject builds a rejecting verdict with a code and diagnostic detail.
func reject(code RejectionCode, detail string) Verdict {
	return Verdict{accept: false, code: code, detail: detail}
}

// IsAccept reports whether the verdict is Accept.
func (v Verdict) IsAccept() bool { return v.accept }

// Code returns the rejection code; valid only when !IsAccept.
func (v Verdict) Code() RejectionCode { return v.code }

// Detail returns the diagnostic detail; valid only when !IsAccept.
func (v Verdict) Detail() string { return v.detail }

// String renders a diagnostic form.
func (v Verdict) String() string {
	if v.accept {
		return "Accept"
	}
	return fmt.Sprintf("Reject{%s: %s}", v.code.Code(), v.detail)
}

// Outcome is the result of check (checker SPI v2, ADR 0036 D8 change 5, #3111): its Verdict, and
// the CheckReport of the work it performed. Rust's check::Outcome.
//
// Equality is the verdict's. Two outcomes are equal when their verdicts are, whatever their reports
// say, so a counter can never turn a verdict test red (the coordinator's ruling of 2026-11-12).
// Compare with Equal, or compare the Verdict fields: Outcome is deliberately NOT comparable with ==,
// which would compare the reports' counters as well, so such a comparison does not compile. Read
// Report where the work is asked about.
type Outcome struct {
	Verdict Verdict
	Report  CheckReport
	// A zero-size array of funcs makes the struct not comparable: == on two outcomes is a compile
	// error rather than a silent comparison of their counters.
	_ [0]func()
}

// IsAccept reports whether the outcome's verdict is Accept.
func (o Outcome) IsAccept() bool { return o.Verdict.IsAccept() }

// Equal reports whether two outcomes carry the same verdict. Their reports are not compared (Rust's
// PartialEq for Outcome).
func (o Outcome) Equal(other Outcome) bool { return o.Verdict == other.Verdict }

// String renders the verdict's diagnostic form, the part of the outcome its equality reads. The
// report is read by its fields.
func (o Outcome) String() string { return o.Verdict.String() }

// CheckLimits holds the checker's BEHAVIOUR PARAMETERS (§4.3): budgets on the *untrusted*
// supplied derivation. (Checker SPI v2, ADR 0036 D8 change 1, #3111: the inert term identity is
// deleted.) The budgets are distinct from search-effort limits: they bound *proof size on verify*,
// and the node cap is a hard, deterministic rejection checked *before any node delegation*.
type CheckLimits struct {
	// MaxNodes is the max total node count (> MaxNodes → too_many_nodes).
	MaxNodes int
	// MaxDepth is the max DAG depth (longest premise chain) (> MaxDepth → too_deep).
	MaxDepth int
	// MaxTermDepth is the max single-term nesting depth (> MaxTermDepth →
	// term_too_deep, issue #253). Bounds the depth of every term the trusted path
	// traverses recursively (node conclusions, the claim, and every cited clause's
	// head/body/subst terms), so a pathologically deep term cannot overflow the
	// goroutine stack. Distinct from MaxDepth (DAG/premise-chain depth). Default
	// MaxTermDepthDefault.
	MaxTermDepth int

	// ---- closed-model certificate budgets (ADR 0007) ----
	// Each bounds one dimension of a cited ClosedModelCert. Validated *before* any scan
	// (against the cert's LimitsDecl AND its actual sizes), so an oversized or lying
	// certificate is refused without doing its work.

	// MaxCertBytes is the max serialized certificate size, in bytes.
	MaxCertBytes int
	// MaxCertFacts is the max total sealed facts across a certificate's extensions.
	MaxCertFacts int
	// MaxDomainValues is the max total domain values across a certificate's domains.
	MaxDomainValues int
	// MaxSupportEdges is the max number of support edges in a certificate.
	MaxSupportEdges int
	// MaxRuleGroundings is the max number of rule groundings the closure join may emit
	// (one per body-true tuple of a sealed-scope clause, #1829); tripped incrementally
	// during the scan.
	MaxRuleGroundings int
	// MaxJoinSteps is the max number of join steps the closure join may perform (one per
	// candidate examined at one body literal, #1829); tripped incrementally during the
	// scan.
	MaxJoinSteps int
}

// DefaultLimits returns the standard check limits. Mirrors arche-core's
// MAX_NODES=100_000; the depth cap is logos's addition; MaxTermDepth is the issue
// #253 single-term nesting bound (tri-core-consistent with contract/{rs,ts}); the
// cert budgets are finite, generous defaults (a cert larger than these is a
// verification-cost DoS, refused before any scan) — byte-identical to Rust's
// CheckLimits::default.
func DefaultLimits() CheckLimits {
	return CheckLimits{
		MaxNodes:          100_000,
		MaxDepth:          4096,
		MaxTermDepth:      MaxTermDepthDefault,
		MaxCertBytes:      16 * 1024 * 1024,
		MaxCertFacts:      1_000_000,
		MaxDomainValues:   1_000_000,
		MaxSupportEdges:   1_000_000,
		MaxRuleGroundings: 10_000_000,
		MaxJoinSteps:      100_000_000,
	}
}

// Budget is one checker budget, named by the key a vector case's `limits` object uses.
type Budget struct {
	Name  string
	Value *int
}

// Budgets is every budget a caller can raise, by its name, in declaration order (#2733, R3): the
// one list of the checker's budgets, which every reader takes rather than keeping its own. A test
// counts the struct's fields by reflection, so a new field fails until it is placed here.
func (l *CheckLimits) Budgets() []Budget {
	return []Budget{
		{"max_nodes", &l.MaxNodes},
		{"max_depth", &l.MaxDepth},
		{"max_term_depth", &l.MaxTermDepth},
		{"max_cert_bytes", &l.MaxCertBytes},
		{"max_cert_facts", &l.MaxCertFacts},
		{"max_domain_values", &l.MaxDomainValues},
		{"max_support_edges", &l.MaxSupportEdges},
		{"max_rule_groundings", &l.MaxRuleGroundings},
		{"max_join_steps", &l.MaxJoinSteps},
	}
}

// CheckLimitError names a caller budget outside the shared proof-count domain.
type CheckLimitError struct {
	Field string
	Value string
}

func (e *CheckLimitError) Error() string {
	return fmt.Sprintf("check limits: %s=%s is outside the index range 0..%d", e.Field, e.Value, IndexMax)
}

// ProofBudgetCount is an exact count in the portable index domain. Its zero value is valid.
type ProofBudgetCount struct {
	value uint64
}

// NewProofBudgetCount validates a count and identifies the caller's field on refusal.
func NewProofBudgetCount(field string, count uint64) (ProofBudgetCount, error) {
	if count > IndexMax {
		return ProofBudgetCount{}, &CheckLimitError{Field: field, Value: fmt.Sprint(count)}
	}
	return ProofBudgetCount{value: count}, nil
}

// ProofBudgetCountFromInt64 validates a signed native or transport input.
func ProofBudgetCountFromInt64(field string, count int64) (ProofBudgetCount, error) {
	if count < 0 {
		return ProofBudgetCount{}, &CheckLimitError{Field: field, Value: fmt.Sprint(count)}
	}
	return NewProofBudgetCount(field, uint64(count))
}

// ProofBudgetCountFromUint32 widens a count which already fits the protocol.
func ProofBudgetCountFromUint32(count uint32) ProofBudgetCount {
	return ProofBudgetCount{value: uint64(count)}
}

// Uint64 returns the exact portable value, including on 32-bit hosts.
func (n ProofBudgetCount) Uint64() uint64 { return n.value }

// Validate checks the caller's proof budgets before any account or verifier is read.
// A zero count is a valid cap.
func (l CheckLimits) Validate() error {
	for _, budget := range l.Budgets() {
		if _, err := ProofBudgetCountFromInt64(budget.Name, int64(*budget.Value)); err != nil {
			return err
		}
	}
	return nil
}

// CheckProfile is the bound extension points + config + limits check verifies
// against (§4). Theory is config-pinned (its config is held inside the value, not
// generic over the context C — see Theory). Leaves/Admit are generic over C.
type CheckProfile[C any] struct {
	Theory Theory
	Leaves LeafVerifier[C]
	Admit  RuleAdmissibility[C]
	Limits CheckLimits
}

// ProfileSlot names one bound-component slot of a CheckProfile[C] — the three slots a
// profile digest folds a component binding for.
type ProfileSlot int

const (
	// ProfileSlotTheory is the profile's Theory.
	ProfileSlotTheory ProfileSlot = iota
	// ProfileSlotLeaves is the profile's LeafVerifier.
	ProfileSlotLeaves
	// ProfileSlotAdmit is the profile's RuleAdmissibility.
	ProfileSlotAdmit
)

// String is the slot's stable name — the identifier the shared vector and every core
// agree on.
func (s ProfileSlot) String() string {
	switch s {
	case ProfileSlotTheory:
		return "theory"
	case ProfileSlotLeaves:
		return "leaves"
	case ProfileSlotAdmit:
		return "admit"
	default:
		return "unknown"
	}
}

// profileComponentIdentity resolves a bound component's identity under the
// "absent = unidentified" convention: a component implementing the OPTIONAL Identified
// seam attests its own identity, otherwise it reads as UnidentifiedComponent().
func profileComponentIdentity(component any) ComponentIdentity {
	if c, ok := component.(Identified); ok {
		return c.Identity()
	}
	return UnidentifiedComponent()
}

// UnidentifiedProfileSlots reports which of a live profile's bound components read as
// UnidentifiedComponent() — the unidentified-component advisory (#708 leg (a)).
//
// Identity() is optional, so a component that does not implement Identified contributes a
// CONSTANT to the profile digest. Two different LeafVerifiers — one strict, one permissive
// — both unattesting produce the SAME digest. For that slot the digest discharges NOTHING,
// while still being a computed 32-byte value that reads as evidence.
//
// This lives in the CONTRACT tier deliberately (#815). It reads only contract types and
// touches nothing the kernel owns; its original placement in kernel put it out of reach of
// any consumer binding logos-contract alone, because contract -> kernel is an UPWARD edge
// on the ADR 0004 stack. Placement follows what a function reads, not what it was written
// next to.
//
// A non-empty result means: the frozen digest says NOTHING about this slot. It does not
// mean the profile is wrong — an anonymous component is legal, and remains so.
func UnidentifiedProfileSlots[C any](profile *CheckProfile[C]) []ProfileSlot {
	return UnidentifiedProfileSlotsAllowing(profile, nil)
}

// UnidentifiedProfileSlotsAllowing is the same report, minus the slots the caller has
// EXPLICITLY DECLARED it accepts as anonymous — ADR 0026 gate G4, the deliberate escape.
//
// Declared, never defaulted: a nil/empty allowance is the default (UnidentifiedProfileSlots
// IS this with nil), and allowing every slot requires naming all three. There is
// deliberately no "allow all" shorthand — the value of an escape is the legible trace it
// leaves at the call site.
//
// It does not touch the digest: this reads identities and participates in no fold. Allowing
// a slot changes what you are TOLD, never what is DERIVED.
func UnidentifiedProfileSlotsAllowing[C any](
	profile *CheckProfile[C],
	allowUnidentified []ProfileSlot,
) []ProfileSlot {
	components := [...]struct {
		slot   ProfileSlot
		handle any
	}{
		{ProfileSlotTheory, profile.Theory},
		{ProfileSlotLeaves, profile.Leaves},
		{ProfileSlotAdmit, profile.Admit},
	}
	allowed := slices.Clone(allowUnidentified)
	var out []ProfileSlot
	for _, component := range components {
		identity := profileComponentIdentity(component.handle)
		if identity.IsUnidentified() && !slices.Contains(allowed, component.slot) {
			out = append(out, component.slot)
		}
	}
	return out
}

// ProfileIsFullyIdentified reports whether every bound component attests an identity — the
// silent case of UnidentifiedProfileSlots.
func ProfileIsFullyIdentified[C any](profile *CheckProfile[C]) bool {
	return len(UnidentifiedProfileSlots(profile)) == 0
}

// CertContext is the four pins a closed-model certificate is sealed against (ADR
// 0007). A Neg-bearing derivation's certificates are valid only for the program /
// profile / context / theory-config they were sealed against; CheckWithCertContext
// compares a cert's pins against this context.
//
// Additive (ADR 0007). A plain Check supplies a *zero* context; it is never consulted
// when ClosedWorld is empty, so positive Check behavior — and its bytes/outcomes — are
// byte-identical to the pre-amendment checker. A consumer that uses negation derives
// this context from the *live* program/profile it actually ran.
type CertContext struct {
	ProgramHash      Hash
	ProfileHash      Hash
	CtxHash          Hash
	TheoryConfigHash Hash
	// DecompositionWitness is the decomposition this run was performed under (ADR 0029 D10),
	// or nil for an ordinary whole-program run. A slice-sealed cert is admitted only when this
	// carries the same pin.
	DecompositionWitness *Hash
}

// WithDecomposition returns this context bound to the decomposition witness (ADR 0029 D10).
// Additive and opt-in: a caller that does not decompose never calls it and its context is
// byte-identical to the pre-D10 one.
func (c CertContext) WithDecomposition(witness Hash) CertContext {
	c.DecompositionWitness = &witness
	return c
}

// NewCertContext builds an explicit context over the four pins.
func NewCertContext(programHash, profileHash, ctxHash, theoryConfigHash Hash) CertContext {
	return CertContext{
		ProgramHash:      programHash,
		ProfileHash:      profileHash,
		CtxHash:          ctxHash,
		TheoryConfigHash: theoryConfigHash,
	}
}

// captureCertContext owns the optional pin before program or verifier callbacks.
func captureCertContext(c CertContext) CertContext {
	if c.DecompositionWitness != nil {
		c = c.WithDecomposition(*c.DecompositionWitness)
	}
	return c
}

// ZeroCertContext is the all-zero context. Supplied by the plain Check wrapper and
// never consulted for an all-positive (ClosedWorld-empty) derivation; for a certifying
// check it is the *unbound* sentinel (see IsUnbound).
func ZeroCertContext() CertContext { return CertContext{} }

// IsUnbound reports whether every pin is all-zero — the *unbound* sentinel (ADR 0007
// §3.1). A certifying check (ClosedWorld non-empty) under an unbound context is
// hard-rejected cert_context_unbound; a real consumer derives a non-zero context from
// the live program/profile.
func (c CertContext) IsUnbound() bool {
	return c.ProgramHash == Hash{} && c.ProfileHash == Hash{} && c.CtxHash == Hash{} && c.TheoryConfigHash == Hash{}
}

// Check verifies a derivation (§4). Total, no search.
//
// Order of obligations (normative §4): empty / node-cap / root-range up front (the
// node cap *before any delegation*); then a single forward pass where each node is
// validated *structurally* and only *then* delegated to its extension point;
// finally the root must conclude claim.
//
// Positive-identical (ADR 0007). This is a thin wrapper over CheckWithCertContext
// supplying a *zero* CertContext. For an all-positive derivation (deriv.ClosedWorld
// empty) the context is never consulted, so an existing positive check behaves
// byte-for-byte as before.
//
// Negation requires a bound context. A zero context is the *unbound* sentinel, never a
// credential: if deriv.ClosedWorld is non-empty (a certifying check), this wrapper
// hard-rejects cert_context_unbound — a certificate must be verified against a context
// DERIVED from the live program/profile the consumer actually ran
// (CheckWithCertContext), not against an all-zero placeholder that any all-zero-pinned
// cert would trivially satisfy.
func Check[C any](program Program, claim GroundLiteral, deriv Derivation, ctx C, profile *CheckProfile[C]) Outcome {
	return CheckWithCertContext(program, claim, deriv, ctx, profile, ZeroCertContext())
}

// CheckClosedModelChain verifies a closed-model certificate CHAIN on its own, with no
// derivation citing it: the completeness gate's certificate check (#2313, design 0008 §1.4.3).
// Each cert, at its place in the chain, passes exactly the verification a cert cited by a Neg
// premise passes in CheckWithCertContext: the same term-depth cap on its deep data, the same
// context-unbound gate, and the same verifyCert, unchanged. So no verdict of that function moves.
//
// The first invalid cert rejects, with its own code and a detail prefixed by its index. An EMPTY
// chain rejects as cert_out_of_range, because it has no cert to seal anything. A vacuous accept
// would certify a completeness claim that nothing backs. Mirrors rs check_closed_model_chain.
func CheckClosedModelChain[C any](program Program, certs []ClosedModelCert, ctx C, profile *CheckProfile[C], certContext CertContext) Outcome {
	var tally checkTally
	verdict := verifyChain(program, certs, ctx, profile, certContext, &tally)
	return tally.outcome(verdict)
}

// verifyChain is CheckClosedModelChain's verdict, its work counted into tally (rs verify_chain).
func verifyChain[C any](program Program, certs []ClosedModelCert, ctx C, profile *CheckProfile[C], certContext CertContext, tally *checkTally) Verdict {
	captured := *profile
	profile = &captured
	if err := profile.Limits.Validate(); err != nil {
		return reject(InvalidCheckLimits, err.Error())
	}
	if len(certs) == 0 {
		return reject(CertOutOfRange, "empty certificate chain: no closed-model certificate to verify")
	}
	certContext = captureCertContext(certContext)
	// #3088: the same native shape boundary as CaptureDerivation, before any certificate is read.
	for own, cert := range certs {
		if d := wellFormedCert(cert, profile.Limits.MaxTermDepth); d != "" {
			return reject(UnknownNodeKind, fmt.Sprintf("chain cert %d: %s", own, d))
		}
	}
	for own, cert := range certs {
		if what := certDepthsWithin(cert, profile.Limits.MaxTermDepth, tally); what != "" {
			return reject(TermTooDeep, fmt.Sprintf("chain cert %d: %s nests deeper than max_term_depth %d", own, what, profile.Limits.MaxTermDepth))
		}
	}
	if certContext.IsUnbound() {
		return reject(CertContextUnbound, "certifying check supplied an all-zero (unbound) cert context")
	}
	// Keep every proposed certificate fixed before verifying the first one.
	certs = cloneWorld(certs)
	// STACKED certificates (#2258 (a)): the chain is the world, verified in ascending scope level
	// exactly as a derivation's closed world is, so a cert that reads a lower cert's seal does so
	// only once that cert's status is final. The first invalid cert in that order rejects.
	status := make([]certStatus, len(certs))
	verified := make([]bool, len(certs))
	readProgram := worldProgram(program)
	for _, own := range verificationOrder(certs) {
		place := certPlace{own: own, worldLen: len(certs)}
		st := verifyCert(certs[own], place, certs, status, verified, readProgram, profile, ctx, certContext, profile.Limits, tally)
		if !st.valid {
			return reject(st.code, fmt.Sprintf("chain cert %d: %s", own, st.detail))
		}
		status[own] = st
		verified[own] = true
	}
	return Accept()
}

// CheckWithCertContext verifies a derivation that may carry closed-model certificates
// (ADR 0007). Total, no search; the cert obligations are bounded deterministic
// verification over the supplied finite tables/domains, every loop pre-bounded by a
// CheckLimits cert budget validated up front.
//
// certContext pins the program/profile/context/theory configuration the cited
// certificates must have been sealed against. It is consulted only when a cert is
// actually verified (i.e. only for a Neg-bearing derivation).
func CheckWithCertContext[C any](program Program, claim GroundLiteral, deriv Derivation, ctx C, profile *CheckProfile[C], certContext CertContext) Outcome {
	return checkNative(program, claim, deriv, ctx, *profile, certContext, nil)
}

// checkNative binds the proposed account and requested fact before program
// lookup or verification. A memo can provide the already owned world and its
// statuses. The forward pass always reads the same world that was verified.
//
// One report accumulator is threaded through the whole check (#3111), never held in ambient
// state; the outcome carries the verdict and the work counted up to it.
func checkNative[C any](
	program Program, claim GroundLiteral, proof Derivation, ctx C,
	profile CheckProfile[C], certContext CertContext, memo *WorldMemo[C],
) Outcome {
	var tally checkTally
	verdict := checkCounted(program, claim, proof, ctx, profile, certContext, memo, &tally)
	return tally.outcome(verdict)
}

// checkCounted is checkNative's verdict, its work counted into tally. The refusals before the
// depth pass (the limits, the derivation header, the shape boundary) count nothing; the depth pass
// counts only max_term_depth_reached.
func checkCounted[C any](
	program Program, claim GroundLiteral, proof Derivation, ctx C,
	profile CheckProfile[C], certContext CertContext, memo *WorldMemo[C], tally *checkTally,
) Verdict {
	if v := checkDerivationShape(proof, profile.Limits); !v.IsAccept() {
		return v
	}
	if why := wellFormedLiteral(claim, profile.Limits.MaxTermDepth, "claim"); why != "" {
		return reject(UnknownNodeKind, why)
	}
	claim = claim.detached()
	world := proof.ClosedWorld
	proof.ClosedWorld = nil
	proof = CloneDerivation(proof)
	var status []certStatus
	if len(world) != 0 {
		certContext = captureCertContext(certContext)
		if memo == nil {
			proof.ClosedWorld = cloneWorld(world)
		} else {
			proof.ClosedWorld, status = memo.captureWorld(world, profile.Limits)
		}
	}
	// This depth pass may call Program.Clause. All subsequent comparisons
	// and verifier calls use the captured data even if that lookup reenters.
	if v := checkTermDepths(program, claim, proof, profile.Limits, tally); !v.IsAccept() {
		return v
	}
	if len(proof.ClosedWorld) != 0 {
		if status == nil {
			status = verifyWorld(proof.ClosedWorld, program, &profile, ctx, certContext, tally)
			if memo != nil {
				memo.rememberWorld(proof.ClosedWorld, status, profile.Limits)
			}
		} else {
			// certs_memo_hits: every certificate of the world, served by the memo instead of
			// verified. Counted here, after the depth pass, where rs consults its memo.
			tally.certsMemoHits += len(proof.ClosedWorld)
		}
	}
	return checkNodes(program, claim, proof, ctx, &profile, status, tally)
}

// verifyWorld is step 3a of CheckWithCertContext: every certificate of world verified, into the
// status slice the forward pass reads. Its statuses are a pure function of its arguments, which is
// what lets a WorldMemo serve them again for an equal world under the same inputs (#2569); the
// verification's work is counted into tally.
func verifyWorld[C any](world []ClosedModelCert, program Program, profile *CheckProfile[C], ctx C, certContext CertContext, tally *checkTally) []certStatus {
	// 3a. verify every cited certificate ONCE, up front, memoized into a parallel
	//     []certStatus. A Neg premise reuses the cached result. For an all-positive
	//     derivation ClosedWorld is empty, so this is a no-op and the zero certContext
	//     is never consulted — positive behavior is byte-identical.
	//
	//     CONTEXT-UNBOUND GATE (ADR 0007 §3.1): a certifying check needs a context
	//     DERIVED from the live program/profile. An all-zero context is the *unbound*
	//     sentinel — if any cert is cited under it, every cert is invalid with
	//     cert_context_unbound (a zero context must never *satisfy* a cert's pins).
	//
	//     STACKED certificates (#2258 (a)): certs are verified in ascending scope level, so a
	//     cert that reads a predicate from a strictly lower cert does so only once that cert's
	//     status is final (validity precedes citation).
	contextUnbound := len(world) > 0 && certContext.IsUnbound()
	certStatus := make([]certStatus, len(world))
	verified := make([]bool, len(world))
	readProgram := worldProgram(program)
	for _, i := range verificationOrder(world) {
		if contextUnbound {
			certStatus[i] = invalidCert(CertContextUnbound, "certifying check supplied an all-zero (unbound) cert context")
		} else {
			place := certPlace{own: i, worldLen: len(world)}
			certStatus[i] = verifyCert(world[i], place, world, certStatus, verified, readProgram, profile, ctx, certContext, profile.Limits, tally)
		}
		verified[i] = true
	}
	return certStatus
}

// checkNodes is steps 4 and 5 of CheckWithCertContext: the forward pass over the derivation's
// nodes, reading the certificates' statuses, then the root against the claim.
func checkNodes[C any](program Program, claim GroundLiteral, deriv Derivation, ctx C, profile *CheckProfile[C], certStatus []certStatus, tally *checkTally) Verdict {
	// 4. one forward pass: validate each node (structural, then delegate).
	depth := make([]int, len(deriv.Nodes))
	for i, node := range deriv.Nodes {
		if v := checkNode(i, node, program, deriv, ctx, profile, certStatus, depth, tally); !v.IsAccept() {
			return v
		}
	}

	// 5. root concludes the claim, structurally (#3022): the certified claim is exactly the fact
	//    the root proves, never another spelling of it.
	if !deriv.Nodes[deriv.Root].Conclusion().Equal(claim) {
		return reject(RootConclusionMismatch, "root conclusion does not equal claim")
	}

	return Accept()
}

// equalGroundFilter reports positional + value agreement of two ground count filters
// (ADR 0023): same length, and each (Pos, Value) pair equal in order. Values are compared
// by EXACT structural equality (mirroring Rust's Vec<(u32, Value)> PartialEq on the count
// premise filter — the filter is not list-canonicalized, unlike the count slot k).
func equalGroundFilter(a, b []GroundFilterEntry) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].Pos != b[i].Pos || !a[i].Value.Equal(b[i].Value) {
			return false
		}
	}
	return true
}

// checkTermDepths validates, ITERATIVELY with an early cutoff, that no term the
// trusted path will traverse recursively nests deeper than limits.MaxTermDepth (issue
// #253). Covers the claim's args, every node's conclusion args + (for a Rule) its
// subst image terms, and every cited clause's head + body-literal args. Returns Accept
// when every term is within bound, else a term_too_deep rejection. Each *DepthLE call
// is itself non-recursive and cuts off at the bound, so this gate's own cost is
// bounded by MaxTermDepth, not by the (unbounded) depth of a pathological term.
// certDepthsWithin is the certificate half of checkTermDepths (its block (c)): every deep
// datum of one closed-model certificate that the cert path traverses recursively is within max.
// A non-empty result names the first datum over the bound, in the same words the derivation path
// reports. Shared with CheckClosedModelChain (#2313), whose certificates no derivation cites.
// Mirrors rs cert_depths_within. Each depth it measures goes into tally (max_term_depth_reached).
func certDepthsWithin(cert ClosedModelCert, max int, tally *checkTally) string {
	for _, table := range cert.Extensions {
		for _, fact := range table.Rows {
			if !groundWithin(fact, max, tally) {
				return "certificate extension row argument"
			}
		}
	}
	for _, domain := range cert.Domains {
		for _, v := range domain.Values {
			if !tally.valueWithin(v, max) {
				return "certificate domain value"
			}
		}
	}
	for _, edge := range cert.Supports.Edges {
		if !groundWithin(edge.Fact, max, tally) {
			return "certificate support-edge fact argument"
		}
		for _, term := range edge.Subst {
			if !tally.termWithin(term, max) {
				return "certificate support-edge subst image"
			}
		}
		for _, bodyRef := range edge.BodyRefs {
			atom, ok := supportRefAtom(bodyRef)
			if !ok {
				continue
			}
			if !groundWithin(atom, max, tally) {
				return "certificate support-ref atom argument"
			}
		}
	}
	return ""
}

// checkTermDepths' every measurement (a term's depth, cut off at the first level past max) goes
// into tally (max_term_depth_reached), so a term_too_deep refusal reports max + 1.
func checkTermDepths(program Program, claim GroundLiteral, deriv Derivation, limits CheckLimits, tally *checkTally) Verdict {
	max := limits.MaxTermDepth
	tooDeep := func(what string) Verdict {
		return reject(TermTooDeep, fmt.Sprintf("%s nests deeper than max_term_depth %d", what, max))
	}
	// (a) the claim.
	if !groundWithin(claim, max, tally) {
		return tooDeep("claim argument")
	}
	// (b) every node conclusion + (for Rule) subst images, and every cited clause.
	for _, node := range deriv.Nodes {
		if !groundWithin(node.Conclusion(), max, tally) {
			return tooDeep("node conclusion argument")
		}
		if rule, ok := node.(RuleNode); ok {
			for _, term := range rule.Subst {
				if !tally.termWithin(term, max) {
					return tooDeep("subst image term")
				}
			}
			// A missing clause is the structural unknown_clause error raised later in
			// the forward pass; here we only depth-check a clause that exists.
			if clause, ok := program.Clause(rule.Clause); ok {
				if !goalWithin(clause.Head, max, tally) {
					return tooDeep("cited clause head argument")
				}
				for _, bl := range clause.Body {
					if bl.IsCount() {
						// A Count body literal has no single Goal: depth-check its filter
						// terms + the count slot instead.
						for _, e := range bl.CountVal.Filter {
							if !tally.termWithin(e.Term, max) {
								return tooDeep("cited clause count filter term")
							}
						}
						if !tally.termWithin(bl.CountVal.Count, max) {
							return tooDeep("cited clause count slot term")
						}
						continue
					}
					inner, _ := bl.AsInner() // ok: the Count arm above covers the inner-less form
					if !goalWithin(inner, max, tally) {
						return tooDeep("cited clause body-literal argument")
					}
				}
			}
		}
	}
	// (c) every cited closed-model certificate's deep data (ADR 0007). For an
	//     all-positive derivation ClosedWorld is empty, so this is a no-op and the
	//     positive path is byte-identical (it never reaches a term_too_deep).
	for _, cert := range deriv.ClosedWorld {
		if what := certDepthsWithin(cert, max, tally); what != "" {
			return tooDeep(what)
		}
	}
	// (d) every Neg premise's atom + every Count premise's filter/k values (ground data
	//     the cert path traverses recursively).
	for _, node := range deriv.Nodes {
		if rule, ok := node.(RuleNode); ok {
			for _, premise := range rule.Premises {
				switch p := premise.(type) {
				case NegPremise:
					if !groundWithin(p.Atom, max, tally) {
						return tooDeep("negated premise atom argument")
					}
				case CountPremise:
					for _, e := range p.Filter {
						if !tally.valueWithin(e.Value, max) {
							return tooDeep("count premise filter value")
						}
					}
					if p.K != nil && !tally.valueWithin(p.K, max) {
						return tooDeep("count premise k value")
					}
				case PosPremise:
					// A node index: the node's own conclusion is depth-checked above.
				default:
					// The derivation is untrusted: nil, or a foreign type embedding Premise
					// (#3074, seat:caa's ruling), is refused by name, never skipped.
					return reject(UnknownNodeKind, fmt.Sprintf("premise of type %T is none of the known premise kinds", premise))
				}
			}
		}
	}
	return Accept()
}

// groundWithin reports that every argument of a GroundLiteral nests within max, each measured
// into tally.
func groundWithin(lit GroundLiteral, max int, tally *checkTally) bool {
	for _, v := range lit.Args {
		if !tally.valueWithin(v, max) {
			return false
		}
	}
	return true
}

// goalWithin reports that every argument term of a Goal nests within max, each measured into
// tally.
func goalWithin(goal Goal, max int, tally *checkTally) bool {
	for _, t := range goal.Args {
		if !tally.termWithin(t, max) {
			return false
		}
	}
	return true
}

// saturatingAddOne adds 1 to n without overflowing past the max int — keeps Check
// total even under a pathological consumer-set MaxDepth near the int ceiling (never
// attacker-reachable, since the node cap bounds chain length first) — defensive
// only, mirroring Rust's saturating_add.
func saturatingAddOne(n int) int {
	const maxInt = int(^uint(0) >> 1)
	if n == maxInt {
		return maxInt
	}
	return n + 1
}

func checkNode[C any](i int, node Node, program Program, deriv Derivation, ctx C, profile *CheckProfile[C], certStatus []certStatus, depth []int, tally *checkTally) Verdict {
	// nodes_walked: the walk begins this node, before any of its checks (a node that then rejects
	// counts). Its kind is counted first thing in its arm below.
	tally.nodesWalked++
	switch n := node.(type) {
	case RuleNode:
		// rule_nodes
		tally.ruleNodes++
		// (a) cited clause exists.
		clause, ok := program.Clause(n.Clause)
		if !ok {
			return reject(UnknownClause, fmt.Sprintf("no clause for id %q", n.Clause.String()))
		}
		// (b) positive premise indices reference strictly earlier nodes (acyclic DAG).
		//     A Neg premise carries no node index — it is a checked side-condition
		//     against a certificate, validated in (f).
		for _, premise := range n.Premises {
			if pos, ok := premise.(PosPremise); ok {
				if pos.Node >= uint64(i) {
					return reject(BadDependencyOrder, fmt.Sprintf("premise %d not < node %d", pos.Node, i))
				}
			}
		}
		// (c) depth (positive premises are < i, so already computed); cap → too_deep. A
		//     Neg premise contributes no depth (no node chain). saturatingAddOne keeps
		//     this total even under a pathological consumer-set MaxDepth near the int
		//     ceiling (never attacker-reachable, since the node cap bounds chain length
		//     first) — defensive only.
		maxPremiseDepth := 0
		for _, premise := range n.Premises {
			if pos, ok := premise.(PosPremise); ok {
				if depth[pos.Node] > maxPremiseDepth {
					maxPremiseDepth = depth[pos.Node]
				}
			}
		}
		depth[i] = saturatingAddOne(maxPremiseDepth)
		// max_depth_reached: the depth compared against MaxDepth, a tripping one included.
		tally.reachDepth(depth[i])
		if depth[i] > profile.Limits.MaxDepth {
			return reject(TooDeep, fmt.Sprintf("depth %d exceeds max_depth %d", depth[i], profile.Limits.MaxDepth))
		}
		// (d) subst applied to the head is ground and equals the conclusion.
		head, ok := clause.Head.Substitute(n.Subst).AsGround()
		if !ok {
			return reject(InstantiationMismatch, "clause head not ground under subst")
		}
		// Structural (#3022): a conclusion is never a relabeling of the instantiated head.
		if !head.Equal(n.Conc) {
			return reject(InstantiationMismatch, "instantiated head != conclusion")
		}
		// (e) one premise per body literal.
		if len(n.Premises) != len(clause.Body) {
			return reject(InstantiationMismatch, fmt.Sprintf("premise count %d != body length %d", len(n.Premises), len(clause.Body)))
		}
		// (f) premise k matches body literal k under subst, *with polarity* (ADR 0007 /
		//     ADR 0023):
		//     - Pos body lit ↔ PosPremise: the cited node's conclusion equals the
		//       grounded body literal.
		//     - Neg body lit ↔ NegPremise: the grounded body literal equals the
		//       premise's Atom, which is then discharged as ABSENT from the cited
		//       (verified) certificate.
		//     - Count body lit ↔ CountPremise: the grounded count literal's
		//       pred/filter/project/k equal the premise's, which is then discharged by
		//       recomputing the count over the cited (verified) cert.
		//     A polarity/kind mismatch in any direction is an instantiation_mismatch.
		//
		//     Every comparison here is STRUCTURAL (#3022). With (d) structural too, every node's
		//     conclusion is its exact fact, so the exact cone #2256 kept for spelling-sensitive
		//     clauses now holds for every clause by construction.
		for k, bodyLit := range clause.Body {
			// premises_pos / premises_neg: (f) begins examining premise k, counted by its own kind
			// (a count premise is positive) before any of its checks.
			tally.premise(n.Premises[k])
			// A Count body literal has no single underlying Goal (AsInner() reports none), so
			// branch on it BEFORE computing the Pos/Neg `expected` grounding.
			if bodyLit.IsCount() {
				premise, ok := n.Premises[k].(CountPremise)
				if !ok {
					return reject(InstantiationMismatch, fmt.Sprintf("premise %d polarity != body literal %d polarity", k, k))
				}
				// The grounded count body literal must agree with the premise's
				// pred/filter/project/k (positional + value agreement) before the count is
				// re-derived against the cited (verified) cert.
				gc := bodyLit.CountVal.Substitute(n.Subst)
				gFilter := make([]GroundFilterEntry, 0, len(gc.Filter))
				groundOK := true
				for _, e := range gc.Filter {
					v, ok := e.Term.EraseGround()
					if !ok {
						groundOK = false
						break
					}
					gFilter = append(gFilter, GroundFilterEntry{Pos: e.Pos, Value: v})
				}
				gCount, countOK := gc.Count.EraseGround()
				if !groundOK || !countOK {
					return reject(InstantiationMismatch, fmt.Sprintf("count body literal %d not ground under subst", k))
				}
				// Structural, like every site (#3022).
				if !gc.Pred.Equal(premise.Pred) ||
					!equalGroundFilter(gFilter, premise.Filter) ||
					!gc.Project.Equal(premise.Project) ||
					!gCount.Equal(premise.K) {
					return reject(InstantiationMismatch, fmt.Sprintf("count premise %d != body literal %d under subst", k, k))
				}
				if v := verifyCountPremise(premise.Pred, premise.Filter, premise.Project, premise.K, premise.Cert, n.Conc.Pred, deriv, certStatus); !v.IsAccept() {
					return v
				}
				continue
			}
			inner, _ := bodyLit.AsInner() // ok: the Count premise arm above ends in continue
			expected, ok := inner.Substitute(n.Subst).AsGround()
			if !ok {
				return reject(InstantiationMismatch, fmt.Sprintf("body literal %d not ground under subst", k))
			}
			switch premise := n.Premises[k].(type) {
			case PosPremise:
				if bodyLit.IsNeg() {
					return reject(InstantiationMismatch, fmt.Sprintf("premise %d polarity != body literal %d polarity", k, k))
				}
				// The cited node's conclusion must be EXACTLY the grounded body literal, for every
				// cited node kind (#3022; #2232 already required it of a Builtin, whose theory
				// decides on its own spelling).
				if !deriv.Nodes[premise.Node].Conclusion().Equal(expected) {
					return reject(InstantiationMismatch, fmt.Sprintf("premise %d conclusion != body literal %d under subst", k, k))
				}
			case NegPremise:
				if !bodyLit.IsNeg() {
					return reject(InstantiationMismatch, fmt.Sprintf("premise %d polarity != body literal %d polarity", k, k))
				}
				// #2227: the premise's Atom must EXACTLY equal the grounded negated body literal.
				// Its absence is then looked up by exact membership in the sealed table, so a match
				// under account equality would transfer an absence judged about one spelling to another.
				if !premise.Atom.Equal(expected) {
					return reject(InstantiationMismatch, fmt.Sprintf("neg premise %d atom != body literal %d under subst", k, k))
				}
				if v := verifyNegPremise(premise.Atom, premise.Cert, premise.Nonmember, n.Conc.Pred, deriv, certStatus); !v.IsAccept() {
					return v
				}
			case CountPremise:
				// A count premise cited for a body literal that is not a count: its kind does not match.
				return reject(InstantiationMismatch, fmt.Sprintf("premise %d polarity != body literal %d polarity", k, k))
			default:
				// The derivation is untrusted: nil, or a foreign type embedding Premise, is refused by name
				// (#3074, seat:caa's ruling). check's boundary refuses it first (#3088); defence in depth.
				return reject(UnknownNodeKind, fmt.Sprintf("premise %d of type %T is none of the known premise kinds", k, premise))
			}
		}
		// (g) sealing / partition on the head predicate (local checks, §4.2/§4.4):
		//     a clause head must be intensional — not extensional, not theory-owned.
		if profile.Leaves.Extensional().Contains(n.Conc.Pred) {
			return reject(SealedViolation, "rule head collides with an extensional predicate")
		}
		if profile.Theory.Owns(n.Conc.Pred) {
			return reject(PredicatePartitionViolation, "rule head predicate is owned by a theory")
		}
		// (h) THEN delegate metadata admissibility (§4 ob.2: structural-then-delegate).
		// admissibility_checks: one Admissible call.
		tally.admissibilityChecks++
		switch out := profile.Admit.Admissible(CloneClause(clause), n.Meta, ctx).(type) {
		case RuleAdmit:
			return Accept()
		case RuleReject:
			return reject(RuleInadmissible, out.Code)
		default:
			panic("contract: Admissible returned an unknown RuleOutcome")
		}

	case BuiltinNode:
		// builtin_nodes
		tally.builtinNodes++
		depth[i] = 1
		// max_depth_reached
		tally.reachDepth(depth[i])
		if depth[i] > profile.Limits.MaxDepth {
			return reject(TooDeep, "depth 1 exceeds max_depth")
		}
		owned := profile.Theory.Owns(n.Conc.Pred)
		// partition: a builtin predicate must be theory-owned, and not also
		// extensional (overlap is a partition violation, §4.4).
		if !owned {
			return reject(PredicatePartitionViolation, "no theory owns the builtin predicate")
		}
		if profile.Leaves.Extensional().Contains(n.Conc.Pred) {
			return reject(PredicatePartitionViolation, "builtin predicate is also extensional")
		}
		// #3126: the ground verdict, which can say "not decided". The detail of a false is the
		// theory's own code, read before any conversion into the algebra.
		// theory_decisions: one DecideGround call.
		tally.theoryDecisions++
		ground := readGround(DecideGround(profile.Theory, n.Conc))
		switch {
		case ground.arm == groundHolds:
			return Accept()
		case ground.arm == groundFails:
			return reject(BuiltinFailed, ground.code)
		case ground.disowned():
			// owns() said yes but decide disowns: an inconsistent theory.
			return reject(PredicatePartitionViolation, "theory owns predicate but returned NotMine")
		default:
			// A stop is refused by name, never read as a decision (#3126).
			return reject(BuiltinNotDecided, ground.cause.Kind().Tag())
		}

	case LeafNode:
		// leaf_nodes
		tally.leafNodes++
		depth[i] = 1
		// max_depth_reached
		tally.reachDepth(depth[i])
		if depth[i] > profile.Limits.MaxDepth {
			return reject(TooDeep, "depth 1 exceeds max_depth")
		}
		extensional := profile.Leaves.Extensional().Contains(n.Conc.Pred)
		owned := profile.Theory.Owns(n.Conc.Pred)
		// sealing / partition (§4.2/§4.4): a leaf may conclude only an extensional
		// predicate.
		if extensional && owned {
			return reject(PredicatePartitionViolation, "leaf predicate is both extensional and theory-owned")
		}
		if !extensional {
			if owned {
				return reject(PredicatePartitionViolation, "leaf predicate is owned by a theory, not extensional")
			}
			// not extensional and not a builtin ⇒ it is intensional: a leaf
			// concluding an intensional predicate is the sealing error.
			return reject(SealedViolation, "leaf concludes a non-extensional (intensional) predicate")
		}
		// leaf_verifications: one Verify call.
		tally.leafVerifications++
		switch out := profile.Leaves.Verify(n.Conc.detached(), n.Evidence, ctx).(type) {
		case LeafAdmit:
			return Accept()
		case LeafReject:
			return reject(LeafRejected, out.Code)
		default:
			panic("contract: Verify returned an unknown LeafOutcome")
		}

	default:
		// A well-typed Node is one of the three known kinds; this is the
		// decoder-band code, unreachable from typed input.
		return reject(UnknownNodeKind, "unknown node kind")
	}
}

// UnownedBuiltinPredicates reports the Builtin predicates in deriv that no theory bound by
// this profile owns - the pre-check capability query (issue #1371).
//
// Ask this BEFORE Check. An empty result means this host can decide every builtin the
// derivation cites; a non-empty one names exactly the predicates it cannot, so a caller
// knows WHICH theory to bind rather than only that something is missing.
//
// Why it exists: Check re-decides every BuiltinNode through profile.Theory. On a host that
// binds no theory owning the predicate, the rejection is PredicatePartitionViolation - a
// structural-band code meaning "this account is malformed". But the account may be sound;
// it is the VERIFIER that lacks a capability. A consumer branching on the code then
// dispatches an investigator at the producer, when nothing is wrong except the binding set
// of the host doing the re-check.
//
// WHAT AN EMPTY RESULT DOES NOT PROMISE: it does not mean Check will accept. It answers ONE
// condition - theory ownership. Two others raise the same structural code and are untouched:
// a builtin predicate that is also extensional (a genuine partition overlap), and a theory
// whose Owns says yes while DecideGround disowns the atom (an inconsistent theory). Empty means no
// capability refusal will occur, never that the account is valid.
//
// Additive and non-breaking: a helper over existing contract types, adding no RejectionCode
// and moving no vector. It reads BuiltinNode conclusions and Theory.Owns only - no DecideGround
// call, so it is total and side-effect-free. Order is derivation node order, deduplicated on
// first appearance, so the result is deterministic for a given derivation.
func UnownedBuiltinPredicates[C any](deriv Derivation, profile *CheckProfile[C]) []Symbol {
	out := []Symbol{}
	for _, node := range deriv.Nodes {
		b, ok := node.(BuiltinNode)
		if !ok {
			continue
		}
		if profile.Theory.Owns(b.Conc.Pred) {
			continue
		}
		seen := false
		for _, p := range out {
			if p == b.Conc.Pred {
				seen = true
				break
			}
		}
		if !seen {
			out = append(out, b.Conc.Pred)
		}
	}
	return out
}

// ProfileDecidesAllBuiltins reports whether this profile can decide every Builtin predicate
// deriv cites - the boolean convenience over UnownedBuiltinPredicates.
//
// Same limit as the report it wraps: true means no capability refusal will occur, not that
// Check will accept. Prefer the list form when reporting to a human or a log - it names what
// to bind, and a bare false invites the "the account is bad" reading this query exists to
// prevent.
func ProfileDecidesAllBuiltins[C any](deriv Derivation, profile *CheckProfile[C]) bool {
	return len(UnownedBuiltinPredicates(deriv, profile)) == 0
}

// IncoherentBuiltinAtoms returns the Builtin conclusions this profile's theory owns but
// disowns - Owns(pred) is true while DecideGround(conclusion) answers the inconsistent_theory
// fault (completion.TheoryGroundDisowned).
//
// A non-empty result is a VERIFIER-side defect: the bound Theory violates the coherence
// obligation of §5, which requires DecideGround to reach a verdict on every atom whose predicate
// Owns claims. Check rejects this with the structural code PredicatePartitionViolation -
// correctly, since the account cannot be verified by this profile - but a consumer reading
// that code alone is pointed at the PRODUCER for what is a bug in the host's own theory
// binding. This query is the attribution the code cannot carry (issue #1378): it names the
// atoms that expose it.
//
// Unlike UnownedBuiltinPredicates, this one CALLS DecideGround. Ownership is a property of a
// predicate, but incoherence is only observable per atom, so the question cannot be answered
// without deciding. It therefore costs what the corresponding part of Check costs and is not
// side-effect-free against a theory whose DecideGround is expensive or stateful. Its value is
// attribution after a rejection, not avoidance before one.
//
// An empty result does NOT certify the theory coherent. It witnesses only that no atom this
// derivation cites exposes the disagreement; a theory incoherent on any other atom returns
// empty here. Read it as "this rejection is not that bug", never as "the theory is sound".
//
// Additive and non-breaking: no RejectionCode variant, no vector moved. Order is derivation
// node order, deduplicated on first appearance, so the result is deterministic for a given
// derivation. The dedup test precedes the DecideGround call, so a repeated offending atom is
// decided once.
func IncoherentBuiltinAtoms[C any](deriv Derivation, profile *CheckProfile[C]) []GroundLiteral {
	out := []GroundLiteral{}
	for _, node := range deriv.Nodes {
		b, ok := node.(BuiltinNode)
		if !ok {
			continue
		}
		if !profile.Theory.Owns(b.Conc.Pred) {
			continue
		}
		seen := false
		for _, a := range out {
			if a.Equal(b.Conc) {
				seen = true
				break
			}
		}
		if seen {
			continue
		}
		// The disowning fault, completion.TheoryGroundDisowned (#3126). A theory that
		// stopped (a work cap) is not listed: it did not disown the atom.
		if readGround(DecideGround(profile.Theory, b.Conc)).disowned() {
			out = append(out, b.Conc)
		}
	}
	return out
}
