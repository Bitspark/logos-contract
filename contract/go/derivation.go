// §3 Derivation — the shared DTO, the heart. [FIRM]
//
// A finite DAG of nodes; each node concludes a *ground* literal; premises reference
// earlier nodes (acyclic). The node set is *closed and positive* — Rule | Builtin |
// Leaf — with no negation/cut/findall/aggregation (§3.1): that is the single
// decision making the contract checkable by a verifier *and* producible by a
// solver, rather than "arche with holes".
//
// ADR 0007 (additive). A Rule premise gains polarity: a positive premise discharges
// a positive body literal by an earlier node; a Neg premise discharges a negated
// body literal \+ r(a) as a checked side-condition against a sealed ClosedModelCert
// carried in Derivation.ClosedWorld. An all-positive, empty-ClosedWorld derivation
// is exactly today's account, and Check over it behaves byte-identically.
package contract

import core "github.com/bitspark/ontos/core/go"

// NodeMeta is provenance / placement metadata attached to a Rule node. *Opaque to
// the core* — only a RuleAdmissibility verifier interprets it (it carries, e.g.,
// arche's RuleProvenance: signer, projection binding, space). Modelled as an
// optional ontos value so a consumer can pack arbitrary structured data the kernel
// never inspects. The inner value is private so opacity-to-core is enforced by the
// type, not merely by convention: the kernel cannot read it, only thread it to the
// verifier.
type NodeMeta struct {
	value core.Value // nil means "none"
}

// NoMeta is empty metadata (the common case for non-provenance-bound rules).
func NoMeta() NodeMeta { return NodeMeta{} }

// NewNodeMeta packs a consumer value as rule metadata.
func NewNodeMeta(value core.Value) NodeMeta { return NodeMeta{value: value} }

// Value returns the packed value (and ok=false if none), for a consumer's
// RuleAdmissibility to interpret.
func (m NodeMeta) Value() (core.Value, bool) {
	if m.value == nil {
		return nil, false
	}
	return m.value, true
}

// Evidence is attestation / admission evidence attached to a Leaf node. *Opaque to
// the core* — only a LeafVerifier interprets it (it carries, e.g., arche's
// {signer, signature, admission, space}). The inner value is private for the same
// opacity reason as NodeMeta.
type Evidence struct {
	value core.Value // nil means "none"
}

// NoEvidence is no evidence (e.g. a trusted axiom leaf).
func NoEvidence() Evidence { return Evidence{} }

// NewEvidence packs consumer evidence for a LeafVerifier to interpret.
func NewEvidence(value core.Value) Evidence { return Evidence{value: value} }

// Value returns the packed value (and ok=false if none), for a consumer's
// LeafVerifier to interpret.
func (e Evidence) Value() (core.Value, bool) {
	if e.value == nil {
		return nil, false
	}
	return e.value, true
}

// Premise is a Rule premise — one per clause body literal, with polarity (ADR 0007).
// The unexported marker method keeps the sum type closed — only PosPremise and
// NegPremise in this package implement it (mirroring Rust's Premise enum).
//
//   - PosPremise discharges a positive body literal by an earlier derivation node
//     (the same backward edge today's account carried as a bare int).
//   - NegPremise discharges a negated body literal \+ r(a) as a checked side-condition
//     (NOT a node): the negated atom r(a) must be absent from a cited, already-verified
//     ClosedModelCert. This is what makes absence sound rather than an upper bound — the
//     cert proves the sealed relation is exact.
type Premise interface {
	isPremise()
}

// PosPremise is a positive body literal, discharged by node index Node (< this node).
type PosPremise struct {
	Node uint64
}

// NegPremise is a negated body literal \+ Atom, discharged by absence from
// ClosedWorld[Cert] (ADR 0007).
type NegPremise struct {
	// Atom is the grounded negated atom that must be absent from the sealed relation.
	Atom GroundLiteral
	// Cert indexes Derivation.ClosedWorld for the certificate to consult.
	Cert CertId
	// Nonmember is how non-membership is witnessed (a direct table lookup in v1).
	Nonmember NonMemberProof
}

// CountPremise is a certifiable count / count_distinct body literal (ADR 0023),
// discharged NOT by an earlier node but as a checked side-condition: the checker
// recomputes the cardinality over closedWorld[Cert].Table(Pred) — a relation it has
// independently proven exact — and accepts only if it equals the claimed K. Go sibling
// of Rust's Premise::Count variant.
type CountPremise struct {
	// Pred is the sealed relation being counted — matched by name AND arity (#581).
	Pred PredicateRef
	// Filter is the GROUND bound-position filter selecting the counted rows: each
	// (position, value) requires the row's argument at position to equal value. Mirrors
	// Rust's GroundFilter = Vec<(u32, Value)> (ground values, not terms).
	Filter []GroundFilterEntry
	// Project is Rows (count) or Distinct{attr} (count_distinct).
	Project ProjectSpec
	// K is the CLAIMED cardinality, embedded as the canonical ontos/data int ground
	// value. The checker recomputes n and requires n == k.
	K core.Value
	// Cert indexes Derivation.ClosedWorld for the certificate to consult.
	Cert CertId
}

// GroundFilterEntry is one (position, value) of a Count premise's GROUND filter: it
// requires the counted row's argument at Pos to equal Value. Go sibling of one element of
// Rust's GroundFilter.
type GroundFilterEntry struct {
	Pos   uint32
	Value core.Value
}

func (PosPremise) isPremise()   {}
func (NegPremise) isPremise()   {}
func (CountPremise) isPremise() {}

// PosNode builds a positive premise referencing node index n. The all-positive
// premise list [PosNode(0), PosNode(2)] is the common case (and the only one engines
// emit today). Named PosNode (not Pos) because Pos is already the positive Polarity
// tag on a BodyLit.
func PosNode(n uint64) Premise { return PosPremise{Node: n} }

// PosPremises lifts a list of node indices to positive premises — so an existing
// all-positive premise list ([]int{0, 2}) ports to PosPremises(0, 2) unchanged in
// meaning. The common case for every all-positive derivation.
func PosPremises(nodes ...uint64) []Premise {
	ps := make([]Premise, len(nodes))
	for i, n := range nodes {
		ps[i] = PosPremise{Node: n}
	}
	return ps
}

// Node is a derivation node. Every kind concludes a GroundLiteral. The unexported
// marker method keeps the sum type closed — only RuleNode, BuiltinNode, and
// LeafNode in this package implement it (mirroring Rust's enum).
type Node interface {
	// Conclusion returns the ground literal this node concludes (every kind has one).
	Conclusion() GroundLiteral

	isNode()
}

// RuleNode is an intensional step: instantiate a cited clause.
type RuleNode struct {
	Conc   GroundLiteral
	Clause ClauseId
	// Subst is the grounding substitution applied to the clause.
	Subst Subst
	// Premises is one Premise per body literal, in body order; each PosPremise index <
	// this node's index. A NegPremise is a checked side-condition (ADR 0007).
	Premises []Premise
	// Meta is opaque to core (provenance / projection binding / …).
	Meta NodeMeta
}

// BuiltinNode is a theory/builtin atom, decided by the Theory SPI (§5), not by
// clauses. Carries NO TheoryId — dispatch is by predicate ownership (§3, §4
// obligation 3).
type BuiltinNode struct {
	Conc GroundLiteral
}

// LeafNode is an extensional leaf, admitted by the LeafVerifier SPI (§6), not
// derived.
type LeafNode struct {
	Conc     GroundLiteral
	Evidence Evidence
}

func (RuleNode) isNode()    {}
func (BuiltinNode) isNode() {}
func (LeafNode) isNode()    {}

// Conclusion returns the rule node's ground conclusion.
func (n RuleNode) Conclusion() GroundLiteral { return n.Conc }

// Conclusion returns the builtin node's ground conclusion.
func (n BuiltinNode) Conclusion() GroundLiteral { return n.Conc }

// Conclusion returns the leaf node's ground conclusion.
func (n LeafNode) Conclusion() GroundLiteral { return n.Conc }

// Derivation is a finite DAG of nodes with a distinguished Root (an index into
// Nodes), plus the ClosedModelCerts the derivation's Neg premises cite (ADR 0007).
// This is arche-core's Proof { nodes, root }, generalized so the two non-structural
// node kinds delegate to extension points and a negated premise discharges against a
// sealed certificate.
//
// Additive (ADR 0007): ClosedWorld defaults to empty (NewDerivation); an all-Pos,
// empty-ClosedWorld derivation is exactly today's account, and Check over it behaves
// byte-identically — the certificate machinery is only consulted when a Neg premise
// (and hence a non-empty ClosedWorld) is present.
// THIS TYPE IS THE ACCOUNT.
//
// Account is not a separate type and never has been — it is the name the v2 design and
// ADR 0003 give to this artifact:
//
//   - ADR 0003's layer table: "A. Account / proof artifact" -> Derivation
//     (Rule|Theory|Leaf), FIRM / invariant per ADR 0001.
//   - docs/spec/logos-contract.md: "the account grammar — the Derivation node set".
//   - v2 section 0 glossary: "Account — a derivation in the core evidence language".
//
// So a plan item written Account::foo() is a method on Derivation — e.g. v2 section 8.2's
// Account::is_self_contained() ships as Derivation.IsSelfContained.
//
// Stated because a DECLARATION-shaped search (struct|type Account) returns zero and reads
// as "unbuilt". Two agents concluded exactly that on 2026-08-29; the mapping was already in
// the three documents above and neither looked, because a code-shaped question invites a
// code-shaped search. This note cannot make that query succeed — only a public alias could,
// and adding a public name to FIRM layer A is outside ADR 0003's additive permission and is
// not a documentation change. What it does is make a plain search for "account" state the
// identity outright instead of only alluding to it.
type Derivation struct {
	Nodes []Node
	Root  uint64
	// ClosedWorld holds the closed-model certificates this derivation CARRIES, indexed by
	// CertId: every certificate its Neg and Count premises cite, at the index they cite it by.
	// The in-tree producer carries the prefix up to the highest cited certificate, and none when
	// nothing is cited (#2533), so a carried certificate is not by itself a dependency: read the
	// citations.
	ClosedWorld []ClosedModelCert
}

// NewDerivation builds a Derivation from nodes and a root index, with NO closed-model
// certificates (the all-positive case). Every existing call site is unchanged —
// ClosedWorld defaults to empty.
func NewDerivation(nodes []Node, root uint64) Derivation {
	return Derivation{Nodes: append([]Node(nil), nodes...), Root: root}
}

// NewDerivationWithClosedWorld builds a Derivation that carries the closed-model
// certificates its Neg premises cite (ADR 0007).
// IsSelfContained reports whether this account can be checked against a trivial
// context — no closure certificates to resolve against.
//
// Section 8.2 of the v2 design: "an account is portable iff it is either fully
// self-contained or carries authenticated ...". This is the FIRST arm, and it is the
// account-side mirror of the kernel seam's CheckContext.IsTrivial (named in prose, not
// imported: contract is the bottom tier and does not depend on kernel — ADR 0004).
//
// The polarity it reads is already load-bearing in Check: a non-empty ClosedWorld is a
// certifying check that needs a bound cert context, and for an all-positive derivation
// the context is never consulted.
//
// Deliberately HALF of its mirror, and that asymmetry is the point. CheckContext.IsTrivial
// is two-half (base commitments AND certificates); this is the CLOSURE half only — the
// base-facts half has no account-side carrier, because contract's Check reads
// base_commitments nowhere (0 references). Widen this when base facts become
// context-dependent. An && over a field nothing reads would be vacuously true and would
// read as coverage it does not provide (ruled 2026-08-29, seat:cca).
// RootOffset is the root's host offset into Nodes, ok only when it is in range (#2735).
func (d Derivation) RootOffset() (int, bool) { return IndexOffset(d.Root, len(d.Nodes)) }

func (d Derivation) IsSelfContained() bool {
	return len(d.ClosedWorld) == 0
}

func NewDerivationWithClosedWorld(nodes []Node, root uint64, closedWorld []ClosedModelCert) Derivation {
	return Derivation{
		Nodes:       append([]Node(nil), nodes...),
		Root:        root,
		ClosedWorld: append([]ClosedModelCert(nil), closedWorld...),
	}
}
