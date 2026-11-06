// netreach — the SECOND, non-arche, check-only consumer of the STABLE-v1 checker SPI
// (issue #461). It discharges the single named open obligation on the [STABLE v1]
// promise in docs/spec/logos-contract.md (§ firmness-layers intro): *"Genericity is
// provisional — v1 is validated for production use by arche as first consumer, not
// proven the final generic shape (a second, non-arche checker consumer is still
// wanted)."*
//
// # What makes this a GENUINE second consumer (not "arche with the names changed")
//
// This file binds the public checker SPI — Theory (§5), LeafVerifier[C] (§6),
// RuleAdmissibility[C] (§5a), Context (§4.1), CheckLimits (§4.3), Outcome — over its
// OWN small domain (a directed network's reachability), driving Check() with no shared
// code path with arche's bindings. Every seam is exercised with a shape arche does NOT
// use, so the surface's genericity is *demonstrated, not asserted* (the §0 "lift the
// concept, not the name" discipline, logos#3):
//
//   - Context (§4.1) = a NETWORK SNAPSHOT (`netSnapshot` — a set of admitted directed
//     links), NOT arche's `{targetSpace, factIndex, root_pubkey}`. A non-trivial,
//     read-only verification snapshot the LeafVerifier consults — exactly the issue's
//     "DB-snapshot leaves, no signatures, a non-trivial Context" vehicle.
//   - LeafVerifier (§6) = `linkVerifier` — admits an extensional `link(a,b)` iff the
//     pair is present in the snapshot. NO signatures, NO Ed25519, NO ledger: a leaf is
//     admitted by mere membership in a trusted DB snapshot (the §6 "DB-snapshot facts"
//     case the spec names but arche does not take). Its extensional namespace is `link`
//     — a custom leaf predicate arche has no concept of.
//   - Theory (§5) = `parityTheory` — a CUSTOM theory relation `same_parity(m, n)` over
//     the FROZEN ontos-data `int` embedding. This is a config-pinned PURE numeric
//     predicate, NOT arche's `is_root` trust-anchor: it proves the generic concept
//     logos owns ("a config-pinned axiom/relation set") beyond arche's single binding.
//   - RuleAdmissibility (§5a): two bindings, to exercise BOTH ends of the seam —
//     (1) the no-op `AlwaysAdmit` (proving a non-arche consumer pays nothing for the
//     hook), and (2) a CUSTOM `tagPolicy` that reads opaque `NodeMeta` and rejects a
//     rule whose meta carries a tag the consumer disallows — a metadata policy arche's
//     projection-binding does not resemble (it is a plain allow-list over a custom tag).
//
// # The result this records
//
// The v1 generic shape holds for this consumer with NO contract change: every seam was
// bindable against the public surface with non-arche-shaped types, Check accepted every
// well-formed netreach derivation and rejected every malformed one with the documented
// FIRM structural / host-extension codes. This is the second consumer the caveat wanted;
// the spec's provisional-genericity sentence is updated to record it (this PR).
package contract

import (
	"math/big"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ---------------------------------------------------------------------------
// The domain vocabulary (all non-arche).
//
//	link(a, b)         — EXTENSIONAL: a directed edge admitted from the snapshot (Leaf).
//	reachable(X, Y)    — INTENSIONAL: transitive reachability, defined by two clauses (Rule).
//	same_parity(m, n)  — BUILTIN: a config-pinned numeric relation decided by parityTheory.
//
// ---------------------------------------------------------------------------

const (
	predLink       = "link"
	predReachable  = "reachable"
	predSameParity = "same_parity"
)

// node builds a network-node atom value (e.g. node("a")) — a bare ontos Atom, the
// netreach domain's identifier (arche's leaf args are byte pubkeys; ours are short
// names — both are just bytes, which is the point of an Atom).
func node(name string) core.Value { return core.NewAtom([]byte(name)) }

// intVal builds the frozen ontos-data int embedding for n — the value sort parityTheory
// decides over. Reuses the SAME canonical encoder the ArithmeticTheory uses, so the
// numeric domain is the real frozen embedding, not a netreach re-invention.
func intVal(n int64) core.Value { return data.EncodeInt(big.NewInt(n)) }

// ---------------------------------------------------------------------------
// Context (§4.1) — a network snapshot, the netreach verification snapshot.
// ---------------------------------------------------------------------------

// linkKey is a comparable key for a directed (from, to) edge, so a snapshot is an
// ordinary set.
type linkKey struct{ from, to string }

// netSnapshot is the netreach Context: an immutable, read-only set of directed links
// the checker threads to the LeafVerifier (§4.1 — "any data it needs is built into ctx
// BEFORE check runs"). It is NOT a live service handle: it is consulted by membership
// only, performs no I/O, reads no clock, and is fixed for the whole Check call — the §6
// / G14 determinism obligation. This is the netreach analogue of arche's factIndex, but
// shaped to netreach, not copied from arche.
type netSnapshot struct {
	links map[linkKey]struct{}
}

// newSnapshot builds a snapshot from (from,to) string pairs.
func newSnapshot(pairs ...[2]string) netSnapshot {
	m := make(map[linkKey]struct{}, len(pairs))
	for _, p := range pairs {
		m[linkKey{from: p[0], to: p[1]}] = struct{}{}
	}
	return netSnapshot{links: m}
}

// has reports whether the snapshot admits the directed link (from, to).
func (s netSnapshot) has(from, to string) bool {
	_, ok := s.links[linkKey{from: from, to: to}]
	return ok
}

// ---------------------------------------------------------------------------
// LeafVerifier (§6) — linkVerifier: DB-snapshot leaves, NO signatures.
// ---------------------------------------------------------------------------

// linkVerifier admits an extensional link(a, b) leaf iff the snapshot in ctx contains
// the directed edge. It verifies NO signature and consults NO ledger — a leaf is trusted
// because it is present in the trusted snapshot (the §6 "trusted local facts /
// DB-snapshot facts" profile, explicitly NOT arche's signed_fact profile). Its
// extensional set is exactly {link}; a Leaf concluding any other predicate is sealed out
// by the core before verify is ever called.
// test-double: consumer(link facts from a trusted snapshot ctx)
type linkVerifier struct {
	ext *PredicateSet
}

func newLinkVerifier() linkVerifier {
	return linkVerifier{ext: PredicateSetOf(predLink)}
}

// Extensional declares the single sealed predicate `link` (§4.2).
func (v linkVerifier) Extensional() *PredicateSet { return v.ext }

// Verify admits link(from, to) iff the snapshot has it. Total + deterministic over
// (atom, evidence, ctx); evidence is ignored entirely (no attestation in this domain).
// The host-band reject sub-code `link_not_in_snapshot` is netreach's own — pinned only
// in this consumer's suite (the host-extension band is open, §4).
func (v linkVerifier) Verify(atom GroundLiteral, _ Evidence, ctx netSnapshot) LeafOutcome {
	if atom.Pred.String() != predLink || len(atom.Args) != 2 {
		return LeafReject{Code: "link_malformed"}
	}
	from, ok1 := atomName(atom.Args[0])
	to, ok2 := atomName(atom.Args[1])
	if !ok1 || !ok2 {
		return LeafReject{Code: "link_malformed"}
	}
	if ctx.has(from, to) {
		return LeafAdmit{}
	}
	return LeafReject{Code: "link_not_in_snapshot"}
}

// atomName reads a bare ontos Atom's bytes as a UTF-8 name (false for a tuple/non-atom).
func atomName(v core.Value) (string, bool) {
	a, ok := v.(core.Atom)
	if !ok {
		return "", false
	}
	return string(a.Bytes()), true
}

// ---------------------------------------------------------------------------
// Theory (§5) — parityTheory: a CUSTOM config-pinned numeric relation.
// ---------------------------------------------------------------------------

// parityTheory decides the custom relation same_parity(m, n): HOLDS iff m and n are both
// even or both odd, over the frozen ontos-data int embedding. It is config-pinned and
// PURE in the §5 sense: the verdict is a function of the ground arguments alone, with no
// I/O, clock, or live ctx (the seam never receives ctx — that is the structural purity
// guarantee, §5.1). It is NOT arche's is_root: it carries a relation arche has no
// concept of, exercising the generic "config-pinned axiom/relation set" the spec says
// logos owns rather than is_root specifically.
//
// "config-pinned" here is trivial (the relation has no tunable config), so parityTheory
// exposes the canonical UNIDENTIFIED component identity via the optional Identified seam
// — proving the optional-identity type-assertion path works for a non-arche component too.
// test-double: consumer(a custom same_parity relation)
type parityTheory struct{}

// Owns claims exactly same_parity (by name, any arity — a malformed arity is decided as
// a non-holding atom, never a panic, mirroring ArithmeticTheory's owns-by-name).
func (parityTheory) Owns(pred Symbol) bool { return pred.String() == predSameParity }

// Decide decides a ground same_parity atom. Pure / total / deterministic.
func (parityTheory) Decide(atom GroundLiteral) TheoryOutcome {
	if atom.Pred.String() != predSameParity {
		return TheoryNotMine{}
	}
	if len(atom.Args) != 2 {
		return TheoryFails{Code: "same_parity_bad_arity"}
	}
	m, err1 := data.ReadInt(atom.Args[0])
	n, err2 := data.ReadInt(atom.Args[1])
	if err1 != nil || err2 != nil {
		return TheoryFails{Code: "same_parity_not_int"}
	}
	// Bit(0) is the low bit of the magnitude — parity is sign-independent, which is all
	// we need (and matches a "both even or both odd" reading).
	if m.Bit(0) == n.Bit(0) {
		return TheoryHolds{}
	}
	return TheoryFails{Code: "same_parity_does_not_hold"}
}

// Identity exposes the canonical unidentified identity (parityTheory has no config to
// pin). It thus implements the optional Identified seam — the kernel-side
// type-assertion resolves it exactly as it would arche's is_root identity.
func (parityTheory) Identity() ComponentIdentity { return UnidentifiedComponent() }

// ---------------------------------------------------------------------------
// RuleAdmissibility (§5a) — a CUSTOM tag policy (the non-no-op binding).
// ---------------------------------------------------------------------------

// tagPolicy is a custom RuleAdmissibility that reads the opaque NodeMeta and rejects a
// Rule whose meta carries a `tag` the consumer disallows. NodeMeta stays opaque to the
// core; only this verifier interprets it (§5a). This is a metadata policy arche does NOT
// use — a plain allow-list over a custom meta tag, not projection binding — so it
// exercises the seam with a non-arche shape. Total + deterministic over (clause, meta,
// ctx); it never touches ctx.
//
// The meta shape: NodeMeta packs Tuple[Atom("tag"), Atom(<tag-bytes>)]; a missing/other
// shape is treated as the untagged default (admitted). A disallowed tag rejects with the
// host-band sub-code `disallowed_rule_tag`.
// test-double: consumer(a custom rule-tag allow-list)
type tagPolicy struct {
	disallowed map[string]struct{}
}

func newTagPolicy(disallowed ...string) tagPolicy {
	m := make(map[string]struct{}, len(disallowed))
	for _, t := range disallowed {
		m[t] = struct{}{}
	}
	return tagPolicy{disallowed: m}
}

// Admissible reads the meta tag (if any) and rejects a disallowed one.
func (p tagPolicy) Admissible(_ Clause, meta NodeMeta, _ netSnapshot) RuleOutcome {
	tag, ok := metaTag(meta)
	if !ok {
		return RuleAdmit{} // untagged ⇒ admitted (the common case).
	}
	if _, bad := p.disallowed[tag]; bad {
		return RuleReject{Code: "disallowed_rule_tag"}
	}
	return RuleAdmit{}
}

// metaTag extracts a tag string from NodeMeta packed as Tuple[Atom("tag"), Atom(bytes)].
func metaTag(meta NodeMeta) (string, bool) {
	v, ok := meta.Value()
	if !ok {
		return "", false
	}
	tup, ok := v.(core.Tuple)
	if !ok {
		return "", false
	}
	items := tup.Items()
	if len(items) != 2 {
		return "", false
	}
	head, ok := items[0].(core.Atom)
	if !ok || string(head.Bytes()) != "tag" {
		return "", false
	}
	tagAtom, ok := items[1].(core.Atom)
	if !ok {
		return "", false
	}
	return string(tagAtom.Bytes()), true
}

// taggedMeta packs a rule tag as the NodeMeta shape tagPolicy reads.
func taggedMeta(tag string) NodeMeta {
	return NewNodeMeta(core.NewTuple(core.NewAtom([]byte("tag")), core.NewAtom([]byte(tag))))
}

// ---------------------------------------------------------------------------
// The netreach program + profiles.
// ---------------------------------------------------------------------------

// netreach clause ids (opaque stable handles, §2 — netreach uses plain string handles,
// not arche's canonical hashes; the v1 "stable + lookup-able" contract allows either).
const (
	clauseReachBase = "reachable/base" // reachable(X, Y) :- link(X, Y).
	clauseReachRec  = "reachable/rec"  // reachable(X, Z) :- link(X, Y), reachable(Y, Z).
)

// netreachProgram builds the two-clause transitive-reachability program.
func netreachProgram() *MapProgram {
	return NewMapProgram().
		With(NewClauseId(clauseReachBase), NewClause(
			NewGoal(predReachable, Var("X"), Var("Y")),
			NewGoal(predLink, Var("X"), Var("Y")),
		)).
		With(NewClauseId(clauseReachRec), NewClause(
			NewGoal(predReachable, Var("X"), Var("Z")),
			NewGoal(predLink, Var("X"), Var("Y")),
			NewGoal(predReachable, Var("Y"), Var("Z")),
		))
}

// netreachProfile builds the CheckProfile over netSnapshot with the chosen
// RuleAdmissibility binding. The Theory and LeafVerifier are netreach's own; the limits
// are the standard defaults.
func netreachProfile(admit RuleAdmissibility[netSnapshot]) *CheckProfile[netSnapshot] {
	return &CheckProfile[netSnapshot]{
		Theory: parityTheory{},
		Leaves: newLinkVerifier(),
		Admit:  admit,
		Limits: DefaultLimits(),
	}
}

// linkLeaf builds a Leaf node concluding link(from, to) with no evidence (no attestation
// in this domain).
func linkLeaf(from, to string) Node {
	return LeafNode{Conc: NewGroundLiteral(predLink, node(from), node(to)), Evidence: NoEvidence()}
}

// reachBaseNode builds a Rule node reachable(from,to) :- link(from,to) over the base
// clause, discharging its one positive premise by linkNode.
func reachBaseNode(from, to string, linkNode int, meta NodeMeta) Node {
	return RuleNode{
		Conc:   NewGroundLiteral(predReachable, node(from), node(to)),
		Clause: NewClauseId(clauseReachBase),
		Subst: Subst{
			NewVarId("X"): Atom([]byte(from)),
			NewVarId("Y"): Atom([]byte(to)),
		},
		Premises: PosPremises(uint64(linkNode)),
		Meta:     meta,
	}
}

// reachRecNode builds a Rule node reachable(from,to) :- link(from,mid), reachable(mid,to)
// over the recursive clause, discharging link by linkNode and reachable by reachNode.
func reachRecNode(from, mid, to string, linkNode, reachNode int, meta NodeMeta) Node {
	return RuleNode{
		Conc:   NewGroundLiteral(predReachable, node(from), node(to)),
		Clause: NewClauseId(clauseReachRec),
		Subst: Subst{
			NewVarId("X"): Atom([]byte(from)),
			NewVarId("Y"): Atom([]byte(mid)),
			NewVarId("Z"): Atom([]byte(to)),
		},
		Premises: PosPremises(uint64(linkNode), uint64(reachNode)),
		Meta:     meta,
	}
}

// ===========================================================================
// The conformance suite: drive Check over netreach's own domain.
// ===========================================================================

// TestNetreach_AcceptsTransitiveReachability is the headline ACCEPT: a two-hop
// reachable(a, c) derivation over link(a,b), link(b,c). Three node kinds are NOT all
// present here (no Builtin) — this is the pure Rule+Leaf reachability backbone arche's
// projection domain has no analogue of.
func TestNetreach_AcceptsTransitiveReachability(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot([2]string{"a", "b"}, [2]string{"b", "c"})
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	// nodes:
	//   0: link(b, c)              [leaf]
	//   1: reachable(b, c)         [rule base, premise 0]
	//   2: link(a, b)              [leaf]
	//   3: reachable(a, c)         [rule rec, premises link=2, reachable=1]
	deriv := NewDerivation([]Node{
		linkLeaf("b", "c"),
		reachBaseNode("b", "c", 0, NoMeta()),
		linkLeaf("a", "b"),
		reachRecNode("a", "b", "c", 2, 1, NoMeta()),
	}, 3)

	claim := NewGroundLiteral(predReachable, node("a"), node("c"))
	out := Check[netSnapshot](prog, claim, deriv, snap, profile)
	if !out.IsAccept() {
		t.Fatalf("expected Accept, got %s", out)
	}
}

// TestNetreach_AcceptsAllThreeNodeKinds proves the full account is bindable: a derivation
// mixing a Leaf (link), a Rule (reachable), and a Builtin (same_parity) — every node
// kind the closed-positive account allows, over netreach's own vocabulary. The claim is
// a reachable; the same_parity Builtin stands as an independent accepted node to witness
// the Theory seam inside a real multi-kind derivation.
func TestNetreach_AcceptsAllThreeNodeKinds(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot([2]string{"a", "b"})
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	// A standalone same_parity(2, 4) Builtin (both even ⇒ Holds), checked as its own root.
	parityDeriv := NewDerivation([]Node{
		BuiltinNode{Conc: NewGroundLiteral(predSameParity, intVal(2), intVal(4))},
	}, 0)
	parityClaim := NewGroundLiteral(predSameParity, intVal(2), intVal(4))
	if out := Check[netSnapshot](prog, parityClaim, parityDeriv, snap, profile); !out.IsAccept() {
		t.Fatalf("same_parity(2,4) builtin: expected Accept, got %s", out)
	}

	// A reachable(a, b) base derivation (Leaf + Rule) accepted in the same profile.
	reachDeriv := NewDerivation([]Node{
		linkLeaf("a", "b"),
		reachBaseNode("a", "b", 0, NoMeta()),
	}, 1)
	reachClaim := NewGroundLiteral(predReachable, node("a"), node("b"))
	if out := Check[netSnapshot](prog, reachClaim, reachDeriv, snap, profile); !out.IsAccept() {
		t.Fatalf("reachable(a,b): expected Accept, got %s", out)
	}
}

// TestNetreach_RejectsLeafNotInSnapshot proves the Context-threaded LeafVerifier actually
// gates: a derivation citing link(a, c), which the snapshot does NOT contain, is rejected
// through the host-extension band (leaf_rejected) with netreach's own sub-code. This is
// the genericity payoff — the SAME Check, with a non-arche Context, enforces a non-arche
// leaf policy.
func TestNetreach_RejectsLeafNotInSnapshot(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot([2]string{"a", "b"}) // no a→c link
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	deriv := NewDerivation([]Node{
		linkLeaf("a", "c"), // not in the snapshot
		reachBaseNode("a", "c", 0, NoMeta()),
	}, 1)
	claim := NewGroundLiteral(predReachable, node("a"), node("c"))

	out := Check[netSnapshot](prog, claim, deriv, snap, profile)
	if out.IsAccept() {
		t.Fatal("expected Reject (link not in snapshot), got Accept")
	}
	if out.Code() != LeafRejected {
		t.Fatalf("expected leaf_rejected, got %s", out.Code().Code())
	}
	if out.Detail() != "link_not_in_snapshot" {
		t.Fatalf("expected sub-code link_not_in_snapshot, got %q", out.Detail())
	}
}

// TestNetreach_ParityTheoryDecidesCustomRelation pins the custom Theory both ways: a
// same-parity pair HOLDS (accepted Builtin) and a mixed-parity pair FAILS through the
// host-extension band (builtin_failed) with netreach's sub-code. Proves a non-arche,
// non-is_root config-pinned relation is decidable through the §5 seam.
func TestNetreach_ParityTheoryDecidesCustomRelation(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot()
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	// 3 and 5 are both odd ⇒ Holds.
	holdsDeriv := NewDerivation([]Node{
		BuiltinNode{Conc: NewGroundLiteral(predSameParity, intVal(3), intVal(5))},
	}, 0)
	if out := Check[netSnapshot](prog, NewGroundLiteral(predSameParity, intVal(3), intVal(5)), holdsDeriv, snap, profile); !out.IsAccept() {
		t.Fatalf("same_parity(3,5): expected Accept, got %s", out)
	}

	// 2 and 3 differ in parity ⇒ Fails{same_parity_does_not_hold} via builtin_failed.
	failsDeriv := NewDerivation([]Node{
		BuiltinNode{Conc: NewGroundLiteral(predSameParity, intVal(2), intVal(3))},
	}, 0)
	out := Check[netSnapshot](prog, NewGroundLiteral(predSameParity, intVal(2), intVal(3)), failsDeriv, snap, profile)
	if out.IsAccept() {
		t.Fatal("same_parity(2,3): expected Reject, got Accept")
	}
	if out.Code() != BuiltinFailed {
		t.Fatalf("expected builtin_failed, got %s", out.Code().Code())
	}
	if out.Detail() != "same_parity_does_not_hold" {
		t.Fatalf("expected sub-code same_parity_does_not_hold, got %q", out.Detail())
	}
}

// TestNetreach_CustomRuleAdmissibilityGates exercises the §5a seam with a non-no-op
// binding: tagPolicy reads the opaque NodeMeta and rejects a Rule whose meta carries a
// disallowed tag, through the host-extension band (rule_inadmissible). It also confirms
// the no-op path: the same derivation with an allowed/absent tag is accepted. This is a
// metadata policy arche's projection-binding does not resemble.
func TestNetreach_CustomRuleAdmissibilityGates(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot([2]string{"a", "b"})

	mkDeriv := func(meta NodeMeta) Derivation {
		return NewDerivation([]Node{
			linkLeaf("a", "b"),
			reachBaseNode("a", "b", 0, meta),
		}, 1)
	}
	claim := NewGroundLiteral(predReachable, node("a"), node("b"))

	// (a) tagPolicy disallows "draft": a rule tagged "draft" is rule_inadmissible.
	strict := netreachProfile(newTagPolicy("draft"))
	out := Check[netSnapshot](prog, claim, mkDeriv(taggedMeta("draft")), snap, strict)
	if out.IsAccept() {
		t.Fatal("expected Reject (disallowed rule tag), got Accept")
	}
	if out.Code() != RuleInadmissible {
		t.Fatalf("expected rule_inadmissible, got %s", out.Code().Code())
	}
	if out.Detail() != "disallowed_rule_tag" {
		t.Fatalf("expected sub-code disallowed_rule_tag, got %q", out.Detail())
	}

	// (b) an allowed tag ("prod") and the untagged form both pass under the same policy.
	if out := Check[netSnapshot](prog, claim, mkDeriv(taggedMeta("prod")), snap, strict); !out.IsAccept() {
		t.Fatalf("allowed tag: expected Accept, got %s", out)
	}
	if out := Check[netSnapshot](prog, claim, mkDeriv(NoMeta()), snap, strict); !out.IsAccept() {
		t.Fatalf("untagged: expected Accept, got %s", out)
	}
}

// TestNetreach_StructuralBandStillFires confirms the FIRM structural band is consumer-
// agnostic: a netreach derivation with a broken instantiation (the rule's conclusion
// disagrees with the substituted clause head) is rejected with the SAME frozen structural
// code (instantiation_mismatch) the kernel emits for arche — the genericity boundary cuts
// the right way (structural codes are domain-independent; only the host-band codes are
// netreach's own).
func TestNetreach_StructuralBandStillFires(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot([2]string{"a", "b"})
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	// A base rule whose subst grounds the head to reachable(a, b) but whose stated
	// conclusion is reachable(a, c) — an instantiation mismatch.
	badRule := RuleNode{
		Conc:   NewGroundLiteral(predReachable, node("a"), node("c")),
		Clause: NewClauseId(clauseReachBase),
		Subst: Subst{
			NewVarId("X"): Atom([]byte("a")),
			NewVarId("Y"): Atom([]byte("b")),
		},
		Premises: PosPremises(0),
		Meta:     NoMeta(),
	}
	deriv := NewDerivation([]Node{linkLeaf("a", "b"), badRule}, 1)
	claim := NewGroundLiteral(predReachable, node("a"), node("c"))

	out := Check[netSnapshot](prog, claim, deriv, snap, profile)
	if out.IsAccept() {
		t.Fatal("expected Reject (instantiation mismatch), got Accept")
	}
	if out.Code() != InstantiationMismatch {
		t.Fatalf("expected instantiation_mismatch, got %s", out.Code().Code())
	}
	if !out.Code().IsStructural() {
		t.Fatal("instantiation_mismatch should be in the FIRM structural band")
	}
}

// TestNetreach_SealingRejectsLeafOnIntensionalPred proves §4.2 sealing holds for
// netreach's partition: a Leaf concluding `reachable` (an INTENSIONAL predicate — a
// clause head, not in the LeafVerifier's extensional set) is rejected sealed_violation.
// The extensional set is the consumer's data (here {link}); the sealing machinery is
// generic.
func TestNetreach_SealingRejectsLeafOnIntensionalPred(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot()
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	// A leaf trying to conclude reachable(a, b) directly — reachable is intensional.
	deriv := NewDerivation([]Node{
		LeafNode{Conc: NewGroundLiteral(predReachable, node("a"), node("b")), Evidence: NoEvidence()},
	}, 0)
	claim := NewGroundLiteral(predReachable, node("a"), node("b"))

	out := Check[netSnapshot](prog, claim, deriv, snap, profile)
	if out.IsAccept() {
		t.Fatal("expected Reject (sealed violation), got Accept")
	}
	if out.Code() != SealedViolation {
		t.Fatalf("expected sealed_violation, got %s", out.Code().Code())
	}
}

// TestNetreach_PartitionRejectsBuiltinOnUnownedPred proves §4.4 partition holds: a
// Builtin node whose predicate NO theory owns (here `reachable`, which is intensional)
// is rejected predicate_partition_violation. parityTheory owns only same_parity, so the
// partition is netreach's own and the core enforces it generically.
func TestNetreach_PartitionRejectsBuiltinOnUnownedPred(t *testing.T) {
	prog := netreachProgram()
	snap := newSnapshot()
	profile := netreachProfile(AlwaysAdmit[netSnapshot]{})

	deriv := NewDerivation([]Node{
		BuiltinNode{Conc: NewGroundLiteral(predReachable, node("a"), node("b"))},
	}, 0)
	claim := NewGroundLiteral(predReachable, node("a"), node("b"))

	out := Check[netSnapshot](prog, claim, deriv, snap, profile)
	if out.IsAccept() {
		t.Fatal("expected Reject (partition violation), got Accept")
	}
	if out.Code() != PredicatePartitionViolation {
		t.Fatalf("expected predicate_partition_violation, got %s", out.Code().Code())
	}
}

// TestNetreach_TheoryExposesIdentityViaOptionalSeam confirms the OPTIONAL Identified
// type-assertion seam (go has no default interface methods) resolves a non-arche
// component: parityTheory implements Identified, so a kernel-side resolution recovers its
// identity exactly as it would for arche's is_root. This pins that the optional-seam shape
// is bindable by a second consumer, not just arche.
func TestNetreach_TheoryExposesIdentityViaOptionalSeam(t *testing.T) {
	var component any = parityTheory{}
	id := UnidentifiedComponent()
	if c, ok := component.(Identified); ok {
		id = c.Identity()
	} else {
		t.Fatal("parityTheory should implement the optional Identified seam")
	}
	// parityTheory pins the canonical unidentified identity (no config to attest).
	if string(id.Id) != "unidentified" {
		t.Fatalf("Id = %q, want unidentified", id.Id)
	}
}
