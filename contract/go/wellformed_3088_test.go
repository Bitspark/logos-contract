package contract

// #3088 (seat:caa's ruling): an untrusted derivation's nil or foreign interface value is refused by
// name at the boundary, never a panic and never an accept. Every shape measured on the issue and in
// seat:cca's census on #3094 is planted here through Check, against an accepting control. Before the
// boundary pass some panicked (the depth pass, supportRefAtom, the byte measurement's
// writeSupportRef), some were refused under another code, and some were ACCEPTED: a foreign value
// judged through Go method promotion, a nil term in an unread Subst entry, nil or foreign parts of an
// uncited certificate.
//
// Why refusing the accepted ones is not a narrowing under ADR 0035 D1, and needs no CHECKER_VERSION
// bump (seat:caa's ruling on #3088): D1's narrowing concerns check's domain, the account, whose
// grammar D2 fixes. A nil or foreign component is outside that grammar: no decoder produces one, and
// the encoder refuses every one, so it has no digest and no stored verdict can refer to it. That is a
// claim this file CHECKS: every refused shape must fail to encode. A change that gave one of them an
// encoding reds it, and D1's gate, bump included, would then apply.

import (
	"strings"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// test-double: adversarial(a producer's own Node type; embedding satisfies the sealed interface)
type foreignNode3088 struct{ Node }

// test-double: adversarial(a producer's own Term type)
type foreignTerm3088 struct{ Term }

// test-double: adversarial(a producer's own Premise type)
type foreignPremise3088 struct{ Premise }

// test-double: adversarial(a producer's own ontos Value type)
type foreignValue3088 struct{ core.Value }

// test-double: adversarial(a producer's own SupportRef type)
type foreignSupportRef3088 struct{ SupportRef }

func atom3088(s string) core.Value {
	v, ok := Atom([]byte(s)).EraseGround()
	if !ok {
		panic("an atom is ground")
	}
	return v
}

type shape3088 struct {
	name  string
	deriv Derivation
	// detail is the component the refusal must name. "" marks an accepting row: a control, or
	// opaque (a payload the core does not read, accepted and not claimed to encode).
	detail string
	opaque bool
}

// encodes3088 reports whether d has a wire encoding, i.e. is an account with a digest.
func encodes3088(d Derivation) (ok bool) {
	defer func() {
		if recover() != nil {
			ok = false
		}
	}()
	EncodeDerivationWireV1(d)
	return true
}

// runShapes3088 checks each shape: the control accepts and encodes; every other shape is refused
// unknown_node_kind with the component named and does NOT encode; nothing panics.
func runShapes3088(t *testing.T, shapes []shape3088, check func(Derivation) Outcome) {
	t.Helper()
	for _, s := range shapes {
		var got Outcome
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Fatalf("%s: Check panicked on untrusted input: %v", s.name, r)
				}
			}()
			got = check(s.deriv)
		}()
		switch {
		case s.detail == "":
			if !got.IsAccept() {
				t.Errorf("%s: an accepting row must accept, got %s: %s", s.name, negOutcomeString(got), got.Detail())
			}
			if !s.opaque && !encodes3088(s.deriv) {
				t.Errorf("%s: the control must encode, or the encodability check below proves nothing", s.name)
			}
		case got.IsAccept() || got.Code() != UnknownNodeKind:
			t.Errorf("%s: want reject:unknown_node_kind, got %s: %s", s.name, negOutcomeString(got), got.Detail())
		case !strings.Contains(got.Detail(), s.detail):
			t.Errorf("%s: the detail %q does not name the component %q", s.name, got.Detail(), s.detail)
		}
		if s.detail != "" && encodes3088(s.deriv) {
			t.Errorf("%s: a refused shape ENCODES, so it is an account and its refusal is a narrowing under ADR 0035 D1 (a CHECKER_VERSION bump and D1's gate; seat:caa's ruling on #3088)", s.name)
		}
	}
}

func TestAnUntrustedNodeTermPremiseOrValueOfUnknownKindIsRefusedByName3088(t *testing.T) {
	a := atom3088("a")
	program := NewMapProgram()
	program.Insert(NewClauseId("r"), NewClauseLits(NewGoal("p", Var("X")), PosLit(NewGoal("q", Var("X")))))
	ext := NewPredicateSet()
	ext.Insert(SymbolFromString("q"))
	profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: ext},
		Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
	claim := NewGroundLiteral("p", a)
	leaf := LeafNode{Conc: NewGroundLiteral("q", a), Evidence: NoEvidence()}
	subst := Subst{NewVarId("X"): Atom([]byte("a"))}
	rule := func(subst Subst, premises ...Premise) RuleNode {
		return RuleNode{Conc: claim, Clause: NewClauseId("r"), Subst: subst, Premises: premises, Meta: NoMeta()}
	}
	leafWith := func(v core.Value) LeafNode {
		return LeafNode{Conc: GroundLiteral{Pred: SymbolFromString("q"), Args: []core.Value{v}}, Evidence: NoEvidence()}
	}
	tuple := core.NewTuple(atom3088("f"), a)
	runShapes3088(t, []shape3088{
		{"control", NewDerivation([]Node{leaf, rule(subst, PosNode(0))}, 1), "", false},
		{"a nil node", NewDerivation([]Node{leaf, nil}, 1), "node 1: the node is absent (nil)", false},
		{"a foreign node embedding nil", NewDerivation([]Node{leaf, foreignNode3088{}}, 1), "node 1: the node is of unknown kind", false},
		{"a foreign node embedding a rule", NewDerivation([]Node{leaf, foreignNode3088{rule(subst, PosNode(0))}}, 1), "node 1: the node is of unknown kind", false},
		{"a nil subst term", NewDerivation([]Node{leaf, rule(Subst{NewVarId("X"): nil}, PosNode(0))}, 1), "subst image of X (a term) is absent (nil)", false},
		{"a foreign subst term embedding nil", NewDerivation([]Node{leaf, rule(Subst{NewVarId("X"): foreignTerm3088{}}, PosNode(0))}, 1), "subst image of X (a term) is of unknown kind", false},
		{"a foreign term nested in a tuple", NewDerivation([]Node{leaf, rule(Subst{NewVarId("X"): Tuple(Atom([]byte("f")), foreignTerm3088{Atom([]byte("a"))})}, PosNode(0))}, 1), "subst image of X (a term) is of unknown kind", false},
		// Accepted on main through Go method promotion (seat:cca's census on #3094): the wrapper answers
		// Equal and EraseGround as the atom it embeds. Not an account: the encoder refuses it.
		{"a foreign value wrapping a real atom, judged by promotion", NewDerivation([]Node{leafWith(foreignValue3088{a}), rule(subst, PosNode(0))}, 1), "node 0: conclusion argument 0 (a value) is of unknown kind", false},
		{"a foreign term wrapping a real atom, judged by promotion", NewDerivation([]Node{leaf, rule(Subst{NewVarId("X"): foreignTerm3088{Atom([]byte("a"))}}, PosNode(0))}, 1), "subst image of X (a term) is of unknown kind", false},
		// Accepted on main because no clause variable reads it.
		{"a nil term in an unread subst entry", NewDerivation([]Node{leaf, rule(Subst{NewVarId("X"): Atom([]byte("a")), NewVarId("Unread"): nil}, PosNode(0))}, 1), "subst image of Unread (a term) is absent (nil)", false},
		// Accepted on main because no premise cites the certificate, so nothing verified it.
		{"an uncited certificate with a nil support ref", NewDerivationWithClosedWorld([]Node{leaf, rule(subst, PosNode(0))}, 1, []ClosedModelCert{{Supports: SupportWitness{Edges: []SupportEdge{{BodyRefs: []SupportRef{nil}}}}}}), "certificate 0: support edge 0 ref 0 is absent (nil)", false},
		{"an uncited certificate with a foreign domain value", NewDerivationWithClosedWorld([]Node{leaf, rule(subst, PosNode(0))}, 1, []ClosedModelCert{{Domains: []FiniteDomain{{TypeTag: SymbolFromString("d"), Values: []core.Value{foreignValue3088{a}}}}}}), "certificate 0: domain 0 value 0 (a value) is of unknown kind", false},
		{"a nil premise", NewDerivation([]Node{leaf, rule(subst, nil)}, 1), "premise 0 is absent (nil)", false},
		{"a foreign premise", NewDerivation([]Node{leaf, rule(subst, foreignPremise3088{PosNode(0)})}, 1), "premise 0 is of unknown kind", false},
		{"a count premise with no k", NewDerivation([]Node{leaf, rule(subst, CountPremise{Pred: NewPredicateRef(SymbolFromString("q"), 1), Cert: NewCertId(0)})}, 1), "premise 0 k (a value) is absent (nil)", false},
		{"a foreign value in a conclusion", NewDerivation([]Node{leafWith(foreignValue3088{}), rule(subst, PosNode(0))}, 1), "node 0: conclusion argument 0 (a value) is of unknown kind", false},
		{"a nil value in a conclusion", NewDerivation([]Node{leafWith(nil), rule(subst, PosNode(0))}, 1), "node 0: conclusion argument 0 (a value) is absent (nil)", false},
		{"a pointer to a tuple in a conclusion", NewDerivation([]Node{leafWith(&tuple), rule(subst, PosNode(0))}, 1), "node 0: conclusion argument 0 (a value) is of unknown kind *core.Tuple", false},
		{"a foreign value nested in a tuple", NewDerivation([]Node{leafWith(core.NewTuple(atom3088("f"), foreignValue3088{a})), rule(subst, PosNode(0))}, 1), "node 0: conclusion argument 0 (a value) is of unknown kind", false},
		// Metadata is opaque to the core: only a consumer's RuleAdmissibility reads it, so a foreign value
		// there is not the checker's to refuse. Accepted, as before #3088 (no narrowing).
		{"foreign metadata, opaque to the core", NewDerivation([]Node{leaf, RuleNode{Conc: claim, Clause: NewClauseId("r"), Subst: subst, Premises: []Premise{PosNode(0)}, Meta: NewNodeMeta(foreignValue3088{})}}, 1), "", true},
	}, func(d Derivation) Outcome { return Check[unitCtx](program, claim, d, unitCtx{}, profile) })
}

func TestAnUntrustedCertificateComponentOfUnknownKindIsRefusedByName3088(t *testing.T) {
	x, z := atom3088("x"), atom3088("z")
	program := NewMapProgram()
	program.Insert(NewClauseId("d_rule"), NewClauseLits(NewGoal("d", Var("X")), PosLit(NewGoal("base", Var("X")))))
	program.Insert(NewClauseId("q_rule"), NewClauseLits(NewGoal("q"), NegLit(NewGoal("d", Atom([]byte("z"))))))
	ext := NewPredicateSet()
	ext.Insert(SymbolFromString("base"))
	edb := map[string][]GroundLiteral{"base": {NewGroundLiteral("base", x)}}
	profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: ext, edb: edb},
		Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))
	claim := NewGroundLiteral("q")
	lower := LowerStratumRef{Cert: NewCertId(0), Atom: NewGroundLiteral("base", x)}
	derivation := func(ref SupportRef, domain []core.Value) Derivation {
		cert := ClosedModelCert{
			Scope:       NewStratumPrefix(1, []Symbol{SymbolFromString("base"), SymbolFromString("d")}),
			ProgramHash: derived.ProgramHash, ProfileHash: derived.ProfileHash, CtxHash: derived.CtxHash,
			TheoryConfigHash: derived.TheoryConfigHash,
			Domains:          []FiniteDomain{{TypeTag: SymbolFromString("d"), Values: domain}},
			Extensions: []RelationTable{
				NewRelationTable(SymbolFromString("base"), 1, []GroundLiteral{NewGroundLiteral("base", x)}),
				NewRelationTable(SymbolFromString("d"), 1, []GroundLiteral{NewGroundLiteral("d", x)}),
			},
			Supports: SupportWitness{Edges: []SupportEdge{{Fact: NewGroundLiteral("d", x), Clause: NewClauseId("d_rule"),
				Subst: Subst{NewVarId("X"): Atom([]byte("x"))}, BodyRefs: []SupportRef{ref}, Rank: 1}}},
			LimitsDecl: CertSizeDecl{CertFacts: 2, DomainValues: uint64(len(domain)), SupportEdges: 1, RuleGroundings: 1000, JoinSteps: 10000, CertBytes: 4096},
		}
		node := RuleNode{Conc: claim, Clause: NewClauseId("q_rule"), Subst: Subst{},
			Premises: []Premise{NegPremise{Atom: NewGroundLiteral("d", z), Cert: NewCertId(0), Nonmember: DirectLookup}}, Meta: NoMeta()}
		return NewDerivationWithClosedWorld([]Node{node}, 0, []ClosedModelCert{cert})
	}
	domain := []core.Value{x, z}
	shapes := []shape3088{
		{"control", derivation(lower, domain), "", false},
		{"a nil support ref", derivation(nil, domain), "certificate 0: support edge 0 ref 0 is absent (nil)", false},
		{"a foreign support ref embedding a real one", derivation(foreignSupportRef3088{lower}, domain), "certificate 0: support edge 0 ref 0 is of unknown kind", false},
		{"a foreign support ref embedding nil", derivation(foreignSupportRef3088{}, domain), "certificate 0: support edge 0 ref 0 is of unknown kind", false},
		{"a foreign value in a domain", derivation(lower, []core.Value{x, foreignValue3088{z}}), "certificate 0: domain 0 value 1 (a value) is of unknown kind", false},
	}
	runShapes3088(t, shapes, func(d Derivation) Outcome {
		return CheckWithCertContext[unitCtx](program, claim, d, unitCtx{}, profile, derived)
	})
	// The memoized entry reads the same boundary.
	runShapes3088(t, shapes, func(d Derivation) Outcome {
		return CheckWithWorldMemo(NewWorldMemo[unitCtx](program, profile, unitCtx{}, derived), claim, d)
	})
}

// The encoder once lifted a nil value to the empty tuple (FromValue's nil sentinel collided with a nil
// input), so a derivation holding nil and one holding () shared one encoding and one digest. A nil
// value now has no encoding; () keeps its own.
func TestANilValueIsNotEncodedAsTheEmptyTuple3088(t *testing.T) {
	leaf := func(v core.Value) Derivation {
		return NewDerivation([]Node{LeafNode{Conc: GroundLiteral{Pred: SymbolFromString("q"), Args: []core.Value{v}}, Evidence: NoEvidence()}}, 0)
	}
	if !encodes3088(leaf(core.NewTuple())) {
		t.Fatal("the empty tuple must encode")
	}
	if encodes3088(leaf(nil)) {
		t.Fatal("a nil value encodes: it aliases the empty tuple's encoding and digest")
	}
}

// CheckClosedModelChain reads certificates without derivationPrechecks, so it runs the same walk.
func TestTheCertificateChainEntryRefusesAnUnknownComponentByName3088(t *testing.T) {
	x := atom3088("x")
	program := NewMapProgram()
	program.Insert(NewClauseId("d_rule"), NewClauseLits(NewGoal("d", Var("X")), PosLit(NewGoal("base", Var("X")))))
	ext := NewPredicateSet()
	ext.Insert(SymbolFromString("base"))
	profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: ext, edb: map[string][]GroundLiteral{"base": {NewGroundLiteral("base", x)}}},
		Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))
	cert := func(ref SupportRef) ClosedModelCert {
		return ClosedModelCert{
			Scope:       NewStratumPrefix(1, []Symbol{SymbolFromString("base"), SymbolFromString("d")}),
			ProgramHash: derived.ProgramHash, ProfileHash: derived.ProfileHash, CtxHash: derived.CtxHash,
			TheoryConfigHash: derived.TheoryConfigHash,
			Domains:          []FiniteDomain{NewFiniteDomain(SymbolFromString("d"), []core.Value{x})},
			Extensions: []RelationTable{
				NewRelationTable(SymbolFromString("base"), 1, []GroundLiteral{NewGroundLiteral("base", x)}),
				NewRelationTable(SymbolFromString("d"), 1, []GroundLiteral{NewGroundLiteral("d", x)}),
			},
			Supports: SupportWitness{Edges: []SupportEdge{{Fact: NewGroundLiteral("d", x), Clause: NewClauseId("d_rule"),
				Subst: Subst{NewVarId("X"): Atom([]byte("x"))}, BodyRefs: []SupportRef{ref}, Rank: 1}}},
			LimitsDecl: CertSizeDecl{CertFacts: 2, DomainValues: 1, SupportEdges: 1, RuleGroundings: 1000, JoinSteps: 10000, CertBytes: 4096},
		}
	}
	chain := func(ref SupportRef) (out Outcome) {
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("CheckClosedModelChain panicked on untrusted input: %v", r)
			}
		}()
		return CheckClosedModelChain[unitCtx](program, []ClosedModelCert{cert(ref)}, unitCtx{}, profile, derived)
	}
	if got := chain(LowerStratumRef{Cert: NewCertId(0), Atom: NewGroundLiteral("base", x)}); !got.IsAccept() {
		t.Fatalf("control: want accept, got %s: %s", negOutcomeString(got), got.Detail())
	}
	for _, c := range []struct {
		name string
		ref  SupportRef
	}{{"nil", nil}, {"a foreign ref embedding nil", foreignSupportRef3088{}}} {
		got := chain(c.ref)
		if got.IsAccept() || got.Code() != UnknownNodeKind || !strings.Contains(got.Detail(), "chain cert 0: support edge 0 ref 0") {
			t.Errorf("%s: want reject:unknown_node_kind naming chain cert 0's ref, got %s: %s", c.name, negOutcomeString(got), got.Detail())
		}
	}
}
