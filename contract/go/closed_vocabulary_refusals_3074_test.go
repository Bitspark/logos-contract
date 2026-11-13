package contract

// #3074 (research 0025 rows A3 and A24, seat:caa's ruling): the source of a closed-vocabulary value
// decides what an unknown one gets. A value from the untrusted derivation or certificate is refused
// by name, unknown_node_kind, never a panic and never an accept: planted here as nil and as a foreign
// type embedding the interface, each against an accepting control. A value only the program or the
// checker's own constants can produce panics by name, fail-closed (no recover() in the verifier).

import (
	"strings"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// test-double: adversarial(a producer's own Premise type; embedding satisfies the sealed interface)
type foreignPremise3074 struct{ Premise }

// test-double: adversarial(a producer's own SupportRef type)
type foreignSupportRef3074 struct{ SupportRef }

// test-double: adversarial(a Term kind the checker does not know)
type foreignTerm3074 struct{ Term }

func atom3074(s string) core.Value {
	v, ok := Atom([]byte(s)).EraseGround()
	if !ok {
		panic("an atom is ground")
	}
	return v
}

// checkOutcome3074 runs check, turning a panic into a failure: an untrusted value must never panic.
func checkOutcome3074(t *testing.T, name string, run func() Outcome) Outcome {
	t.Helper()
	var out Outcome
	func() {
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("%s: Check panicked on untrusted input: %v", name, r)
			}
		}()
		out = run()
	}()
	return out
}

func TestAnUntrustedPremiseOfUnknownKindIsRefusedByName3074(t *testing.T) {
	a := atom3074("a")
	program := NewMapProgram()
	program.Insert(NewClauseId("r"), NewClauseLits(NewGoal("p", Var("X")), PosLit(NewGoal("q", Var("X")))))
	ext := NewPredicateSet()
	ext.Insert(SymbolFromString("q"))
	profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: ext},
		Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
	claim := NewGroundLiteral("p", a)
	derivation := func(premise Premise) Derivation {
		return NewDerivation([]Node{
			LeafNode{Conc: NewGroundLiteral("q", a), Evidence: NoEvidence()},
			RuleNode{Conc: claim, Clause: NewClauseId("r"), Subst: Subst{NewVarId("X"): Atom([]byte("a"))},
				Premises: []Premise{premise}, Meta: NoMeta()},
		}, 1)
	}
	for _, c := range []struct {
		name    string
		premise Premise
		accept  bool
	}{
		{"control: the positive premise", PosNode(0), true},
		{"nil", nil, false},
		{"a foreign type embedding a real premise", foreignPremise3074{PosNode(0)}, false},
		{"a foreign type embedding nil", foreignPremise3074{}, false},
	} {
		got := checkOutcome3074(t, c.name, func() Outcome {
			return Check[unitCtx](program, claim, derivation(c.premise), unitCtx{}, profile)
		})
		switch {
		case c.accept && !got.IsAccept():
			t.Errorf("%s: want accept, got %s: %s", c.name, negOutcomeString(got), got.Verdict.Detail())
		case !c.accept && (got.IsAccept() || got.Verdict.Code() != UnknownNodeKind):
			t.Errorf("%s: want reject:unknown_node_kind, got %s", c.name, negOutcomeString(got))
		}
	}
}

func TestAnUntrustedSupportRefOfUnknownKindIsRefusedByName3074(t *testing.T) {
	x, z := atom3074("x"), atom3074("z")
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
	derivation := func(ref SupportRef) Derivation {
		cert := ClosedModelCert{
			Scope:       NewStratumPrefix(1, []Symbol{SymbolFromString("base"), SymbolFromString("d")}),
			ProgramHash: derived.ProgramHash, ProfileHash: derived.ProfileHash, CtxHash: derived.CtxHash,
			TheoryConfigHash: derived.TheoryConfigHash,
			Domains:          []FiniteDomain{NewFiniteDomain(SymbolFromString("d"), []core.Value{x, z})},
			Extensions: []RelationTable{
				NewRelationTable(SymbolFromString("base"), 1, []GroundLiteral{NewGroundLiteral("base", x)}),
				NewRelationTable(SymbolFromString("d"), 1, []GroundLiteral{NewGroundLiteral("d", x)}),
			},
			Supports: SupportWitness{Edges: []SupportEdge{{Fact: NewGroundLiteral("d", x), Clause: NewClauseId("d_rule"),
				Subst: Subst{NewVarId("X"): Atom([]byte("x"))}, BodyRefs: []SupportRef{ref}, Rank: 1}}},
			LimitsDecl: CertSizeDecl{CertFacts: 2, DomainValues: 2, SupportEdges: 1, RuleGroundings: 1000, JoinSteps: 10000, CertBytes: 4096},
		}
		node := RuleNode{Conc: claim, Clause: NewClauseId("q_rule"), Subst: Subst{},
			Premises: []Premise{NegPremise{Atom: NewGroundLiteral("d", z), Cert: NewCertId(0), Nonmember: DirectLookup}}, Meta: NoMeta()}
		return NewDerivationWithClosedWorld([]Node{node}, 0, []ClosedModelCert{cert})
	}
	lower := LowerStratumRef{Cert: NewCertId(0), Atom: NewGroundLiteral("base", x)}
	for _, c := range []struct {
		name   string
		ref    SupportRef
		accept bool
	}{
		{"control: the lower-stratum ref", lower, true},
		{"nil", nil, false},
		{"a foreign type embedding a real ref", foreignSupportRef3074{lower}, false},
		{"a foreign type embedding nil", foreignSupportRef3074{}, false},
	} {
		got := checkOutcome3074(t, c.name, func() Outcome {
			return CheckWithCertContext[unitCtx](program, claim, derivation(c.ref), unitCtx{}, profile, derived)
		})
		switch {
		case c.accept && !got.IsAccept():
			t.Errorf("%s: want accept, got %s: %s", c.name, negOutcomeString(got), got.Verdict.Detail())
		case !c.accept && (got.IsAccept() || got.Verdict.Code() != UnknownNodeKind):
			t.Errorf("%s: want reject:unknown_node_kind, got %s: %s", c.name, negOutcomeString(got), got.Verdict.Detail())
		}
	}
}

// panicsNaming3074 reports whether f panics with a message containing want.
func panicsNaming3074(f func(), want string) (msg string, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			msg, _ = r.(string)
			ok = strings.Contains(msg, want)
		}
	}()
	f()
	return "", false
}

func TestAnInternalValueOfUnknownKindPanicsByName3074(t *testing.T) {
	for _, c := range []struct {
		name, want string
		f          func()
	}{
		{"IsStructural", "IsStructural: unknown RejectionCode 250", func() { RejectionCode(250).IsStructural() }},
		{"projectAsTerm", "projectAsTerm: unknown ProjectKind 99", func() { projectAsTerm(ProjectSpec{Kind: ProjectKind(99)}) }},
		{"evaluateAggregate", "evaluateAggregate: unknown ProjectKind 99", func() { _, _ = evaluateAggregate(nil, nil, ProjectSpec{Kind: ProjectKind(99)}) }},
		{"collectVarsTerm, nil", "collectVarsTerm: unknown Term", func() { collectVarsTerm(nil, map[VarId]struct{}{}) }},
		{"collectVarsTerm, foreign", "collectVarsTerm: unknown Term", func() { collectVarsTerm(foreignTerm3074{Var("X")}, map[VarId]struct{}{}) }},
	} {
		if msg, ok := panicsNaming3074(c.f, c.want); !ok {
			t.Errorf("%s: want a panic naming %q, got %q", c.name, c.want, msg)
		}
	}
	// Every known code is placed in a band: the switch names each one, so none panics.
	for c := EmptyDerivation; c <= InvalidCheckLimits; c++ {
		if msg, panicked := panicsNaming3074(func() { c.IsStructural() }, ""); panicked {
			t.Errorf("IsStructural panicked on the known code %s: %s", c.Code(), msg)
		}
	}
}
