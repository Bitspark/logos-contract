package contract

// #3074, seat:caa's grade: the Check-level plants in closed_vocabulary_refusals_3074_test.go cannot
// go red on the untrusted sites' default arms, because check's boundary pass (#3088) refuses an
// unknown premise or support ref before any of those sites runs. These tests call each untrusted site
// directly, past the boundary, so a site that loses its default arm fails here. Each site also gets a
// known-kind control that must NOT read unknown_node_kind: a site refusing everything fails too.

import "testing"

// directOutcome3074 runs one site, turning a panic into a failure: an untrusted value must never
// panic, at the boundary or behind it.
func directOutcome3074[T any](t *testing.T, name string, run func() T) T {
	t.Helper()
	var out T
	func() {
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("%s: the site panicked on an untrusted value: %v", name, r)
			}
		}()
		out = run()
	}()
	return out
}

// direct3074 is p(a) :- q(a), with q extensional: node 0 is the leaf q(a), node 1 the rule node
// whose one premise is the one under test.
func direct3074(premise Premise) (Program, GroundLiteral, Derivation, *CheckProfile[unitCtx]) {
	a := atom3074("a")
	program := NewMapProgram()
	program.Insert(NewClauseId("r"), NewClauseLits(NewGoal("p", Var("X")), PosLit(NewGoal("q", Var("X")))))
	ext := NewPredicateSet()
	ext.Insert(SymbolFromString("q"))
	profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: ext},
		Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
	claim := NewGroundLiteral("p", a)
	deriv := NewDerivation([]Node{
		LeafNode{Conc: NewGroundLiteral("q", a), Evidence: NoEvidence()},
		RuleNode{Conc: claim, Clause: NewClauseId("r"), Subst: Subst{NewVarId("X"): Atom([]byte("a"))},
			Premises: []Premise{premise}, Meta: NoMeta()},
	}, 1)
	return program, claim, deriv, profile
}

var unknownPremises3074 = []struct {
	name    string
	premise Premise
}{
	{"nil", nil},
	{"a foreign type embedding a real premise", foreignPremise3074{PosNode(0)}},
	{"a foreign type embedding nil", foreignPremise3074{}},
}

func TestCheckTermDepthsRefusesAnUnknownPremiseKindByName3074(t *testing.T) {
	program, claim, deriv, _ := direct3074(PosNode(0))
	if got := directOutcome3074(t, "control", func() Verdict {
		var tally checkTally
		return checkTermDepths(program, claim, deriv, DefaultLimits(), &tally)
	}); !got.IsAccept() {
		t.Fatalf("control: a positive premise within the limits is accepted, got %s", got)
	}
	for _, c := range unknownPremises3074 {
		program, claim, deriv, _ := direct3074(c.premise)
		got := directOutcome3074(t, c.name, func() Verdict {
			var tally checkTally
			return checkTermDepths(program, claim, deriv, DefaultLimits(), &tally)
		})
		if got.IsAccept() || got.Code() != UnknownNodeKind {
			t.Errorf("%s: want unknown_node_kind, got %s", c.name, got)
		}
	}
}

func TestCheckNodeRefusesAnUnknownPremiseKindByName3074(t *testing.T) {
	run := func(premise Premise) Verdict {
		program, _, deriv, profile := direct3074(premise)
		node := deriv.Nodes[1]
		var tally checkTally
		return checkNode[unitCtx](1, node, program, deriv, unitCtx{}, profile, nil, make([]int, len(deriv.Nodes)), &tally)
	}
	if got := directOutcome3074(t, "control", func() Verdict { return run(PosNode(0)) }); !got.IsAccept() {
		t.Fatalf("control: the positive premise is accepted, got %s", got)
	}
	// A KNOWN kind in the wrong place keeps its own code: the default arm is not a catch-all refusal.
	// Its arm reads no field, so the zero value is enough.
	count := CountPremise{}
	if got := directOutcome3074(t, "count premise", func() Verdict { return run(count) }); got.Code() != InstantiationMismatch {
		t.Fatalf("control: a count premise at a positive literal is instantiation_mismatch, got %s", got)
	}
	for _, c := range unknownPremises3074 {
		got := directOutcome3074(t, c.name, func() Verdict { return run(c.premise) })
		if got.IsAccept() || got.Code() != UnknownNodeKind {
			t.Errorf("%s: want unknown_node_kind, got %s", c.name, got)
		}
	}
}

func TestResolveSupportRefRefusesAnUnknownRefKindByName3074(t *testing.T) {
	bodyLit := PosLit(NewGoal("q", Var("X")))
	grounded := NewGroundLiteral("q", atom3074("a"))
	run := func(ref SupportRef) *certErr {
		return resolveSupportRef(0, bodyLit, ref, grounded, 1, certView{}, certPlace{}, ltTheory{}, nil, nil)
	}
	// A KNOWN kind keeps its own verdict: a count's ref cited for a positive literal is cert_unsupported.
	if got := directOutcome3074(t, "count lower ref", func() *certErr { return run(CountLowerRef{}) }); got == nil || got.code != CertUnsupported {
		t.Fatalf("control: a count lower ref at a positive literal is cert_unsupported, got %+v", got)
	}
	for _, c := range []struct {
		name string
		ref  SupportRef
	}{
		{"nil", nil},
		{"a foreign type embedding a real ref", foreignSupportRef3074{CountLowerRef{}}},
		{"a foreign type embedding nil", foreignSupportRef3074{}},
	} {
		got := directOutcome3074(t, c.name, func() *certErr { return run(c.ref) })
		if got == nil || got.code != UnknownNodeKind {
			t.Errorf("%s: want unknown_node_kind, got %+v", c.name, got)
		}
	}
}
