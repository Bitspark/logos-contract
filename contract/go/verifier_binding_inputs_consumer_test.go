package contract_test

import (
	"bytes"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

func bindingIdentity(name, version string, config byte) contract.ComponentIdentity {
	return contract.NewComponentIdentity([]byte(name), []byte(version), [32]byte{config})
}

func TestComponentIdentityOwnsItsConstructorInputs(t *testing.T) {
	id, version := []byte("first"), []byte("1")
	reported := contract.NewComponentIdentity(id, version, [32]byte{1})
	copy(id, "other")
	copy(version, "2")
	if !reported.Equal(bindingIdentity("first", "1", 1)) {
		t.Fatal("constructor inputs rewrote the completed identity")
	}
}

// test-double: consumer(an independently implemented one-atom relation with its own identity report)
type bindingRelation struct{ report contract.ComponentIdentity }

func (*bindingRelation) Owns(pred contract.Symbol) bool {
	return pred == contract.SymbolFromString("is_allowed")
}
func (*bindingRelation) DecideGround(atom contract.GroundLiteral) completion.TheoryGround {
	if len(atom.Args) == 1 && core.Equal(atom.Args[0], core.NewAtom([]byte("a"))) {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("not_allowed")
}
func (r *bindingRelation) Identity() contract.ComponentIdentity { return r.report }

// test-double: consumer(a different zero-argument relation whose report callback changes earlier supplied storage)
type bindingReady struct{ first *bindingRelation }

func (*bindingReady) Owns(pred contract.Symbol) bool {
	return pred == contract.SymbolFromString("ready")
}
func (*bindingReady) DecideGround(atom contract.GroundLiteral) completion.TheoryGround {
	if len(atom.Args) == 0 {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("wrong_arity")
}
func (r *bindingReady) Identity() contract.ComponentIdentity {
	copy(r.first.report.Id, "other")
	copy(r.first.report.Version, "2")
	r.first.report.ConfigDigest = [32]byte{2}
	return bindingIdentity("second", "3", 3)
}

func TestCompoundCapturesEachCompletedMemberReport(t *testing.T) {
	first := &bindingRelation{report: bindingIdentity("first", "1", 1)}
	second := &bindingReady{first: first}
	compound := contract.NewCompoundTheory(first, second)
	want := contract.CompoundIdentityOf([]contract.ComponentIdentity{
		bindingIdentity("first", "1", 1), bindingIdentity("second", "3", 3),
	})
	if !compound.Identity().Equal(want) {
		t.Error("the second independent report rewrote the first contribution")
	}
	allowed := contract.NewGroundLiteral("is_allowed", core.NewAtom([]byte("a")))
	if contract.DecideGround(compound, allowed) != completion.TheoryGroundHolds() {
		t.Error("the first member's relation was not preserved")
	}
	refused := contract.NewGroundLiteral("is_allowed", core.NewAtom([]byte("b")))
	if contract.DecideGround(compound, refused) != completion.TheoryGroundFails("not_allowed") {
		t.Error("the first member's refusal was not preserved")
	}
	if contract.DecideGround(compound, contract.NewGroundLiteral("ready")) != completion.TheoryGroundHolds() {
		t.Error("the second member's independent relation was not preserved")
	}
	later := contract.CompoundIdentityOf([]contract.ComponentIdentity{
		bindingIdentity("other", "2", 2), bindingIdentity("second", "3", 3),
	})
	if !compound.Identity().Equal(later) {
		t.Error("a later operation did not observe the new member identity")
	}
}

// test-double: consumer(an empty extensional interpretation with a callback at declaration)
type bindingEmptyLeaves struct {
	during func()
	calls  int
}

func (l *bindingEmptyLeaves) Extensional() *contract.PredicateSet {
	l.calls++
	if l.during != nil {
		l.during()
	}
	return contract.NewPredicateSet()
}
func (*bindingEmptyLeaves) Verify(contract.GroundLiteral, contract.Evidence, struct{}) contract.LeafOutcome {
	return contract.LeafReject{Code: "no_attestation"}
}

type bindingContextFixture struct {
	program *contract.MapProgram
	profile *contract.CheckProfile[struct{}]
	leaves  *bindingEmptyLeaves
	context contract.CertContext
	proof   contract.Derivation
	claim   contract.GroundLiteral
}

func bindingContext() bindingContextFixture {
	a := core.NewAtom([]byte("a"))
	id := contract.NewClauseId("negative")
	absent := contract.NewGroundLiteral("sealed", a)
	claim := contract.NewGroundLiteral("derived", a)
	program := contract.NewMapProgram().With(id, contract.WithNeg(
		contract.NewGoal("derived", contract.Atom([]byte("a"))), nil,
		[]contract.Goal{contract.NewGoal("sealed", contract.Atom([]byte("a")))},
	))
	cx := contract.NewCertContext(contract.ProgramDigestOf(program), contract.Hash{1}, contract.Hash{2}, contract.Hash{3}).
		WithDecomposition(contract.Hash{4})
	witness := contract.Hash{4}
	cert := contract.ClosedModelCert{
		Scope:       contract.NewStratumPrefix(0, []contract.Symbol{absent.Pred}),
		ProgramHash: contract.ProgramDigestOf(contract.NewMapProgram()),
		ProfileHash: cx.ProfileHash, CtxHash: cx.CtxHash, TheoryConfigHash: cx.TheoryConfigHash,
		DecompositionWitness: &witness,
		Domains:              []contract.FiniteDomain{contract.NewFiniteDomain(contract.SymbolFromString("domain"), []core.Value{a})},
		Extensions:           []contract.RelationTable{contract.NewRelationTable(absent.Pred, 1, nil)},
		LimitsDecl:           contract.CertSizeDecl{CertFacts: 8, DomainValues: 8, SupportEdges: 8, RuleGroundings: 20, JoinSteps: 20, CertBytes: 4096},
	}
	proof := contract.NewDerivationWithClosedWorld([]contract.Node{
		contract.RuleNode{Conc: claim, Clause: id, Premises: []contract.Premise{contract.NegPremise{Atom: absent, Cert: contract.NewCertId(0)}}},
	}, 0, []contract.ClosedModelCert{cert})
	leaves := &bindingEmptyLeaves{}
	profile := &contract.CheckProfile[struct{}]{
		Theory: contract.NewCompoundTheory(), Leaves: leaves, Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
	}
	return bindingContextFixture{program: program, profile: profile, leaves: leaves, context: cx, proof: proof, claim: claim}
}

func TestCertificateContextOwnsItsOptionalWitnessBeforeCallbacks(t *testing.T) {
	routes := map[string]func(bindingContextFixture) contract.Outcome{
		"direct": func(f bindingContextFixture) contract.Outcome {
			return contract.CheckWithCertContext(f.program, f.claim, f.proof, struct{}{}, f.profile, f.context)
		},
		"whole_chain": func(f bindingContextFixture) contract.Outcome {
			return contract.CheckClosedModelChain(f.program, f.proof.ClosedWorld, struct{}{}, f.profile, f.context)
		},
		"memo": func(f bindingContextFixture) contract.Outcome {
			memo := contract.NewWorldMemo(f.program, f.profile, struct{}{}, f.context)
			return contract.CheckWithWorldMemo(memo, f.claim, f.proof)
		},
	}
	for name, run := range routes {
		t.Run(name+"/controls", func(t *testing.T) {
			f := bindingContext()
			if got := run(f); !got.IsAccept() {
				t.Fatalf("matching slice control: %s", got)
			}
			*f.context.DecompositionWitness = contract.Hash{99}
			if got := run(f); got.IsAccept() || got.Verdict.Code() != contract.CertContextMismatch {
				t.Fatalf("mismatched slice control: %s", got)
			}
		})
		t.Run(name+"/mismatch_remains_refused", func(t *testing.T) {
			f := bindingContext()
			*f.context.DecompositionWitness = contract.Hash{99}
			f.leaves.during = func() { *f.context.DecompositionWitness = contract.Hash{4} }
			got := run(f)
			if f.leaves.calls == 0 || got.IsAccept() || got.Verdict.Code() != contract.CertContextMismatch {
				t.Fatalf("witness changed during declaration: %s (%d calls)", got, f.leaves.calls)
			}
		})
		t.Run(name+"/matching_remains_accepted", func(t *testing.T) {
			f := bindingContext()
			f.leaves.during = func() { *f.context.DecompositionWitness = contract.Hash{99} }
			got := run(f)
			if f.leaves.calls == 0 || !got.IsAccept() {
				t.Fatalf("matching witness changed during declaration: %s (%d calls)", got, f.leaves.calls)
			}
		})
	}
}

func TestReturnedIdentityFieldsRemainCallerOwned(t *testing.T) {
	// Inspection of the Go data contract is ordinary caller-owned byte storage.
	report := bindingIdentity("first", "1", 1)
	copy(report.Id, "other")
	if !bytes.Equal(report.Id, []byte("other")) {
		t.Fatal("caller could not update its own explicit identity value")
	}
}
