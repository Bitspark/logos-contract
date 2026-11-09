package contract_test

import (
	"bytes"
	"errors"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

// test-double: consumer(the rule-fact proof needs no extensional evidence)
type clauseIDLeaves struct{}

func (clauseIDLeaves) Extensional() *contract.PredicateSet { return contract.NewPredicateSet() }
func (clauseIDLeaves) Verify(contract.GroundLiteral, contract.Evidence, struct{}) contract.LeafOutcome {
	return contract.LeafReject{Code: "no_facts"}
}

func TestProgramEncodingPreservesPortableClauseIDs(t *testing.T) {
	p := contract.NewGoal("p")
	for _, handle := range []string{"", "A\uFFFD", "A\U0001F600B", "\uFEFFid"} {
		id := contract.NewClauseId(handle)
		program := contract.NewMapProgram().With(id, contract.Fact(p))
		value, err := contract.ProgramToValue(program)
		if err != nil {
			t.Fatal(err)
		}
		restored, err := contract.ProgramFromValue(value)
		if err != nil {
			t.Fatal(err)
		}
		if _, ok := restored.Clause(id); !ok {
			t.Fatalf("round trip lost %q", handle)
		}
		first, err := contract.ProgramBytes(program)
		if err != nil {
			t.Fatal(err)
		}
		again, err := contract.ProgramBytes(restored)
		if err != nil || !bytes.Equal(first, again) {
			t.Fatalf("%q: bytes changed, err=%v", handle, err)
		}
	}
}

func TestOpaqueNativeClauseIDsRefusePortableEncoding(t *testing.T) {
	p := contract.NewGoal("p")
	claim, _ := p.AsGround()
	profile := &contract.CheckProfile[struct{}]{
		Theory: contract.NewStandardTheory(), Leaves: clauseIDLeaves{},
		Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
	}
	for _, handle := range []string{"A\xff", "A\xed\xa0\x80"} {
		id := contract.NewClauseId(handle)
		program := contract.NewMapProgram().With(id, contract.Fact(p)).
			With(contract.NewClauseId("A\uFFFD"), contract.Fact(contract.NewGoal("other")))
		proof := contract.NewDerivation([]contract.Node{contract.RuleNode{Conc: claim, Clause: id}}, 0)
		if !contract.Check(program, claim, proof, struct{}{}, profile).IsAccept() {
			t.Fatalf("native lookup of %q changed", handle)
		}
		var encodingError *contract.ClauseIdEncodingError
		if value, err := contract.ProgramToValue(program); !errors.As(err, &encodingError) || encodingError.ClauseID != id || value != nil {
			t.Errorf("encoded nonportable handle %q as a program value", handle)
		}
		if data, err := contract.ProgramBytes(program); !errors.As(err, &encodingError) || encodingError.ClauseID != id || data != nil {
			t.Errorf("encoded nonportable handle %q as bytes", handle)
		}
	}
}
