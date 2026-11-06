package contract

import (
	"fmt"

	core "github.com/bitspark/ontos/core/go"
)

// exampleLeaves is the ONE seam a check-only consumer must implement: which
// predicates are leaves (extensional), and whether a given leaf's evidence is
// acceptable.
// test-double: consumer(a trusted EDB admitting every leaf)
type exampleLeaves struct{ extensional *PredicateSet }

func (e exampleLeaves) Extensional() *PredicateSet { return e.extensional }

func (exampleLeaves) Verify(GroundLiteral, Evidence, struct{}) LeafOutcome {
	// This fixture's EDB is trusted, so every leaf is admitted. A consumer that
	// must VERIFY evidence decides here — that decision is the entire purpose of
	// the seam, which is why the example does not hide it behind a helper.
	return LeafAdmit{}
}

// ExampleCheck is the whole check-side API in one call (issue #1027).
//
// Every CheckProfile slot binds a shipped value except Leaves, so this is the
// shortest CORRECT consumer rather than a sketch. Note what Check does not do:
// it SEARCHES FOR NOTHING. It verifies the derivation it was handed, against the
// program it was handed, under the profile it was handed.
func ExampleCheck() {
	// The program a derivation may cite:  permit(S) :- grant(S).
	permitRule := NewClauseId("permit_rule")
	program := NewMapProgram().With(
		permitRule,
		NewClause(NewGoal("permit", Var("S")), NewGoal("grant", Var("S"))),
	)

	grantS1 := NewGroundLiteral("grant", core.NewAtom([]byte("s1")))
	permitS1 := NewGroundLiteral("permit", core.NewAtom([]byte("s1")))

	// Node 0 is the leaf grant(s1); node 1 applies the rule to it and is the ROOT
	// (the trailing 1 is the root INDEX, not a node count).
	deriv := NewDerivation([]Node{
		LeafNode{Conc: grantS1, Evidence: NoEvidence()},
		RuleNode{
			Conc:     permitS1,
			Clause:   permitRule,
			Subst:    Subst{NewVarId("S"): Atom([]byte("s1"))},
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}, 1)

	// The profile IS the checker's trust policy — what it decides, what it takes
	// on faith.
	profile := &CheckProfile[struct{}]{
		Theory: NewCompoundTheory(), // no builtins in this program
		Leaves: exampleLeaves{PredicateSetOf("grant")},
		Admit:  AlwaysAdmit[struct{}]{}, // no rule-admissibility policy
		Limits: DefaultLimits(),
	}

	fmt.Println("permit(s1):", Check(program, permitS1, deriv, struct{}{}, profile).IsAccept())

	// The same derivation does not prove a different claim — this line is the
	// example's own control: a build where Check always accepts fails here.
	permitS2 := NewGroundLiteral("permit", core.NewAtom([]byte("s2")))
	fmt.Println("permit(s2):", Check(program, permitS2, deriv, struct{}{}, profile).IsAccept())

	// Output:
	// permit(s1): true
	// permit(s2): false
}
