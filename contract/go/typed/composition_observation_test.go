package typed_test

import "github.com/Bitspark/logos-contract/contract/go/typed"

// This invented measurement domain owns its predicate and observation assumption.
// It uses only the public checking syntax; no name is registered in the checker.
// The predicate's real-world interpretation and the observation's truth are
// explicitly outside what this fixture claims to establish.
type observationFixture struct {
	declarations []typed.Declaration
	predicate    typed.Expr
	witness      typed.Expr
	dependencies []string
}

func observationAtZero(namespace string) observationFixture {
	predicate := typed.Const(namespace + ".permitted")
	witness := typed.Const(namespace + ".observed-zero")
	dependencies := []string{namespace + ".interpretation", namespace + ".observation"}
	return observationFixture{
		declarations: []typed.Declaration{
			typed.Assume(predicate.Name(), typed.Pi(typed.Nat(), typed.Sort(0)), dependencies[0]),
			typed.Assume(witness.Name(), typed.App(predicate, typed.Zero()), dependencies[1]),
		},
		predicate: predicate, witness: witness, dependencies: dependencies,
	}
}
