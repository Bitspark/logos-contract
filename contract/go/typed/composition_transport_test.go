package typed_test

import "github.com/Bitspark/logos-contract/contract/go/typed"

// This independent logical contribution knows no observation, mapping or native
// language. It derives transport for an arbitrary Type-0 family using the public
// calculus. These are fixture-owned constructions, not a new package/registry API.
//
// forall A : Type0, P : A -> Type0, x y : A, e : Id(A,x,y), px : P(x), P(y)
func predicateTransport() (typed.Expr, typed.Expr) {
	domains := []typed.Expr{
		typed.Sort(0),
		typed.Pi(typed.Var(0), typed.Sort(0)),
		typed.Var(1),
		typed.Var(2),
		typed.ID(typed.Var(3), typed.Var(1), typed.Var(0)),
		typed.App(typed.Var(3), typed.Var(2)),
	}
	expected := typed.App(typed.Var(4), typed.Var(2))
	candidate := typed.Transport(typed.Var(5), typed.Var(3), typed.Var(2), typed.Var(1), typed.Var(4), typed.Var(0))
	for i := len(domains) - 1; i >= 0; i-- {
		expected = typed.Pi(domains[i], expected)
		candidate = typed.Lam(domains[i], candidate)
	}
	return expected, candidate
}

func applyTransport(theorem, domain, predicate, from, to, equality, witness typed.Expr) typed.Expr {
	result := theorem
	for _, arg := range []typed.Expr{domain, predicate, from, to, equality, witness} {
		result = typed.App(result, arg)
	}
	return result
}
