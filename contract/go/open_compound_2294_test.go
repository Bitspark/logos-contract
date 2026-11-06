package contract

// #2294 (ruled seat:caa): IsOpenCompound, the ONE classification of "compound" the function-free
// fragment excludes. The same rows as contract/rs/tests/open_compound_2294.rs.

import "testing"

func TestOnlyATupleWithAVariableIsAnOpenCompound2294(t *testing.T) {
	a := func(s string) Term { return Atom([]byte(s)) }
	f := func(x Term) Term { return Tuple(a("f"), x) }
	g := func(x Term) Term { return Tuple(a("g"), x) }
	rows := []struct {
		name string
		term Term
		open bool
	}{
		{"an atom", a("a"), false},
		{"a variable", Var("X"), false},
		{"a string", Tuple(a("utf8-text"), a("a")), false},
		{"f(a)", f(a("a")), false},
		{"f(g(a))", f(g(a("a"))), false},
		{"f(X)", f(Var("X")), true},
		{"f(g(X))", f(g(Var("X"))), true},
	}
	for _, r := range rows {
		if got := IsOpenCompound(r.term); got != r.open {
			t.Errorf("%s: IsOpenCompound = %v, want %v", r.name, got, r.open)
		}
	}
}
