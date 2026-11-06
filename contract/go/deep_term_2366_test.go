package contract

import "testing"

// #2366: go is MEASURED on the long list that overflowed the ts walks, not assumed. Go's
// term walks recurse once per nesting level too, but a goroutine stack grows (up to 1 GB by
// default), so a 20,000-element list, one level per element, is walked whole. ts made its
// walks iterative for the same list; rs bounds them (#2357).
func TestDeepListTermWalks2366(t *testing.T) {
	const n = 20000
	nilAtom := Atom([]byte("[]"))
	list := func(tail Term) Term {
		l := tail
		for i := 0; i < n; i++ {
			l = Tuple(Atom([]byte(".")), Atom([]byte("a")), l)
		}
		return l
	}

	ground := list(nilAtom)
	if !ground.IsGround() {
		t.Fatal("a ground 20,000-element list must be ground")
	}
	if list(Var("T")).IsGround() {
		t.Fatal("a variable at the bottom must be found")
	}
	v, ok := ground.EraseGround()
	if !ok {
		t.Fatal("a ground list must erase")
	}
	if !FromValue(v).Equal(ground) {
		t.Fatal("eraseGround then FromValue must give back the same term")
	}
	out := list(Var("T")).Substitute(Subst{NewVarId("T"): nilAtom})
	if !out.IsGround() || !out.Equal(ground) {
		t.Fatal("substituting the bottom variable must give the ground list")
	}
}
