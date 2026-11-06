package contract

import (
	"reflect"
	"testing"
)

// TestBodyLitFirstClassModes pins the first-class binding & dependency mode descriptors
// (research-doc 0009): BindingTerms / RequiredTerms / Dependency, each total over Pos/Neg/Count.
// The analyzer's safety + dependency passes rely on these uniformly; this mirrors the rs
// program::tests::bodylit_first_class_modes and the ts BodyLit modes test.
func TestBodyLitFirstClassModes(t *testing.T) {
	x, y, z, g, n := Var("X"), Var("Y"), Var("Z"), Var("G"), Var("N")
	pos := PosLit(NewGoal("p", x, y))
	neg := NegLit(NewGoal("q", z))
	count := CountLitBody(CountLit{
		Pred:    NewPredicateRef(SymbolFromString("obs"), 3),
		Filter:  []CountFilterEntry{{Pos: 0, Term: g}},
		Project: Rows(),
		Count:   n,
	})

	// BindingTerms: a positive atom binds all its args; a negation binds nothing; a count binds
	// only its result.
	if !reflect.DeepEqual(pos.BindingTerms(), []Term{x, y}) {
		t.Errorf("pos.BindingTerms() = %v, want [X Y]", pos.BindingTerms())
	}
	if len(neg.BindingTerms()) != 0 {
		t.Errorf("neg.BindingTerms() = %v, want empty", neg.BindingTerms())
	}
	if !reflect.DeepEqual(count.BindingTerms(), []Term{n}) {
		t.Errorf("count.BindingTerms() = %v, want [N]", count.BindingTerms())
	}

	// RequiredTerms: a positive atom requires nothing; a negation requires all its args; a count
	// requires its filter/group vars (the result is exempt).
	if len(pos.RequiredTerms()) != 0 {
		t.Errorf("pos.RequiredTerms() = %v, want empty", pos.RequiredTerms())
	}
	if !reflect.DeepEqual(neg.RequiredTerms(), []Term{z}) {
		t.Errorf("neg.RequiredTerms() = %v, want [Z]", neg.RequiredTerms())
	}
	if !reflect.DeepEqual(count.RequiredTerms(), []Term{g}) {
		t.Errorf("count.RequiredTerms() = %v, want [G]", count.RequiredTerms())
	}

	// Dependency: (read predicate, non-monotone?). A positive atom is monotone; a negation and an
	// aggregate are non-monotone (both read a sealed, strictly-lower stratum).
	for _, tc := range []struct {
		name      string
		b         BodyLit
		wantPred  string
		wantNonMo bool
	}{
		{"pos", pos, "p", false},
		{"neg", neg, "q", true},
		{"count", count, "obs", true},
	} {
		gotPred, gotNonMo := tc.b.Dependency()
		if string(gotPred.Bytes()) != tc.wantPred || gotNonMo != tc.wantNonMo {
			t.Errorf("%s.Dependency() = (%s, %v), want (%s, %v)", tc.name, gotPred.Bytes(), gotNonMo, tc.wantPred, tc.wantNonMo)
		}
	}
}
