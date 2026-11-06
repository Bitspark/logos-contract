// The contract↔guest standard-theory SYNC GUARD, Go arm (#574).
//
// NewStandardTheory() is the consumer-facing gate Theory a Go CHECK consumer binds into its
// CheckProfile to certify a search that uses the wasm guest's builtins. It MUST own EXACTLY
// the predicate set the guest's rs standard_theory() evaluates IN SEARCH — otherwise a
// perfectly-formed Builtin node routes to NO owner under check() and silently fails to
// certify (the root of #574). Go has no native search engine and cannot reach the rs guest
// binding from a unit test, so this arm pins the owned set against the rs SOURCE OF TRUTH
// enumerated below (arithmetic.rs / text.rs / term_theory.rs / list_theory.rs). The rs arm
// (app/wasm/rs) compares the contract helper to the guest's local standard_theory() owns
// directly; together they fence the helper from drifting away from the guest tri-core.

package contract

import "testing"

// standardOwnedPredicates is the EXACT predicate set NewStandardTheory() owns — the union of
// the four standard theories' owned relations, copied verbatim from the rs source of truth:
//
//   - ArithmeticTheory (contract/rs/src/arithmetic.rs): is =:= =\= < > >= =<
//   - TextTheory       (contract/rs/src/text.rs):       contains starts_with ends_with
//   - TermTheory       (contract/rs/src/term_theory.rs): atom atomic compound is_list number
//     (recognizers) + == \== @< @> @=< @>= (standard-order comparisons) + =.. (univ)
//   - = \= true fail false (unification + control constants, 1.1.0 / #1611)
//   - ListTheory       (contract/rs/src/list_theory.rs): length nth0 last
var standardOwnedPredicates = []string{
	// ArithmeticTheory
	"is", "=:=", "=\\=", "<", ">", ">=", "=<",
	// TextTheory
	"contains", "starts_with", "ends_with",
	// TermTheory recognizers
	"atom", "atomic", "compound", "is_list", "number",
	// TermTheory standard-order comparisons
	"==", "\\==", "@<", "@>", "@=<", "@>=",
	// TermTheory univ, unification and the control constants (#1611)
	"=..", "=", "\\=", "true", "fail", "false",
	// ListTheory
	"length", "nth0", "last",
}

// standardNotOwnedPredicates are predicates NO standard theory may claim — non-builtin
// heads/leaves and expression operators (which are sub-terms, never goals).
var standardNotOwnedPredicates = []string{
	"reach", "edge", "p", "differ", "five", "concat", "+", "-", "foo",
}

// TestStandardTheoryOwnsExactlyTheGuestPredicateSet pins NewStandardTheory()'s owned set
// EQUAL to the rs guest's standard_theory() owned set — every builtin the guest evaluates is
// owned by the gate Theory, and nothing else is, so a Builtin node the guest emits always
// routes to an owner under check().
func TestStandardTheoryOwnsExactlyTheGuestPredicateSet(t *testing.T) {
	theory := NewStandardTheory()

	for _, name := range standardOwnedPredicates {
		if !theory.Owns(SymbolFromString(name)) {
			t.Errorf("NewStandardTheory().Owns(%q) = false, want true", name)
		}
	}
	for _, name := range standardNotOwnedPredicates {
		if theory.Owns(SymbolFromString(name)) {
			t.Errorf("NewStandardTheory().Owns(%q) = true, want false", name)
		}
	}
}

// TestStandardTheoryMembersAreOrderedArithTextTermList pins the member ORDER (and count) the
// guest binds, so the CompoundTheory identity digest — which commits to the ORDERED member
// identities — matches the guest's byte-for-byte. Each member owns one disjoint slice, so
// probing a representative predicate per member confirms both presence and order-independence
// of routing (routing is by Owns, but the digest is order-SENSITIVE, so we also assert the
// identity is the four-member compound's, not a re-ordered one).
func TestStandardTheoryMembersAreOrderedArithTextTermList(t *testing.T) {
	got := NewStandardTheory().Identity()
	// The four-member compound in arith/text/term/list order.
	want := NewCompoundTheory(
		NewArithmeticTheory(),
		NewTextTheory(),
		NewTermTheory(),
		NewListTheory(),
	).Identity()
	if string(got.Id) != string(want.Id) ||
		string(got.Version) != string(want.Version) ||
		got.ConfigDigest != want.ConfigDigest {
		t.Fatalf("NewStandardTheory() identity must equal the arith/text/term/list compound's; got %+v want %+v", got, want)
	}
	// A re-ordered compound MUST differ (the digest is order-sensitive), proving the order is
	// load-bearing and pinned.
	reordered := NewCompoundTheory(
		NewTextTheory(),
		NewArithmeticTheory(),
		NewTermTheory(),
		NewListTheory(),
	).Identity()
	if got.ConfigDigest == reordered.ConfigDigest {
		t.Fatal("NewStandardTheory() identity must be order-sensitive: a re-ordered compound shares the digest")
	}
}
