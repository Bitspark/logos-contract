// Language-local id-pin tests for the §9 canonical clause encoding — the load-bearing
// ORACLE for the ADR-0007 negation account encoding (NEG_TAG). These mirror Rust's
// account.rs #[cfg(test)] pins; they are NOT cross-core vectors (that is the shared
// vectors/account.json driven by the differential harness), but they assert the
// SAME frozen ids, so a drift in the Go encoding fails here too.
package contract

import "testing"

// The frozen canonical id of permit(S,A) :- grant(S,A), \+ denied(S,A). under the
// NEG_TAG reading — byte-pinned in vectors/account.json and Rust's account.rs.
const frozenPermitNegID = "3670ee8eebbd14d90621ddf82d8244a555562194c64d11dcd9986bcfefed705d"

// TestNegClauseIDPinnedAndDistinctFromPositive is the load-bearing oracle: the
// WithNeg clause's canonical id must equal the frozen hash, AND must DIFFER from the
// same body literals read as all-positive (the Neg tag is part of the id).
func TestNegClauseIDPinnedAndDistinctFromPositive(t *testing.T) {
	permitNeg := WithNeg(
		NewGoal("permit", Var("S"), Var("A")),
		[]Goal{NewGoal("grant", Var("S"), Var("A"))},
		[]Goal{NewGoal("denied", Var("S"), Var("A"))},
	)
	// The SAME body literals, but BOTH read as positive.
	permitAllPos := NewClause(
		NewGoal("permit", Var("S"), Var("A")),
		NewGoal("grant", Var("S"), Var("A")),
		NewGoal("denied", Var("S"), Var("A")),
	)

	negID := CanonicalClauseId(permitNeg).String()
	posID := CanonicalClauseId(permitAllPos).String()

	// Polarity is part of the id: the negated reading is distinct.
	if negID == posID {
		t.Fatalf("neg-bearing id must differ from the all-positive reading; both were %s", negID)
	}
	// Pin the new Neg-bearing id (locks the NEG_TAG reading against drift).
	if negID != frozenPermitNegID {
		t.Fatalf("neg clause id\n got  %s\n want %s", negID, frozenPermitNegID)
	}
}

// TestPositiveClauseIDsUnchanged re-asserts the 4 frozen positive clause ids from
// vectors/account.json after the BodyLit amendment — a Pos body literal reads as the
// bare goalAsTerm with no wrapper tag, so every pre-amendment positive id is
// byte-for-byte unchanged.
func TestPositiveClauseIDsUnchanged(t *testing.T) {
	cases := []struct {
		name   string
		clause Clause
		want   string
	}{
		{
			// edge(a, b).
			name:   "edge_ab_fact",
			clause: Fact(NewGoal("edge", Atom([]byte("a")), Atom([]byte("b")))),
			want:   "0fa66252d400869a272c064a66c32d461b30f95f30e1d03a5fb961cb957bead3",
		},
		{
			// reach(X, Y) :- edge(X, Y).
			name: "reach_base",
			clause: NewClause(
				NewGoal("reach", Var("X"), Var("Y")),
				NewGoal("edge", Var("X"), Var("Y")),
			),
			want: "c52ab14799945827045a4410caed08ca26f2704944da2a6fe48546c096702234",
		},
		{
			// reach(X, Z) :- edge(X, Y), reach(Y, Z).
			name: "reach_rec",
			clause: NewClause(
				NewGoal("reach", Var("X"), Var("Z")),
				NewGoal("edge", Var("X"), Var("Y")),
				NewGoal("reach", Var("Y"), Var("Z")),
			),
			want: "d5cb2f8c0811500282cacd5cdf0db22d3356d0eadbdc64e73a149d1c8122dd5d",
		},
		{
			// reach(X, Z) :- edge(X, Z).
			name: "reach_base_renamed_Y_to_Z_differs",
			clause: NewClause(
				NewGoal("reach", Var("X"), Var("Z")),
				NewGoal("edge", Var("X"), Var("Z")),
			),
			want: "fff905c2dd63fb17d66bd109e0940df053606dd0270fdfa02b6a43168f5197b1",
		},
	}
	for _, tc := range cases {
		got := CanonicalClauseId(tc.clause).String()
		if got != tc.want {
			t.Errorf("%s id\n got  %s\n want %s", tc.name, got, tc.want)
		}
	}
}
