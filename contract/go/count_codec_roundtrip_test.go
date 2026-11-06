// Does a Count body literal survive the CLAUSE CODEC? — the reachability question behind
// thesmos#409 / stele#579 / logos-db#153.
//
// WHY IT DECIDED SEVERITY, not just tidiness. Consumers read a rule-fact's body literals via
// Inner(), and the three cores disagreed on a Count: go returned the ZERO Goal (silently empty)
// and RUST PANICKED by design. (That partial accessor was deleted tri-core in #2733; the Lit
// field this test now reads is still exported.) That divergence mattered only if a Count could
// actually ARRIVE in a
// rule-fact — i.e. survive ClauseAsValue -> ClauseFromValue, the codec a signed rule-fact
// travels through. Two possible worlds:
//
//	NOT REPRESENTABLE  the encoding cannot carry a Count -> unreachable by construction, and a
//	                   consumer-side polarity guard is defence-in-depth that can ride any lane.
//	REPRESENTABLE      a signed rule-fact can carry one -> a consumer calling inner() on the
//	                   rust core takes a REMOTE PANIC on attacker-supplied bytes, and the guard
//	                   is urgent in every core.
//
// caa@stele attempted this and their probe died in the FIXTURE (a zero-value CountLit has no
// quotable Pred, so Quote panicked while building the clause, long before the codec). They
// correctly refused to cite that panic as evidence. This test builds a WELL-FORMED CountLit so
// the codec is what is actually exercised.
package contract

import "testing"

// countBodyClause is a rule-fact-shaped clause whose body carries a well-formed Count.
func countBodyClause() Clause {
	return Clause{
		Head: NewGoal("authorized", Var("S")),
		Body: []BodyLit{CountLitBody(CountLit{
			Pred:    NewPredicateRef(NewSymbol([]byte("signed_fact")), 1),
			Filter:  []CountFilterEntry{{Pos: 0, Term: Var("S")}},
			Project: Rows(),
			Count:   Var("N"),
		})},
	}
}

// TestCountBodyLitSurvivesClauseCodec answers the reachability question by measurement.
//
// It asserts the ROUND TRIP, not just that encoding succeeds: a Count that encoded but decoded
// as something else would be worse than one that could not encode at all, because the consumer
// would then act on a silently different clause.
func TestCountBodyLitSurvivesClauseCodec(t *testing.T) {
	original := countBodyClause()

	value := ClauseAsValue(original)
	decoded, ok := ClauseFromValue(value)
	if !ok {
		t.Fatalf("NOT REPRESENTABLE: ClauseFromValue refused a clause with a Count body literal. " +
			"If this is the real behaviour, a Count cannot reach a consumer through a signed " +
			"rule-fact and the polarity hazard is unreachable by construction.")
	}

	if len(decoded.Body) != 1 {
		t.Fatalf("round trip changed the body length: got %d, want 1", len(decoded.Body))
	}
	b := decoded.Body[0]

	// The polarity must survive. A Count decoding as Pos would be the silent-misdecode case:
	// the consumer would see a positive literal over the count's term structure.
	if !b.IsCount() {
		t.Fatalf("POLARITY LOST IN ROUND TRIP: a Count body literal decoded as IsPos=%v IsNeg=%v "+
			"IsCount=%v. A Count that decodes as something else is worse than one that cannot "+
			"encode, because the consumer acts on a clause that is silently not the one signed.",
			b.IsPos(), b.IsNeg(), b.IsCount())
	}

	// And the payload must survive, or the round trip is lossy in a way a consumer could act on.
	if got, want := b.CountVal.Pred.Pred.String(), "signed_fact"; got != want {
		t.Fatalf("counted predicate lost in round trip: got %q, want %q", got, want)
	}
	if len(b.CountVal.Filter) != 1 {
		t.Fatalf("count filter lost in round trip: got %d entries, want 1", len(b.CountVal.Filter))
	}
}

// TestCountBodyLitInnerAfterRoundTrip pins what a consumer actually sees, since that is the
// thing three consumers got wrong.
//
// After the round trip, a decoded Count's Lit is the ZERO Goal — an EMPTY predicate, the
// fail-closed choice (a gate matching on pred matches nothing). The ts core's placeholder was
// aligned to empty in #726, and the partial accessors were deleted tri-core in #2733.
// Consumers must branch on polarity — IsPos() (#722) — rather than read any field off a Count.
func TestCountBodyLitInnerAfterRoundTrip(t *testing.T) {
	decoded, ok := ClauseFromValue(ClauseAsValue(countBodyClause()))
	if !ok {
		t.Skip("clause codec refused a Count body literal; the round-trip test reports that")
	}
	b := decoded.Body[0]
	if !b.IsCount() {
		t.Skip("polarity did not survive; the round-trip test reports that")
	}

	// Reads the exported Lit field directly. The partial Inner() accessor was deleted (#2733), but
	// the field stays exported, so a decoded Count must still carry the ZERO Goal there.
	if inner := b.Lit; inner.Pred.String() != "" {
		t.Fatalf("a decoded Count's Lit exposed predicate %q; the go core's contract is "+
			"the ZERO Goal, and a non-empty value here is what let consumer gates match on a name "+
			"the rule author never wrote", inner.Pred.String())
	}

	// The counted predicate is reachable where it belongs — via the polarity-aware accessor.
	if got := b.Pred().String(); got != "signed_fact" {
		t.Fatalf("Pred() should still expose the counted relation: got %q", got)
	}
}
