// BodyLit polarity predicates — IsPos / IsNeg / IsCount must PARTITION the polarity.
//
// WHY THIS EXISTS. Before IsPos, the contract exported only the complements (IsNeg,
// IsCount). A consumer gating on positive-only bodies — e.g. arche PROTOCOL 3.10a, which
// says a rule-fact body is positive Horn — could therefore only express its rule as
// "not Neg and not Count": a BLACKLIST. That admits every polarity added later BY DEFAULT,
// silently, in every consumer not updated in lockstep. It is how a `count` body literal
// came to be admitted by one consumer core and rejected by two others (thesmos#409) — an
// authorization split on attacker-supplied bytes, since rule-fact clauses are untrusted.
//
// The partition assertion below is the load-bearing one: it fails if a new polarity is
// added without a matching predicate, which is exactly the moment a downstream whitelist
// would otherwise start silently under-matching.
package contract

import "testing"

// bodyLitPolarityCases returns one BodyLit per polarity the contract defines. ADD A CASE
// HERE WHEN A POLARITY IS ADDED.
//
// ⚠ This doc used to read "TestBodyLitPolarityPartition will fail until you do, and that failure
// is the point". THAT WAS FALSE, and measured false (#996): every guard in this package iterates
// this map, so a polarity added without touching it left them all passing VACUOUSLY — including
// TestBodyLitIsPosIsNotTheComplement, whose own message warns that "the blacklist formulation
// admits a polarity it was never told about". A guard that cannot see the thing it warns about is
// the defect it warns about. (rust carried the identical false promise; #991 removed it there.)
//
// What actually forces the update now is TestPolarityCorpusCoversEveryDeclaredPolarity, which
// parses program.go and compares the DECLARED polarity count against this map's size. Go cannot
// force at compile time the way rust and ts can — see polarity_tripwire_test.go for why.
func bodyLitPolarityCases() map[string]BodyLit {
	g := NewGoal("p", Var("X"))
	return map[string]BodyLit{
		"pos": PosLit(g),
		"neg": NegLit(g),
		"count": CountLitBody(CountLit{
			Pred:    NewPredicateRef(NewSymbol([]byte("q")), 1),
			Filter:  nil,
			Project: Rows(),
			Count:   Var("N"),
		}),
	}
}

func TestBodyLitIsPos(t *testing.T) {
	g := NewGoal("p", Var("X"))
	if !PosLit(g).IsPos() {
		t.Fatal("PosLit must be IsPos")
	}
	if NegLit(g).IsPos() {
		t.Fatal("NegLit must not be IsPos")
	}
	count := CountLitBody(CountLit{
		Pred:    NewPredicateRef(NewSymbol([]byte("q")), 1),
		Project: Rows(),
		Count:   Var("N"),
	})
	if count.IsPos() {
		t.Fatal("CountLitBody must not be IsPos")
	}
}

// TestBodyLitPolarityPartition asserts EXACTLY ONE predicate holds for every polarity.
//
// Both halves matter and they fail differently:
//   - "at least one" fails when a polarity is added with no predicate — the case where a
//     downstream whitelist (IsPos) silently stops matching a body it should classify.
//   - "at most one" fails if two predicates ever overlap, which would make whitelist and
//     blacklist disagree about the same literal.
func TestBodyLitPolarityPartition(t *testing.T) {
	for name, bl := range bodyLitPolarityCases() {
		n := 0
		for _, held := range []bool{bl.IsPos(), bl.IsNeg(), bl.IsCount()} {
			if held {
				n++
			}
		}
		if n != 1 {
			t.Fatalf("polarity %q: %d of {IsPos, IsNeg, IsCount} hold, want exactly 1 — "+
				"a polarity with no predicate is admitted by default in any consumer that "+
				"gates by ruling out the others", name, n)
		}
	}
}

// TestBodyLitIsPosIsNotTheComplement pins the distinction the whole method exists for: a
// whitelist and the negated blacklist agree TODAY, and the test states why that agreement
// must not be relied on. If a polarity is added without updating the cases above, the
// partition test fails; if one is added and the cases ARE updated, this test shows the two
// formulations diverging — which is the defect, made visible.
func TestBodyLitIsPosIsNotTheComplement(t *testing.T) {
	for name, bl := range bodyLitPolarityCases() {
		whitelist := bl.IsPos()
		blacklist := !bl.IsNeg() && !bl.IsCount()
		if whitelist != blacklist {
			t.Fatalf("polarity %q: IsPos()=%v but !IsNeg()&&!IsCount()=%v — the blacklist "+
				"formulation admits a polarity it was never told about; consumers gating on "+
				"positive-Horn bodies must use IsPos", name, whitelist, blacklist)
		}
	}
}
