package contract_test

// #3111 (checker SPI v2, ADR 0036 D8 change 5): Check returns Outcome{Verdict, Report}, and the
// report counts the work the check did by the rules in the module doc of
// contract/rs/src/check/report.rs. These tests pin those rules on tiny hand-built derivations: the
// go port of contract/rs/tests/check_report_3111.rs, with the same derivations and the same expected
// numbers. Every expected count below is computed by hand from the rules, never read back from a run.

import (
	"bytes"
	"math"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// ltTheory3111 owns `lt`: lt(a, b) holds iff both arguments are atoms and a < b bytewise.
// test-double: consumer(a less-than theory over atoms)
type ltTheory3111 struct{}

func (ltTheory3111) Owns(pred contract.Symbol) bool {
	return pred.Equal(contract.SymbolFromString("lt"))
}

func (ltTheory3111) DecideGround(atom contract.GroundLiteral) completion.TheoryGround {
	if len(atom.Args) != 2 {
		return completion.TheoryGroundFails("lt_arity")
	}
	a, aok := atom.Args[0].(core.Atom)
	b, bok := atom.Args[1].(core.Atom)
	if aok && bok && bytes.Compare(a.Bytes(), b.Bytes()) < 0 {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("not_less_than")
}

// edgeLeaves3111: `edge` is extensional, and every edge leaf is admitted.
// test-double: consumer(admits every leaf of its extensional set)
type edgeLeaves3111 struct{ extensional *contract.PredicateSet }

func (l edgeLeaves3111) Extensional() *contract.PredicateSet { return l.extensional }

func (edgeLeaves3111) Verify(contract.GroundLiteral, contract.Evidence, struct{}) contract.LeafOutcome {
	return contract.LeafAdmit{}
}

func profile3111(limits contract.CheckLimits) *contract.CheckProfile[struct{}] {
	return &contract.CheckProfile[struct{}]{
		Theory: ltTheory3111{},
		Leaves: edgeLeaves3111{contract.PredicateSetOf("edge")},
		Admit:  contract.AlwaysAdmit[struct{}]{},
		Limits: limits,
	}
}

// program3111 is `path(X, Y) :- edge(X, Y).` and `step(X, Y) :- edge(X, Y), lt(X, Y).`
func program3111() *contract.MapProgram {
	args := func() []contract.Term { return []contract.Term{contract.Var("X"), contract.Var("Y")} }
	return contract.NewMapProgram().
		With(contract.NewClauseId("path_edge"),
			contract.NewClause(contract.NewGoal("path", args()...), contract.NewGoal("edge", args()...))).
		With(contract.NewClauseId("step"),
			contract.NewClause(contract.NewGoal("step", args()...), contract.NewGoal("edge", args()...), contract.NewGoal("lt", args()...)))
}

func atom3111(s string) core.Value { return core.NewAtom([]byte(s)) }

func lit3111(pred, x, y string) contract.GroundLiteral {
	return contract.NewGroundLiteral(pred, atom3111(x), atom3111(y))
}

// xy3111 is X = x, Y = y.
func xy3111(x, y string) contract.Subst {
	return contract.Subst{
		contract.NewVarId("X"): contract.Atom([]byte(x)),
		contract.NewVarId("Y"): contract.Atom([]byte(y)),
	}
}

func leaf3111(x, y string) contract.Node {
	return contract.LeafNode{Conc: lit3111("edge", x, y), Evidence: contract.NoEvidence()}
}

func rule3111(pred, clause, x, y string, premises []contract.Premise) contract.Node {
	return contract.RuleNode{
		Conc:     lit3111(pred, x, y),
		Clause:   contract.NewClauseId(clause),
		Subst:    xy3111(x, y),
		Premises: premises,
		Meta:     contract.NoMeta(),
	}
}

func run3111(claim contract.GroundLiteral, deriv contract.Derivation, limits contract.CheckLimits) contract.Outcome {
	return contract.Check(program3111(), claim, deriv, struct{}{}, profile3111(limits))
}

// wantCode3111 fails unless the outcome rejects with code.
func wantCode3111(t *testing.T, name string, o contract.Outcome, code contract.RejectionCode) {
	t.Helper()
	if o.Verdict.IsAccept() || o.Verdict.Code() != code {
		t.Fatalf("%s: want reject %s, got %s", name, code.Code(), o.Verdict)
	}
}

// small3111 is path(a, b) from one edge(a, b) leaf: two nodes.
func small3111() (contract.GroundLiteral, contract.Derivation) {
	deriv := contract.NewDerivation([]contract.Node{
		leaf3111("a", "b"),
		rule3111("path", "path_edge", "a", "b", contract.PosPremises(0)),
	}, 1)
	return lit3111("path", "a", "b"), deriv
}

// larger3111 is step(a, b) from an edge(a, b) leaf and an lt(a, b) builtin: three nodes.
func larger3111() (contract.GroundLiteral, contract.Derivation) {
	deriv := contract.NewDerivation([]contract.Node{
		leaf3111("a", "b"),
		contract.BuiltinNode{Conc: lit3111("lt", "a", "b")},
		rule3111("step", "step", "a", "b", contract.PosPremises(0, 1)),
	}, 2)
	return lit3111("step", "a", "b"), deriv
}

// wrongSecondPremise3111 is step(a, b) whose second premise cites lt(a, c), which holds but is not
// the grounded body literal lt(a, b): the rule node rejects at premise 1.
func wrongSecondPremise3111() (contract.GroundLiteral, contract.Derivation) {
	deriv := contract.NewDerivation([]contract.Node{
		leaf3111("a", "b"),
		contract.BuiltinNode{Conc: lit3111("lt", "a", "c")},
		rule3111("step", "step", "a", "b", contract.PosPremises(0, 1)),
	}, 2)
	return lit3111("step", "a", "b"), deriv
}

// failingBuiltin3111 is step(b, a) over an lt(b, a) builtin the theory decides false: the builtin
// node rejects before the rule node is walked.
func failingBuiltin3111() (contract.GroundLiteral, contract.Derivation) {
	deriv := contract.NewDerivation([]contract.Node{
		leaf3111("b", "a"),
		contract.BuiltinNode{Conc: lit3111("lt", "b", "a")},
		rule3111("step", "step", "b", "a", contract.PosPremises(0, 1)),
	}, 2)
	return lit3111("step", "b", "a"), deriv
}

// negativeAgainstPositive3111 is path(a, b) whose one premise is NEGATIVE against the clause's
// positive body literal: counted as a negative premise, then refused on its polarity.
func negativeAgainstPositive3111() (contract.GroundLiteral, contract.Derivation) {
	neg := contract.NegPremise{Atom: lit3111("edge", "a", "b"), Cert: contract.NewCertId(0), Nonmember: contract.DirectLookup}
	deriv := contract.NewDerivation([]contract.Node{
		rule3111("path", "path_edge", "a", "b", []contract.Premise{neg}),
	}, 0)
	return lit3111("path", "a", "b"), deriv
}

func TestOutcomeEqualityIsTheVerdicts3111(t *testing.T) {
	smallClaim, smallDeriv := small3111()
	largerClaim, largerDeriv := larger3111()
	a := run3111(smallClaim, smallDeriv, contract.DefaultLimits())
	b := run3111(largerClaim, largerDeriv, contract.DefaultLimits())
	if a.Verdict != contract.Accept() || b.Verdict != contract.Accept() {
		t.Fatalf("both derivations must accept, got %s and %s", a.Verdict, b.Verdict)
	}
	// Two different-sized derivations, two different reports, one verdict: equal outcomes.
	if a.Report == b.Report {
		t.Fatalf("two sizes, two reports: both are %+v", a.Report)
	}
	if !a.Equal(b) {
		t.Fatal("an outcome's equality is its verdict's")
	}
	// And the converse: different verdicts, unequal outcomes.
	wrongClaim, wrongDeriv := wrongSecondPremise3111()
	rejected := run3111(wrongClaim, wrongDeriv, contract.DefaultLimits())
	if rejected.Equal(b) {
		t.Fatalf("a rejection equals an accept: %s", rejected)
	}
}

func TestNodeKindsSum3111(t *testing.T) {
	for _, c := range []struct {
		name  string
		build func() (contract.GroundLiteral, contract.Derivation)
	}{
		{"small", small3111},
		{"larger", larger3111},
		{"wrong second premise", wrongSecondPremise3111},
		{"failing builtin", failingBuiltin3111},
		{"negative against positive", negativeAgainstPositive3111},
	} {
		claim, deriv := c.build()
		outcome := run3111(claim, deriv, contract.DefaultLimits())
		if !outcome.Report.NodeKindsSum() {
			t.Errorf("%s: the node kinds must sum to NodesWalked, got %+v", c.name, outcome.Report)
		}
	}
	// The control: a report whose kinds do not sum fails the check.
	broken := contract.ZeroCheckReport()
	broken.NodesWalked = contract.Counted(2)
	broken.LeafNodes = contract.Counted(1)
	if broken.NodeKindsSum() {
		t.Fatalf("a report with 2 nodes walked and 1 leaf node passes NodeKindsSum: %+v", broken)
	}
}

func TestARejectionReportsTheWorkUpToTheRejectingNode3111(t *testing.T) {
	// Node 0, the leaf: walked, depth 1, one leaf verification. Node 1, the builtin: walked,
	// depth 1, one theory decision (it holds). Node 2, the rule: walked, depth 2; step (f) counts
	// premise 0 (it matches), then premise 1, which rejects. No admissibility call is reached.
	claim, deriv := wrongSecondPremise3111()
	outcome := run3111(claim, deriv, contract.DefaultLimits())
	wantCode3111(t, "wrong second premise", outcome, contract.InstantiationMismatch)
	r := outcome.Report
	for _, c := range []struct {
		name string
		got  contract.ReportCount
		want int
	}{
		{"NodesWalked", r.NodesWalked, 3},
		{"RuleNodes", r.RuleNodes, 1},
		{"BuiltinNodes", r.BuiltinNodes, 1},
		{"LeafNodes", r.LeafNodes, 1},
		{"PremisesPos", r.PremisesPos, 2},
		{"PremisesNeg", r.PremisesNeg, 0},
		{"TheoryDecisions", r.TheoryDecisions, 1},
		{"LeafVerifications", r.LeafVerifications, 1},
		{"AdmissibilityChecks", r.AdmissibilityChecks, 0},
		{"MaxDepthReached", r.MaxDepthReached, 2},
	} {
		if c.got != contract.Counted(c.want) {
			t.Errorf("wrong second premise: %s is %s, want counted(%d)", c.name, c.got, c.want)
		}
	}

	// The builtin decided false: nodes 0 and 1 are walked, node 2 never is.
	claim, deriv = failingBuiltin3111()
	outcome = run3111(claim, deriv, contract.DefaultLimits())
	wantCode3111(t, "failing builtin", outcome, contract.BuiltinFailed)
	expected := contract.ZeroCheckReport()
	expected.NodesWalked = contract.Counted(2)
	expected.BuiltinNodes = contract.Counted(1)
	expected.LeafNodes = contract.Counted(1)
	expected.TheoryDecisions = contract.Counted(1)
	expected.LeafVerifications = contract.Counted(1)
	expected.MaxDepthReached = contract.Counted(1)
	expected.MaxTermDepthReached = contract.Counted(1)
	if outcome.Report != expected {
		t.Errorf("failing builtin: report %+v, want %+v", outcome.Report, expected)
	}

	// A negative premise is counted as negative before its polarity is checked.
	claim, deriv = negativeAgainstPositive3111()
	outcome = run3111(claim, deriv, contract.DefaultLimits())
	wantCode3111(t, "negative against positive", outcome, contract.InstantiationMismatch)
	expected = contract.ZeroCheckReport()
	expected.NodesWalked = contract.Counted(1)
	expected.RuleNodes = contract.Counted(1)
	expected.PremisesNeg = contract.Counted(1)
	expected.MaxDepthReached = contract.Counted(1)
	expected.MaxTermDepthReached = contract.Counted(1)
	if outcome.Report != expected {
		t.Errorf("negative against positive: report %+v, want %+v", outcome.Report, expected)
	}
}

func TestALimitsRefusalReportsZeros3111(t *testing.T) {
	// A budget past the protocol index domain (a 64-bit math.MaxInt is): the configuration is refused
	// before any node is read. On a 32-bit host math.MaxInt is inside the domain, as rs's test is
	// 64-bit only.
	if uint64(math.MaxInt) <= contract.IndexMax {
		t.Skip("math.MaxInt is inside the protocol index domain on this host")
	}
	claim, deriv := small3111()
	limits := contract.DefaultLimits()
	limits.MaxNodes = math.MaxInt
	outcome := run3111(claim, deriv, limits)
	wantCode3111(t, "limits", outcome, contract.InvalidCheckLimits)
	if outcome.Report != contract.ZeroCheckReport() {
		t.Errorf("limits: report %+v, want zeros", outcome.Report)
	}
}

func TestTheOtherRefusalsBeforeTheWalkReportWhatTheyDid3111(t *testing.T) {
	// The node cap reads no node: zeros.
	claim, deriv := small3111()
	limits := contract.DefaultLimits()
	limits.MaxNodes = 1
	outcome := run3111(claim, deriv, limits)
	wantCode3111(t, "node cap", outcome, contract.TooManyNodes)
	if outcome.Report != contract.ZeroCheckReport() {
		t.Errorf("node cap: report %+v, want zeros", outcome.Report)
	}

	// The term-depth cap measured the claim's first argument, t(a) (depth 2), against a cap of 1,
	// and stopped there: zeros, except the depth it measured.
	deep := core.NewTuple(atom3111("t"), atom3111("a"))
	claim = contract.NewGroundLiteral("path", deep, atom3111("b"))
	limits = contract.DefaultLimits()
	limits.MaxTermDepth = 1
	outcome = run3111(claim, deriv, limits)
	wantCode3111(t, "term depth", outcome, contract.TermTooDeep)
	expected := contract.ZeroCheckReport()
	expected.MaxTermDepthReached = contract.Counted(2)
	if outcome.Report != expected {
		t.Errorf("term depth: report %+v, want %+v", outcome.Report, expected)
	}
}

func TestAnAcceptedCheckReportsItsExactWork3111(t *testing.T) {
	// Node 0, the leaf: depth 1, one leaf verification. Node 1, the builtin: depth 1, one theory
	// decision. Node 2, the rule: depth 2, two positive premises, one admissibility call. Every term
	// is an atom, so the deepest term is 1. No certificate is cited.
	claim, deriv := larger3111()
	outcome := run3111(claim, deriv, contract.DefaultLimits())
	if outcome.Verdict != contract.Accept() {
		t.Fatalf("larger: want accept, got %s", outcome.Verdict)
	}
	expected := contract.CheckReport{
		CountersVersion:      contract.CheckReportCountersVersion,
		NodesWalked:          contract.Counted(3),
		RuleNodes:            contract.Counted(1),
		BuiltinNodes:         contract.Counted(1),
		LeafNodes:            contract.Counted(1),
		PremisesPos:          contract.Counted(2),
		PremisesNeg:          contract.Counted(0),
		TheoryDecisions:      contract.Counted(1),
		LeafVerifications:    contract.Counted(1),
		AdmissibilityChecks:  contract.Counted(1),
		CertsVerified:        contract.Counted(0),
		CertsMemoHits:        contract.Counted(0),
		CertTablesRead:       contract.Counted(0),
		CertRowsRead:         contract.Counted(0),
		JoinStepsUsed:        contract.Counted(0),
		GroundingsEnumerated: contract.Counted(0),
		MaxDepthReached:      contract.Counted(2),
		MaxTermDepthReached:  contract.Counted(1),
	}
	if outcome.Report != expected {
		t.Errorf("larger: report %+v, want %+v", outcome.Report, expected)
	}

	// The smaller derivation: one leaf and one rule over it.
	claim, deriv = small3111()
	outcome = run3111(claim, deriv, contract.DefaultLimits())
	if outcome.Verdict != contract.Accept() {
		t.Fatalf("small: want accept, got %s", outcome.Verdict)
	}
	expected = contract.ZeroCheckReport()
	expected.NodesWalked = contract.Counted(2)
	expected.RuleNodes = contract.Counted(1)
	expected.LeafNodes = contract.Counted(1)
	expected.PremisesPos = contract.Counted(1)
	expected.LeafVerifications = contract.Counted(1)
	expected.AdmissibilityChecks = contract.Counted(1)
	expected.MaxDepthReached = contract.Counted(2)
	expected.MaxTermDepthReached = contract.Counted(1)
	if outcome.Report != expected {
		t.Errorf("small: report %+v, want %+v", outcome.Report, expected)
	}
}

// TestReportCountZeroIsCountedZero3111: the zero ReportCount is Counted(0), as rs's Default is, and
// Unsupported is never a zero.
func TestReportCountZeroIsCountedZero3111(t *testing.T) {
	var zero contract.ReportCount
	if n, ok := zero.Get(); !ok || n != 0 || zero != contract.Counted(0) {
		t.Fatalf("the zero ReportCount is %s, want counted(0)", zero)
	}
	if n, ok := contract.Unsupported().Get(); ok || contract.Unsupported() == contract.Counted(n) {
		t.Fatal("Unsupported reads as a count")
	}
}
