package contract

// check's report of the work it actually performed (checker SPI v2, ADR 0036 D8 change 5, #3111;
// design 0006 P1, #1932). The go sibling of contract/rs/src/check/report.rs, whose module doc holds
// the NORMATIVE counting rules every core mirrors. Each increment site in this core's checker
// carries a comment naming its counter, at the point that corresponds to rs's site.
//
// The report rides beside the verdict in Outcome and never decides it: an outcome's equality is its
// verdict's (Outcome.Equal), so a counter can never turn a verdict test red. It counts the work done
// up to and including a rejecting node.
//
// Counters are defined per checker version. CheckReportCountersVersion names the checker version
// whose counting rules these are, and a kernel test pins it equal to CheckerVersionCurrent: a
// change to what a counter counts is a checker-version bump.
//
// One accumulator (checkTally) is threaded through the check by pointer, never held in ambient
// state. A check refused before the walk reports zeros plus what was genuinely done: invalid
// limits, an empty derivation, the node cap, a root out of range and the shape boundary (#3088)
// report ZeroCheckReport; a term_too_deep refusal reports zeros except MaxTermDepthReached. The
// chain check refuses an invalid configuration, an empty chain and a malformed certificate with
// zeros, and an unbound context with only the term depths it measured.

import (
	"fmt"

	core "github.com/bitspark/ontos/core/go"
)

// CheckReportCountersVersion is the checker version whose counting rules CheckReport's counters
// follow. A kernel test asserts it equals CheckerVersionCurrent. rs CHECK_REPORT_COUNTERS_VERSION.
const CheckReportCountersVersion uint32 = 24

// ReportCount is one counter: a count the checker kept (Counted), or Unsupported where this core
// does not count it. Unsupported is never a zero (omit, never fake). The zero value is Counted(0),
// as rs's Default is. rs ReportCount.
//
// A count is a Go int (rs u64): Go's count type, 64 bits on every target logos builds for, and the
// type of every meter the checker counts from (a length, a depth, a join-step meter), so the report
// takes them with no value-losing conversion (the #3956 boundary census). It is never negative.
type ReportCount struct {
	n           int
	unsupported bool
}

// Counted is a count the checker kept. rs ReportCount::Counted.
func Counted(n int) ReportCount { return ReportCount{n: n} }

// Unsupported is a counter this core does not count. rs ReportCount::Unsupported.
func Unsupported() ReportCount { return ReportCount{unsupported: true} }

// Get returns the count, and false where it is not supported. rs ReportCount::get.
func (c ReportCount) Get() (int, bool) {
	if c.unsupported {
		return 0, false
	}
	return c.n, true
}

// String renders "counted(n)" or "unsupported".
func (c ReportCount) String() string {
	if c.unsupported {
		return "unsupported"
	}
	return fmt.Sprintf("counted(%d)", c.n)
}

// CheckReport is the work one check performed. Each field's increment event is the rule of the
// same name in rs report.rs; the three node kinds sum to NodesWalked, a checked invariant
// (NodeKindsSum). A plain comparable value. rs CheckReport.
type CheckReport struct {
	// CountersVersion is the checker version whose counting rules these counters follow.
	CountersVersion uint32
	// NodesWalked counts each derivation node visited, up to and including a rejecting node.
	NodesWalked ReportCount
	// RuleNodes counts each Rule node visited.
	RuleNodes ReportCount
	// BuiltinNodes counts each Builtin node visited.
	BuiltinNodes ReportCount
	// LeafNodes counts each Leaf node visited.
	LeafNodes ReportCount
	// PremisesPos counts each positive premise examined (a count premise is positive).
	PremisesPos ReportCount
	// PremisesNeg counts each negative premise examined.
	PremisesNeg ReportCount
	// TheoryDecisions counts each call to a theory's DecideGround.
	TheoryDecisions ReportCount
	// LeafVerifications counts each leaf-verifier call.
	LeafVerifications ReportCount
	// AdmissibilityChecks counts each rule-admissibility test.
	AdmissibilityChecks ReportCount
	// CertsVerified counts each closed-model certificate verified (a memo hit is not a
	// verification).
	CertsVerified ReportCount
	// CertsMemoHits counts each certificate whose verification the world memo answered instead.
	CertsMemoHits ReportCount
	// CertTablesRead counts each certificate table read during verification.
	CertTablesRead ReportCount
	// CertRowsRead counts each certificate row read during verification.
	CertRowsRead ReportCount
	// JoinStepsUsed is the closure join steps actually spent (beside the declared MaxJoinSteps
	// budget).
	JoinStepsUsed ReportCount
	// GroundingsEnumerated is the rule groundings actually enumerated (beside the declared
	// MaxRuleGroundings).
	GroundingsEnumerated ReportCount
	// MaxDepthReached is the deepest derivation depth reached.
	MaxDepthReached ReportCount
	// MaxTermDepthReached is the deepest term depth reached.
	MaxTermDepthReached ReportCount
}

// ZeroCheckReport is a report under the current counting rules with every counter at zero: what a
// check refused before its walk reports. rs CheckReport::zero.
func ZeroCheckReport() CheckReport {
	return CheckReport{CountersVersion: CheckReportCountersVersion}
}

// NodeKindsSum reports RuleNodes + BuiltinNodes + LeafNodes == NodesWalked, where all four are
// counted (and true where none is). rs CheckReport::node_kinds_sum.
func (r CheckReport) NodeKindsSum() bool {
	n, nOK := r.NodesWalked.Get()
	rule, ruleOK := r.RuleNodes.Get()
	builtin, builtinOK := r.BuiltinNodes.Get()
	leaf, leafOK := r.LeafNodes.Get()
	switch {
	case nOK && ruleOK && builtinOK && leafOK:
		return rule+builtin+leaf == n
	case !nOK && !ruleOK && !builtinOK && !leafOK:
		return true
	default:
		return false
	}
}

// checkTally is one check's running counts (#3111): plain counters the checker bumps at the points
// rs report.rs names, turned into the CheckReport of the Outcome once the check ends. Private to
// the checker, and threaded through it as *checkTally. rs Tally.
type checkTally struct {
	nodesWalked          int
	ruleNodes            int
	builtinNodes         int
	leafNodes            int
	premisesPos          int
	premisesNeg          int
	theoryDecisions      int
	leafVerifications    int
	admissibilityChecks  int
	certsVerified        int
	certsMemoHits        int
	certTablesRead       int
	certRowsRead         int
	joinStepsUsed        int
	groundingsEnumerated int
	maxDepthReached      int
	maxTermDepthReached  int
}

// premise counts premises_pos / premises_neg: one premise examined, by its kind (a count is
// positive). A premise of no known kind is refused by the shape boundary before the walk, so it is
// never examined here.
func (t *checkTally) premise(p Premise) {
	switch p.(type) {
	case PosPremise, CountPremise:
		t.premisesPos++
	case NegPremise:
		t.premisesNeg++
	}
}

// reachDepth counts max_depth_reached: one derivation depth compared against MaxDepth.
func (t *checkTally) reachDepth(depth int) {
	t.maxDepthReached = max(t.maxDepthReached, depth)
}

// termWithin counts max_term_depth_reached: measure term against limit; true when it is within.
func (t *checkTally) termWithin(term Term, limit int) bool {
	return t.reachTermDepth(termDepthCapped(term, limit), limit)
}

// valueWithin counts max_term_depth_reached: measure value against limit; true when it is within.
func (t *checkTally) valueWithin(value core.Value, limit int) bool {
	return t.reachTermDepth(valueDepthCapped(value, limit), limit)
}

func (t *checkTally) reachTermDepth(depth, limit int) bool {
	t.maxTermDepthReached = max(t.maxTermDepthReached, depth)
	return depth <= limit
}

// outcome is the check's result: verdict, with the report of the work counted so far.
func (t *checkTally) outcome(verdict Verdict) Outcome {
	return Outcome{Verdict: verdict, Report: t.report()}
}

// report is the CheckReport: every counter Counted, since go counts all of them. Every field is
// named, in the order of the struct; a new counter is placed here and in checkTally together.
func (t *checkTally) report() CheckReport {
	return CheckReport{
		CountersVersion:      CheckReportCountersVersion,
		NodesWalked:          Counted(t.nodesWalked),
		RuleNodes:            Counted(t.ruleNodes),
		BuiltinNodes:         Counted(t.builtinNodes),
		LeafNodes:            Counted(t.leafNodes),
		PremisesPos:          Counted(t.premisesPos),
		PremisesNeg:          Counted(t.premisesNeg),
		TheoryDecisions:      Counted(t.theoryDecisions),
		LeafVerifications:    Counted(t.leafVerifications),
		AdmissibilityChecks:  Counted(t.admissibilityChecks),
		CertsVerified:        Counted(t.certsVerified),
		CertsMemoHits:        Counted(t.certsMemoHits),
		CertTablesRead:       Counted(t.certTablesRead),
		CertRowsRead:         Counted(t.certRowsRead),
		JoinStepsUsed:        Counted(t.joinStepsUsed),
		GroundingsEnumerated: Counted(t.groundingsEnumerated),
		MaxDepthReached:      Counted(t.maxDepthReached),
		MaxTermDepthReached:  Counted(t.maxTermDepthReached),
	}
}
