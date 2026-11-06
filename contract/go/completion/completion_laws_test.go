// The completion algebra's laws, checked over EVERY ground outcome its vocabulary can form (research
// 0031 row 15, #3164; seat:caa's ruling on #3179): the Go twin of contract/rs/tests/completion_laws.rs.
// The carrier is finite, so each law is checked over every pair or triple, not a sample. The Kleene
// tables and the legal kind/scope pairs are written out independently of the implementation.
//
// It also checks what only Go and TypeScript can express: a value no exported constructor builds
// legally (a zero value, an unknown code, a stop without a scope) is read as the fault
// malformed_outcome, and never as an answer. This is an external test, so it sees only the exported
// API, as a caller does.
package completion_test

import (
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
)

type outcome = completion.GroundOutcome[string]

var (
	scopes = []completion.CauseScope{
		completion.ScopeLiteral, completion.ScopeBranch, completion.ScopeEnumeration,
		completion.ScopeDependency, completion.ScopeTheorySnapshot, completion.ScopeRequest,
	}
	kinds = []completion.NonCompletionKind{
		completion.KindCapacity, completion.KindWorkCap, completion.KindInstantiation,
		completion.KindHostRefusal, completion.KindReplyUnreadable,
		completion.KindInconsistentTheory, completion.KindMalformedOutcome,
	}
)

// legalPair is the ruling's table, written independently of NewCause. (An if chain, not a switch:
// an external test cannot name the unexported invalid kind the census would require.)
func legalPair(k completion.NonCompletionKind, s completion.CauseScope) bool {
	if k == completion.KindCapacity || k == completion.KindWorkCap || k == completion.KindInstantiation {
		return s != completion.NoScope
	}
	if k == completion.KindHostRefusal || k == completion.KindReplyUnreadable {
		return s == completion.ScopeRequest
	}
	if k == completion.KindInconsistentTheory || k == completion.KindMalformedOutcome {
		return s == completion.NoScope
	}
	return false
}

func allScopes() []completion.CauseScope {
	return append([]completion.CauseScope{completion.NoScope}, scopes...)
}

func carrier() []outcome {
	all := []outcome{
		completion.Completed[completion.Decision, string](completion.Holds()),
		completion.Completed[completion.Decision, string](completion.Fails(completion.FalseUnsatisfied)),
		completion.LimitExceeded[completion.Decision, string]("limit_a"),
		completion.LimitExceeded[completion.Decision, string]("limit_b"),
	}
	for _, k := range kinds {
		for _, s := range allScopes() {
			if c, err := completion.NewCause(k, s); err == nil {
				all = append(all, completion.NotCompleted[completion.Decision, string](c))
			}
		}
	}
	return all
}

type truth int

const (
	tTrue truth = iota
	tFalse
	tUndecided
)

// read reads an outcome's truth and tier (0 decided or absorbable, 1 a dominant stop or a limit,
// 2 a fault) through the exported eliminator.
type read struct{}

type reading struct {
	truth truth
	tier  int
	text  string
}

func (read) Holds() reading { return reading{tTrue, 0, "holds"} }
func (read) Fails(c completion.FalseCode) reading {
	return reading{tFalse, 0, "fails(" + c.Tag() + ")"}
}
func (read) LimitExceeded(l string) reading { return reading{tUndecided, 1, "limit(" + l + ")"} }
func (read) NotCompleted(c completion.NonCompletion) reading {
	text := "not_completed(" + c.Kind().Tag() + "," + c.Scope().Tag() + ")"
	switch {
	case c.Kind().IsFault():
		return reading{tUndecided, 2, text}
	case c.Scope().Absorbable():
		return reading{tUndecided, 0, text}
	default:
		return reading{tUndecided, 1, text}
	}
}

func of(o outcome) reading { return completion.MatchOutcome[string, reading](o, read{}) }

func show(o outcome) string { return of(o).text }

func class(o outcome) [2]int { r := of(o); return [2]int{int(r.truth), r.tier} }

func kNot(a truth) truth {
	switch a {
	case tTrue:
		return tFalse
	case tFalse:
		return tTrue
	case tUndecided:
		return tUndecided
	default:
		return tUndecided
	}
}

func kAnd(a, b truth) truth {
	if a == tFalse || b == tFalse {
		return tFalse
	}
	if a == tUndecided || b == tUndecided {
		return tUndecided
	}
	return tTrue
}

func kOr(a, b truth) truth {
	if a == tTrue || b == tTrue {
		return tTrue
	}
	if a == tUndecided || b == tUndecided {
		return tUndecided
	}
	return tFalse
}

var (
	not = completion.Not[string]
	and = completion.And[string]
	or  = completion.Or[string]
	ops = []func(outcome, outcome) outcome{and, or}
)

func TestCompletionTheConstructorBuildsExactlyTheLegalPairs(t *testing.T) {
	for _, k := range kinds {
		for _, s := range allScopes() {
			c, err := completion.NewCause(k, s)
			if (err == nil) != legalPair(k, s) {
				t.Errorf("NewCause(%s, %q): err=%v, legal=%v", k.Tag(), s.Tag(), err, legalPair(k, s))
			}
			if err == nil && (c.Kind() != k || c.Scope() != s) {
				t.Errorf("NewCause(%s, %q) built %s", k.Tag(), s.Tag(), show(completion.NotCompleted[completion.Decision, string](c)))
			}
		}
		if k.IsFault() != legalPair(k, completion.NoScope) {
			t.Errorf("%s: a fault is exactly a kind with no scope", k.Tag())
		}
	}
	if completion.HostRefusal().Scope() != completion.ScopeRequest || completion.ReplyUnreadable().Scope() != completion.ScopeRequest {
		t.Error("a host refusal and an unreadable reply are request-wide")
	}
	if completion.InconsistentTheory().Scope() != completion.NoScope || completion.MalformedOutcome().Scope() != completion.NoScope {
		t.Error("a fault carries no scope")
	}
}

func TestCompletionCarrierIsTheWholeVocabulary(t *testing.T) {
	if n := len(carrier()); n != 26 {
		t.Fatalf("carrier has %d outcomes, want 26 (2 decisions + 2 limits + 3 scoped stops x 6 scopes + 2 request stops + 2 faults)", n)
	}
}

func TestCompletionNegationIsStrongKleeneAndAnInvolution(t *testing.T) {
	for _, a := range carrier() {
		if of(not(a)).truth != kNot(of(a).truth) {
			t.Errorf("not %s", show(a))
		}
		if not(not(a)) != a {
			t.Errorf("not not %s = %s", show(a), show(not(not(a))))
		}
		if of(a).truth == tUndecided && not(a) != a {
			t.Errorf("not changed the undecided %s", show(a))
		}
	}
}

func TestCompletionIdempotence(t *testing.T) {
	for _, a := range carrier() {
		if and(a, a) != a || or(a, a) != a {
			t.Errorf("%s is not idempotent", show(a))
		}
	}
}

func TestCompletionCommutativityOfTheClass(t *testing.T) {
	for _, a := range carrier() {
		for _, b := range carrier() {
			for _, f := range ops {
				ab, ba := f(a, b), f(b, a)
				if class(ab) != class(ba) {
					t.Errorf("%s, %s: class depends on order", show(a), show(b))
				}
				if class(a) != class(b) && ab != ba {
					t.Errorf("%s, %s: one operand outranks the other, so the result must not depend on order", show(a), show(b))
				}
			}
		}
	}
}

func TestCompletionAssociativityIsExact(t *testing.T) {
	all := carrier()
	for _, a := range all {
		for _, b := range all {
			for _, c := range all {
				if and(and(a, b), c) != and(a, and(b, c)) {
					t.Errorf("and is not associative at %s %s %s", show(a), show(b), show(c))
				}
				if or(or(a, b), c) != or(a, or(b, c)) {
					t.Errorf("or is not associative at %s %s %s", show(a), show(b), show(c))
				}
			}
		}
	}
}

func TestCompletionDeMorganIsExact(t *testing.T) {
	for _, a := range carrier() {
		for _, b := range carrier() {
			if not(and(a, b)) != or(not(a), not(b)) || not(or(a, b)) != and(not(a), not(b)) {
				t.Errorf("De Morgan fails at %s, %s", show(a), show(b))
			}
		}
	}
}

func TestCompletionWithoutADominantOperandTheTruthIsStrongKleene(t *testing.T) {
	for _, a := range carrier() {
		for _, b := range carrier() {
			if of(a).tier != 0 || of(b).tier != 0 {
				continue
			}
			ta, tb := of(a).truth, of(b).truth
			if of(and(a, b)).truth != kAnd(ta, tb) || of(or(a, b)).truth != kOr(ta, tb) {
				t.Errorf("Kleene table fails at %s, %s", show(a), show(b))
			}
			if of(and(a, or(a, b))).truth != ta || of(or(a, and(a, b))).truth != ta {
				t.Errorf("lattice absorption fails at %s, %s", show(a), show(b))
			}
		}
	}
}

func TestCompletionTheHighestTierIsNeverAbsorbed(t *testing.T) {
	for _, a := range carrier() {
		for _, b := range carrier() {
			top := max(of(a).tier, of(b).tier)
			if top == 0 {
				continue
			}
			leftmost := b
			if of(a).tier == top {
				leftmost = a
			}
			if and(a, b) != leftmost || or(a, b) != leftmost {
				t.Errorf("%s, %s: the leftmost operand of the highest tier must be the result", show(a), show(b))
			}
		}
	}
}

// The absorption criterion (advice §3): a decided result must not rely on how an undecided operand
// would resolve.
func TestCompletionADecidedResultDoesNotDependOnAnUndecidedOperand(t *testing.T) {
	decided := []outcome{
		completion.Completed[completion.Decision, string](completion.Holds()),
		completion.Completed[completion.Decision, string](completion.Fails(completion.FalseUnsatisfied)),
	}
	for _, a := range carrier() {
		for _, b := range carrier() {
			for _, f := range ops {
				r := of(f(a, b)).truth
				if r == tUndecided {
					continue
				}
				for _, d := range decided {
					if of(a).truth == tUndecided && of(f(d, b)).truth != r {
						t.Errorf("%s, %s: resolving the left operand to %s changes the decided result", show(a), show(b), show(d))
					}
					if of(b).truth == tUndecided && of(f(a, d)).truth != r {
						t.Errorf("%s, %s: resolving the right operand to %s changes the decided result", show(a), show(b), show(d))
					}
				}
			}
		}
	}
}

// ---- values no exported constructor builds legally ----

func TestCompletionAnInvalidValueIsAMalformedFaultNeverAnAnswer(t *testing.T) {
	malformed := completion.NotCompleted[completion.Decision, string](completion.MalformedOutcome())
	fails := completion.Completed[completion.Decision, string](completion.Fails(completion.FalseUnsatisfied))
	holds := completion.Completed[completion.Decision, string](completion.Holds())
	limit := completion.LimitExceeded[completion.Decision, string]("limit_a")
	invalid := map[string]outcome{
		"the zero outcome":             {},
		"a zero decision":              completion.Completed[completion.Decision, string](completion.Decision{}),
		"a fails with no code":         completion.Completed[completion.Decision, string](completion.Fails(completion.FalseCode(0))),
		"a fails with an unknown code": completion.Completed[completion.Decision, string](completion.Fails(completion.FalseCode(200))),
		"a zero cause":                 completion.NotCompleted[completion.Decision, string](completion.NonCompletion{}),
		"a stop with no scope":         completion.NotCompleted[completion.Decision, string](completion.Capacity(completion.NoScope)),
		"a stop at an unknown scope":   completion.NotCompleted[completion.Decision, string](completion.WorkCap(completion.CauseScope(200))),
	}
	for name, v := range invalid {
		if got := show(v); got != "not_completed(malformed_outcome,)" {
			t.Errorf("%s reads as %s", name, got)
		}
		// A malformed value is a fault: it outranks a limit and is absorbed by nothing.
		for _, r := range []outcome{not(v), and(fails, v), and(v, fails), or(holds, v), or(v, holds), and(limit, v), and(v, limit)} {
			if r != malformed {
				t.Errorf("%s: a combinator returned %s, not the malformed fault", name, show(r))
			}
		}
	}
}

type arms struct{}

func (arms) Completed(completion.Decision) string { return "completed" }
func (arms) LimitExceeded(string) string          { return "limit_exceeded" }
func (arms) NotCompleted(c completion.NonCompletion) string {
	return "not_completed(" + c.Kind().Tag() + "," + c.Scope().Tag() + ")"
}

func TestCompletionMatchReadsAZeroValueAsMalformed(t *testing.T) {
	if got := completion.Match[completion.Decision, string, string](outcome{}, arms{}); got != "not_completed(malformed_outcome,)" {
		t.Fatalf("Match read the zero value as %s", got)
	}
}
