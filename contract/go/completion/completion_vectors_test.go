// Go replay of vectors/completion_algebra.json, the completion algebra's Not/And/Or (research 0031
// row 15, #3164; seat:caa's ruling on #3179). The same file is replayed by Rust
// (contract/rs/tests/completion_vectors.rs) and TypeScript (contract/ts/test/completion_vectors.test.ts).
//
// Each case is checked twice: the written operand order must give `expect` exactly, and every
// reordering of every and/or node's operands must give an outcome of the same class. A case with
// `construct` names a kind and scope NewCause must refuse; this is an internal test so it can also
// hand-build that illegal value, as only code inside the package can, and check that the
// eliminators read it as malformed_outcome. The replay is also run against three deliberately wrong
// algebras (one that never absorbs, one that absorbs a request-scope stop, one that ranks a fault
// with a limit) and must reject each: the broken counterparts design/0004 §7.7 asks for.
package completion

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

type outcome = GroundOutcome[string]

type algebra struct {
	not func(outcome) outcome
	and func(outcome, outcome) outcome
	or  func(outcome, outcome) outcome
}

var correct = algebra{not: Not[string], and: And[string], or: Or[string]}

type vectorFile struct {
	Vocabulary struct {
		FalseCodes       []string `json:"false_codes"`
		Kinds            []string `json:"kinds"`
		Scopes           []string `json:"scopes"`
		AbsorbableScopes []string `json:"absorbable_scopes"`
		ScopedStops      []string `json:"scoped_stops"`
		RequestStops     []string `json:"request_stops"`
		Faults           []string `json:"faults"`
	} `json:"vocabulary"`
	Cases []struct {
		Name      string          `json:"name"`
		Why       string          `json:"why"`
		Construct *node           `json:"construct"`
		Refused   bool            `json:"refused"`
		Expr      json.RawMessage `json:"expr"`
		Expect    json.RawMessage `json:"expect"`
	} `json:"cases"`
}

type node struct {
	Arm   string            `json:"arm"`
	Code  string            `json:"false_code"`
	Kind  string            `json:"kind"`
	Scope string            `json:"scope"`
	Limit string            `json:"limit"`
	Op    string            `json:"op"`
	Args  []json.RawMessage `json:"args"`
}

func loadVectors(t *testing.T) vectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "completion_algebra.json")
		if raw, err := os.ReadFile(candidate); err == nil {
			var vf vectorFile
			if err := json.Unmarshal(raw, &vf); err != nil {
				t.Fatalf("unmarshal %s: %v", candidate, err)
			}
			return vf
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("could not locate vectors/completion_algebra.json")
		}
		dir = parent
	}
}

// The vocabulary, each list written out; TestCompletionVocabularyMatchesTheVector compares it with
// the vector's.
var (
	scopes = []CauseScope{
		ScopeLiteral, ScopeBranch, ScopeEnumeration, ScopeDependency, ScopeTheorySnapshot, ScopeRequest,
	}
	kinds = []NonCompletionKind{
		KindCapacity, KindWorkCap, KindInstantiation, KindHostRefusal, KindReplyUnreadable,
		KindInconsistentTheory, KindMalformedOutcome,
	}
	falseCodes = []FalseCode{FalseUnsatisfied}
)

func scopeOf(t *testing.T, tag string) CauseScope {
	if tag == "" {
		return NoScope
	}
	for _, s := range scopes {
		if s.Tag() == tag {
			return s
		}
	}
	t.Fatalf("unknown scope %q", tag)
	return NoScope
}

func kindOf(t *testing.T, tag string) NonCompletionKind {
	for _, k := range kinds {
		if k.Tag() == tag {
			return k
		}
	}
	t.Fatalf("unknown kind %q", tag)
	return kindInvalid
}

func codeOf(t *testing.T, tag string) FalseCode {
	for _, c := range falseCodes {
		if c.Tag() == tag {
			return c
		}
	}
	t.Fatalf("unknown false code %q", tag)
	return falseCodeInvalid
}

func parse(t *testing.T, raw json.RawMessage) node {
	t.Helper()
	var n node
	if err := json.Unmarshal(raw, &n); err != nil {
		t.Fatalf("parse %s: %v", raw, err)
	}
	return n
}

// leaf builds a leaf. A not_completed leaf goes through NewCause; with handBuilt, an illegal pair
// is built directly instead, as only code inside this package can.
func leaf(t *testing.T, n node, handBuilt bool) outcome {
	t.Helper()
	switch n.Arm {
	case "holds":
		return Completed[Decision, string](Holds())
	case "fails":
		return Completed[Decision, string](Fails(codeOf(t, n.Code)))
	case "not_completed":
		kind, scope := kindOf(t, n.Kind), scopeOf(t, n.Scope)
		c, err := NewCause(kind, scope)
		if err != nil {
			if !handBuilt {
				t.Fatalf("a vector leaf must be constructible: %v", err)
			}
			c = NonCompletion{kind: kind, scope: scope}
		}
		return NotCompleted[Decision, string](c)
	case "limit_exceeded":
		return LimitExceeded[Decision, string](n.Limit)
	}
	t.Fatalf("unknown arm %q", n.Arm)
	return outcome{}
}

// render is an outcome's text, the class plus its payload, for messages.
type render struct{}

func (render) Holds() string                 { return "holds" }
func (render) Fails(c FalseCode) string      { return "fails(" + c.Tag() + ")" }
func (render) LimitExceeded(l string) string { return "limit_exceeded(" + l + ")" }
func (render) NotCompleted(c NonCompletion) string {
	return "not_completed(" + c.Kind().Tag() + "," + c.Scope().Tag() + ")"
}

func show(o outcome) string { return MatchOutcome[string, string](o, render{}) }

// classes names an outcome's class: the part that must not depend on operand order.
type classes struct{}

func (classes) Holds() string               { return "holds" }
func (classes) Fails(FalseCode) string      { return "fails" }
func (classes) LimitExceeded(string) string { return "dominant" }
func (classes) NotCompleted(c NonCompletion) string {
	if c.Kind().IsFault() {
		return "fault"
	}
	if c.Scope().Absorbable() {
		return "absorbable"
	}
	return "dominant"
}

func classNameOf(o outcome) string { return MatchOutcome[string, string](o, classes{}) }

func fold(alg algebra, op string, operands []outcome) outcome {
	combine := alg.and
	if op == "or" {
		combine = alg.or
	}
	acc := operands[0]
	for _, o := range operands[1:] {
		acc = combine(acc, o)
	}
	return acc
}

func eval(t *testing.T, alg algebra, raw json.RawMessage, handBuilt bool) outcome {
	n := parse(t, raw)
	if n.Arm != "" {
		return leaf(t, n, handBuilt)
	}
	var operands []outcome
	for _, a := range n.Args {
		operands = append(operands, eval(t, alg, a, handBuilt))
	}
	switch n.Op {
	case "not":
		return alg.not(operands[0])
	case "and", "or":
		return fold(alg, n.Op, operands)
	}
	t.Fatalf("unknown op %q", n.Op)
	return outcome{}
}

func permutations(n int) [][]int {
	if n == 0 {
		return [][]int{{}}
	}
	var out [][]int
	for _, rest := range permutations(n - 1) {
		for at := 0; at <= len(rest); at++ {
			p := append(append(append([]int{}, rest[:at]...), n-1), rest[at:]...)
			out = append(out, p)
		}
	}
	return out
}

// evalEveryOrder is the expression under every reordering of every and/or node's operands.
func evalEveryOrder(t *testing.T, alg algebra, raw json.RawMessage, handBuilt bool) []outcome {
	n := parse(t, raw)
	if n.Arm != "" {
		return []outcome{leaf(t, n, handBuilt)}
	}
	var children [][]outcome
	for _, a := range n.Args {
		children = append(children, evalEveryOrder(t, alg, a, handBuilt))
	}
	if n.Op == "not" {
		var out []outcome
		for _, o := range children[0] {
			out = append(out, alg.not(o))
		}
		return out
	}
	var out []outcome
	for _, order := range permutations(len(children)) {
		combos := [][]outcome{{}}
		for _, i := range order {
			var next [][]outcome
			for _, combo := range combos {
				for _, o := range children[i] {
					next = append(next, append(append([]outcome{}, combo...), o))
				}
			}
			combos = next
		}
		for _, c := range combos {
			out = append(out, fold(alg, n.Op, c))
		}
	}
	return out
}

func replay(t *testing.T, alg algebra) []string {
	vf := loadVectors(t)
	var failures []string
	for _, c := range vf.Cases {
		// Every failure carries the case's why, so the reader sees what the case pins.
		c.Name = c.Name + " (" + c.Why + ")"
		handBuilt := c.Construct != nil
		if handBuilt {
			if !c.Refused {
				t.Fatalf("%s: a construct case must say refused: true", c.Name)
			}
			if got, err := NewCause(kindOf(t, c.Construct.Kind), scopeOf(t, c.Construct.Scope)); err == nil {
				failures = append(failures, fmt.Sprintf("%s: NewCause built %s", c.Name, show(NotCompleted[Decision, string](got))))
				continue
			}
		}
		expect := leaf(t, parse(t, c.Expect), false)
		got := eval(t, alg, c.Expr, handBuilt)
		if got != expect {
			failures = append(failures, fmt.Sprintf("%s: written order gave %s, expected %s", c.Name, show(got), show(expect)))
			continue
		}
		for _, o := range evalEveryOrder(t, alg, c.Expr, handBuilt) {
			if classNameOf(o) != classNameOf(expect) {
				failures = append(failures, fmt.Sprintf("%s: a reordering gave %s, class %s instead of %s", c.Name, show(o), classNameOf(o), classNameOf(expect)))
				break
			}
		}
	}
	return failures
}

func TestCompletionVectorsReplay(t *testing.T) {
	vf := loadVectors(t)
	if len(vf.Cases) < 55 {
		t.Fatalf("expected the full vector, loaded %d cases", len(vf.Cases))
	}
	if failures := replay(t, correct); len(failures) > 0 {
		t.Fatalf("%d of %d cases fail:\n%s", len(failures), len(vf.Cases), strings.Join(failures, "\n"))
	}
}

func TestCompletionVocabularyMatchesTheVector(t *testing.T) {
	vf := loadVectors(t)
	accepts := func(k NonCompletionKind, s CauseScope) bool { _, err := NewCause(k, s); return err == nil }
	var scopeTags, absorbable, kindTags, codeTags, scoped, request, faults []string
	for _, s := range scopes {
		scopeTags = append(scopeTags, s.Tag())
		if s.Absorbable() {
			absorbable = append(absorbable, s.Tag())
		}
	}
	for _, k := range kinds {
		kindTags = append(kindTags, k.Tag())
		switch {
		case accepts(k, ScopeLiteral):
			scoped = append(scoped, k.Tag())
		case accepts(k, ScopeRequest):
			request = append(request, k.Tag())
		case accepts(k, NoScope) && k.IsFault():
			faults = append(faults, k.Tag())
		}
	}
	for _, c := range falseCodes {
		codeTags = append(codeTags, c.Tag())
	}
	for _, pair := range []struct {
		name      string
		got, want []string
	}{
		{"scopes", scopeTags, vf.Vocabulary.Scopes},
		{"absorbable_scopes", absorbable, vf.Vocabulary.AbsorbableScopes},
		{"kinds", kindTags, vf.Vocabulary.Kinds},
		{"false_codes", codeTags, vf.Vocabulary.FalseCodes},
		{"scoped_stops", scoped, vf.Vocabulary.ScopedStops},
		{"request_stops", request, vf.Vocabulary.RequestStops},
		{"faults", faults, vf.Vocabulary.Faults},
	} {
		if !reflect.DeepEqual(pair.got, pair.want) {
			t.Errorf("%s: Go declares %v, the vector %v", pair.name, pair.got, pair.want)
		}
	}
}

// ---- the broken counterparts ----

func mutant(rank func(outcome) int) func(outcome, outcome) outcome {
	return func(a, b outcome) outcome {
		if rank(b) > rank(a) {
			return b
		}
		return a
	}
}

func rankBy(read func(outcome) string, order ...string) func(outcome) int {
	return func(o outcome) int {
		for i, c := range order {
			if c == read(o) {
				return i
			}
		}
		return len(order)
	}
}

// neverAbsorbs ranks an undecided operand above a decided one in And and in Or.
var neverAbsorbs = algebra{
	not: Not[string],
	and: mutant(rankBy(classNameOf, "holds", "fails", "absorbable", "dominant", "fault")),
	or:  mutant(rankBy(classNameOf, "fails", "holds", "absorbable", "dominant", "fault")),
}

// everyScope reads every stop as absorbable, wherever it reaches.
func everyScope(o outcome) string {
	c := classNameOf(o)
	if c == "dominant" && o.arm == armNotCompleted {
		return "absorbable"
	}
	return c
}

var absorbsEveryScope = algebra{
	not: Not[string],
	and: mutant(rankBy(everyScope, "holds", "absorbable", "fails", "dominant", "fault")),
	or:  mutant(rankBy(everyScope, "fails", "absorbable", "holds", "dominant", "fault")),
}

// faultAsDominant ranks a fault with a limit, as before seat:caa's ruling on #3179.
func faultAsDominant(o outcome) string {
	if c := classNameOf(o); c != "fault" {
		return c
	}
	return "dominant"
}

var noFaultClass = algebra{
	not: Not[string],
	and: mutant(rankBy(faultAsDominant, "holds", "absorbable", "fails", "dominant")),
	or:  mutant(rankBy(faultAsDominant, "fails", "absorbable", "holds", "dominant")),
}

func assertRejected(t *testing.T, alg algebra, mutantName, mustFail string) {
	t.Helper()
	failures := replay(t, alg)
	for _, f := range failures {
		if strings.HasPrefix(f, mustFail+" (") {
			return
		}
	}
	t.Errorf("the vector must reject the %s mutant at %s; it failed only:\n%s", mutantName, mustFail, strings.Join(failures, "\n"))
}

func TestCompletionVectorsRejectAnAlgebraThatNeverAbsorbs(t *testing.T) {
	assertRejected(t, neverAbsorbs, "never-absorbs", "and_fails_absorbs_literal_undecided")
	assertRejected(t, neverAbsorbs, "never-absorbs", "or_holds_absorbs_literal_undecided")
}

func TestCompletionVectorsRejectAnAlgebraThatAbsorbsARequestStop(t *testing.T) {
	assertRejected(t, absorbsEveryScope, "absorbs-request-scope", "and_fails_keeps_request_undecided")
	assertRejected(t, absorbsEveryScope, "absorbs-request-scope", "or_holds_keeps_request_undecided")
}

func TestCompletionVectorsRejectAnAlgebraThatRanksAFaultWithALimit(t *testing.T) {
	assertRejected(t, noFaultClass, "no-fault-class", "and_limit_then_fault_reports_fault")
	assertRejected(t, noFaultClass, "no-fault-class", "and_fault_then_limit_reports_fault")
}
