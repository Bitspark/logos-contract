// #3123: an arithmetic expression's depth is never a decided false. Until #3123 each core's
// evaluator recursed once per level and stopped at 256 levels, and the stop was read as Fails, so
// `not(1 =:= E)` with E 257 levels deep could be answered and certified. The walk is iterative
// now, so a deep expression evaluates; the only depth limit left is the caller's
// CheckLimits.MaxTermDepth, a completed policy decision Check makes before any theory.
//
// Every witness is placed against arithOldDepthCap and carries a control inside it. The same cases
// are pinned in contract/rs (tests/arithmetic_depth_3123.rs) and contract/ts
// (test/arithmetic_depth_3123.test.ts).
package contract

import (
	"fmt"
	"math/big"
	"runtime/debug"
	"strings"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// arithOldDepthCap is the depth at which the recursive evaluator stopped until #3123: an
// expression whose innermost operand sits one level past it was read as Fails.
const arithOldDepthCap = 256

// arithDepths are the depths every witness runs at: a control inside the old cap, and two past it.
var arithDepths = []struct {
	name   string
	levels int
}{
	{"control, inside the old cap", arithOldDepthCap - 56},
	{"one past the old cap", arithOldDepthCap + 1},
	{"well past the old cap", arithOldDepthCap + 50},
}

func adInt(n int64) core.Value { return data.EncodeInt(big.NewInt(n)) }

// adDeepOne is '+'('+'(… int(1) …, int(0)), int(0)): levels operators over int(1), value 1.
func adDeepOne(levels int) core.Value {
	e := adInt(1)
	for i := 0; i < levels; i++ {
		e = core.NewTuple(core.NewAtom([]byte("+")), e, adInt(0))
	}
	return e
}

func adDecide(pred string, lhs, rhs core.Value) completion.TheoryGround {
	return DecideGround(NewArithmeticTheory(), NewGroundLiteral(pred, lhs, rhs))
}

func adHolds(o completion.TheoryGround) bool {
	return o == completion.TheoryGroundHolds()
}

// The theory decides a deep expression by its value, in both polarities.
func TestTheDeepExpressionIsDecidedByItsValue3123(t *testing.T) {
	var wrong []string
	for _, d := range arithDepths {
		for _, c := range []struct {
			what string
			got  completion.TheoryGround
			want bool
		}{
			{"1 =:= E holds", adDecide("=:=", adInt(1), adDeepOne(d.levels)), true},
			{`2 =\= E holds`, adDecide(`=\=`, adInt(2), adDeepOne(d.levels)), true},
			{`1 =\= E fails`, adDecide(`=\=`, adInt(1), adDeepOne(d.levels)), false},
			{"1 is E holds", adDecide("is", adInt(1), adDeepOne(d.levels)), true},
			{"0 < E holds", adDecide("<", adInt(0), adDeepOne(d.levels)), true},
		} {
			if adHolds(c.got) != c.want {
				wrong = append(wrong, fmt.Sprintf("%s: %s, got %#v", d.name, c.what, c.got))
			}
		}
	}
	if len(wrong) > 0 {
		t.Fatal(strings.Join(wrong, "\n"))
	}
}

// Stack safety: 100,000 levels under a goroutine stack cap far too small for one native frame per
// level. Go grows a goroutine's stack on demand, so without the cap a recursive walk would pass
// here; with it, a recursive walk dies with "goroutine stack exceeds", and the iterative one runs.
func TestAHundredThousandLevelExpressionIsDecidedUnderASmallStackCap3123(t *testing.T) {
	e := adDeepOne(100_000)
	prev := debug.SetMaxStack(1 << 20)
	defer debug.SetMaxStack(prev)
	got := adDecide("=:=", adInt(1), e)
	if !adHolds(got) {
		t.Fatalf("1 =:= E must hold, got %#v", got)
	}
}

// test-double: consumer(an empty extensional set; admits nothing because nothing is a leaf)
type adNoLeaves struct{ extensional *PredicateSet }

func (l adNoLeaves) Extensional() *PredicateSet { return l.extensional }
func (adNoLeaves) Verify(GroundLiteral, Evidence, struct{}) LeafOutcome {
	return LeafReject{Code: "no_leaves"}
}

func adVerdict(o Outcome) string {
	if o.IsAccept() {
		return "accept"
	}
	return o.Verdict.Code().Code() + " (" + o.Verdict.Detail() + ")"
}

func adCode(o Outcome) string {
	if o.IsAccept() {
		return "accept"
	}
	return o.Verdict.Code().Code()
}

// adCheckBuiltin checks one Builtin node concluding pred(lhs, E) under limits.
func adCheckBuiltin(pred string, lhs int64, levels int, limits CheckLimits) Outcome {
	claim := NewGroundLiteral(pred, adInt(lhs), adDeepOne(levels))
	deriv := NewDerivation([]Node{BuiltinNode{Conc: claim}}, 0)
	profile := &CheckProfile[struct{}]{
		Theory: NewArithmeticTheory(),
		Leaves: adNoLeaves{PredicateSetOf()},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: limits,
	}
	return Check[struct{}](NewMapProgram(), claim, deriv, struct{}{}, profile)
}

// A Builtin node past the old cap is either accepted by its value (the caller's budget covers it)
// or refused term_too_deep by that budget. Never builtin_failed for a relation that holds.
func TestADeepBuiltinNodeIsDecidedByValueOrRefusedByTheCallersBudget3123(t *testing.T) {
	wide := DefaultLimits()
	wide.MaxTermDepth = 1_024
	var wrong []string
	for _, d := range arithDepths {
		// Term depth is the operator levels plus 2 (the int leaf is int(Atom)).
		wantDefault := "accept"
		if d.levels+2 > DefaultLimits().MaxTermDepth {
			wantDefault = "term_too_deep"
		}
		for _, c := range []struct {
			what string
			got  Outcome
			want string
		}{
			{"=:=(1, E), default budget", adCheckBuiltin("=:=", 1, d.levels, DefaultLimits()), wantDefault},
			{"=:=(1, E), a budget that covers it", adCheckBuiltin("=:=", 1, d.levels, wide), "accept"},
			{`=\=(2, E), a budget that covers it`, adCheckBuiltin(`=\=`, 2, d.levels, wide), "accept"},
			// The relation is false, decided by a completed evaluation.
			{`=\=(1, E), a budget that covers it`, adCheckBuiltin(`=\=`, 1, d.levels, wide), "builtin_failed"},
		} {
			if adCode(c.got) != c.want {
				wrong = append(wrong, fmt.Sprintf("%s: %s: %s, want %s", d.name, c.what, adVerdict(c.got), c.want))
			}
		}
	}
	if len(wrong) > 0 {
		t.Fatal(strings.Join(wrong, "\n"))
	}
}

// The certified form: a closed-model certificate's closure reads the comparison through
// theoryTruth. Sealing r EMPTY claims r(a) is false; a closure that reads a capacity as false
// accepts that claim, and every negation citing the certificate inherits it.

// adRSealedEmpty verifies one certificate sealing {d, r}, with d = {d(a)} and r EMPTY, over
// program, under the standard arithmetic theory and limits. ctnmLeaves (closure_theory_not_mine_
// 3022_test.go) admits every leaf and attests d's one-row snapshot.
func adRSealedEmpty(program *MapProgram, limits CheckLimits) Outcome {
	d, r := SymbolFromString("d"), SymbolFromString("r")
	pin := Hash{7}
	cert := ClosedModelCert{
		Scope:             NewStratumPrefix(0, []Symbol{d, r}),
		ProgramHash:       ProgramDigestOf(program),
		ProfileHash:       pin,
		CtxHash:           pin,
		TheoryConfigHash:  pin,
		EdbSnapshotHashes: []Hash{EdbTableHash(d, []GroundLiteral{ctnmLit("d")})},
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("v"), []core.Value{core.NewAtom([]byte("a"))})},
		Extensions: []RelationTable{
			NewRelationTable(d, 1, []GroundLiteral{ctnmLit("d")}),
			NewRelationTable(r, 1, nil),
		},
		Supports:   SupportWitness{},
		LimitsDecl: CertSizeDecl{CertFacts: 1, DomainValues: 1, RuleGroundings: 1_000, JoinSteps: 10_000},
	}
	cert.LimitsDecl.CertBytes = CertEncodedBytes(cert)
	profile := &CheckProfile[struct{}]{
		Theory: NewArithmeticTheory(),
		Leaves: ctnmLeaves{PredicateSetOf("d")},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: limits,
	}
	return CheckClosedModelChain(program, []ClosedModelCert{cert}, struct{}{}, profile,
		NewCertContext(ProgramDigestOf(program), pin, pin, pin))
}

// adRIf is `r(X) :- d(X), pred(lhs, E).`; adRUnless is `r(X) :- d(X), \+ pred(lhs, E).`
func adRIf(pred string, lhs int64, levels int) *MapProgram {
	x := Var("X")
	return NewMapProgram().With(NewClauseId("r_if"), NewClauseLits(NewGoal("r", x),
		PosLit(NewGoal("d", x)), PosLit(NewGoal(pred, FromValue(adInt(lhs)), FromValue(adDeepOne(levels))))))
}

func adRUnless(pred string, lhs int64, levels int) *MapProgram {
	x := Var("X")
	return NewMapProgram().With(NewClauseId("r_unless"), NewClauseLits(NewGoal("r", x),
		PosLit(NewGoal("d", x)), NegLit(NewGoal(pred, FromValue(adInt(lhs)), FromValue(adDeepOne(levels))))))
}

// r sealed empty is accepted exactly when the comparison in the clause body, read by value, keeps
// r(a) out of the model; when r(a) is in the model the table is refused as not closed.
//
// Either verdict may instead be term_too_deep, the caller's budget: the chain path does not apply
// MaxTermDepth to the program's clauses today (it measures only the certificate's own data), so at
// the default budget the closure reaches the theory and decides E by value. That gap is a
// budget-enforcement residue named on #3123's PR, not a soundness one, and this test does not pin
// it either way.
func TestACertificateSealingREmptyIsJudgedByTheComparisonsValue3123(t *testing.T) {
	wide := DefaultLimits()
	wide.MaxTermDepth = 1_024
	var wrong []string
	for _, d := range arithDepths {
		for _, limits := range []CheckLimits{DefaultLimits(), wide} {
			for _, c := range []struct {
				clause  string
				program *MapProgram
				rHolds  bool
			}{
				{"r(X) :- d(X), 1 =:= E", adRIf("=:=", 1, d.levels), true},
				{`r(X) :- d(X), 2 =\= E`, adRIf(`=\=`, 2, d.levels), true},
				{`r(X) :- d(X), 1 =\= E`, adRIf(`=\=`, 1, d.levels), false},
				{`r(X) :- d(X), \+ 1 =:= E`, adRUnless("=:=", 1, d.levels), false},
				{`r(X) :- d(X), \+ 2 =:= E`, adRUnless("=:=", 2, d.levels), true},
			} {
				got := adRSealedEmpty(c.program, limits)
				// r(a) in the model: sealing r empty must be refused. Otherwise it is accepted.
				verdict := adCode(got)
				ok := verdict == "term_too_deep" || (c.rHolds && verdict == "cert_not_closed") || (!c.rHolds && verdict == "accept")
				if !ok {
					wrong = append(wrong, fmt.Sprintf("%s, MaxTermDepth %d: %s: %s, r(a) holds=%v",
						d.name, limits.MaxTermDepth, c.clause, adVerdict(got), c.rHolds))
				}
			}
		}
	}
	if len(wrong) > 0 {
		t.Fatal(strings.Join(wrong, "\n"))
	}
}
