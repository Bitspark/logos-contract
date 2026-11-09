package typed_test

import (
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	"github.com/Bitspark/logos-contract/contract/go/typed"
	core "github.com/bitspark/ontos/core/go"
)

var _ func(typed.Statement, typed.Expr, typed.Policy, typed.Limits) typed.Outcome = typed.Check

func TestGroundValueAndOpenTermPublicConstruction(t *testing.T) {
	v := core.NewTuple(core.NewAtom([]byte("a")))
	term := contract.Tuple(contract.Atom([]byte("a")))
	ground, ok := term.EraseGround()
	if !ok || !core.Equal(v, ground) || !contract.FromValue(v).Equal(term) {
		t.Fatal("ground terms and their Ontos values must agree")
	}
	if _, ok := contract.Tuple(contract.Var("X")).EraseGround(); ok {
		t.Fatal("a term containing a variable cannot erase to an Ontos value")
	}
}

func TestPortableTypedJudgmentAndCapacityNames(t *testing.T) {
	input := typed.Statement{Foundation: typed.Foundation, Expected: typed.Pi(typed.Nat(), typed.Nat())}
	proof := typed.Lam(typed.Nat(), typed.Var(0))
	policy := typed.Policy{Foundation: typed.Foundation, Checker: typed.Checker}
	limits := typed.DefaultLimits()
	if typed.MaxInputDepth != 128 || typed.MaxDepth != 512 || typed.MaxNatural != 0xffffffff ||
		limits.InputDepth != typed.MaxInputDepth || limits.Depth != typed.MaxDepth {
		t.Fatalf("unexpected typed capacities or defaults: %+v", limits)
	}
	out := typed.Check(input, proof, policy, limits)
	var acceptance typed.Acceptance
	acceptance, ok := out.Accepted()
	if !ok || out.Status() != typed.AcceptedStatus || acceptance.Statement().Expected.Kind() != typed.PiKind ||
		acceptance.Candidate().Kind() != typed.LamKind || len(acceptance.Dependencies()) != 0 {
		t.Fatalf("expected the exact identity judgment: %v", out.Status())
	}
	noWork := limits
	noWork.Work = 0
	other := policy
	other.Checker = "unselected"
	universe := typed.Statement{Foundation: typed.Foundation, Expected: typed.Sort(typed.MaxNatural)}
	for _, row := range []struct {
		out    typed.Outcome
		status typed.Status
		code   typed.Code
	}{
		{typed.Check(input, typed.False(), policy, limits), typed.InvalidStatus, typed.TypeMismatch},
		{typed.Check(input, proof, policy, noWork), typed.IncompleteStatus, typed.Work},
		{typed.Check(input, proof, other, limits), typed.UnsupportedStatus, typed.UnadmittedChecker},
		{typed.Check(universe, typed.Sort(typed.MaxNatural-1), policy, limits), typed.IncompleteStatus, typed.UniverseCapacity},
	} {
		if _, ok := row.out.Accepted(); ok || row.out.Status() != row.status || row.out.Code() != row.code {
			t.Fatalf("wanted %s/%s, got %s/%s", row.status, row.code, row.out.Status(), row.out.Code())
		}
	}
}
