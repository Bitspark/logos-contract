package contract_test

import (
	"math"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

// test-double: consumer(a verifier that counts positive leaf attestations)
type proofBudgetLeaves struct{ calls int }

func (*proofBudgetLeaves) Extensional() *contract.PredicateSet {
	return contract.PredicateSetOf("fact")
}
func (l *proofBudgetLeaves) Verify(contract.GroundLiteral, contract.Evidence, struct{}) contract.LeafOutcome {
	l.calls++
	return contract.LeafAdmit{}
}

func TestPublicCheckerProofBudgetDomain(t *testing.T) {
	program := contract.NewMapProgram()
	claim := contract.NewGroundLiteral("fact")
	proof := contract.NewDerivation([]contract.Node{contract.LeafNode{Conc: claim, Evidence: contract.NoEvidence()}}, 0)
	check := func(limits contract.CheckLimits, memo bool) (contract.Outcome, int) {
		leaves := &proofBudgetLeaves{}
		profile := &contract.CheckProfile[struct{}]{
			Theory: contract.NewStandardTheory(), Leaves: leaves, Admit: contract.AlwaysAdmit[struct{}]{}, Limits: limits,
		}
		if memo {
			cache := contract.NewWorldMemo(program, profile, struct{}{}, contract.ZeroCertContext())
			out := contract.CheckWithWorldMemo(cache, claim, proof)
			return out, leaves.calls
		}
		out := contract.Check(program, claim, proof, struct{}{}, profile)
		return out, leaves.calls
	}

	for _, path := range []string{"direct", "memo"} {
		memo := path == "memo"
		t.Run(path, func(t *testing.T) {
			base := contract.DefaultLimits()
			for i, budget := range base.Budgets() {
				t.Run(budget.Name, func(t *testing.T) {
					invalid := base
					*invalid.Budgets()[i].Value = -1
					out, calls := check(invalid, memo)
					if out.IsAccept() || out.Verdict.Code().Code() != "invalid_check_limits" || calls != 0 {
						t.Fatalf("negative %s: verdict %+v, verifier called %d times", budget.Name, out, calls)
					}
					above := contract.IndexMax + 1
					if above <= uint64(math.MaxInt) {
						*invalid.Budgets()[i].Value = int(above)
						out, calls = check(invalid, memo)
						if out.IsAccept() || out.Verdict.Code() != contract.InvalidCheckLimits || calls != 0 {
							t.Fatalf("out-of-domain %s: verdict %+v, verifier called %d times", budget.Name, out, calls)
						}
					}
				})
			}
			base.MaxNodes = 0
			out, calls := check(base, memo)
			if out.IsAccept() || out.Verdict.Code() != contract.TooManyNodes || calls != 0 {
				t.Fatalf("zero cap: verdict %+v, calls %d", out, calls)
			}
			for _, n := range []int{1, int(min(uint64(math.MaxInt), contract.IndexMax))} {
				base.MaxNodes, base.MaxDepth = n, n
				if result, calls := check(base, memo); !result.IsAccept() || calls != 1 {
					t.Fatalf("cap %d: verdict %+v, calls %d", n, result, calls)
				}
			}
		})
	}
}
