// #2759 (seat:caa's design gate): check admits an open compound in a sealed scope inside the
// CONSTRUCTOR-ACYCLIC fragment and refuses one outside it, re-deriving the fragment from the bound
// program. The certificates are vectors/negation.json's hand-authored pair, verified here as a
// CHAIN (the completeness gate's check), and the refusal must NAME the cycle: the function-free gate
// this replaced rejected both with the same code, so the code alone cannot tell them apart.
package contract

import (
	"strings"
	"testing"
)

func chainVectorCase2759(t *testing.T, name string) chainVectorCase {
	t.Helper()
	for _, c := range chainVectorCases(t) {
		if c.name == name {
			return c
		}
	}
	t.Fatalf("vectors/negation.json carries no case %q", name)
	return chainVectorCase{}
}

func TestAConstructorAcyclicSealedScopeVerifies2759(t *testing.T) {
	c := chainVectorCase2759(t, "round3_structural_subterm_closed_accept_2759")
	got := CheckClosedModelChain[unitCtx](c.program, c.certs, unitCtx{}, c.profile, c.cx)
	if !got.IsAccept() {
		t.Fatalf("a closed cert over r(box(box(X))) :- e(box(X)), a constructor on no cycle, must verify; got %s (%s)", got.Verdict.Code().Code(), got.Verdict.Detail())
	}
}

func TestAConstructorCyclicSealedScopeIsRefusedByName2759(t *testing.T) {
	c := chainVectorCase2759(t, "constructor_cycle_stratum_rejects_2759")
	got := CheckClosedModelChain[unitCtx](c.program, c.certs, unitCtx{}, c.profile, c.cx)
	if got.IsAccept() || got.Verdict.Code() != CertScopeIncomplete {
		t.Fatalf("a planted cert over nat(s(X)) :- nat(X), nsmall(X) must be refused cert_scope_incomplete; got accept=%v %s", got.IsAccept(), got.Verdict.Detail())
	}
	if !strings.Contains(got.Verdict.Detail(), `"nat" constructs an open compound`) || !strings.Contains(got.Verdict.Detail(), `dependency cycle through "nat"`) {
		t.Fatalf("the refusal must name the constructor cycle, not the retired function-free gate; got %q", got.Verdict.Detail())
	}
}
