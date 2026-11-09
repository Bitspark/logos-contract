package contract_test

import (
	"reflect"
	"slices"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

// test-double: consumer(reconfigures the next identity report after supplying its own identity)
type advisoryTheory struct {
	contract.Theory
	report func() contract.ComponentIdentity
}

func (t advisoryTheory) Identity() contract.ComponentIdentity { return t.report() }

// test-double: consumer(publishes the independently selected leaf verifier's identity)
type advisoryNamedLeaves struct{ clauseIDLeaves }

func (advisoryNamedLeaves) Identity() contract.ComponentIdentity {
	return bindingIdentity("example/leaves", "1", 1)
}

// test-double: consumer(admits rules without supplying a component identity)
type advisoryAdmit struct{}

func (advisoryAdmit) Admissible(contract.Clause, contract.NodeMeta, struct{}) contract.RuleOutcome {
	return contract.RuleAdmit{}
}

func TestIdentityAdvisoryCapturesSlotsAndAllowances(t *testing.T) {
	allow := []contract.ProfileSlot{contract.ProfileSlotAdmit}
	profile := contract.CheckProfile[struct{}]{Leaves: clauseIDLeaves{}, Admit: advisoryAdmit{}}
	profile.Theory = advisoryTheory{Theory: contract.NewStandardTheory(), report: func() contract.ComponentIdentity {
		profile.Leaves = advisoryNamedLeaves{}
		allow[0] = contract.ProfileSlotLeaves
		return bindingIdentity("example/theory", "1", 2)
	}}
	for _, want := range []contract.ProfileSlot{contract.ProfileSlotLeaves, contract.ProfileSlotAdmit} {
		if got := contract.UnidentifiedProfileSlotsAllowing(&profile, allow); !slices.Equal(got, []contract.ProfileSlot{want}) {
			t.Fatalf("reported %v, want just %s", got, want)
		}
	}
}

func TestConformanceVariationsStayOutsideTheSDK(t *testing.T) {
	limits := reflect.TypeFor[contract.CheckLimits]()
	if _, exists := limits.MethodByName("EachBudgetRaised"); exists {
		t.Fatal("the SDK exposes conformance-only budget variations")
	}
}
