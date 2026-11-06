package contract

import (
	"reflect"
	"testing"
)

// Budgets lists every budget field of CheckLimits exactly once (#2733, R3): the one list, which the
// kernel's R3 table and every reader take. Go has no exhaustive struct destructuring, so the struct's
// fields are counted by reflection instead: a new field fails here until it is placed.
func TestBudgetsListEveryCheckLimitsBudgetOnce2733(t *testing.T) {
	limits := DefaultLimits()
	listed := map[*int]string{}
	for _, b := range limits.Budgets() {
		if prev, dup := listed[b.Value]; dup {
			t.Fatalf("%s and %s name the same field", prev, b.Name)
		}
		listed[b.Value] = b.Name
	}
	v := reflect.ValueOf(&limits).Elem()
	for i := 0; i < v.NumField(); i++ {
		name := v.Type().Field(i).Name
		if name == "TermIdentity" {
			continue // not a budget: INERT since #3022
		}
		field, ok := v.Field(i).Addr().Interface().(*int)
		if !ok {
			t.Fatalf("CheckLimits.%s is not an int budget: place it in Budgets or here", name)
		}
		if _, ok := listed[field]; !ok {
			t.Fatalf("CheckLimits.%s is not in Budgets", name)
		}
		delete(listed, field)
	}
	if len(listed) != 0 {
		t.Fatalf("Budgets lists fields CheckLimits does not have: %v", listed)
	}
}
