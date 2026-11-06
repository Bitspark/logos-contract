// Go replay of vectors/decider_completion.json's declarations (#3142, research 0031 row 13): what
// each standard decider declares about completing, per theory as seat:caa ruled, a compound
// routing to the owning member, and a theory that declares nothing reading undeclared (fail
// closed). The rs (contract/rs/tests/decider_completion_3142.rs) and ts
// (contract/ts/test/decider_completion_3142.test.ts) bindings replay the same rows.
package contract

import (
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"testing"
)

type completionRow struct {
	Name       string  `json:"name"`
	Theory     string  `json:"theory"`
	Pred       string  `json:"pred"`
	Completion string  `json:"completion"`
	Decider    *string `json:"decider"`
}

// declaresNothing owns p and declares nothing: no Completion, no Identity.
// test-double: consumer(a domain theory that declares nothing about completing)
type declaresNothing struct{}

func (declaresNothing) Owns(pred Symbol) bool              { return pred.String() == "p" }
func (declaresNothing) Decide(GroundLiteral) TheoryOutcome { return TheoryHolds{} }

// stopsUntyped owns q and declares that a decision may stop and still answer TheoryFails: the
// population the guard still refuses (host builtins until #3506, v1-only deciders). No standard
// theory declares it after #3313, so the replay carries its own to exercise the kind.
// test-double: consumer(a domain theory whose stops still surface as Fails)
type stopsUntyped struct{}

func (stopsUntyped) Owns(pred Symbol) bool              { return pred.String() == "q" }
func (stopsUntyped) Decide(GroundLiteral) TheoryOutcome { return TheoryHolds{} }
func (stopsUntyped) Completion(Symbol) DecisionCompletion {
	return DecisionMayNotComplete{
		Decider: NewComponentIdentity([]byte("demo/stops-untyped-theory"), []byte("1"), [32]byte{}),
		Cause:   "a stop surfaces as Fails",
	}
}

func completionTheory(t *testing.T, name string) Theory {
	t.Helper()
	switch name {
	case "arithmetic":
		return NewArithmeticTheory()
	case "text":
		return NewTextTheory()
	case "term":
		return NewTermTheory()
	case "list":
		return NewListTheory()
	case "standard":
		return NewStandardTheory()
	case "undeclared":
		return declaresNothing{}
	case "stops_untyped":
		return stopsUntyped{}
	default:
		t.Fatalf("unknown theory %q", name)
		return nil
	}
}

func TestEveryCoreDeclaresTheSameCompletion3142(t *testing.T) {
	dir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	raw, err := os.ReadFile(filepath.Join(dir, "..", "..", "vectors", "decider_completion.json"))
	if err != nil {
		t.Fatalf("read decider_completion.json: %v", err)
	}
	var v struct {
		Declarations []completionRow `json:"declarations"`
	}
	if err := json.Unmarshal(raw, &v); err != nil {
		t.Fatal(err)
	}
	if len(v.Declarations) == 0 {
		t.Fatal("the declarations section is empty")
	}
	seen := map[string]bool{}
	for _, row := range v.Declarations {
		got := CompletionOf(completionTheory(t, row.Theory), SymbolFromString(row.Pred))
		if tag := DecisionCompletionTag(got); tag != row.Completion {
			t.Errorf("%s: declares %s, the vector says %s", row.Name, tag, row.Completion)
		}
		if StopsAreTyped(got) != (row.Completion == "stops_are_typed") {
			t.Errorf("%s: StopsAreTyped() disagrees with the tag", row.Name)
		}
		var decider *ComponentIdentity
		switch d := got.(type) {
		case DecisionStopsAreTyped:
		case DecisionMayNotComplete:
			decider = &d.Decider
		case DecisionUndeclared:
			decider = &d.Decider
		default:
			t.Fatalf("%s: unknown declaration %T", row.Name, got)
		}
		switch {
		case row.Decider == nil && decider != nil:
			t.Errorf("%s: a completing decider names nobody, got %q", row.Name, decider.Id)
		case row.Decider != nil && (decider == nil || string(decider.Id) != *row.Decider):
			t.Errorf("%s: names decider %v, the vector says %q", row.Name, decider, *row.Decider)
		}
		seen[row.Completion] = true
	}
	kinds := make([]string, 0, len(seen))
	for k := range seen {
		kinds = append(kinds, k)
	}
	sort.Strings(kinds)
	if want := []string{"may_not_complete", "stops_are_typed", "undeclared"}; len(kinds) != 3 || kinds[0] != want[0] || kinds[1] != want[1] || kinds[2] != want[2] {
		t.Fatalf("every declaration kind is exercised, got %v", kinds)
	}
}
