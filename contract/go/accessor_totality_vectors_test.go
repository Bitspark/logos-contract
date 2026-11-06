// Go replay of vectors/accessor_totality.json — the BodyLit accessor family's behaviour around
// the Count variant.
//
// Every case carries ONE outcome, the same in every core: the file is an interface section
// (vectors/CORPUS-CLASSES.md). It keyed outcomes per core until #2733, because the partial
// Inner() accessor failed differently on a Count (the zero Goal here, a trap in rs, #728). That
// accessor was deleted tri-core (#2733, seat:caa's D1), and the total AsInner() is the only one.
package contract

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

type accessorTotalityFile struct {
	Fixture struct {
		Goal struct {
			Pred string `json:"pred"`
			Args []struct {
				AtomStr string `json:"atom_str"`
			} `json:"args"`
		} `json:"goal"`
		Count struct {
			Pred     string          `json:"pred"`
			Arity    uint32          `json:"arity"`
			Filter   json.RawMessage `json:"filter"`
			Project  string          `json:"project"`
			CountVar string          `json:"count_var"`
		} `json:"count"`
	} `json:"fixture"`
	Cases []struct {
		Name     string          `json:"name"`
		Accessor string          `json:"accessor"`
		Variant  string          `json:"variant"`
		Outcome  json.RawMessage `json:"outcome"`
	} `json:"cases"`
}

func loadAccessorTotality(t *testing.T) accessorTotalityFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "accessor_totality.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read vector: %v", readErr)
			}
			var file accessorTotalityFile
			if jsonErr := json.Unmarshal(raw, &file); jsonErr != nil {
				t.Fatalf("parse vector: %v", jsonErr)
			}
			return file
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("could not locate vectors/accessor_totality.json")
		}
		dir = parent
	}
}

func accessorFixtureGoal(t *testing.T, f accessorTotalityFile) Goal {
	t.Helper()
	if len(f.Fixture.Goal.Args) != 1 {
		t.Fatalf("fixture goal must carry exactly one arg, got %d", len(f.Fixture.Goal.Args))
	}
	return NewGoal(f.Fixture.Goal.Pred, Atom([]byte(f.Fixture.Goal.Args[0].AtomStr)))
}

func buildAccessorBodyLit(t *testing.T, variant string, f accessorTotalityFile) BodyLit {
	t.Helper()
	switch variant {
	case "pos":
		return PosLit(accessorFixtureGoal(t, f))
	case "neg":
		return NegLit(accessorFixtureGoal(t, f))
	case "count":
		if f.Fixture.Count.Project != "rows" {
			t.Fatalf("fixture count project must be rows, got %q", f.Fixture.Count.Project)
		}
		return CountLitBody(CountLit{
			Pred:    NewPredicateRef(SymbolFromString(f.Fixture.Count.Pred), f.Fixture.Count.Arity),
			Filter:  nil,
			Project: Rows(),
			Count:   Var(f.Fixture.Count.CountVar),
		})
	default:
		t.Fatalf("unknown variant %q", variant)
		return BodyLit{}
	}
}

// classifyAccessorGoal maps a returned goal onto the closed outcome vocabulary.
func classifyAccessorGoal(g, expected Goal) string {
	if g.Pred.String() == expected.Pred.String() && len(g.Args) == len(expected.Args) {
		return "goal"
	}
	return "other"
}

// observeAccessor runs one accessor and maps its result onto the outcome vocabulary.
func observeAccessor(bl BodyLit, accessor string, expected Goal) (outcome string) {
	switch accessor {
	case "as_inner":
		g, ok := bl.AsInner()
		if !ok {
			outcome = "none"
		} else {
			outcome = classifyAccessorGoal(g, expected)
		}
	default:
		outcome = "unknown_accessor"
	}
	return outcome
}

func TestAccessorTotalityVectorsReplay(t *testing.T) {
	f := loadAccessorTotality(t)
	if len(f.Cases) != 3 {
		t.Fatalf("the pin file carries exactly 3 cases, got %d", len(f.Cases))
	}
	expected := accessorFixtureGoal(t, f)
	for _, c := range f.Cases {
		// An interface section: ONE outcome for every core, never an object keyed by core.
		var pinned string
		if err := json.Unmarshal(c.Outcome, &pinned); err != nil {
			t.Fatalf("case %s: the outcome must be one value for every core, got %s", c.Name, c.Outcome)
		}
		bl := buildAccessorBodyLit(t, c.Variant, f)
		if got := observeAccessor(bl, c.Accessor, expected); got != pinned {
			t.Errorf("case %s: observed %q, pinned %q", c.Name, got, pinned)
		}
	}
}
