package typed_test

import (
	"encoding/json"
	"os"
	"reflect"
	"slices"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/typed"
)

// JSON below is fixture notation only. This decoder is test-owned and is not a
// production byte decoder or a supported proof transport.
type fixtureDeclaration struct {
	Kind         string          `json:"kind"`
	Name         string          `json:"symbol"`
	Type         json.RawMessage `json:"type"`
	Value        json.RawMessage `json:"value"`
	Dependencies []string        `json:"dependencies"`
}

type fixtureCase struct {
	ID        string `json:"id"`
	Statement struct {
		Declarations string            `json:"declarations"`
		Context      []json.RawMessage `json:"context"`
		Expected     json.RawMessage   `json:"expected"`
		Foundation   *string           `json:"foundation"`
	} `json:"statement"`
	Candidate json.RawMessage `json:"candidate"`
	Policy    struct {
		Dependencies []string `json:"dependencies"`
		Foundation   *string  `json:"foundation"`
		Checker      *string  `json:"checker"`
	} `json:"policy"`
	Limits map[string]uint32 `json:"limits"`
	Expect struct {
		Status       string   `json:"status"`
		Code         string   `json:"code"`
		Dependencies []string `json:"dependencies"`
	} `json:"expect"`
}

type fixtureFile struct {
	Schema          string                          `json:"schema"`
	Foundation      string                          `json:"foundation"`
	DeclarationSets map[string][]fixtureDeclaration `json:"declaration_sets"`
	Cases           []fixtureCase                   `json:"cases"`
}

func readFixtures(t *testing.T) fixtureFile {
	t.Helper()
	data, err := os.ReadFile("../../../vectors/typed_check.json")
	if err != nil {
		t.Fatal(err)
	}
	var file fixtureFile
	if err := json.Unmarshal(data, &file); err != nil {
		t.Fatal(err)
	}
	if file.Schema != "logos/typed-check-fixtures/v1" || file.Foundation != typed.Foundation || len(file.Cases) == 0 {
		t.Fatal("unexpected fixture contract")
	}
	return file
}

func fixtureExpr(t *testing.T, data json.RawMessage) typed.Expr {
	t.Helper()
	var node []json.RawMessage
	if err := json.Unmarshal(data, &node); err != nil || len(node) == 0 {
		t.Fatalf("bad fixture expression %s: %v", data, err)
	}
	var tag string
	if err := json.Unmarshal(node[0], &tag); err != nil {
		t.Fatal(err)
	}
	if tag == "sort" || tag == "var" {
		if len(node) != 2 {
			t.Fatal("natural fixture arity")
		}
		var value uint32
		if err := json.Unmarshal(node[1], &value); err != nil {
			t.Fatal(err)
		}
		if tag == "sort" {
			return typed.Sort(value)
		}
		return typed.Var(value)
	}
	if tag == "const" {
		if len(node) != 2 {
			t.Fatal("constant fixture arity")
		}
		var name string
		if err := json.Unmarshal(node[1], &name); err != nil {
			t.Fatal(err)
		}
		return typed.Const(name)
	}
	args := make([]typed.Expr, len(node)-1)
	for i, operand := range node[1:] {
		args[i] = fixtureExpr(t, operand)
	}
	counts := map[string]int{"pi": 2, "lam": 2, "app": 2, "sigma": 2, "pair": 3, "fst": 1, "snd": 1, "nat": 0, "zero": 0, "succ": 1, "nat-elim": 4, "bool": 0, "false": 0, "true": 0, "bool-elim": 4, "id": 3, "refl": 2, "transport": 6}
	if count, ok := counts[tag]; !ok || count != len(args) {
		t.Fatalf("invalid %s fixture arity", tag)
	}
	switch tag {
	case "pi":
		return typed.Pi(args[0], args[1])
	case "lam":
		return typed.Lam(args[0], args[1])
	case "app":
		return typed.App(args[0], args[1])
	case "sigma":
		return typed.Sigma(args[0], args[1])
	case "pair":
		return typed.Pair(args[0], args[1], args[2])
	case "fst":
		return typed.Fst(args[0])
	case "snd":
		return typed.Snd(args[0])
	case "nat":
		return typed.Nat()
	case "zero":
		return typed.Zero()
	case "succ":
		return typed.Succ(args[0])
	case "nat-elim":
		return typed.NatElim(args[0], args[1], args[2], args[3])
	case "bool":
		return typed.Bool()
	case "false":
		return typed.False()
	case "true":
		return typed.True()
	case "bool-elim":
		return typed.BoolElim(args[0], args[1], args[2], args[3])
	case "id":
		return typed.ID(args[0], args[1], args[2])
	case "refl":
		return typed.Refl(args[0], args[1])
	case "transport":
		return typed.Transport(args[0], args[1], args[2], args[3], args[4], args[5])
	default:
		t.Fatalf("unknown fixture constructor %s", tag)
		return typed.Expr{}
	}
}

func fixtureDeclarations(t *testing.T, data []fixtureDeclaration) []typed.Declaration {
	t.Helper()
	result := make([]typed.Declaration, 0, len(data))
	for _, declaration := range data {
		typ := fixtureExpr(t, declaration.Type)
		switch declaration.Kind {
		case "assume":
			result = append(result, typed.Assume(declaration.Name, typ, declaration.Dependencies...))
		case "define":
			result = append(result, typed.Define(declaration.Name, typ, fixtureExpr(t, declaration.Value)))
		default:
			t.Fatalf("unknown fixture declaration %s", declaration.Kind)
		}
	}
	return result
}

func fixtureInput(t *testing.T, file fixtureFile, c fixtureCase) (typed.Statement, typed.Expr, typed.Policy, typed.Limits) {
	t.Helper()
	declarations, ok := file.DeclarationSets[c.Statement.Declarations]
	if !ok {
		t.Fatalf("missing declaration set %s", c.Statement.Declarations)
	}
	s := typed.Statement{Foundation: file.Foundation, Declarations: fixtureDeclarations(t, declarations), Expected: fixtureExpr(t, c.Statement.Expected)}
	if c.Statement.Foundation != nil {
		s.Foundation = *c.Statement.Foundation
	}
	for _, e := range c.Statement.Context {
		s.Context = append(s.Context, fixtureExpr(t, e))
	}
	p := typed.Policy{Foundation: file.Foundation, Checker: typed.Checker, Dependencies: c.Policy.Dependencies}
	if c.Policy.Foundation != nil {
		p.Foundation = *c.Policy.Foundation
	}
	if c.Policy.Checker != nil {
		p.Checker = *c.Policy.Checker
	}
	l := typed.DefaultLimits()
	for field, value := range c.Limits {
		switch field {
		case "input_nodes":
			l.InputNodes = value
		case "input_depth":
			l.InputDepth = value
		case "collection_entries":
			l.CollectionEntries = value
		case "name_bytes":
			l.NameBytes = value
		case "work":
			l.Work = value
		case "depth":
			l.Depth = value
		default:
			t.Fatalf("unknown fixture limit %s", field)
		}
	}
	return s, fixtureExpr(t, c.Candidate), p, l
}

func TestSharedTypedCheckVectors(t *testing.T) {
	file := readFixtures(t)
	seen := make(map[string]bool)
	for _, c := range file.Cases {
		if seen[c.ID] {
			t.Fatalf("duplicate case %s", c.ID)
		}
		seen[c.ID] = true
		t.Run(c.ID, func(t *testing.T) {
			s, candidate, p, limits := fixtureInput(t, file, c)
			result := typed.Check(s, candidate, p, limits)
			if string(result.Status()) != c.Expect.Status || string(result.Code()) != c.Expect.Code {
				t.Fatalf("got %s/%s (%s) at %+v after %d work; expected %s/%s", result.Status(), result.Code(), result.Detail(), result.Location(), result.Steps(), c.Expect.Status, c.Expect.Code)
			}
			if result.Steps() > limits.Work {
				t.Fatal("work counter exceeded request")
			}
			if accepted, ok := result.Accepted(); ok && !slices.Equal(accepted.Dependencies(), c.Expect.Dependencies) {
				t.Fatalf("got basis %v, expected %v", accepted.Dependencies(), c.Expect.Dependencies)
			}
			if c.Expect.Status == "accepted" {
				for name, raised := range EachBudgetRaised(limits) {
					t.Run("raised-"+name, func(t *testing.T) {
						replayed := typed.Check(s, candidate, p, raised)
						a, ok := replayed.Accepted()
						if !ok || !slices.Equal(a.Dependencies(), c.Expect.Dependencies) {
							t.Fatalf("raised allowance changed acceptance: %s/%s", replayed.Status(), replayed.Code())
						}
						if !exactStatement(a.Statement(), s) || !reflect.DeepEqual(a.Candidate(), candidate) {
							t.Fatal("raised allowance changed exact association")
						}
					})
				}
			}
		})
	}
}

// EachBudgetRaised exercises R3 for this in-process checking profile. Increasing
// a depth request still leaves the implementation's fixed ceiling in force.
func EachBudgetRaised(base typed.Limits) map[string]typed.Limits {
	result := make(map[string]typed.Limits)
	for _, key := range []string{"input_nodes", "input_depth", "collection_entries", "name_bytes", "work", "depth"} {
		raised := base
		switch key {
		case "input_nodes":
			raised.InputNodes = ^uint32(0)
		case "input_depth":
			raised.InputDepth = ^uint32(0)
		case "collection_entries":
			raised.CollectionEntries = ^uint32(0)
		case "name_bytes":
			raised.NameBytes = ^uint32(0)
		case "work":
			raised.Work = ^uint32(0)
		case "depth":
			raised.Depth = ^uint32(0)
		}
		result[key] = raised
	}
	return result
}

func exactStatement(a, b typed.Statement) bool {
	if a.Foundation != b.Foundation || !reflect.DeepEqual(a.Expected, b.Expected) || len(a.Declarations) != len(b.Declarations) || len(a.Context) != len(b.Context) {
		return false
	}
	for i := range a.Declarations {
		if !reflect.DeepEqual(a.Declarations[i], b.Declarations[i]) {
			return false
		}
	}
	for i := range a.Context {
		if !reflect.DeepEqual(a.Context[i], b.Context[i]) {
			return false
		}
	}
	return true
}

func TestPublicConsumerRechecksPageApplications(t *testing.T) {
	file := readFixtures(t)
	var theorem, person, nested, corrupted fixtureCase
	for _, c := range file.Cases {
		switch c.ID {
		case "page-symbolic-theorem":
			theorem = c
		case "page-person-application":
			person = c
		case "page-nested-application-consumes-both-projections":
			nested = c
		case "page-nesting-cannot-substitute-membership-for-representation":
			corrupted = c
		}
	}
	if theorem.ID == "" || person.ID == "" || nested.ID == "" || corrupted.ID == "" {
		t.Fatal("consumer fixtures absent")
	}
	s, _, policy, limits := fixtureInput(t, file, theorem)
	last := s.Declarations[len(s.Declarations)-1]
	proof, ok := last.Definition()
	if !ok || last.Name() != "page.proof" {
		t.Fatal("expected checked Page definition")
	}
	s.Declarations = s.Declarations[:len(s.Declarations)-1]
	s.Expected = last.Type()
	if len(s.Context) != 0 {
		t.Fatal("Page theorem must be closed over its external context")
	}
	result := typed.Check(s, proof, policy, limits)
	accepted, ok := result.Accepted()
	if !ok {
		t.Fatalf("closed Page theorem: %s/%s at %+v", result.Status(), result.Code(), result.Location())
	}
	checked := accepted.Statement()
	checked.Declarations = append(checked.Declarations, typed.Define(last.Name(), checked.Expected, accepted.Candidate()))
	// Acceptance is never imported as a trusted axiom. Each application rebuilds
	// the signature, checks the stored definition and checks the new exact claim.
	for _, c := range []fixtureCase{person, nested, corrupted} {
		input, candidate, policy, limits := fixtureInput(t, file, c)
		input.Declarations = checked.Declarations
		actual := typed.Check(input, candidate, policy, limits)
		if string(actual.Status()) != c.Expect.Status || string(actual.Code()) != c.Expect.Code {
			t.Fatalf("%s: %s/%s at %+v", c.ID, actual.Status(), actual.Code(), actual.Location())
		}
		if c.Expect.Status == "accepted" {
			application, ok := actual.Accepted()
			if !ok || !exactStatement(application.Statement(), input) || !reflect.DeepEqual(application.Candidate(), candidate) {
				t.Fatalf("%s lost the exact application association", c.ID)
			}
			if !slices.Equal(application.Dependencies(), c.Expect.Dependencies) {
				t.Fatalf("%s basis %v, expected %v", c.ID, application.Dependencies(), c.Expect.Dependencies)
			}
		}
	}
}

func TestReplacingAcceptanceHandleCannotReplaceOutcomeState(t *testing.T) {
	policy := typed.Policy{Foundation: typed.Foundation, Checker: typed.Checker}
	natStatement := typed.Statement{Foundation: typed.Foundation, Expected: typed.Nat()}
	boolStatement := typed.Statement{Foundation: typed.Foundation, Expected: typed.Bool()}
	natProof, boolProof := typed.Zero(), typed.True()
	natResult := typed.Check(natStatement, natProof, policy, typed.DefaultLimits())
	boolResult := typed.Check(boolStatement, boolProof, policy, typed.DefaultLimits())
	natAcceptance, natOK := natResult.Accepted()
	boolAcceptance, boolOK := boolResult.Accepted()
	if !natOK || !boolOK {
		t.Fatal("expected both independent claims to check")
	}
	retained := natAcceptance
	// A consumer can replace a complete exported value even when its fields are
	// private. This pointer addresses only the caller's copied value handle.
	replace := func(destination *typed.Acceptance, value typed.Acceptance) { *destination = value }
	replace(&natAcceptance, boolAcceptance)
	if !exactStatement(natAcceptance.Statement(), boolStatement) {
		t.Fatal("local handle assignment did not take effect")
	}
	replace(&natAcceptance, typed.Acceptance{})
	if natAcceptance.Valid() {
		t.Fatal("zero handle appeared accepted")
	}
	again, ok := natResult.Accepted()
	if !ok || !retained.Valid() || !exactStatement(again.Statement(), natStatement) || !reflect.DeepEqual(again.Candidate(), natProof) || !exactStatement(retained.Statement(), natStatement) {
		t.Fatal("replacing a caller handle mutated retained acceptance")
	}
	other, ok := boolResult.Accepted()
	if !ok || !exactStatement(other.Statement(), boolStatement) || !reflect.DeepEqual(other.Candidate(), boolProof) {
		t.Fatal("independent outcome was mutated")
	}
}
