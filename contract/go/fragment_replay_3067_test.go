package contract

// #3067 (research 0028 row A15; seat:caa's rulings Q1 to Q3): vectors/fragment.json replayed through
// check's scope gate, as rs's check/fragment_replay.rs and the ts replay do. Each case states one
// sealed clause of a program and its context; the gate refuses the program by the case's expect (the
// first gate the clause fails, and that gate's subject), or admits it when expect is null.

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
)

type fragmentExpect struct {
	Outside   string `json:"outside"`
	Pred      string `json:"pred"`
	SameScope bool   `json:"same_scope"`
	Through   string `json:"through"`
	Var       string `json:"var"`
}

type fragmentCase struct {
	Name       string          `json:"name"`
	Program    []any           `json:"program"`
	Clause     int             `json:"clause"`
	Seals      []string        `json:"seals"`
	ReadsLower []string        `json:"reads_lower"`
	Owns       []string        `json:"owns"`
	Expect     *fragmentExpect `json:"expect"`
}

// test-double: consumer(owns the relations a fragment.json case lists, decides none)
type fragmentOwns []Symbol

func (o fragmentOwns) Owns(pred Symbol) bool {
	for _, s := range o {
		if s == pred {
			return true
		}
	}
	return false
}

func (fragmentOwns) DecideGround(GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundDisowned()
}

func fragmentTerm(v any) Term {
	switch x := v.(type) {
	case string:
		if x != "" && x[0] >= 'A' && x[0] <= 'Z' {
			return Var(x)
		}
		return Atom([]byte(x))
	case []any:
		children := []Term{Atom([]byte(x[0].(string)))}
		for _, a := range x[1:] {
			children = append(children, fragmentTerm(a))
		}
		return Tuple(children...)
	}
	panic(fmt.Sprintf("not a term in fragment.json's notation: %v", v))
}

func fragmentGoal(v any) Goal {
	items := v.([]any)
	args := make([]Term, 0, len(items)-1)
	for _, a := range items[1:] {
		args = append(args, fragmentTerm(a))
	}
	return NewGoal(items[0].(string), args...)
}

func fragmentBodyLit(v any) BodyLit {
	m, ok := v.(map[string]any)
	if !ok {
		return PosLit(fragmentGoal(v))
	}
	if neg, ok := m["neg"]; ok {
		return NegLit(fragmentGoal(neg))
	}
	c := m["count"].(map[string]any)
	var filter []CountFilterEntry
	for _, e := range c["filter"].([]any) {
		pair := e.([]any)
		filter = append(filter, CountFilterEntry{Pos: uint32(pair[0].(float64)), Term: fragmentTerm(pair[1])})
	}
	return CountLitBody(CountLit{
		Pred:    NewPredicateRef(SymbolFromString(c["pred"].(string)), uint32(c["arity"].(float64))),
		Filter:  filter,
		Project: ProjectSpec{Kind: ProjectRows},
		Count:   fragmentTerm(c["result"]),
	})
}

func fragmentClause(v any) Clause {
	m := v.(map[string]any)
	clause := Clause{Head: fragmentGoal(m["head"])}
	if body, ok := m["body"].([]any); ok {
		for _, b := range body {
			clause.Body = append(clause.Body, fragmentBodyLit(b))
		}
	}
	return clause
}

func fragmentSymbols(names []string) []Symbol {
	out := make([]Symbol, 0, len(names))
	for _, n := range names {
		out = append(out, SymbolFromString(n))
	}
	return out
}

// fragmentPhrase is the phrase check's refusal carries for expect: the gate, and its subject.
func fragmentPhrase(e fragmentExpect) string {
	switch e.Outside {
	case "count_not_lower":
		if e.SameScope {
			return fmt.Sprintf("contains a count over predicate %q, which this same certificate seals", e.Pred)
		}
		return fmt.Sprintf("contains a count over predicate %q, which no unique, exact, Valid strictly lower certificate seals", e.Pred)
	case "count_open_compound":
		return fmt.Sprintf("count over predicate %q contains an open compound", e.Pred)
	case "constructor_cycle":
		return fmt.Sprintf("on a dependency cycle through %q", e.Through)
	case "unserved":
		return fmt.Sprintf("references predicate %q that is neither sealed", e.Pred)
	case "intra_scope_negation":
		return fmt.Sprintf("negates predicate %q sealed by this same prefix", e.Pred)
	case "unbound_count_filter":
		return fmt.Sprintf("count over predicate %q has filter variable %q not bound", e.Pred, e.Var)
	case "unbound_variable":
		return fmt.Sprintf("has unsafe variable %q:", e.Var)
	}
	panic("fragment.json names an unknown gate: " + e.Outside)
}

func loadFragmentVectors(t *testing.T) []fragmentCase {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "fragment.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/fragment.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var doc struct {
		Cases []fragmentCase `json:"cases"`
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	if len(doc.Cases) < 20 {
		t.Fatalf("fragment.json holds its cases: %d", len(doc.Cases))
	}
	return doc.Cases
}

func TestFragmentCasesAreClassifiedByTheirFirstGateInCheck3067(t *testing.T) {
	for _, c := range loadFragmentVectors(t) {
		program := NewMapProgram()
		for i, cl := range c.Program {
			program.Insert(NewClauseId(fmt.Sprintf("c%02d", i)), fragmentClause(cl))
		}
		readsLower := fragmentSymbols(c.ReadsLower)
		lowerCert := ClosedModelCert{Scope: NewStratumPrefix(1, readsLower)}
		view := certView{cert: ClosedModelCert{Scope: NewStratumPrefix(1, fragmentSymbols(c.Seals))}, lower: map[Symbol]lowerSeal{}}
		for _, pred := range readsLower {
			view.lower[pred] = lowerSeal{index: 0, cert: lowerCert}
		}
		err := checkScopeDownwardClosed(view, program, fragmentOwns(fragmentSymbols(c.Owns)))
		switch {
		case c.Expect == nil && err == nil:
		case c.Expect == nil:
			t.Errorf("%s: inside the fragment, but refused: %s", c.Name, err.detail)
		case err == nil:
			t.Errorf("%s: expected %+v, admitted", c.Name, *c.Expect)
		default:
			want := fragmentPhrase(*c.Expect)
			if err.code != CertScopeIncomplete || !strings.Contains(err.detail, want) {
				t.Errorf("%s: expected %q, got %v: %s", c.Name, want, err.code, err.detail)
			}
		}
	}
}

// fragmentOutside is the Outside a case's expect names.
func fragmentOutside(e fragmentExpect) Outside {
	kinds := map[string]OutsideKind{
		"count_not_lower":      OutsideCountNotLower,
		"count_open_compound":  OutsideCountOpenCompound,
		"constructor_cycle":    OutsideConstructorCycle,
		"unserved":             OutsideUnserved,
		"intra_scope_negation": OutsideIntraScopeNegation,
		"unbound_count_filter": OutsideUnboundCountFilter,
		"unbound_variable":     OutsideUnboundVariable,
	}
	kind, ok := kinds[e.Outside]
	if !ok {
		panic("fragment.json names an unknown gate: " + e.Outside)
	}
	o := Outside{Kind: kind, SameScope: e.SameScope}
	if e.Pred != "" {
		o.Pred = SymbolFromString(e.Pred)
	}
	if e.Through != "" {
		o.Through = SymbolFromString(e.Through)
	}
	if e.Var != "" {
		o.Var = NewVarId(e.Var)
	}
	return o
}

// The same file through the contract tier's one function, compared structurally, and a census: Go
// has no exhaustive switch (research 0025), so every OutsideKind fragment.go DECLARES must be reached
// by some row, or a kind added without a vector row (and so without a tested wording in
// scopeIncompleteDetail) reds.
func TestFragmentCasesAreClassifiedByTheContractTierFunction3067(t *testing.T) {
	reached := map[OutsideKind]bool{}
	for _, c := range loadFragmentVectors(t) {
		program := make([]Clause, 0, len(c.Program))
		for _, cl := range c.Program {
			program = append(program, fragmentClause(cl))
		}
		ctx := NewSealContext(fragmentSymbols(c.Seals), fragmentSymbols(c.ReadsLower))
		graph := NewScopeGraph()
		for _, cl := range program {
			graph.Add(cl, func(s Symbol) bool { return ctx.Seals[s] })
		}
		owns := fragmentOwns(fragmentSymbols(c.Owns))
		got, outside := ClassifySealedClause(program[c.Clause], ctx, graph, owns.Owns, owns.Owns)
		switch {
		case c.Expect == nil && !outside:
		case c.Expect == nil:
			t.Errorf("%s: inside the fragment, got %+v", c.Name, got)
		case !outside:
			t.Errorf("%s: expected %+v, inside the fragment", c.Name, *c.Expect)
		default:
			want := fragmentOutside(*c.Expect)
			reached[want.Kind] = true
			if got != want {
				t.Errorf("%s: expected %+v, got %+v", c.Name, want, got)
			}
		}
	}
	for _, k := range declaredOutsideKinds(t) {
		if !reached[k.value] {
			t.Errorf("%s is declared in fragment.go and reached by no fragment.json row: add a row, "+
				"and a wording in scopeIncompleteDetail", k.name)
		}
	}
}

// declaredOutsideKind is one OutsideKind constant as fragment.go declares it.
type declaredOutsideKind struct {
	name  string
	value OutsideKind
}

// declaredOutsideKinds reads the OutsideKind constants from fragment.go's declarations with
// go/parser (research 0025's construction for Go, as kernel/go/runtime/terminal_outcome_2736_test.go
// does), so the census's domain comes from the declarations and not from the code it checks: a kind
// appended to the block is in the domain whatever else changes (seat:caa's grade on #3312). The
// block is `First OutsideKind = iota + 1` followed by bare names, so a constant's value is its
// position plus one; any other shape fails here by name rather than being read wrongly.
func declaredOutsideKinds(t *testing.T) []declaredOutsideKind {
	t.Helper()
	file, err := parser.ParseFile(token.NewFileSet(), "fragment.go", nil, 0)
	if err != nil {
		t.Fatalf("parsing fragment.go: %v", err)
	}
	var kinds []declaredOutsideKind
	for _, d := range file.Decls {
		gen, ok := d.(*ast.GenDecl)
		if !ok || gen.Tok != token.CONST || len(gen.Specs) == 0 {
			continue
		}
		first := gen.Specs[0].(*ast.ValueSpec)
		if id, ok := first.Type.(*ast.Ident); !ok || id.Name != "OutsideKind" {
			continue
		}
		for i, spec := range gen.Specs {
			vs := spec.(*ast.ValueSpec)
			plain := len(vs.Names) == 1 && vs.Type == nil && len(vs.Values) == 0
			if i == 0 {
				bin, isBin := vs.Values[0].(*ast.BinaryExpr)
				plain = len(vs.Names) == 1 && len(vs.Values) == 1 && isBin && bin.Op == token.ADD
				if plain {
					iota, a := bin.X.(*ast.Ident)
					one, b := bin.Y.(*ast.BasicLit)
					plain = a && b && iota.Name == "iota" && one.Value == "1"
				}
			}
			if !plain {
				t.Fatalf("fragment.go's OutsideKind block is not `First OutsideKind = iota + 1` followed "+
					"by bare names (at %s): the census cannot read the values; update declaredOutsideKinds",
					vs.Names[0].Name)
			}
			kinds = append(kinds, declaredOutsideKind{name: vs.Names[0].Name, value: OutsideKind(i + 1)})
		}
	}
	if len(kinds) < 7 {
		t.Fatalf("anti-vacuity: fragment.go declares %d OutsideKind constants, expected at least 7", len(kinds))
	}
	return kinds
}
