// #2247: a positive literal whose predicate is an account tag byte (0x00 negation, 0x01 count)
// reads exactly like the tagged literal, so it shares that literal's clause bytes, id and program
// digest. Every ingress refuses it by name (seat:caa, issuecomment-5812420549). The same witnesses
// are pinned in contract/rs and contract/ts; K6 is pinned in each kernel.
package contract

import (
	"encoding/json"
	"errors"
	"strings"
	"testing"
)

// rpK1B is K1's B: `p(Y) :- r(Y), <0x00>(q(Y)).`, a positive literal that reads as `\+ q(Y)`.
func rpK1B() Clause {
	y := Var("Y")
	return NewClause(NewGoal("p", y), NewGoal("r", y), NewGoal("\x00", Tuple(Atom([]byte("q")), y)))
}

// rpK2D is K2's D: `n(N) :- <0x01>(N).`, a positive literal led by the count tag.
func rpK2D() Clause {
	n := Var("N")
	return NewClause(NewGoal("n", n), NewGoal("\x01", n))
}

func TestReservedPredicates2247BothTagBytes(t *testing.T) {
	if len(ReservedProgramPredicateSymbols()) != 2 || string(ReservedProgramPredicateSymbols()[0]) != "\x00" || string(ReservedProgramPredicateSymbols()[1]) != "\x01" {
		t.Fatalf("ReservedProgramPredicateSymbols() = %v, want [0x00 0x01]", ReservedProgramPredicateSymbols())
	}
	for name, c := range map[string]struct {
		clause Clause
		want   string
	}{
		"K1":            {rpK1B(), "\x00"},
		"K2":            {rpK2D(), "\x01"},
		"a head":        {Fact(NewGoal("\x01", Atom([]byte("a")))), "\x01"},
		"ordinary fact": {Fact(NewGoal("p", Atom([]byte("a")))), ""},
	} {
		pred, ok := ReservedPredicateOf(c.clause)
		if string(pred) != c.want || ok != (c.want != "") {
			t.Errorf("%s: ReservedPredicateOf = %x, %v; want %x", name, pred, ok, c.want)
		}
	}
}

func TestReservedPredicates2247ProgramSerdeRefusesK1AndK2(t *testing.T) {
	for name, clause := range map[string]Clause{"K1": rpK1B(), "K2": rpK2D()} {
		program := NewMapProgram().With(NewClauseId("c"), clause)
		if _, err := ProgramToValue(program); !errors.Is(err, ErrProgramReservedPredicate) {
			t.Errorf("%s: ProgramToValue = %v, want ErrProgramReservedPredicate", name, err)
		}
		if _, err := ProgramBytes(program); !errors.Is(err, ErrProgramReservedPredicate) {
			t.Errorf("%s: ProgramBytes = %v, want ErrProgramReservedPredicate", name, err)
		}
	}
}

// K5: a bundle carrying B is refused as a bad clause BEFORE the digest check. The pinned digest is
// deliberately wrong, so a digest mismatch here would mean the refusal came too late.
func TestReservedPredicates2247PreludeRefusesBeforeTheDigest(t *testing.T) {
	for _, tag := range []string{"\x00", "\x01"} {
		clause := map[string]any{
			"head": map[string]any{"pred": "p", "args": []any{map[string]any{"var": "Y"}}},
			"body": []any{
				map[string]any{"pred": "r", "args": []any{map[string]any{"var": "Y"}}},
				map[string]any{"pred": tag, "args": []any{map[string]any{"var": "Y"}}},
			},
		}
		doc, err := json.Marshal(map[string]any{
			"name": "t", "version": "0.0.0", "program_digest": strings.Repeat("00", 32),
			"clauses": []any{map[string]any{"clause": clause}},
		})
		if err != nil {
			t.Fatal(err)
		}
		_, err = LoadPrelude(doc)
		var perr *PreludeError
		if !errors.As(err, &perr) || perr.Kind != PreludeBadClause || perr.Index != 0 || !strings.Contains(perr.Detail, "reserved predicate") {
			t.Errorf("tag %x: got %v, want a bad_clause refusal at index 0 naming the reserved predicate", tag, err)
		}
	}
}
