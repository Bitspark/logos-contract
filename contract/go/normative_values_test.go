package contract_test

import (
	"bytes"
	"errors"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	core "github.com/bitspark/ontos/core/go"
)

func changeFirstByte(t *testing.T, data []byte) {
	t.Helper()
	first := data[0]
	data[0] ^= 0xff
	t.Cleanup(func() { data[0] = first })
}

func TestProgramWireSettingsAreOwnedByTheCodec(t *testing.T) {
	fact := contract.Fact(contract.NewGoal("p"))
	id := contract.NewClauseId("key")
	program := contract.NewMapProgram().With(id, fact)
	t.Run("version", func(t *testing.T) {
		wire, err := contract.ProgramToValue(program)
		if err != nil {
			t.Fatal(err)
		}
		before, err := contract.ProgramBytes(program)
		if err != nil {
			t.Fatal(err)
		}
		changeFirstByte(t, contract.ProgramFormatTag())
		if _, err := contract.ProgramFromValue(wire); err != nil {
			t.Fatalf("valid existing header refused: %v", err)
		}
		after, err := contract.ProgramBytes(program)
		if err != nil || !bytes.Equal(before, after) {
			t.Fatalf("canonical header changed: %x, %v", after, err)
		}
	})
	for _, tag := range []byte{0, 1} {
		t.Run([]string{"negation", "count"}[tag], func(t *testing.T) {
			clause := contract.Fact(contract.NewGoal(string([]byte{tag})))
			program := contract.NewMapProgram().With(id, clause)
			if _, err := contract.ProgramBytes(program); err == nil {
				t.Fatal("control admitted a reserved predicate")
			}
			changeFirstByte(t, contract.ReservedProgramPredicateSymbols()[tag])
			if _, reserved := contract.ReservedPredicateOf(clause); !reserved {
				t.Fatal("reserved predicate became available")
			}
			if _, err := contract.ProgramBytes(program); err == nil {
				t.Fatal("a reserved predicate entered the codec")
			}
		})
	}
}

func TestAccountHashDomainsAreOwnedByTheChecker(t *testing.T) {
	goal := contract.NewGoal("p")
	fact := contract.Fact(goal)
	ground, _ := goal.AsGround()
	for _, tc := range []struct {
		name   string
		prefix []byte
		read   func() string
	}{
		{"clause", contract.ClauseHashPrefix(), func() string { return contract.CanonicalClauseId(fact).String() }},
		{"program", contract.ProgramHashPrefix(), func() string {
			hash := contract.ProgramDigest([]contract.Clause{fact})
			return string(hash[:])
		}},
		{"edb", contract.EDBSnapshotHashPrefix(), func() string {
			hash := contract.EdbTableHash(goal.Pred, []contract.GroundLiteral{ground})
			return string(hash[:])
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			before := tc.read()
			changeFirstByte(t, tc.prefix)
			if tc.read() != before {
				t.Fatal("another consumer changed the hash of the same input")
			}
		})
	}
}

func TestMalformedProgramKeepsItsFailure(t *testing.T) {
	// A consumer can bind these named refusals as constants. Package variables
	// would make this declaration fail to compile.
	const (
		badVersion = contract.ErrProgramBadVersion
		badEntry   = contract.ErrProgramBadEntry
		badClause  = contract.ErrProgramBadClause
		notTuple   = contract.ErrProgramNotATuple
		reserved   = contract.ErrProgramReservedPredicate
	)
	tag := core.NewAtom(contract.ProgramFormatTag())
	for _, tc := range []struct {
		value core.Value
		want  error
	}{
		{core.NewAtom(nil), notTuple},
		{core.NewTuple(), badVersion},
		{core.NewTuple(tag, tag), badEntry},
		{core.NewTuple(tag, core.NewTuple(core.NewAtom([]byte("key")), tag)), badClause},
	} {
		out, err := contract.ProgramFromValue(tc.value)
		if out != nil || err == nil || !errors.Is(err, tc.want) {
			t.Fatalf("malformed program returned %v, %v; want %v", out, err, tc.want)
		}
	}
	fact := contract.Fact(contract.NewGoal(string([]byte{0})))
	program := contract.NewMapProgram().With(contract.NewClauseId("key"), fact)
	if _, err := contract.ProgramBytes(program); err == nil || !errors.Is(err, reserved) {
		t.Fatalf("missing wrapped reserved-predicate refusal: %v", err)
	}
}
