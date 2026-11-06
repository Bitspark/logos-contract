package contract

// #1914 — the public strict inverse of the ground-literal account representation, exercised
// ONLY through the exported surface: no derivation is fabricated, no private decoder copied.

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

func glRoundTrip(t *testing.T, l GroundLiteral) {
	t.Helper()
	v := GroundLiteralAsValue(l)
	back, err := GroundLiteralFromValueV1(v)
	if err != nil {
		t.Fatalf("valid encoding refused: %v", err)
	}
	if !GroundLiteralAsValue(back).Equal(v) {
		t.Fatalf("round trip is not byte-stable: %v vs %v", GroundLiteralAsValue(back), v)
	}
	if back.Pred != l.Pred || len(back.Args) != len(l.Args) {
		t.Fatalf("round trip changed the literal: %+v vs %+v", back, l)
	}
}

func TestGroundLiteralDecodePositiveCasesRoundTrip(t *testing.T) {
	glRoundTrip(t, NewGroundLiteral("p"))
	glRoundTrip(t, GroundLiteral{Pred: NewSymbol([]byte("pred with bytes \x00\xff")), Args: []core.Value{core.NewAtom([]byte("a"))}})
	glRoundTrip(t, NewGroundLiteral("q", core.NewAtom([]byte{}), core.NewAtom([]byte{0, 255, 7})))
	glRoundTrip(t, NewGroundLiteral("nested", core.NewTuple(
		core.NewAtom([]byte("a")),
		core.NewTuple(core.NewAtom([]byte("b")), core.NewTuple()),
	)))
}

// An atom whose bytes spell a variable name is DATA: Quote marks it as an atom.
func TestGroundLiteralDecodeDataThatLooksLikeAVariableIsPreserved(t *testing.T) {
	glRoundTrip(t, NewGroundLiteral("looks", core.NewAtom([]byte("X")), core.NewAtom([]byte("_"))))
}

func TestGroundLiteralDecodeRefusalsNameTheClass(t *testing.T) {
	// #2630: the one decoder's refusal text, byte-identical to rs's (its path, then its class).
	refuse := func(name string, v core.Value, want string) {
		t.Helper()
		_, err := GroundLiteralFromValueV1(v)
		if err == nil {
			t.Fatalf("%s: accepted", name)
		}
		if err.Error() != want {
			t.Fatalf("%s: refusal %q, want %q", name, err, want)
		}
	}
	refuse("missing predicate", core.NewTuple(), "decode ground literal: expected arity 1, got 0")
	refuse("non-atom predicate", core.NewTuple(core.NewTuple()), "decode ground literal: expected a different value shape")
	// the RAW Ontos compound reading: an unquoted argument is outside the image of Quote
	refuse("unquoted argument", core.NewTuple(core.NewAtom([]byte("p")), core.NewAtom([]byte("a"))), "decode ground literal: value is not a quoted ground term")
	refuse("quoted variable", core.NewTuple(core.NewAtom([]byte("p")), Quote(Var("X"))), "decode ground literal: value is not a quoted ground term")
	refuse("nested variable", core.NewTuple(core.NewAtom([]byte("p")), Quote(Tuple(Atom([]byte("a")), Var("Y")))), "decode ground literal: value is not a quoted ground term")
	refuse("not a tuple", core.NewAtom([]byte("p")), "decode ground literal: expected a different value shape")
}
