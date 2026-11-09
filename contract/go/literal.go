// §1.1 Literal — a predicate application p(args…). [FIRM]
//
// The logic-level "atom" of Horn logic — deliberately a *different type* from an
// ontos Atom(bytes) (both senses of "atom" are load-bearing, so the logic one is
// named Literal). It is the labeled-compound reading from ontos/compound:
// p(args…) ≅ Tuple[Atom("p"), args…].
//
// Ground-ness is made a *type*, not just prose:
//   - Goal = Literal over Term — may contain Vars (clause heads/bodies, claims).
//   - GroundLiteral = Literal over ontos Value — ground; every derivation-node
//     conclusion (§3).
//
// Go has no generics-friendly way to keep Goal and GroundLiteral the exact same
// struct without boxing, so (idiomatic divergence) they are two distinct structs
// that observe the same shape. What a vector observes — substitute, as-ground,
// to-goal, structural equality — is identical to Rust.
package contract

import (
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"

	core "github.com/bitspark/ontos/core/go"
)

// Symbol is a predicate symbol — an ontos Atom(bytes), by convention a name.
// Compared by exact bytes. The bytes are held as a string so Symbol is a
// comparable value type (usable as a map/set key, mirroring Rust's deriving
// Ord/Hash); a Go string is an immutable byte sequence and may hold arbitrary
// bytes, so this is byte-exact, not UTF-8-restricted.
type Symbol struct {
	bytes string
}

// NewSymbol builds a Symbol from bytes.
func NewSymbol(b []byte) Symbol { return Symbol{bytes: string(b)} }

// SymbolFromString builds a Symbol from a UTF-8 string (authoring convenience).
func SymbolFromString(s string) Symbol { return Symbol{bytes: s} }

// Bytes returns the symbol's exact bytes.
func (s Symbol) Bytes() []byte { return []byte(s.bytes) }

// Equal reports byte equality of two symbols.
func (s Symbol) Equal(other Symbol) bool { return s.bytes == other.bytes }

// String renders the symbol bytes as a (possibly lossy) string for diagnostics.
func (s Symbol) String() string { return s.bytes }

// EscapedName is THE injective rendering of a name's bytes as text (#1961's ruling; shared by
// #2763, and moved beside Symbol by #3057, since a type's canonical rendering lives with the type:
// seat:caa's ruling on #2984): valid UTF-8 verbatim except '%', which becomes "%25", and every byte
// outside valid UTF-8 as "%XX" (uppercase hex). Injective because '%' only ever starts an escape. A
// raw or lossy render lets two identities that differ only in an ill-formed byte read as one, or as
// bytes that are not text at all. rs (logos_contract::escaped_name) and ts (escapedName) render the
// same bytes to the same text, pinned by vectors/identity_bytes.json's escaped_name section.
func EscapedName(b []byte) string {
	var out strings.Builder
	for len(b) > 0 {
		r, size := utf8.DecodeRune(b)
		switch {
		case r == utf8.RuneError && size <= 1:
			// An ill-formed byte. A continuation byte never starts a valid sequence, so escaping
			// byte by byte escapes exactly the bytes rs's maximal-subpart split escapes.
			fmt.Fprintf(&out, "%%%02X", b[0])
		case r == '%':
			out.WriteString("%25")
		default:
			out.Write(b[:size])
		}
		b = b[size:]
	}
	return out.String()
}

// Goal is a clause head / body literal / claim-with-holes (§1.1). May contain Vars.
// Equality is structural.
type Goal struct {
	Pred Symbol
	Args []Term
}

// NewGoal builds a Goal from a predicate string and argument terms.
func NewGoal(pred string, args ...Term) Goal {
	return Goal{Pred: SymbolFromString(pred), Args: append([]Term(nil), args...)}
}

// GroundLiteral is a ground literal — the conclusion of every Derivation node (§3).
// Its args are ontos Values, so ground-ness is guaranteed by the type. Equality is
// structural.
type GroundLiteral struct {
	Pred Symbol
	Args []core.Value
}

func (g GroundLiteral) detached() GroundLiteral {
	g.Args = slices.Clone(g.Args)
	return g
}

// NewGroundLiteral builds a GroundLiteral from a predicate string and ground values.
func NewGroundLiteral(pred string, args ...core.Value) GroundLiteral {
	return GroundLiteral{Pred: SymbolFromString(pred), Args: append([]core.Value(nil), args...)}
}

// Substitute applies a grounding substitution to every argument (§3, Rule
// obligation).
func (g Goal) Substitute(subst Subst) Goal {
	args := make([]Term, len(g.Args))
	for i, t := range g.Args {
		args[i] = t.Substitute(subst)
	}
	return Goal{Pred: g.Pred, Args: args}
}

// AsGround erases a fully-ground goal to a GroundLiteral; the second result is
// false if any argument still contains a Var.
func (g Goal) AsGround() (GroundLiteral, bool) {
	args := make([]core.Value, 0, len(g.Args))
	for _, arg := range g.Args {
		v, ok := arg.EraseGround()
		if !ok {
			return GroundLiteral{}, false
		}
		args = append(args, v)
	}
	return GroundLiteral{Pred: g.Pred, Args: args}, true
}

// ToGoal lifts a GroundLiteral back into a Goal (ground, no holes) — used to
// compare a node conclusion against a substituted clause literal.
func (gl GroundLiteral) ToGoal() Goal {
	args := make([]Term, len(gl.Args))
	for i, v := range gl.Args {
		args[i] = FromValue(v)
	}
	return Goal{Pred: gl.Pred, Args: args}
}

// Equal reports structural identity of two ground literals (same predicate bytes,
// same arity, elementwise-equal ontos values in order).
func (gl GroundLiteral) Equal(other GroundLiteral) bool {
	if !gl.Pred.Equal(other.Pred) {
		return false
	}
	if len(gl.Args) != len(other.Args) {
		return false
	}
	for i := range gl.Args {
		if !gl.Args[i].Equal(other.Args[i]) {
			return false
		}
	}
	return true
}
