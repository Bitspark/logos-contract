// ListTheory — the Go binding of logos-core's reified list-relation Theory, a
// judgment-for-judgment mirror of the Rust ListTheory in
// contract/rs/src/list_theory.rs (ADR 0016, Shelf A1). [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the list
// relations length/2, nth0/3, last/2 over the ontos/data REIFIED list embedding
// list(e0..e_{n-1}) = Tuple(Atom("list"), e0, ..., e_{n-1}): a program that uses them on
// the list() embedding can now be CHECKED in Go, because the same decide() that the Rust
// core uses is reproduced here byte-for-byte. All three cores agree on EVERY ground atom —
// the §7 dual-conformance law, pinned by vectors/list.json.
//
// # The home (why contract/go)
//
// Rust's ListTheory lives in the contract tier (contract/rs), beside the Theory SPI, per
// ADR 0014 / ADR 0016: a pure, total, deterministic function of a resolved ground term is
// a shared certifiable artifact, not a search-only Rust builtin. Go has no core tier; the
// reusable Theory impls a consumer binds (ArithmeticTheory, TextTheory, TermTheory) live
// HERE, beside the SPI. So this is where a Go consumer binds the list relations.
//
// # The A1 fast-path complement (NOT a duplicate)
//
// The Shelf-B lists@1.1.0 prelude ships length/2, nth0/3, last/2 as Rule clauses over
// CONS cells ([H|T] = Tuple(Atom("."), H, T)); the existing check() verifies them. This
// theory is the native A1 reading over the list() embedding instead — the SAME relations,
// a DIFFERENT representation. The two share predicate names but own structurally disjoint
// argument shapes, so a profile binds exactly one of them per predicate (the §4.4 builtin
// partition forbids a theory-owned name from also being a rule head).
//
// # Judgments (mirroring Rust exactly)
//
// Owns(pred): by NAME only (any arity) — length, nth0, last.
// DecideGround(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{list_unknown_predicate}   (defensive)
//   - wrong arity (length/2, nth0/3, last/2)
//     -> Fails{list_bad_arity}
//   - the relation is true           -> Holds
//   - the relation is false          -> Fails{list_does_not_hold}
//     (non-list argument, out-of-range index, count/element mismatch, empty list for last)
package contract

import (
	"math/big"
	"unicode/utf8"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// listPredicates is the set of predicate names ListTheory owns, mirroring Rust's
// LIST_PREDICATES. Owned by name only (any arity); a wrong arity is then a list_bad_arity
// failure.
var listPredicates = map[string]struct{}{
	"length": {},
	"nth0":   {},
	"last":   {},
}

// ListTheory is the config-pinned §5 Theory that owns the A1 list relations (length nth0
// last) over the ontos/data list embedding and decides a GROUND atom by a direct
// structural match against list(…) (constant/linear, no search, no trail). Pure / total /
// deterministic / config-free — a faithful mirror of Rust's
// contract::list_theory::ListTheory.
type ListTheory struct{}

// NewListTheory builds the standard list Theory (no configuration).
func NewListTheory() ListTheory { return ListTheory{} }

// compile-time proofs that the theory satisfies the SPI seam (Theory + the optional
// Identified seam), exactly like TermTheory's parity with the Rust binding.
var (
	_ Theory     = ListTheory{}
	_ Identified = ListTheory{}
)

// Owns reports whether pred names an owned list relation. Mirrors Rust's
// ListTheory::owns / owns_name — by name, at any arity.
func (ListTheory) Owns(pred Symbol) bool {
	_, ok := listPredicates[string(pred.Bytes())]
	return ok
}

// Identity reports this theory's canonical component identity,
// logos-core/list-theory@1.0.0 with a zero config digest — byte-identical to the Rust
// theory's identity(), so a CheckProfile binding it derives the same theory binding (and
// thus the same stamped digest) tri-core. The logos-core/ namespace is a STABLE IDENTITY,
// not a path (ADR 0014/0016).
func (ListTheory) Identity() ComponentIdentity {
	return NewComponentIdentity(
		[]byte("logos-core/list-theory"),
		[]byte("1.0.0"),
		[32]byte{},
	)
}

// DecideGround decides an owned GROUND atom, byte-identically to the Rust
// ListTheory::decide_ground. A ground list relation binds nothing, so it either Holds (the
// relation is true) or Fails with a pinned host-band sub-code.
func (t ListTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	// Not one of ours: a routing safety net (check routes by Owns, so this is
	// unreachable on a correctly-routed call — but stay total). Mirrors Rust.
	if !t.Owns(atom.Pred) {
		return completion.TheoryGroundDisowned()
	}
	predBytes := atom.Pred.Bytes()
	if !utf8.Valid(predBytes) {
		return completion.TheoryGroundFails("list_unknown_predicate")
	}

	switch string(predBytes) {
	case "length":
		return decideLength(atom.Args)
	case "nth0":
		return decideNth0(atom.Args)
	case "last":
		return decideLast(atom.Args)
	default:
		// Owned name routed here but not handled above — unreachable (the name set is
		// exactly the switch arms), but stay total.
		return completion.TheoryGroundFails("list_does_not_hold")
	}
}

// listElements reads the elements of a GROUND list embedding Tuple(Atom("list"), e0, …),
// returning (elems, true), or (nil, false) if v is not a canonical list embedding. Thin
// wrapper over the frozen data.ReadList — the SAME recognizer the producer's reify emits
// through, so producer and checker agree by construction. Mirrors Rust's list_elements.
func listElements(v core.Value) ([]core.Value, bool) {
	elems, err := data.ReadList(v)
	if err != nil {
		return nil, false
	}
	return elems, true
}

// listDoesNotHold / listBadArity are the pinned host-band sub-codes, mirroring Rust's
// does_not_hold() / bad_arity().
func listDoesNotHold() completion.TheoryGround {
	return completion.TheoryGroundFails("list_does_not_hold")
}
func listBadArity() completion.TheoryGround { return completion.TheoryGroundFails("list_bad_arity") }

// decideLength decides length(list(e0..e_{n-1}), int(n)): arity must be 2; then arg0 must
// be a list embedding of n elements AND arg1 must be the canonical int embedding of that
// same n. A non-list arg0, a non-int arg1, or a count mismatch is list_does_not_hold.
// Mirrors Rust's decide_length.
func decideLength(args []core.Value) completion.TheoryGround {
	if len(args) != 2 {
		return listBadArity()
	}
	elems, ok := listElements(args[0])
	if !ok {
		return listDoesNotHold()
	}
	// Build the canonical int embedding of the length and compare structurally — so arg1
	// must be the SAME canonical int the Shelf-B length clauses (is/2 over the int
	// embedding) accumulate. A non-int or a wrong-int arg1 simply fails to equal it.
	want := data.EncodeInt(big.NewInt(int64(len(elems))))
	if core.Equal(args[1], want) {
		return completion.TheoryGroundHolds()
	}
	return listDoesNotHold()
}

// decideNth0 decides nth0(int(i), list(e0..e_{n-1}), e_i): arity must be 3; then arg0 must
// be a non-negative int index i, arg1 a list embedding, i in range 0 <= i < n, and arg2
// structurally equal to the i-th element. A non-int index, a non-list, an out-of-range
// index, or an element mismatch is list_does_not_hold. (Prolog/SWI argument order: index,
// list, element.) Mirrors Rust's decide_nth0.
func decideNth0(args []core.Value) completion.TheoryGround {
	if len(args) != 3 {
		return listBadArity()
	}
	// Index must be the canonical int embedding. A non-int / negative / out-of-range index
	// is simply a false relation (the element does not exist at that position).
	index, err := data.ReadInt(args[0])
	if err != nil {
		return listDoesNotHold()
	}
	elems, ok := listElements(args[1])
	if !ok {
		return listDoesNotHold()
	}
	if index.Sign() < 0 {
		return listDoesNotHold()
	}
	// index >= 0 here; a value that does not fit an int is trivially out of range.
	if !index.IsInt64() {
		return listDoesNotHold()
	}
	idx := index.Int64()
	if idx >= int64(len(elems)) {
		return listDoesNotHold()
	}
	if core.Equal(elems[idx], args[2]) {
		return completion.TheoryGroundHolds()
	}
	return listDoesNotHold()
}

// decideLast decides last(list(e0..e_{n-1}), e_{n-1}): arity must be 2; then arg0 must be a
// NON-EMPTY list embedding and arg1 structurally equal to its last element. A non-list, an
// empty list, or a mismatch is list_does_not_hold. Mirrors Rust's decide_last.
func decideLast(args []core.Value) completion.TheoryGround {
	if len(args) != 2 {
		return listBadArity()
	}
	elems, ok := listElements(args[0])
	if !ok {
		return listDoesNotHold()
	}
	if len(elems) == 0 {
		return listDoesNotHold()
	}
	if core.Equal(elems[len(elems)-1], args[1]) {
		return completion.TheoryGroundHolds()
	}
	return listDoesNotHold()
}
