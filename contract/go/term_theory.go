// TermTheory — the Go binding of logos-core's term-algebra Theory, a
// judgment-for-judgment mirror of the Rust TermTheory in
// contract/rs/src/term_theory.rs (ADR 0016, Shelf A0). [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the term
// recognizers and standard order: a program that uses atom/1, atomic/1, compound/1,
// is_list/1, number/1, ==/2, \==/2, @</2, @>/2, @=</2, @>=/2 can now be CHECKED in Go,
// because the same decide() that the Rust core uses is reproduced here byte-for-byte.
// All three cores agree on EVERY ground term atom — the §7 dual-conformance law, pinned
// by vectors/term.json.
//
// # The home (why contract/go)
//
// Rust's TermTheory lives in the contract tier (contract/rs), beside the Theory SPI, per
// ADR 0014 / ADR 0016: a pure, total, deterministic function of a resolved ground term is
// a shared certifiable artifact, not a search-only Rust builtin. Go has no core tier; the
// checker SPI is tri-core in contract/go, and the reusable Theory impls a consumer binds
// (e.g. AlwaysAdmit, ArithmeticTheory, TextTheory) live HERE, beside the SPI. So this is
// where a Go consumer binds the term recognizers + standard order.
//
// # The standard order (ground restriction: Atom < Tuple)
//
// Ground terms are an ontos Value = Atom(bytes) | Tuple(items) — there is NO Var. The full
// standard order is Var < Atom < Tuple; restricted to ground terms it is Atom < Tuple,
// ties by atom bytes / tuple arity-then-elementwise. A number is the int embedding
// Tuple(Atom("int"), Atom(payload)) — structurally a Tuple — so it sorts with the
// compound rank, NOT before atoms (matching the search-side compare_terms). number/1
// still distinguishes a number from a bare atom via the embedding shape (data.ReadInt).
//
// # Judgments (mirroring Rust exactly)
//
// Owns(pred): by NAME only (any arity) — the five recognizers, six comparisons, univ, and
// (since 1.1.0, #1611) unification + the control constants.
// DecideGround(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{term_unknown_predicate}   (defensive)
//   - recognizer not at arity 1
//     OR comparison not at arity 2
//     OR control constant not at 0   -> Fails{term_bad_arity}
//   - the relation is true           -> Holds
//   - the relation is false          -> Fails{term_does_not_hold}
//
// # Unification and the control constants (1.1.0, #1611 — seat:caa's ruling)
//
// =/2, \=/2, true/0, fail/0 and false/0 are served by the rs engine's Stage-A registry but
// dispatched only behind theory.Owns, and the checker's Builtin arm accepts a node only if a
// bound theory owns its predicate — so until a theory owned them, `X = a` in a body yielded
// a SILENT empty answer and no Builtin node could certify. On ground terms syntactic
// unification is structural equality, so `t = u` holds iff compareValues(t, u) == 0 and
// `t \= u` iff it differs; `true` holds; `fail`/`false` never hold. Mirrors Rust exactly.
package contract

import (
	"bytes"
	"unicode/utf8"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// consFunctor is the list-cons functor `.`/2 ([H|T] = Tuple(Atom("."), H, T)); nilAtom
// is the empty-list atom `[]`. Mirror the Rust CONS_FUNCTOR / NIL_ATOM bytes.
var (
	consFunctor = []byte(".")
	nilAtom     = []byte("[]")
)

// recognizerPredicates is the set of arity-1 recognizer names TermTheory owns, mirroring
// Rust's RECOGNIZER_PREDICATES. Owned by name only.
var recognizerPredicates = map[string]struct{}{
	"atom":     {},
	"atomic":   {},
	"compound": {},
	"is_list":  {},
	"number":   {},
}

// comparisonPredicates is the set of arity-2 standard-order comparison names TermTheory
// owns, mirroring Rust's COMPARISON_PREDICATES. Owned by name only.
var comparisonPredicates = map[string]struct{}{
	"==":   {},
	"\\==": {},
	"@<":   {},
	"@>":   {},
	"@=<":  {},
	"@>=":  {},
}

// univPredicate is the arity-2 structural decomposition primitive `=..` (univ): relates a
// term to the cons-list [Functor | Args] of its principal functor and arguments. Mirrors
// Rust's UNIV_PREDICATE (#658). Owned by name only.
const univPredicate = "=.."

// unificationPredicates is the set of arity-2 unification relation names TermTheory owns
// since 1.1.0 (#1611), mirroring Rust's UNIFICATION_PREDICATES. Owned by name only.
var unificationPredicates = map[string]struct{}{
	"=":   {},
	"\\=": {},
}

// controlPredicates is the set of arity-0 control constants TermTheory owns since 1.1.0
// (#1611), mirroring Rust's CONTROL_PREDICATES. Owned by name only.
var controlPredicates = map[string]struct{}{
	"true":  {},
	"fail":  {},
	"false": {},
}

// TermTheory is the config-pinned §5 Theory that owns the A0 term recognizers and the
// standard-order comparisons and decides a GROUND term atom by a constant-time structural
// match (no search, no trail). Pure / total / deterministic / config-free — a faithful
// mirror of Rust's contract::term_theory::TermTheory.
type TermTheory struct{}

// NewTermTheory builds the standard term Theory (no configuration).
func NewTermTheory() TermTheory { return TermTheory{} }

// compile-time proofs that the theory satisfies the SPI seam (Theory + the optional
// Identified seam), exactly like TextTheory's parity with the Rust binding.
var (
	_ Theory     = TermTheory{}
	_ Identified = TermTheory{}
)

// Owns reports whether pred names an owned term relation. Mirrors Rust's
// TermTheory::owns / owns_name — by name, at any arity.
func (TermTheory) Owns(pred Symbol) bool {
	name := string(pred.Bytes())
	if _, ok := recognizerPredicates[name]; ok {
		return true
	}
	if _, ok := comparisonPredicates[name]; ok {
		return true
	}
	if _, ok := unificationPredicates[name]; ok {
		return true
	}
	if _, ok := controlPredicates[name]; ok {
		return true
	}
	return name == univPredicate
}

// Identity reports this theory's canonical component identity,
// logos-core/term-theory@1.1.0 with a zero config digest — byte-identical to the Rust
// theory's identity(), so a CheckProfile binding it derives the same theory binding (and
// thus the same stamped digest) tri-core. The logos-core/ namespace is a STABLE IDENTITY,
// not a path (ADR 0014/0016). 1.0.0 -> 1.1.0 with #1611 (the owned set grew by = \= true
// fail false).
func (TermTheory) Identity() ComponentIdentity {
	return NewComponentIdentity(
		[]byte("logos-core/term-theory"),
		[]byte("1.1.0"),
		[32]byte{},
	)
}

// DecideGround decides an owned GROUND term atom, byte-identically to the Rust
// TermTheory::decide_ground. A ground term relation binds nothing, so it either Holds (the
// relation is true) or Fails with a pinned host-band sub-code.
func (t TermTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	// Not one of ours: a routing safety net (check routes by Owns, so this is
	// unreachable on a correctly-routed call — but stay total). Mirrors Rust.
	if !t.Owns(atom.Pred) {
		return completion.TheoryGroundDisowned()
	}
	predBytes := atom.Pred.Bytes()
	if !utf8.Valid(predBytes) {
		return completion.TheoryGroundFails("term_unknown_predicate")
	}

	switch string(predBytes) {
	// A0 recognizers (arity 1).
	case "atom":
		return decideRecognizer(atom.Args, isAtomValue)
	case "atomic":
		// In the ground term world the only atomic terms are Atoms (no Var, a number is
		// the int Tuple embedding), so atomic coincides with atom.
		return decideRecognizer(atom.Args, isAtomValue)
	case "compound":
		return decideRecognizer(atom.Args, isTupleValue)
	case "is_list":
		return decideRecognizer(atom.Args, isProperList)
	case "number":
		return decideRecognizer(atom.Args, isNumber)
	// A0 standard-order comparisons (arity 2).
	case "==":
		return decideComparison(atom.Args, func(c int) bool { return c == 0 })
	case "\\==":
		return decideComparison(atom.Args, func(c int) bool { return c != 0 })
	case "@<":
		return decideComparison(atom.Args, func(c int) bool { return c < 0 })
	case "@>":
		return decideComparison(atom.Args, func(c int) bool { return c > 0 })
	case "@=<":
		return decideComparison(atom.Args, func(c int) bool { return c <= 0 })
	case "@>=":
		return decideComparison(atom.Args, func(c int) bool { return c >= 0 })
	// A0 structural decomposition (arity 2): univ.
	case "=..":
		return decideUniv(atom.Args)
	// Unification over GROUND terms (arity 2, #1611): structural equality.
	case "=":
		return decideComparison(atom.Args, func(c int) bool { return c == 0 })
	case "\\=":
		return decideComparison(atom.Args, func(c int) bool { return c != 0 })
	// Control constants (arity 0, #1611).
	case "true":
		return decideControl(atom.Args, true)
	case "fail", "false":
		return decideControl(atom.Args, false)
	default:
		// Owned name routed here but not handled above — unreachable (the name set is
		// exactly the switch arms), but stay total.
		return completion.TheoryGroundFails("term_does_not_hold")
	}
}

// isAtomValue reports whether a ground value is a bare Atom.
func isAtomValue(v core.Value) bool {
	_, ok := v.(core.Atom)
	return ok
}

// isTupleValue reports whether a ground value is a compound Tuple.
func isTupleValue(v core.Value) bool {
	_, ok := v.(core.Tuple)
	return ok
}

// isNil reports whether a ground value is the nil atom `[]`.
func isNil(v core.Value) bool {
	a, ok := v.(core.Atom)
	return ok && bytes.Equal(a.Bytes(), nilAtom)
}

// asCons matches a [H|T] cons cell over a GROUND value (a 3-element tuple headed by the
// `.` atom), returning (head, tail, true). Mirrors Rust's as_cons.
func asCons(v core.Value) (core.Value, core.Value, bool) {
	tuple, ok := v.(core.Tuple)
	if !ok {
		return nil, nil, false
	}
	items := tuple.Items()
	if len(items) != 3 {
		return nil, nil, false
	}
	head, ok := items[0].(core.Atom)
	if !ok || !bytes.Equal(head.Bytes(), consFunctor) {
		return nil, nil, false
	}
	return items[1], items[2], true
}

// isProperList reports whether a GROUND value is a proper list (a []-terminated chain of
// `.`/2 cons cells). A ground value can never be partial (no Var), so only the
// improper-tail case fails. Mirrors Rust's is_proper_list.
func isProperList(v core.Value) bool {
	current := v
	for {
		if isNil(current) {
			return true
		}
		_, tail, ok := asCons(current)
		if !ok {
			return false
		}
		current = tail
	}
}

// isNumber reports whether a GROUND value is a (canonical) exact-integer int embedding OR
// a (canonical) exact-decimal decimal embedding (#331). Unlike atom, a number-shaped bare
// atom ("3.14" or Atom("42")) does NOT count — only the genuine embeddings do. Shares the
// recognizers with the search-side number/1, so the two agree byte-for-byte.
func isNumber(v core.Value) bool {
	if _, err := data.ReadInt(v); err == nil {
		return true
	}
	_, ok := decFromTerm(v)
	return ok
}

// decideRecognizer decides an arity-1 recognizer: arity must be 1; then test(arg0). A
// non-1 arity has no such relation (term_bad_arity); a false test is term_does_not_hold.
func decideRecognizer(args []core.Value, test func(core.Value) bool) completion.TheoryGround {
	if len(args) != 1 {
		return completion.TheoryGroundFails("term_bad_arity")
	}
	if test(args[0]) {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("term_does_not_hold")
}

// decideComparison decides an arity-2 standard-order comparison: arity must be 2; then
// accept iff accept(compareValues(arg0, arg1)). A non-2 arity has no such relation
// (term_bad_arity); a false comparison is term_does_not_hold.
func decideComparison(args []core.Value, accept func(int) bool) completion.TheoryGround {
	if len(args) != 2 {
		return completion.TheoryGroundFails("term_bad_arity")
	}
	if accept(compareValues(args[0], args[1])) {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("term_does_not_hold")
}

// decideControl decides an arity-0 control constant (#1611): arity must be 0
// (term_bad_arity otherwise); then `true` holds and `fail`/`false` are term_does_not_hold.
// Mirrors Rust's decide_control.
func decideControl(args []core.Value, holds bool) completion.TheoryGround {
	if len(args) != 0 {
		return completion.TheoryGroundFails("term_bad_arity")
	}
	if holds {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("term_does_not_hold")
}

// valueConsList builds the cons-list [e0, e1, … en] as a ground Value — the frozen `.`/2
// cons form ([]-terminated). Mirrors Rust's value_cons_list.
func valueConsList(elements []core.Value) core.Value {
	var acc core.Value = core.NewAtom(nilAtom)
	for i := len(elements) - 1; i >= 0; i-- {
		acc = core.NewTuple(core.NewAtom(consFunctor), elements[i], acc)
	}
	return acc
}

// univListOf returns the univ image of a ground term: the [Functor | Args] cons-list a
// `T =.. L` relation holds for. A labeled compound Tuple(Atom(f), a1 … an) -> [f, a1, … an];
// a bare Atom(a) -> [a]. An empty tuple or a non-Atom-headed tuple is outside the
// labeled-compound image (ok=false). Mirrors Rust's univ_list_of.
func univListOf(v core.Value) (core.Value, bool) {
	switch t := v.(type) {
	case core.Atom:
		return valueConsList([]core.Value{v}), true
	case core.Tuple:
		items := t.Items()
		if len(items) == 0 {
			return nil, false
		}
		if _, ok := items[0].(core.Atom); !ok {
			return nil, false
		}
		return valueConsList(items), true
	default:
		return nil, false
	}
}

// decideUniv decides the arity-2 univ relation `T =.. L`: arity must be 2; then Holds iff L
// equals the univ image of T. A T that is not a labeled compound / atom -> univ_not_callable;
// a mismatched L -> univ_mismatch. Mirrors Rust's decide_univ.
func decideUniv(args []core.Value) completion.TheoryGround {
	if len(args) != 2 {
		return completion.TheoryGroundFails("term_bad_arity")
	}
	expected, ok := univListOf(args[0])
	if !ok {
		return completion.TheoryGroundFails("univ_not_callable")
	}
	if compareValues(args[1], expected) == 0 {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("univ_mismatch")
}

// compareValues compares two GROUND terms by the standard order of terms — a total order
// consistent with structural equality (compareValues(a, b) == 0 iff a == b). Ground terms
// are ranked Atom < Tuple; within a rank, Atoms order by raw bytes and Tuples first by
// arity then element-wise. Returns a three-way result (-1 / 0 / +1). Mirrors Rust's
// contract::term_theory::compare_values byte-for-byte (and the search-side compare_terms
// over ground terms).
func compareValues(a, b core.Value) int {
	aAtom, aIsAtom := a.(core.Atom)
	bAtom, bIsAtom := b.(core.Atom)
	switch {
	case aIsAtom && bIsAtom:
		return bytes.Compare(aAtom.Bytes(), bAtom.Bytes())
	case aIsAtom && !bIsAtom:
		// Atom (rank 0) before Tuple (rank 1).
		return -1
	case !aIsAtom && bIsAtom:
		return 1
	default:
		// Both Tuples: by arity, then element-wise.
		aItems := a.(core.Tuple).Items()
		bItems := b.(core.Tuple).Items()
		if len(aItems) != len(bItems) {
			if len(aItems) < len(bItems) {
				return -1
			}
			return 1
		}
		for i := range aItems {
			if c := compareValues(aItems[i], bItems[i]); c != 0 {
				return c
			}
		}
		return 0
	}
}
