// TextTheory — the Go binding of logos-core's byte-string Theory, a
// judgment-for-judgment mirror of the Rust TextTheory in contract/rs/src/text.rs
// (ADR 0016, Shelf A). [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification to the text
// relations: a program that uses contains/2, starts_with/2, ends_with/2 can now be
// CHECKED in Go, because the same decide() that the Rust core uses is reproduced here
// byte-for-byte. All three cores agree on EVERY ground text atom — the §7
// dual-conformance law, pinned by vectors/text.json.
//
// # The home (why contract/go)
//
// Rust's TextTheory lives in the contract tier (contract/rs), beside the Theory SPI,
// per ADR 0014 / ADR 0016: a pure, total, deterministic function of ground args is a
// shared certifiable artifact, not a search-only Rust builtin. Go has no core tier; the
// checker SPI is tri-core in contract/go, and the reusable Theory impls a consumer
// binds (e.g. AlwaysAdmit, ArithmeticTheory) live HERE, beside the SPI. So this is
// where a Go consumer binds the text relations.
//
// # The operand domain (raw Atom bytes, NOT the utf8-text embedding)
//
// Operands are RAW Atom bytes — exactly what the search builtins read
// (logos_core::builtins::{builtin_contains, builtin_starts_with, builtin_ends_with})
// and what the Rust TextTheory decides over. The utf8-text *embedding* is a Tuple, so
// it is NOT a bare Atom and therefore does not hold (text_does_not_hold). Matching is
// byte-level over the UTF-8 encoding, not codepoint-level.
//
// # Judgments (mirroring Rust exactly)
//
// Owns(pred): by NAME only (any arity) — contains, starts_with, ends_with. There is no
// nested expression grammar (unlike arithmetic operators), so nothing else to exclude.
// DecideGround(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{text_unknown_predicate}   (defensive)
//   - owned name, arity != 2         -> Fails{text_bad_arity}
//   - both args bare Atoms, test true -> Holds
//   - false test OR a non-Atom arg
//     (a compound, or the utf8-text
//     embedding, which is a Tuple)   -> Fails{text_does_not_hold}
//
// An empty needle / prefix / suffix HOLDS (every byte-slice contains/starts with/ends
// with the empty slice) — Go's bytes.Contains/HasPrefix/HasSuffix agree byte-for-byte
// with Rust's contains_subslice / slice::starts_with / slice::ends_with.
package contract

import (
	"bytes"
	"unicode/utf8"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// textPredicates is the set of relation names TextTheory owns, mirroring Rust's
// TEXT_PREDICATES. Owned by name only — an unregistered arity routes here and Fails
// (a malformed text goal), never panics.
var textPredicates = map[string]struct{}{
	"contains":    {},
	"starts_with": {},
	"ends_with":   {},
}

// TextTheory is the config-pinned §5 Theory that owns the byte-string relations
// (contains/2, starts_with/2, ends_with/2) and decides a GROUND text atom by a
// byte-level test over the raw Atom operands. Pure / total / deterministic /
// config-free — a faithful mirror of Rust's contract::text::TextTheory.
type TextTheory struct{}

// NewTextTheory builds the standard text Theory (no configuration).
func NewTextTheory() TextTheory { return TextTheory{} }

// compile-time proofs that the theory satisfies the SPI seam (Theory + the optional
// Identified seam), exactly like ArithmeticTheory's parity with the Rust binding.
var (
	_ Theory     = TextTheory{}
	_ Identified = TextTheory{}
)

// Owns reports whether pred names an owned text relation. Mirrors Rust's
// TextTheory::owns / owns_name — by name, at any arity.
func (TextTheory) Owns(pred Symbol) bool {
	_, ok := textPredicates[string(pred.Bytes())]
	return ok
}

// Identity reports this theory's canonical component identity,
// logos-core/text-theory@1.0.0 with a zero config digest — byte-identical to the Rust
// theory's identity(), so a CheckProfile binding it derives the same theory binding
// (and thus the same stamped digest) tri-core. The logos-core/ namespace is a STABLE
// IDENTITY, not a path (ADR 0014/0016).
func (TextTheory) Identity() ComponentIdentity {
	return NewComponentIdentity(
		[]byte("logos-core/text-theory"),
		[]byte("1.0.0"),
		[32]byte{},
	)
}

// DecideGround decides an owned GROUND text atom, byte-identically to the Rust
// TextTheory::decide_ground. A ground text relation binds nothing, so it either Holds (the
// byte test is true) or Fails with a pinned host-band sub-code.
func (t TextTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	// Not one of ours: a routing safety net (check routes by Owns, so this is
	// unreachable on a correctly-routed call — but stay total). Mirrors Rust.
	if !t.Owns(atom.Pred) {
		return completion.TheoryGroundDisowned()
	}
	// An owned name is always valid UTF-8 (the names are ASCII), but mirror Rust's
	// std::str::from_utf8 guard so the non-UTF-8 defensive arm carries the identical
	// code on every path.
	predBytes := atom.Pred.Bytes()
	if !utf8.Valid(predBytes) {
		return completion.TheoryGroundFails("text_unknown_predicate")
	}

	switch string(predBytes) {
	case "contains":
		return decideTextRelation(atom.Args, bytes.Contains)
	case "starts_with":
		return decideTextRelation(atom.Args, bytes.HasPrefix)
	case "ends_with":
		return decideTextRelation(atom.Args, bytes.HasSuffix)
	default:
		// Owned name routed here but not handled above — unreachable (the name set is
		// exactly the switch arms), but stay total.
		return completion.TheoryGroundFails("text_does_not_hold")
	}
}

// textAtomBytes returns the bytes of a bare Atom, or ok == false for any non-atom value
// (a compound Tuple — including the utf8-text embedding — which a binary text test
// cannot run over). Mirrors the Rust atom_bytes accessor (and the search builtins).
func textAtomBytes(v core.Value) ([]byte, bool) {
	a, ok := v.(core.Atom)
	if !ok {
		return nil, false
	}
	return a.Bytes(), true
}

// decideTextRelation decides a binary byte-string relation: arity must be 2; both args
// must be bare Atoms; then test(arg0Bytes, arg1Bytes). Mirrors Rust's decide_relation
// (and the search-side builtins): a non-atom arg or a false test is text_does_not_hold;
// a non-2 arity has no such relation (text_bad_arity). The test functions are Go's
// bytes.Contains/HasPrefix/HasSuffix, which agree with Rust byte-for-byte (an empty
// needle/prefix/suffix holds).
func decideTextRelation(args []core.Value, test func(text, sub []byte) bool) completion.TheoryGround {
	if len(args) != 2 {
		return completion.TheoryGroundFails("text_bad_arity")
	}
	lhs, lok := textAtomBytes(args[0])
	rhs, rok := textAtomBytes(args[1])
	if lok && rok && test(lhs, rhs) {
		return completion.TheoryGroundHolds()
	}
	return completion.TheoryGroundFails("text_does_not_hold")
}
