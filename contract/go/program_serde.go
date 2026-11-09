// §10 Program (de)serialization — a clause MapProgram ⇄ a ground ontos Value, with
// CANONICAL, byte-deterministic ontos-codec-v1 output (issue #310). Go sibling of
// contract/rs/src/program_serde.rs.
//
// A consumer's whole policy is a MapProgram — a ClauseId → Clause map. To store,
// transmit, or content-address a WHOLE program (not just a single clause) it must
// become ordinary ground data and back. This is the program-level analogue of the §2a
// Quote/Reify term reification and the §9 per-clause account codec; it REUSES both, so
// it introduces no new frozen bytes:
//
//	ProgramToValue(p) = Tuple[ Atom(version), entry0, entry1, …, entry_{n-1} ]
//	entry_i           = Tuple[ Atom(<clause-id utf8 bytes>), ClauseValue(clause_i) ]
//
// where ClauseValue is the FROZEN account encoding of a clause's head :- body (head +
// polarity-tagged body via the §2a Quote tags and the ADR-0007 negTag). The entries are
// emitted in CANONICAL ORDER — sorted by the clause-id bytes — so the value (and hence
// its ontos-codec-v1 bytes) is INDEPENDENT of MapProgram insertion order: two programs
// with the same (id, clause) set serialize to byte-identical output. The leading
// Atom(version) domain-separates the shape.
//
// Canonical bytes := codec.Encode(ProgramToValue(p)) — the cross-language byte-pin all
// three bindings reproduce (vectors/program_serde.json). Byte-identical to Rust's
// program_bytes and the TS programBytes.
//
// THE RESERVED PREDICATE SYMBOL (why serialization is FALLIBLE). The frozen account
// body-literal encoding is NOT injective over arbitrary predicate symbols: a POSITIVE
// literal reads as the bare goalAsTerm(g) = Tuple[Atom(pred), args...] and a NEGATED one
// as Tuple[Atom(negTag=0x00), goalAsTerm(g)]. A positive literal whose predicate symbol
// is exactly the single byte 0x00 AND which has exactly one argument therefore encodes to
// Tuple[Atom(0x00), arg] — byte-identical to a Neg reading, so a decoder cannot recover
// the polarity. (Symbol/Goal accept arbitrary bytes with no validation, so such a clause
// is reachable via the public API.) Because the account encoding is FROZEN (its bytes
// feed ClauseBytes / ProgramDigest, cross-core vectored), the sound fix is to RESERVE the
// byte 0x00 as the body-literal negation tag: it is not a valid predicate name in a
// serializable program. ProgramToValue / ProgramBytes therefore REJECT (with
// ErrProgramReservedPredicate) any clause whose head or body-literal predicate equals
// a reserved tag. A portable entry also requires a UTF-8 clause ID. Encoding a
// native handle outside that domain returns a ClauseIdEncodingError.
package contract

import (
	"bytes"
	"fmt"
	"sort"
	"unicode/utf8"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// ProgramFormatTag returns the exact leading atom of a v1 serialized program.
func ProgramFormatTag() []byte { return []byte("logos/program/v1") }

// ReservedProgramPredicateSymbols returns the predicate bytes reserved by the
// negation and count literal encodings, in wire order. The caller owns both slices.
func ReservedProgramPredicateSymbols() [][]byte { return [][]byte{{negTag}, {countTag}} }

// ReservedPredicateOf returns the first reserved predicate symbol (see ReservedProgramPredicateSymbols)
// the clause carries, on its head or any body literal, the counted predicate of a count literal
// included, and whether there is one. The one check every ingress shares (#2247). Mirrors Rust's
// reserved_predicate.
func ReservedPredicateOf(clause Clause) ([]byte, bool) {
	preds := [][]byte{clause.Head.Pred.Bytes()}
	for _, lit := range clause.Body {
		preds = append(preds, lit.Pred().Bytes())
	}
	reservedNames := ReservedProgramPredicateSymbols()
	for _, pred := range preds {
		for _, reserved := range reservedNames {
			if bytes.Equal(pred, reserved) {
				return pred, true
			}
		}
	}
	return nil, false
}

type programFormatError string

func (e programFormatError) Error() string { return string(e) }

// These constants classify program codec failures and support errors.Is through wrapping.
const (
	// ErrProgramNotATuple: the top-level value was not a Tuple.
	ErrProgramNotATuple programFormatError = "program value is not a Tuple"
	// ErrProgramBadVersion: the leading child was not Atom(ProgramFormatTag()).
	ErrProgramBadVersion programFormatError = "program value has a bad/missing version tag"
	// ErrProgramBadEntry: an entry was not Tuple[Atom(id), clause].
	ErrProgramBadEntry programFormatError = "program entry is not a Tuple[Atom(id), clause]"
	// ErrProgramBadClause: an entry's clause value was not in the image of ClauseValue.
	ErrProgramBadClause programFormatError = "program entry's clause value is malformed"
	// ErrProgramReservedPredicate identifies either wire-reserved predicate.
	// ProgramToValue and ProgramBytes wrap it with the clause ID and predicate bytes.
	ErrProgramReservedPredicate programFormatError = "clause carries a reserved predicate symbol (an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)"
)

// checkNoReservedPredicate rejects a clause that carries the reserved predicate symbol
// on its head or any body literal — the encode-time guard that keeps the round-trip
// total (see the package note). Returns nil, or an error wrapping
// ErrProgramReservedPredicate (errors.Is matches) naming the clause + predicate.
func checkNoReservedPredicate(id string, clause Clause) error {
	if pred, ok := ReservedPredicateOf(clause); ok {
		return fmt.Errorf("clause %s: predicate 0x%x: %w", id, pred, ErrProgramReservedPredicate)
	}
	return nil
}

// ClauseIdEncodingError reports an opaque native handle without a valid UTF-8
// encoding in a portable program or proof. Native clause lookup still accepts it.
type ClauseIdEncodingError struct {
	ClauseID ClauseId
}

func (e *ClauseIdEncodingError) Error() string {
	return fmt.Sprintf("clause ID %q cannot be encoded as UTF-8", e.ClauseID.String())
}

func (id ClauseId) requirePortable() error {
	if !utf8.ValidString(id.handle) {
		return &ClauseIdEncodingError{ClauseID: id}
	}
	return nil
}

// ProgramToValue serializes a MapProgram to its canonical ground ontos Value (§10).
//
// FALLIBLE — returns an error wrapping ErrProgramReservedPredicate if any clause carries
// a goal (head or body literal) whose predicate symbol equals a reserved account tag; such a clause cannot be serialized unambiguously under the
// frozen account encoding (see the package note). Invalid UTF-8 clause IDs return a
// *ClauseIdEncodingError. For every ACCEPTED program there is
// exactly one canonical value. The clause entries are emitted SORTED by clause-id bytes
// (independent of how the program was built). The canonical BYTES are codec.Encode of
// this.
func ProgramToValue(program *MapProgram) (core.Value, error) {
	type entry struct {
		id  string
		val core.Value
	}
	entries := make([]entry, 0, len(program.clauses))
	for id, clause := range program.clauses {
		if err := checkNoReservedPredicate(id.handle, clause); err != nil {
			return nil, err
		}
		if err := id.requirePortable(); err != nil {
			return nil, err
		}
		entries = append(entries, entry{id: id.handle, val: ClauseValue(clause)})
	}
	// Canonical order: sort ascending by clause-id bytes (the same total order Rust's
	// BTreeMap<ClauseId> iteration / the defensive sort fixes).
	sort.Slice(entries, func(i, j int) bool {
		return bytes.Compare([]byte(entries[i].id), []byte(entries[j].id)) < 0
	})
	children := make([]core.Value, 0, len(entries)+1)
	children = append(children, core.NewAtom(ProgramFormatTag()))
	for _, e := range entries {
		children = append(children, core.NewTuple(core.NewAtom([]byte(e.id)), e.val))
	}
	return core.NewTuple(children...), nil
}

// ProgramBytes is the canonical bytes of a program: ontos-codec-v1(ProgramToValue(p)).
// The single cross-language byte-pin (vectors/program_serde.json). FALLIBLE for the same
// reserved-predicate and clause-ID reasons as ProgramToValue.
func ProgramBytes(program *MapProgram) ([]byte, error) {
	value, err := ProgramToValue(program)
	if err != nil {
		return nil, err
	}
	return codec.Encode(value), nil
}

// ProgramFromValue is the partial inverse of ProgramToValue: rebuild the MapProgram a
// value denotes, or an error if value is not in the image of ProgramToValue (§10). The
// round-trip law is total over accepted programs. For every p that ProgramToValue
// accepts, ProgramFromValue(ProgramToValue(p)) equals p.
func ProgramFromValue(value core.Value) (*MapProgram, error) {
	tup, ok := value.(core.Tuple)
	if !ok {
		return nil, ErrProgramNotATuple
	}
	items := tup.Items()
	if len(items) == 0 {
		return nil, ErrProgramBadVersion
	}
	versionAtom, ok := items[0].(core.Atom)
	if !ok || !bytes.Equal(versionAtom.Bytes(), ProgramFormatTag()) {
		return nil, ErrProgramBadVersion
	}
	program := NewMapProgram()
	for _, entry := range items[1:] {
		pair, ok := entry.(core.Tuple)
		if !ok {
			return nil, ErrProgramBadEntry
		}
		pairItems := pair.Items()
		if len(pairItems) != 2 {
			return nil, ErrProgramBadEntry
		}
		idAtom, ok := pairItems[0].(core.Atom)
		if !ok {
			return nil, ErrProgramBadEntry
		}
		// The id was serialized from a ClauseId's UTF-8 handle bytes; reject a non-UTF-8
		// id (a ClauseId handle is a Go string, so a well-formed program never carries one).
		if !utf8.Valid(idAtom.Bytes()) {
			return nil, ErrProgramBadEntry
		}
		id := string(idAtom.Bytes())
		clause, ok := ClauseFromValue(pairItems[1])
		if !ok {
			return nil, ErrProgramBadClause
		}
		if _, exists := program.clauses[NewClauseId(id)]; exists {
			return nil, fmt.Errorf("duplicate clause id in serialized program: %s", id)
		}
		program.Insert(NewClauseId(id), clause)
	}
	return program, nil
}
