// §2a Reification — quote / reify. [STABLE v1 shape · byte form FROZEN v1]
// Go sibling of contract/rs/src/reify.rs.
//
// Storing or transmitting a *rule* (a clause with variables) as ordinary data
// requires turning a term-with-holes into a ground ontos value and back. The
// *semantic shape* (quote is total and round-trips via reify) and the *exact
// canonical bytes* (the tags below) are now both FROZEN — §9 is settled: VarId is
// SYNTACTIC (variable names are encoded; no alpha-normalization), so quote is the
// canonical encoding the account codec (account.go) hashes. Changing a tag is a
// breaking change shipped as a new version, never an edit.
//
// The encoding tags every node with a leading 1-byte atom so the structure is
// self-describing and reify is an unambiguous partial inverse — including a
// reserved *quoted-variable* shape, distinct from the live Var constructor (which
// is not an ontos value, §1). Because the tagging is uniform, no consumer atom is
// ever "reserved": ordinary data round-trips through the ATOM/TUPLE tags and a
// quoted variable is only ever produced by quote.
//
// The tag bytes below are FROZEN v1 and byte-identical to the Rust and TS bindings.
package contract

import core "github.com/bitspark/ontos/core/go"

const (
	tagQuoteAtom  = 0x00
	tagQuoteTuple = 0x01
	tagQuoteVar   = 0x02
)

// Quote is total: maps Atom/Tuple/Var → a ground ontos value (§2a).
//
// A VarId's name is UTF-8 text. A Go string can hold other bytes, which rs's String cannot, so a
// VarId built from such a string is outside the contract's domain: Quote writes its bytes, and
// Reify refuses them (#3102).
func Quote(term Term) core.Value {
	switch t := term.(type) {
	case AtomTerm:
		return core.NewTuple(core.NewAtom([]byte{tagQuoteAtom}), core.NewAtom(t.bytes))
	case TupleTerm:
		quoted := make([]core.Value, len(t.children))
		for i, c := range t.children {
			quoted[i] = Quote(c)
		}
		return core.NewTuple(core.NewAtom([]byte{tagQuoteTuple}), core.NewTuple(quoted...))
	case VarTerm:
		return core.NewTuple(core.NewAtom([]byte{tagQuoteVar}), core.NewAtom([]byte(t.id.name)))
	default:
		panic("contract: Quote: unknown Term implementation")
	}
}

// Reify is the partial inverse of Quote: (term, true) iff value is in the image of
// Quote, else (nil, false) (§2a).
func Reify(value core.Value) (Term, bool) {
	tuple, ok := value.(core.Tuple)
	if !ok {
		return nil, false
	}
	items := tuple.Items()
	if len(items) != 2 {
		return nil, false
	}
	tagAtom, ok := items[0].(core.Atom)
	if !ok {
		return nil, false
	}
	tag := tagAtom.Bytes()
	if len(tag) != 1 {
		return nil, false
	}
	switch tag[0] {
	case tagQuoteAtom:
		a, ok := items[1].(core.Atom)
		if !ok {
			return nil, false
		}
		return AtomTerm{bytes: a.Bytes()}, true
	case tagQuoteVar:
		a, ok := items[1].(core.Atom)
		if !ok {
			return nil, false
		}
		// A VarId's name is UTF-8 text in every core (rs holds it as a String, ts decodes it
		// strictly), so a quoted variable whose name bytes are not valid UTF-8 is outside
		// quote's image and is refused, exactly as rs's `std::str::from_utf8(..).ok()?` and
		// ts's fatal decoder refuse it. A Go string can hold any bytes, so this check is what
		// keeps go from reading one untrusted wire differently (#3102). The parity is pinned,
		// not asserted: vectors/reify.json (`refused`/`reifies`) and derivation_wire.json's
		// subst_term_quoted_var_not_utf8 are replayed by all three cores. The test is
		// ParseVarId's, the one every VarId construction makes (validVarName, #3115), so reify
		// and the constructor cannot disagree about a name. An atom's bytes (tagQuoteAtom above)
		// are opaque data and are never checked.
		id, err := ParseVarId(string(a.Bytes()))
		if err != nil {
			return nil, false
		}
		return VarTerm{id: id}, true
	case tagQuoteTuple:
		children, ok := items[1].(core.Tuple)
		if !ok {
			return nil, false
		}
		childItems := children.Items()
		out := make([]Term, 0, len(childItems))
		for _, child := range childItems {
			c, ok := Reify(child)
			if !ok {
				return nil, false
			}
			out = append(out, c)
		}
		return TupleTerm{children: out}, true
	default:
		return nil, false
	}
}
