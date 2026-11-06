// §2a/§9 Account codec — the canonical, FROZEN encoding of account artifacts
// (quote byte form · ClauseId canonical hash). Go sibling of
// contract/rs/src/account.rs.
//
// This freezes the Quote byte form (§2a) and defines the canonical ClauseId as the
// SHA-256 of the domain-separated, ontos-codec bytes of a clause Quote'd into a
// ground ontos value.
//
// SYNTACTIC (§9 decision, 2026-06-01): variable names are part of the encoding —
// there is no alpha-normalization. p(X):-q(X) and p(Y):-q(Y) are distinct clauses
// with distinct ids. Cross-language: any {rs,ts,go} binding that follows this
// encoding computes the same id for the same clause — pinned for all three by the
// shared vectors/account.json.
package contract

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"math/big"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ClausePrefix is the domain separator for a canonical clause hash (so a clause id
// can never collide with another hash over the same bytes).
var ClausePrefix = []byte("logos/account/clause/v1\n")

// ProgramPrefix is the domain separator for the canonical whole-program digest (ADR
// 0007 §3.1). Distinct from ClausePrefix so a program digest can never collide with a
// single-clause hash over the same bytes. Mirrors Rust's PROGRAM_PREFIX.
var ProgramPrefix = []byte("logos/account/program/v1\n")

// negTag is the tag byte sealing the negated body-literal reading (ADR 0007). A
// Neg(g) reads as Tuple[Atom(negTag), goalAsTerm(g)] — a 2-tuple whose first child
// is this single-byte atom. A positive goalAsTerm(g) is Tuple[Atom(pred), args…]
// whose first child is the PREDICATE atom. The two readings are distinct only because
// 0x00 is not a valid predicate name: a Symbol itself accepts any bytes, so a positive
// literal with predicate 0x00 WOULD read as a Neg. This reading is therefore injective
// only over clauses without a reserved predicate, and every ingress refuses one
// (ReservedPredicateOf: ProgramToValue, LoadPrelude, the kernel's Analyze; #2247).
// Mirrors Rust's NEG_TAG.
const negTag byte = 0x00

// countTag is the tag byte sealing the count body-literal reading (ADR 0023). A
// Count(c) reads as Tuple[Atom(countTag), pred_ref, filter, project, count] — a 5-tuple
// whose first child is this single-byte atom, distinct from both a positive reading
// (first child = the predicate atom, which is never 0x01 because every ingress refuses
// that predicate, #2247) and the Neg reading (first child =
// Atom(negTag=0x00)). So a body with no Count literal encodes byte-identically to the
// pre-amendment account. Mirrors Rust's COUNT_TAG.
const countTag byte = 0x01

// intTerm is the canonical ontos-data int embedding of a small non-negative count
// (arity / filter position / projection attr) as a Term, byte-identical to Rust's
// BigInt::from_i128(n).to_int_term(). Used only inside the count account reading.
func intTerm(n uint32) Term {
	return FromValue(data.EncodeInt(new(big.Int).SetUint64(uint64(n))))
}

// intTermToUint32 is the inverse of intTerm: decode a canonical int embedding term to a
// uint32, or (0, false) if it is not a canonical non-negative int that fits uint32.
func intTermToUint32(t Term) (uint32, bool) {
	v, ok := t.EraseGround()
	if !ok {
		return 0, false
	}
	n, err := data.ReadInt(v)
	if err != nil {
		return 0, false
	}
	if n.Sign() < 0 || !n.IsUint64() {
		return 0, false
	}
	u := n.Uint64()
	if u > uint64(^uint32(0)) {
		return 0, false
	}
	return uint32(u), true
}

// projectAsTerm is the account-codec reading of a ProjectSpec (ADR 0023). Rows ⇒
// Atom("rows"); each column-bearing fold reads as Tuple[Atom(tag), int(attr)] where the
// tag is "distinct" (#571), "sum"/"min"/"max" (#587). Rows and Distinct are UNCHANGED
// (byte-identical back-compat). Mirrors Rust's project_as_term.
func projectAsTerm(p ProjectSpec) Term {
	switch p.Kind {
	case ProjectRows:
		return Atom([]byte("rows"))
	case ProjectDistinct:
		return Tuple(Atom([]byte("distinct")), intTerm(p.Attr))
	case ProjectSum:
		return Tuple(Atom([]byte("sum")), intTerm(p.Attr))
	case ProjectMin:
		return Tuple(Atom([]byte("min")), intTerm(p.Attr))
	case ProjectMax:
		return Tuple(Atom([]byte("max")), intTerm(p.Attr))
	default:
		// The kind is the program's (#3074: internal, so an unknown one panics by name).
		panic(fmt.Sprintf("contract: projectAsTerm: unknown ProjectKind %d", int(p.Kind)))
	}
}

// projectFromTerm is the inverse of projectAsTerm.
func projectFromTerm(t Term) (ProjectSpec, bool) {
	if at, ok := t.(AtomTerm); ok {
		if string(at.bytes) == "rows" {
			return Rows(), true
		}
		return ProjectSpec{}, false
	}
	tup, ok := t.(TupleTerm)
	if !ok || len(tup.children) != 2 {
		return ProjectSpec{}, false
	}
	tag, ok := tup.children[0].(AtomTerm)
	if !ok {
		return ProjectSpec{}, false
	}
	attr, ok := intTermToUint32(tup.children[1])
	if !ok {
		return ProjectSpec{}, false
	}
	switch string(tag.bytes) {
	case "distinct":
		return Distinct(attr), true
	case "sum":
		return Sum(attr), true
	case "min":
		return Min(attr), true
	case "max":
		return Max(attr), true
	default:
		return ProjectSpec{}, false
	}
}

// predicateRefAsTerm is the account-codec reading of an arity-sensitive PredicateRef
// (ADR 0023, #581): the 2-tuple Tuple[Atom(pred), int(arity)]. Pinning the arity makes
// obs/3 and obs/2 distinct counted relations. Mirrors Rust's predicate_ref_as_term.
func predicateRefAsTerm(p PredicateRef) Term {
	return Tuple(Atom(p.Pred.Bytes()), intTerm(p.Arity))
}

// predicateRefFromTerm is the inverse of predicateRefAsTerm.
func predicateRefFromTerm(t Term) (PredicateRef, bool) {
	tup, ok := t.(TupleTerm)
	if !ok || len(tup.children) != 2 {
		return PredicateRef{}, false
	}
	pred, ok := tup.children[0].(AtomTerm)
	if !ok {
		return PredicateRef{}, false
	}
	arity, ok := intTermToUint32(tup.children[1])
	if !ok {
		return PredicateRef{}, false
	}
	return PredicateRef{Pred: NewSymbol(pred.bytes), Arity: arity}, true
}

// countLitAsTerm is the account-codec reading of a CountLit (ADR 0023): the sealed
// 5-tuple Tuple[Atom(countTag), pred_ref, filter, project, count], where pred_ref is the
// arity-sensitive Tuple[Atom(pred), int(arity)] (#581), filter is
// Tuple[ Tuple[int(pos), term], … ] (caller order preserved), and project/count read via
// projectAsTerm / the raw term. Mirrors Rust's count_lit_as_term.
func countLitAsTerm(c CountLit) Term {
	filter := make([]Term, len(c.Filter))
	for i, e := range c.Filter {
		filter[i] = Tuple(intTerm(e.Pos), e.Term)
	}
	return Tuple(
		Atom([]byte{countTag}),
		predicateRefAsTerm(c.Pred),
		Tuple(filter...),
		projectAsTerm(c.Project),
		c.Count,
	)
}

// countLitFromTerm is the inverse of countLitAsTerm. children is the full 5-tuple's
// children (including the leading countTag atom).
func countLitFromTerm(children []Term) (CountLit, bool) {
	if len(children) != 5 {
		return CountLit{}, false
	}
	pred, ok := predicateRefFromTerm(children[1])
	if !ok {
		return CountLit{}, false
	}
	filterTup, ok := children[2].(TupleTerm)
	if !ok {
		return CountLit{}, false
	}
	filter := make([]CountFilterEntry, 0, len(filterTup.children))
	for _, entry := range filterTup.children {
		pair, ok := entry.(TupleTerm)
		if !ok || len(pair.children) != 2 {
			return CountLit{}, false
		}
		pos, ok := intTermToUint32(pair.children[0])
		if !ok {
			return CountLit{}, false
		}
		filter = append(filter, CountFilterEntry{Pos: pos, Term: pair.children[1]})
	}
	project, ok := projectFromTerm(children[3])
	if !ok {
		return CountLit{}, false
	}
	return CountLit{Pred: pred, Filter: filter, Project: project, Count: children[4]}, true
}

// goalAsTerm is the labeled-compound reading of a goal p(a…) as a Term:
// Tuple[Atom(p), a…] (§1.1). A nullary goal p() is Tuple[Atom(p)] (arity 1) —
// distinct from the bare atom p.
func goalAsTerm(g Goal) Term {
	children := make([]Term, 0, len(g.Args)+1)
	children = append(children, Atom(g.Pred.Bytes()))
	children = append(children, g.Args...)
	return Tuple(children...)
}

// bodyLitAsTerm is the reading of one polarity-tagged body literal (ADR 0007).
//
// Byte-compat invariant: a Pos literal reads byte-identically to the bare
// goalAsTerm(g) — no wrapper, no tag — so every pre-amendment positive clause id is
// unchanged. A Neg literal reads as the sealed 2-tuple Tuple[Atom(negTag),
// goalAsTerm(g)], which is distinct from every positive reading over clauses without a
// reserved predicate, which every ingress refuses (see negTag, #2247).
// Mirrors Rust's body_lit_as_term.
func bodyLitAsTerm(b BodyLit) Term {
	if b.IsCount() {
		return countLitAsTerm(b.CountVal)
	}
	g, _ := b.AsInner() // ok: the Count arm above covers the only inner-less form
	if b.IsNeg() {
		return Tuple(Atom([]byte{negTag}), goalAsTerm(g))
	}
	return goalAsTerm(g)
}

// clauseAsTerm reads a clause head :- b₀,…,bₙ as a Term: Tuple[ head, Tuple[b₀,…,bₙ] ]
// (a 2-tuple of the head reading and the ordered body readings; empty body =
// Tuple[head, Tuple[]]). Each body literal reads via bodyLitAsTerm, so an
// all-positive body is byte-identical to the pre-ADR-0007 encoding.
func clauseAsTerm(c Clause) Term {
	body := make([]Term, len(c.Body))
	for i, b := range c.Body {
		body[i] = bodyLitAsTerm(b)
	}
	return Tuple(goalAsTerm(c.Head), Tuple(body...))
}

// ClauseValue is the canonical ground ontos value of a clause: Quote(clauseAsTerm).
// Total (every clause has one) and injective on distinct clauses (Quote is
// injective; the labeled-compound reading is unambiguous).
func ClauseValue(c Clause) core.Value {
	return Quote(clauseAsTerm(c))
}

// ClauseFromValue is the partial inverse of ClauseValue: recover the Clause whose
// canonical ground value is value, or (Clause{}, false) if value is not in the image
// of ClauseValue. Used by the program (de)serialization (program_serde.go) to read a
// clause back out of an ontos Value without re-deriving its ClauseId. Mirrors Rust's
// account::clause_from_value.
//
// The decode mirrors clauseAsTerm exactly: value must Reify to Tuple[ headTerm,
// Tuple[ bodyTerm... ] ], where headTerm is the labeled compound Tuple[Atom(pred),
// arg...] (arity ≥ 1) and each bodyTerm is either the bare goalAsTerm (positive) or
// the sealed 2-tuple Tuple[Atom(negTag), goalAsTerm] (negated). The polarity rule is
// the producer's: a body term is NEGATED iff it is a 2-tuple whose first child is
// exactly the single-byte atom Atom(negTag) — the reading bodyLitAsTerm commits to. This is
// injective only over clauses without a reserved predicate, which every ingress refuses
// (#2247, ReservedPredicateOf).
func ClauseFromValue(value core.Value) (Clause, bool) {
	term, ok := Reify(value)
	if !ok {
		return Clause{}, false
	}
	tup, ok := term.(TupleTerm)
	if !ok || len(tup.children) != 2 {
		return Clause{}, false
	}
	head, ok := goalFromTerm(tup.children[0])
	if !ok {
		return Clause{}, false
	}
	bodyTup, ok := tup.children[1].(TupleTerm)
	if !ok {
		return Clause{}, false
	}
	body := make([]BodyLit, 0, len(bodyTup.children))
	for _, lit := range bodyTup.children {
		b, ok := bodyLitFromTerm(lit)
		if !ok {
			return Clause{}, false
		}
		body = append(body, b)
	}
	return Clause{Head: head, Body: body}, true
}

// goalFromTerm is the inverse of goalAsTerm: read Tuple[Atom(pred), arg...] back into
// a Goal. The first child is the predicate atom; the rest are the argument terms (which
// may contain Vars — this is a clause head/body literal, not a ground one). False if the
// term is not a tuple headed by an atom (arity ≥ 1).
func goalFromTerm(term Term) (Goal, bool) {
	tup, ok := term.(TupleTerm)
	if !ok || len(tup.children) < 1 {
		return Goal{}, false
	}
	predAtom, ok := tup.children[0].(AtomTerm)
	if !ok {
		return Goal{}, false
	}
	args := make([]Term, len(tup.children)-1)
	copy(args, tup.children[1:])
	return Goal{Pred: NewSymbol(predAtom.bytes), Args: args}, true
}

// bodyLitFromTerm is the inverse of bodyLitAsTerm. Three readings, in order:
//   - a 2-tuple led by exactly Atom(negTag) is a Neg literal over the second child's goal;
//   - a tuple led by exactly Atom(countTag) is a Count literal (ADR 0023, the 5-tuple);
//   - anything else is a Pos literal over the whole term's goal.
//
// THE COUNT READING IS LOAD-BEARING FOR SEVERITY, not just completeness: it means a Count
// body literal ROUND-TRIPS through the clause codec, so a signed rule-fact CAN carry one to
// a consumer (measured in count_codec_roundtrip_test.go). Consumers must therefore branch on
// polarity — IsPos(), or the total AsInner() — before reading any field. The partial
// Inner()/inner() accessors, which let an unguarded read panic the rust core over
// attacker-supplied bytes, were deleted tri-core (#2733). See thesmos#409, stele#579,
// logos-db#153.
func bodyLitFromTerm(term Term) (BodyLit, bool) {
	if tup, ok := term.(TupleTerm); ok {
		// A Neg reading is the 2-tuple [Atom(negTag), goal].
		if len(tup.children) == 2 {
			if tag, ok := tup.children[0].(AtomTerm); ok && len(tag.bytes) == 1 && tag.bytes[0] == negTag {
				g, ok := goalFromTerm(tup.children[1])
				if !ok {
					return BodyLit{}, false
				}
				return NegLit(g), true
			}
		}
		// A Count reading (ADR 0023) is the 5-tuple led by Atom(countTag).
		if len(tup.children) >= 1 {
			if tag, ok := tup.children[0].(AtomTerm); ok && len(tag.bytes) == 1 && tag.bytes[0] == countTag {
				c, ok := countLitFromTerm(tup.children)
				if !ok {
					return BodyLit{}, false
				}
				return CountLitBody(c), true
			}
		}
	}
	g, ok := goalFromTerm(term)
	if !ok {
		return BodyLit{}, false
	}
	return PosLit(g), true
}

// ClauseBytes is the canonical, frozen bytes of a clause: ontos-codec(Quote(clause)).
func ClauseBytes(c Clause) []byte {
	return codec.Encode(ClauseValue(c))
}

// CanonicalClauseId is the canonical ClauseId of a clause — lowercase-hex
// SHA-256(ClausePrefix ‖ ontos-codec(Quote(clause))) (§9, syntactic).
//
// Stable and cross-language: any binding that follows this encoding computes the
// same id for the same clause. The id satisfies the v1 ClauseId contract (stable +
// lookup-able) and is additionally a canonical hash. Mirrors Rust's
// ClauseId::canonical.
func CanonicalClauseId(c Clause) ClauseId {
	h := sha256.New()
	h.Write(ClausePrefix)
	h.Write(ClauseBytes(c))
	return NewClauseId(hex.EncodeToString(h.Sum(nil)))
}

// ProgramDigest is the canonical whole-program digest (ADR 0007 §3.1):
// SHA-256(ProgramPrefix ‖ ⨁ len-prefixed SORTED ClauseBytes) over the program's
// COMPLETE clause set. The per-clause frozen account bytes are SORTED (lexicographic
// byte order — the same total order Rust's Vec<Vec<u8>>::sort uses), so the digest is
// independent of clause enumeration order and commits to the WHOLE clause set: a
// dropped or added clause changes the digest. Each clause's bytes are length-prefixed
// with its length as an 8-byte big-endian u64, so the concatenation is unambiguous.
//
// Byte-identical to Rust's program_digest (contract/rs/src/check.rs) and the TS
// programDigest — the frozen ontos-codec + syntactic VarId pin the same 32 bytes
// across {rs,go,ts} for the same clause set (the prelude trust anchor). Public so a
// consumer that wants certifiable negation can DERIVE the program_hash of its bound
// CertContext from the live program it runs, and a prelude loader can recompute and
// verify the manifest's pinned program_digest.
func ProgramDigest(clauses []Clause) [32]byte {
	byteVecs := make([][]byte, len(clauses))
	for i, c := range clauses {
		byteVecs[i] = ClauseBytes(c)
	}
	sortByteSlices(byteVecs)
	h := sha256.New()
	h.Write(ProgramPrefix)
	var lenBuf [8]byte
	for _, b := range byteVecs {
		binary.BigEndian.PutUint64(lenBuf[:], uint64(len(b)))
		h.Write(lenBuf[:])
		h.Write(b)
	}
	var out [32]byte
	copy(out[:], h.Sum(nil))
	return out
}

// ProgramDigestOf is the whole-program digest recomputed over a Program's COMPLETE
// clause set (via the trusted ForEachClause enumeration) — the ADR-0007 §3.1
// recompute that the certifying Check compares a cert's pinned ProgramHash against.
// Byte-identical to Rust's recompute_program_hash / program_digest(&dyn Program): the
// per-clause frozen bytes are sorted, so the digest is independent of enumeration
// order and commits to the whole clause set.
func ProgramDigestOf(program Program) [32]byte {
	var clauses []Clause
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		clauses = append(clauses, clause)
	})
	return ProgramDigest(clauses)
}
