package contract

// #2605, the go rung of #2602 (seat:caa's lever A): a closed-model certificate's canonical wire
// SHAPE, written ONCE as a pre-order walk over a wireSink, with two readings. valueSink builds the
// ontos value ClosedModelCertAsValue returns, byte for byte. lenSink counts the bytes of that
// value's canonical encoding without building anything. The walk emits each node before its
// children, in encoding order, as the rs `wire_sink` does.
//
// Why: CertEncodedBytes, the measure behind max_cert_bytes (#2524), built the whole value tree and
// then its encoded buffer only to count the bytes. On the rs path that transient was 41% of a
// certified-set run's peak heap (#2602); the go host pays the same when it checks a decoded
// certificate. Measured through lenSink, the budget check refuses an oversized certificate in
// bounded memory.
//
// What the length reading RESTATES, both frozen formats, and pinned against codec.Encode(..) by
// wire_sink_test.go including the uvarint width boundaries:
//   - the ontos codec's framing: Atom = 0x00 ‖ uvarint(len) ‖ bytes, Tuple = 0x01 ‖ uvarint(arity) ‖ children;
//   - the frozen Quote reading (reify.go): an atom b is Tuple[Atom([0x00]), Atom(b)], a variable
//     Tuple[Atom([0x02]), Atom(name)], a tuple Tuple[Atom([0x01]), Tuple[quote(child)…]].
//
// It reads atoms and tuples through Len/At, never Bytes/Items, which copy.

import (
	"math/bits"
	"sort"

	core "github.com/bitspark/ontos/core/go"
)

// wireSink is one reading of the wire shape, fed in pre-order: every node before its children.
type wireSink interface {
	// ordered reports whether the walk must emit a sorted map's entries in codec order. false is
	// legal ONLY for a reading whose result does not depend on that order, which today means
	// lenSink (a length is a sum); any reading of the bytes or of the value must return true.
	ordered() bool
	// atomStr is an Atom of a string's bytes, and digest the Atom of a digest's lowercase hex:
	// typed so the length reading converts, encodes and allocates nothing. (The rs sink takes a
	// deferred closure instead; in go a closure handed through an interface method escapes, which
	// would allocate one per atom.)
	atomStr(str string)
	digest(d Hash)
	// tupleBegin opens a Tuple of arity children; exactly arity nodes follow, then tupleEnd.
	tupleBegin(arity int)
	tupleEnd()
	value(v core.Value)
	quotedValue(v core.Value)
	quotedTerm(t Term)
	int(n uint64)
}

// valueSink is the value reading: exactly the tree ClosedModelCertAsValue has always built.
type valueSink struct {
	// frames holds the open tuples' children so far, innermost last; frame 0 holds the result.
	frames [][]core.Value
}

// buildValue returns the value emit walks.
func buildValue(emit func(s wireSink)) core.Value {
	s := &valueSink{frames: [][]core.Value{make([]core.Value, 0, 1)}}
	emit(s)
	if len(s.frames) != 1 || len(s.frames[0]) != 1 {
		panic("contract: wire walk left an open tuple or emitted other than one value")
	}
	return s.frames[0][0]
}

func (s *valueSink) push(v core.Value) {
	top := len(s.frames) - 1
	s.frames[top] = append(s.frames[top], v)
}

func (s *valueSink) ordered() bool        { return true }
func (s *valueSink) atomStr(str string)   { s.push(core.NewAtom([]byte(str))) }
func (s *valueSink) digest(d Hash)        { s.push(DigestAtom(d)) }
func (s *valueSink) tupleBegin(arity int) { s.frames = append(s.frames, make([]core.Value, 0, arity)) }
func (s *valueSink) tupleEnd() {
	top := len(s.frames) - 1
	items := s.frames[top]
	s.frames = s.frames[:top]
	s.push(core.NewTuple(items...))
}
func (s *valueSink) value(v core.Value)       { s.push(v) }
func (s *valueSink) quotedValue(v core.Value) { s.push(Quote(FromValue(v))) }
func (s *valueSink) quotedTerm(t Term)        { s.push(Quote(t)) }
func (s *valueSink) int(n uint64)             { s.push(U64Atom(n)) }

// lenSink is the length reading: the canonical encoding's byte count, with no tree and no buffer.
type lenSink struct{ total uint64 }

// measureLen returns the encoded length of the value emit walks.
func measureLen(emit func(s wireSink)) uint64 {
	s := &lenSink{}
	emit(s)
	return s.total
}

// uvarintLen is the width of n as a shortest-form LEB128 uvarint.
func uvarintLen(n uint64) uint64 {
	w := (uint64(bits.Len64(n)) + 6) / 7
	if w == 0 {
		return 1
	}
	return w
}

// atomLen is an Atom of n bytes: tag, length, bytes.
func atomLen(n int) uint64 { return 1 + uvarintLen(uint64(n)) + uint64(n) }

// tupleLen is a Tuple of arity children whose encodings sum to children.
func tupleLen(arity int, children uint64) uint64 { return 1 + uvarintLen(uint64(arity)) + children }

// quoteTag is a quote node's one-byte tag atom.
const quoteTag = 3

// encodedLen is the encoded length of v, without encoding it.
func encodedLen(v core.Value) uint64 {
	switch x := v.(type) {
	case core.Atom:
		return atomLen(x.Len())
	case core.Tuple:
		var sum uint64
		for i := 0; i < x.Len(); i++ {
			sum += encodedLen(x.At(i))
		}
		return tupleLen(x.Len(), sum)
	default:
		panic("contract: encodedLen: unknown ontos value")
	}
}

// quotedLen is the encoded length of Quote(FromValue(v)), without building either.
func quotedLen(v core.Value) uint64 {
	var payload uint64
	switch x := v.(type) {
	case core.Atom:
		payload = atomLen(x.Len())
	case core.Tuple:
		var sum uint64
		for i := 0; i < x.Len(); i++ {
			sum += quotedLen(x.At(i))
		}
		payload = tupleLen(x.Len(), sum)
	default:
		panic("contract: quotedLen: unknown ontos value")
	}
	return tupleLen(2, quoteTag+payload)
}

// quotedTermLen is the encoded length of Quote(t), without building it.
func quotedTermLen(t Term) uint64 {
	var payload uint64
	switch x := t.(type) {
	case AtomTerm:
		payload = atomLen(len(x.bytes))
	case VarTerm:
		payload = atomLen(len(x.id.name))
	case TupleTerm:
		var sum uint64
		for _, c := range x.children {
			sum += quotedTermLen(c)
		}
		payload = tupleLen(len(x.children), sum)
	default:
		panic("contract: quotedTermLen: unknown Term implementation")
	}
	return tupleLen(2, quoteTag+payload)
}

func (s *lenSink) ordered() bool            { return false }
func (s *lenSink) atomStr(str string)       { s.total += atomLen(len(str)) }
func (s *lenSink) digest(Hash)              { s.total += atomLen(2 * len(Hash{})) }
func (s *lenSink) tupleBegin(arity int)     { s.total += 1 + uvarintLen(uint64(arity)) }
func (s *lenSink) tupleEnd()                {}
func (s *lenSink) value(v core.Value)       { s.total += encodedLen(v) }
func (s *lenSink) quotedValue(v core.Value) { s.total += quotedLen(v) }
func (s *lenSink) quotedTerm(t Term)        { s.total += quotedTermLen(t) }

// int: the int embedding is ontos-data's to define; measuring its (three-node) value keeps that
// definition in one place, at a constant transient per integer.
func (s *lenSink) int(n uint64) { s.total += encodedLen(U64Atom(n)) }

// uvarintBytes is uvarint(n)'s bytes, shortest-form LEB128, into a stack buffer.
func uvarintBytes(n uint64) ([10]byte, int) {
	var out [10]byte
	w := 0
	for {
		b := byte(n & 0x7f)
		n >>= 7
		if n != 0 {
			b |= 0x80
		}
		out[w] = b
		w++
		if n == 0 {
			return out, w
		}
	}
}

// atomCodecLess is the codec order of two atoms (§0.3.3's sorted-map order) without encoding
// them: 0x00, then uvarint(len), then the bytes. LEB128 is prefix-free, so comparing the length
// prefixes first and the bytes second is the order of the whole encodings.
func atomCodecLess(a, b string) bool {
	la, wa := uvarintBytes(uint64(len(a)))
	lb, wb := uvarintBytes(uint64(len(b)))
	for i := 0; i < wa && i < wb; i++ {
		if la[i] != lb[i] {
			return la[i] < lb[i]
		}
	}
	if wa != wb {
		return wa < wb
	}
	return a < b
}

// ------------------------------ the shape, once ------------------------------

func wireTuple(s wireSink, arity int, children func()) {
	s.tupleBegin(arity)
	children()
	s.tupleEnd()
}

func writeSymbol(s wireSink, sym Symbol) { s.atomStr(sym.bytes) }

func writeDigest(s wireSink, d Hash) { s.digest(d) }

// writeGroundLiteral is p(a…) as Tuple[Atom(p), quote(a)…].
func writeGroundLiteral(s wireSink, lit GroundLiteral) {
	wireTuple(s, 1+len(lit.Args), func() {
		writeSymbol(s, lit.Pred)
		for _, arg := range lit.Args {
			s.quotedValue(arg)
		}
	})
}

// writeSubst is Tuple[Tuple[Atom(var), quote(term)], …], sorted by the key's codec bytes (§0.3.3):
// shorter names first, so Z precedes AB.
func writeSubst(s wireSink, subst Subst) {
	entry := func(id VarId, term Term) {
		wireTuple(s, 2, func() {
			s.atomStr(id.name)
			s.quotedTerm(term)
		})
	}
	if !s.ordered() {
		wireTuple(s, len(subst), func() {
			for id, term := range subst {
				entry(id, term)
			}
		})
		return
	}
	ids := make([]VarId, 0, len(subst))
	for id := range subst {
		ids = append(ids, id)
	}
	sort.Slice(ids, func(i, j int) bool { return atomCodecLess(ids[i].name, ids[j].name) })
	wireTuple(s, len(ids), func() {
		for _, id := range ids {
			entry(id, subst[id])
		}
	})
}

// writeClosedModelCert is a closed-model certificate with decl in its size-declaration slot. The
// trailing-optional elements follow ADR 0029 D10 (the 11th, a slice-seal pin) and ADR 0030 D4 (the
// 12th, a partial scope; with no pin the 11th is Tuple[Atom("none")]).
func writeClosedModelCert(s wireSink, cert ClosedModelCert, decl CertSizeDecl) {
	trailing := 0
	switch {
	case cert.PartialScope != nil:
		trailing = 2
	case cert.DecompositionWitness != nil:
		trailing = 1
	}
	wireTuple(s, 10+trailing, func() {
		writeStratumPrefix(s, cert.Scope)
		writeDigest(s, cert.ProgramHash)
		writeDigest(s, cert.ProfileHash)
		writeDigest(s, cert.CtxHash)
		writeDigest(s, cert.TheoryConfigHash)
		wireTuple(s, len(cert.EdbSnapshotHashes), func() {
			for _, h := range cert.EdbSnapshotHashes {
				writeDigest(s, h)
			}
		})
		wireTuple(s, len(cert.Domains), func() {
			for _, d := range cert.Domains {
				writeFiniteDomain(s, d)
			}
		})
		wireTuple(s, len(cert.Extensions), func() {
			for _, t := range cert.Extensions {
				writeRelationTable(s, t)
			}
		})
		wireTuple(s, len(cert.Supports.Edges), func() {
			for _, e := range cert.Supports.Edges {
				writeSupportEdge(s, e)
			}
		})
		writeCertSizeDecl(s, decl)
		switch {
		case cert.PartialScope != nil:
			if cert.DecompositionWitness != nil {
				writeDigest(s, *cert.DecompositionWitness)
			} else {
				wireTuple(s, 1, func() { s.atomStr("none") })
			}
			writeStratumPrefix(s, *cert.PartialScope)
		case cert.DecompositionWitness != nil:
			writeDigest(s, *cert.DecompositionWitness)
		}
	})
}

func writeStratumPrefix(s wireSink, scope StratumPrefix) {
	wireTuple(s, 2, func() {
		s.int(uint64(scope.Level))
		wireTuple(s, len(scope.Predicates), func() {
			for _, p := range scope.Predicates {
				writeSymbol(s, p)
			}
		})
	})
}

func writeFiniteDomain(s wireSink, domain FiniteDomain) {
	wireTuple(s, 2, func() {
		writeSymbol(s, domain.TypeTag)
		wireTuple(s, len(domain.Values), func() {
			for _, v := range domain.Values {
				s.value(v)
			}
		})
	})
}

func writeRelationTable(s wireSink, table RelationTable) {
	wireTuple(s, 3, func() {
		writeSymbol(s, table.Pred)
		s.int(uint64(table.Arity))
		wireTuple(s, len(table.Rows), func() {
			for _, r := range table.Rows {
				writeGroundLiteral(s, r)
			}
		})
	})
}

func writeSupportEdge(s wireSink, edge SupportEdge) {
	wireTuple(s, 5, func() {
		writeGroundLiteral(s, edge.Fact)
		s.atomStr(edge.Clause.String())
		writeSubst(s, edge.Subst)
		wireTuple(s, len(edge.BodyRefs), func() {
			for _, r := range edge.BodyRefs {
				writeSupportRef(s, r)
			}
		})
		s.int(uint64(edge.Rank))
	})
}

func writeSupportRef(s wireSink, ref SupportRef) {
	tag := func(name string) { s.atomStr(name) }
	switch r := ref.(type) {
	case SameStratumRef:
		wireTuple(s, 3, func() { tag("same_stratum"); writeGroundLiteral(s, r.Fact); s.int(uint64(r.Rank)) })
	case LowerStratumRef:
		wireTuple(s, 3, func() { tag("lower_stratum"); s.int(uint64(r.Cert.Index())); writeGroundLiteral(s, r.Atom) })
	case BuiltinRef:
		wireTuple(s, 2, func() { tag("builtin"); writeGroundLiteral(s, r.Atom) })
	case NegLowerRef:
		wireTuple(s, 3, func() { tag("neg_lower"); s.int(uint64(r.Cert.Index())); writeGroundLiteral(s, r.Atom) })
	case CountLowerRef:
		// #2258 L3.3b: additive on the wire, a fifth tag.
		wireTuple(s, 2, func() { tag("count_lower"); s.int(uint64(r.Cert.Index())) })
	default:
		panic("contract: writeSupportRef: unknown SupportRef")
	}
}

func writeCertSizeDecl(s wireSink, decl CertSizeDecl) {
	wireTuple(s, 6, func() {
		s.int(uint64(decl.CertFacts))
		s.int(uint64(decl.DomainValues))
		s.int(uint64(decl.SupportEdges))
		s.int(uint64(decl.RuleGroundings))
		s.int(uint64(decl.JoinSteps))
		s.int(decl.CertBytes)
	})
}
