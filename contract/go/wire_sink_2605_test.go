// #2605, the go rung of #2602 (seat:caa's four conditions for lever A): wire_sink.go's length
// reading against the codec whose framing it restates, its value reading against the pre-#2605 tree
// (SortedMap's substitution order), and the host path's memory with and without the tree.
package contract

import (
	"bytes"
	"runtime"
	"strings"
	"testing"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// uvarintEdges2605 are the lengths the uvarint's width changes at (1|2 bytes at 127|128, 2|3 at
// 16383|16384), plus 255|256, where the codec order of two lengths is NOT their numeric order:
// uvarint(256) = 0x80 0x02 sorts before uvarint(255) = 0xFF 0x01.
var uvarintEdges2605 = []int{0, 1, 127, 128, 255, 256, 16383, 16384}

func encLen2605(v core.Value) uint64 { return uint64(len(codec.Encode(v))) }

// Condition 2: exact at every width boundary, for every sink entry point.
func TestLengthReadingIsExactAtEveryUvarintBoundary2605(t *testing.T) {
	for _, n := range uvarintEdges2605 {
		str := strings.Repeat("x", n)
		if got, want := measureLen(func(w wireSink) { w.atomStr(str) }), encLen2605(core.NewAtom([]byte(str))); got != want {
			t.Errorf("an atom of %d bytes: measured %d, encoded %d", n, got, want)
		}
		empties := make([]core.Value, n)
		for i := range empties {
			empties[i] = core.NewAtom(nil)
		}
		got := measureLen(func(w wireSink) {
			w.tupleBegin(n)
			for i := 0; i < n; i++ {
				w.atomStr("")
			}
			w.tupleEnd()
		})
		if want := encLen2605(core.NewTuple(empties...)); got != want {
			t.Errorf("a tuple of arity %d: measured %d, encoded %d", n, got, want)
		}
		v := core.NewTuple(core.NewAtom([]byte(str)), core.NewTuple(empties...))
		if got, want := measureLen(func(w wireSink) { w.value(v) }), encLen2605(v); got != want {
			t.Errorf("a verbatim value at %d: measured %d, encoded %d", n, got, want)
		}
		if got, want := measureLen(func(w wireSink) { w.quotedValue(v) }), encLen2605(Quote(FromValue(v))); got != want {
			t.Errorf("a quoted value at %d: measured %d, encoded %d", n, got, want)
		}
		children := make([]Term, n)
		for i := range children {
			children[i] = Var("v")
		}
		term := Tuple(Atom([]byte(str)), Var(str), Tuple(children...))
		if got, want := measureLen(func(w wireSink) { w.quotedTerm(term) }), encLen2605(Quote(term)); got != want {
			t.Errorf("a quoted term at %d: measured %d, encoded %d", n, got, want)
		}
		if got, want := measureLen(func(w wireSink) { w.int(uint64(n)) }), encLen2605(U64Atom(uint64(n))); got != want {
			t.Errorf("the int %d: measured %d, encoded %d", n, got, want)
		}
	}
	for _, n := range []uint64{1 << 32, 1 << 63, ^uint64(0)} {
		if got, want := measureLen(func(w wireSink) { w.int(n) }), encLen2605(U64Atom(n)); got != want {
			t.Errorf("the int %d: measured %d, encoded %d", n, got, want)
		}
	}
	var d Hash
	for i := range d {
		d[i] = byte(i * 7)
	}
	if got, want := measureLen(func(w wireSink) { w.digest(d) }), encLen2605(DigestAtom(d)); got != want {
		t.Errorf("a digest: measured %d, encoded %d", got, want)
	}
}

// substNames2605 cross every order trap: Z before AB (shorter first), and 256 before 255.
var substNames2605 = []string{"AB", "Z", strings.Repeat("c", 255), strings.Repeat("d", 256), strings.Repeat("a", 127), strings.Repeat("b", 128)}

func subst2605() Subst {
	s := Subst{}
	for i, name := range substNames2605 {
		s[NewVarId(name)] = Tuple(Atom([]byte{byte(i)}), Var(name))
	}
	return s
}

// Condition 1's order half: the value reading sorts a substitution by the key's codec bytes, which
// is exactly what SortedMap (the pre-#2605 reading) did, and the length reading agrees with it.
func TestSubstReadsInCodecOrderNotStringOrder2605(t *testing.T) {
	subst := subst2605()
	keys := make([]core.Value, 0, len(subst))
	values := make([]core.Value, 0, len(subst))
	for id, term := range subst {
		keys = append(keys, BytesAtom([]byte(id.String())))
		values = append(values, Quote(term))
	}
	want := codec.Encode(SortedMap(keys, values))
	value := SubstAsValue(subst)
	if got := codec.Encode(value); !bytes.Equal(got, want) {
		t.Fatalf("the substitution's value reading moved from SortedMap's")
	}
	order := make([]int, 0, len(subst))
	entries := value.(core.Tuple)
	for i := 0; i < entries.Len(); i++ {
		name := entries.At(i).(core.Tuple).At(0).(core.Atom).Bytes()
		order = append(order, len(name))
	}
	// codec order: 1 (Z), 2 (AB), 127, 128, 256, 255.
	if wantOrder := []int{1, 2, 127, 128, 256, 255}; !equalInts2605(order, wantOrder) {
		t.Errorf("entry name lengths in order %v, the codec order is %v", order, wantOrder)
	}
	if got := measureLen(func(w wireSink) { writeSubst(w, subst) }); got != uint64(len(want)) {
		t.Errorf("the substitution measures %d, encodes to %d", got, len(want))
	}
}

func equalInts2605(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// cert2605 is a synthetic certificate whose walk reaches every node the shape has: all five
// SupportRef tags, nested domain values, a substitution across the order traps, and the four
// trailing-slot shapes (0 neither, 1 a slice-seal pin, 2 a partial scope with the none marker,
// 3 both). rows sizes its table and its support edges.
func cert2605(rows, trailing int) ClosedModelCert {
	lit := func(i int) GroundLiteral {
		return NewGroundLiteral("p", U64Atom(uint64(i)), core.NewTuple(core.NewAtom([]byte("k")), core.NewAtom([]byte(strings.Repeat("y", i%300)))))
	}
	hash := func(seed byte) Hash {
		var h Hash
		for i := range h {
			h[i] = seed + byte(i)
		}
		return h
	}
	table := make([]GroundLiteral, rows)
	edges := make([]SupportEdge, rows)
	subst := subst2605()
	for i := 0; i < rows; i++ {
		table[i] = lit(i)
		edges[i] = SupportEdge{
			Fact:   lit(i),
			Clause: NewClauseId(strings.Repeat("c", 1+i%200)),
			Subst:  subst,
			BodyRefs: []SupportRef{
				SameStratumRef{Fact: lit(i + 1), Rank: uint32(i)},
				LowerStratumRef{Cert: NewCertId(0), Atom: lit(i)},
				BuiltinRef{Atom: lit(i)},
				NegLowerRef{Cert: NewCertId(1), Atom: lit(i)},
				CountLowerRef{Cert: NewCertId(uint64(i))},
			},
			Rank: uint32(i),
		}
	}
	scope := StratumPrefix{Level: 3, Predicates: []Symbol{SymbolFromString("p"), SymbolFromString("q")}}
	cert := ClosedModelCert{
		Scope:             scope,
		ProgramHash:       hash(1),
		ProfileHash:       hash(2),
		CtxHash:           hash(3),
		TheoryConfigHash:  hash(4),
		EdbSnapshotHashes: []Hash{hash(5), hash(6)},
		Domains: []FiniteDomain{{
			TypeTag: SymbolFromString("t"),
			Values:  []core.Value{core.NewAtom([]byte("a")), core.NewTuple(core.NewAtom(nil), core.NewTuple(U64Atom(7))), U64Atom(1 << 40)},
		}},
		Extensions: []RelationTable{{Pred: SymbolFromString("p"), Arity: 2, Rows: table}},
		Supports:   SupportWitness{Edges: edges},
		LimitsDecl: CertSizeDecl{CertFacts: uint64(rows), DomainValues: 3, SupportEdges: uint64(rows), RuleGroundings: 4, JoinSteps: 5, CertBytes: 123456},
	}
	witness := hash(9)
	partial := StratumPrefix{Level: 1, Predicates: []Symbol{SymbolFromString("q")}}
	if trailing&1 != 0 {
		cert.DecompositionWitness = &witness
	}
	if trailing&2 != 0 {
		cert.PartialScope = &partial
	}
	return cert
}

// Conditions 1 and 3 on every shape: the length reading equals the encoding it restates, with the
// declared CertBytes excluded; and each trailing branch is reached (the arity proves it).
func TestLengthReadingEqualsTheEncodingOfEveryShape2605(t *testing.T) {
	for trailing, arity := range []int{10, 11, 12, 12} {
		cert := cert2605(40, trailing)
		assertLengthReading2605(t, "synthetic", cert)
		if got := mustWire(ClosedModelCertAsValue(cert)).(core.Tuple).Len(); got != arity {
			t.Errorf("trailing shape %d reads as %d elements, want %d", trailing, got, arity)
		}
	}
	// The declaration is excluded from its own measure: two certificates differing only there agree.
	a, b := cert2605(3, 0), cert2605(3, 0)
	b.LimitsDecl.CertBytes = ^uint64(0)
	if CertEncodedBytes(a) != CertEncodedBytes(b) {
		t.Errorf("CertBytes leaked into the measure")
	}
}

// assertLengthReading2605 is seat:caa's condition 3 for go: the length reading equals the encoding it
// measures. The replays of vectors/{cert_encoded_bytes,negation,aggregation}.json call it on every
// certificate they carry.
func assertLengthReading2605(t *testing.T, where string, cert ClosedModelCert) {
	t.Helper()
	zeroed := cert
	zeroed.LimitsDecl.CertBytes = 0
	if got, want := CertEncodedBytes(cert), encLen2605(mustWire(ClosedModelCertAsValue(zeroed))); got != want {
		t.Errorf("%s: the length reading measures %d, the encoding it restates is %d bytes", where, got, want)
	}
}

// allocated2605 is the bytes f allocates, the median of five runs.
func allocated2605(f func()) uint64 {
	var runs [5]uint64
	for i := range runs {
		runtime.GC()
		var before, after runtime.MemStats
		runtime.ReadMemStats(&before)
		f()
		runtime.ReadMemStats(&after)
		runs[i] = after.TotalAlloc - before.TotalAlloc
	}
	for i := 1; i < len(runs); i++ {
		for j := i; j > 0 && runs[j] < runs[j-1]; j-- {
			runs[j], runs[j-1] = runs[j-1], runs[j]
		}
	}
	return runs[len(runs)/2]
}

// Condition 4, the host path's memory: CertEncodedBytes allocates only a constant per integer (the
// int embedding is measured through its three-node value, as in rs), never the tree or the buffer.
// The pre-#2605 path, which builds both, is measured beside it as the control that the instrument
// sees allocation at all.
func TestLengthReadingDoesNotBuildTheTree2605(t *testing.T) {
	cert := cert2605(2000, 3)
	zeroed := cert
	zeroed.LimitsDecl.CertBytes = 0
	var sink uint64
	tree := allocated2605(func() { sink += uint64(len(codec.Encode(mustWire(ClosedModelCertAsValue(zeroed))))) })
	length := allocated2605(func() { sink += CertEncodedBytes(cert) })
	var ints uint64
	for _, e := range cert.Supports.Edges {
		ints += 1 + uint64(len(e.BodyRefs)) - 1 // the rank, and every ref but BuiltinRef carries one
	}
	ints += 64
	perInt := allocated2605(func() {
		for i := uint64(0); i < 1000; i++ {
			sink += encodedLen(U64Atom(1<<40 + i))
		}
	}) / 1000
	encoded := CertEncodedBytes(cert)
	t.Logf("certificate %d bytes encoded; the tree path allocates %d, the length reading %d (%d ints at ~%d B)", encoded, tree, length, ints, perInt)
	if tree < encoded {
		t.Fatalf("control: the tree path allocated %d bytes for a %d-byte encoding; the instrument is not seeing allocation", tree, encoded)
	}
	if bound := 2*ints*perInt + 4096; length > bound {
		t.Errorf("the length reading allocated %d bytes, above the integers' transient %d: something besides the int embedding allocates per node", length, bound)
	}
	if sink == 0 {
		t.Fatal("unreachable: keeps the measured calls live")
	}
}
