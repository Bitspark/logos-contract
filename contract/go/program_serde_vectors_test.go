// Go replay of the cross-core program-(de)serialization byte-pin vector
// vectors/program_serde.json (logos-contract §10, issue #310).
//
// Each case rebuilds a MapProgram from the vector's (id, head, body) clause set
// (authored in a deliberately NON-sorted insertion order), drives the REAL
// ProgramToValue/ProgramFromValue, and asserts:
//   - the ontos-codec-v1 bytes of ProgramToValue(p) equal the pinned program_bytes_hex
//     (the canonical, insertion-order-independent encoding), and
//   - ProgramFromValue(ProgramToValue(p)) round-trips back to the same program.
//
// The SAME file is replayed in Rust (contract/rs/tests/program_serde_vectors.rs) and TS
// (contract/ts/test/program_serde_vectors.test.ts), so one byte-pin oracle pins all three
// cores — the frozen ontos-codec + the syntactic §2a Quote tags + the canonical
// (sorted-by-id) clause order pin the SAME bytes across {rs,go,ts}.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"errors"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ----- the on-disk vector shape -----

type programSerdeFile struct {
	EmptyProgram struct {
		ProgramBytesHex string `json:"program_bytes_hex"`
	} `json:"empty_program"`
	Program struct {
		Clauses              []programSerdeClause `json:"clauses"`
		CanonicalClauseOrder []string             `json:"canonical_clause_order"`
		ProgramBytesHex      string               `json:"program_bytes_hex"`
	} `json:"program"`
}

type programSerdeClause struct {
	ID             string            `json:"id"`
	Head           json.RawMessage   `json:"head"`
	Body           []json.RawMessage `json:"body"`
	ClauseBytesHex string            `json:"clause_bytes_hex"`
}

func loadProgramSerdeVectors(t *testing.T) programSerdeFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "program_serde.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/program_serde.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf programSerdeFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// buildTerm builds a Term from the vector arg notation (mirrors account.json):
// {atom:<hex>} | {atom_str:<utf8>} | {int:N} | {tuple:[term...]} | {var:<id>}.
func buildTerm(t *testing.T, raw json.RawMessage) Term {
	t.Helper()
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		t.Fatalf("term is not an object: %s: %v", raw, err)
	}
	if v, ok := obj["atom"]; ok {
		var s string
		if err := json.Unmarshal(v, &s); err != nil {
			t.Fatalf("bad atom (hex): %v", err)
		}
		b, err := hex.DecodeString(s)
		if err != nil {
			t.Fatalf("atom hex %q: %v", s, err)
		}
		return Atom(b)
	}
	if v, ok := obj["atom_str"]; ok {
		var s string
		if err := json.Unmarshal(v, &s); err != nil {
			t.Fatalf("bad atom_str: %v", err)
		}
		return Atom([]byte(s))
	}
	if v, ok := obj["int"]; ok {
		var n int64
		if err := json.Unmarshal(v, &n); err != nil {
			t.Fatalf("bad int: %v", err)
		}
		// The ontos-data int embedding, lifted from its ground Value into a Term.
		return FromValue(data.EncodeInt(big.NewInt(n)))
	}
	if v, ok := obj["tuple"]; ok {
		var children []json.RawMessage
		if err := json.Unmarshal(v, &children); err != nil {
			t.Fatalf("bad tuple: %v", err)
		}
		items := make([]Term, 0, len(children))
		for _, c := range children {
			items = append(items, buildTerm(t, c))
		}
		return Tuple(items...)
	}
	if v, ok := obj["var"]; ok {
		var s string
		if err := json.Unmarshal(v, &s); err != nil {
			t.Fatalf("bad var: %v", err)
		}
		return Var(s)
	}
	t.Fatalf("unrecognized term shape: %s", raw)
	return nil
}

// buildGoal builds a Goal from {pred:<utf8>, args:[term...]}.
func buildGoal(t *testing.T, raw json.RawMessage) Goal {
	t.Helper()
	var g struct {
		Pred string            `json:"pred"`
		Args []json.RawMessage `json:"args"`
	}
	if err := json.Unmarshal(raw, &g); err != nil {
		t.Fatalf("bad goal: %v", err)
	}
	args := make([]Term, 0, len(g.Args))
	for _, a := range g.Args {
		args = append(args, buildTerm(t, a))
	}
	return NewGoal(g.Pred, args...)
}

// buildBodyLit builds a body literal: a bare goal (positive) or {neg:<goal>} (negated).
func buildBodyLit(t *testing.T, raw json.RawMessage) BodyLit {
	t.Helper()
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		t.Fatalf("body lit is not an object: %v", err)
	}
	if neg, ok := obj["neg"]; ok {
		return NegLit(buildGoal(t, neg))
	}
	return PosLit(buildGoal(t, raw))
}

func buildClause(t *testing.T, c programSerdeClause) Clause {
	t.Helper()
	head := buildGoal(t, c.Head)
	body := make([]BodyLit, 0, len(c.Body))
	for _, b := range c.Body {
		body = append(body, buildBodyLit(t, b))
	}
	return NewClauseLits(head, body...)
}

func buildProgram(t *testing.T, clauses []programSerdeClause) *MapProgram {
	t.Helper()
	p := NewMapProgram()
	for _, c := range clauses {
		p.Insert(NewClauseId(c.ID), buildClause(t, c))
	}
	return p
}

func TestEmptyProgramBytesMatchThePin(t *testing.T) {
	vf := loadProgramSerdeVectors(t)
	emptyBytes, err := ProgramBytes(NewMapProgram())
	if err != nil {
		t.Fatalf("ProgramBytes(empty): %v", err)
	}
	got := hex.EncodeToString(emptyBytes)
	if got != vf.EmptyProgram.ProgramBytesHex {
		t.Fatalf("empty program canonical bytes\n got  %s\n want %s", got, vf.EmptyProgram.ProgramBytesHex)
	}
}

func TestPerClauseBytesMatchThePins(t *testing.T) {
	vf := loadProgramSerdeVectors(t)
	for _, c := range vf.Program.Clauses {
		clause := buildClause(t, c)
		got := hex.EncodeToString(ClauseBytes(clause))
		if got != c.ClauseBytesHex {
			t.Errorf("clause_bytes for %s\n got  %s\n want %s", c.ID, got, c.ClauseBytesHex)
		}
	}
}

func TestProgramBytesMatchThePinAndRoundTrip(t *testing.T) {
	vf := loadProgramSerdeVectors(t)
	if len(vf.Program.Clauses) == 0 {
		t.Fatal("no program clauses loaded")
	}
	program := buildProgram(t, vf.Program.Clauses)

	// 1. Canonical bytes match the pin (insertion-order-independent encoding).
	progBytes, err := ProgramBytes(program)
	if err != nil {
		t.Fatalf("ProgramBytes: %v", err)
	}
	got := hex.EncodeToString(progBytes)
	if got != vf.Program.ProgramBytesHex {
		t.Fatalf("program canonical bytes\n got  %s\n want %s", got, vf.Program.ProgramBytesHex)
	}

	// 2. Round-trip: ProgramFromValue(ProgramToValue(p)) == p.
	value, err := ProgramToValue(program)
	if err != nil {
		t.Fatalf("ProgramToValue: %v", err)
	}
	back, err := ProgramFromValue(value)
	if err != nil {
		t.Fatalf("ProgramFromValue: %v", err)
	}
	// Same id set + same clause per id (compare via the canonical clause bytes).
	for _, id := range vf.Program.CanonicalClauseOrder {
		want, okW := program.Clause(NewClauseId(id))
		gotC, okG := back.Clause(NewClauseId(id))
		if !okW || !okG {
			t.Fatalf("round-trip missing clause %s (want=%v got=%v)", id, okW, okG)
		}
		if hex.EncodeToString(ClauseBytes(want)) != hex.EncodeToString(ClauseBytes(gotC)) {
			t.Errorf("round-trip clause %s differs", id)
		}
	}
	// And no EXTRA clauses crept in: the round-tripped program has exactly the same count.
	if len(back.clauses) != len(program.clauses) {
		t.Fatalf("round-trip clause count: got %d want %d", len(back.clauses), len(program.clauses))
	}
}

// TestMapProgramIterMatchesCanonicalClauseOrder drives the public ordered enumeration
// (MapProgram.Iter / Len) over the vector program — built in a deliberately NON-sorted
// insertion order — and asserts the (id) order it yields equals the pinned
// canonical_clause_order (the same sorted-by-id-bytes order the serializer emits and the
// Rust/TS bindings reproduce). This is the cross-core proof that the new iteration order
// is byte-identical tri-core (issue #368). It also asserts the count.
func TestMapProgramIterMatchesCanonicalClauseOrder(t *testing.T) {
	vf := loadProgramSerdeVectors(t)
	program := buildProgram(t, vf.Program.Clauses)

	entries := program.Iter()
	if program.Len() != len(vf.Program.Clauses) {
		t.Fatalf("Len() = %d, want %d", program.Len(), len(vf.Program.Clauses))
	}
	if len(entries) != len(vf.Program.CanonicalClauseOrder) {
		t.Fatalf("Iter() count = %d, want %d", len(entries), len(vf.Program.CanonicalClauseOrder))
	}
	for i, want := range vf.Program.CanonicalClauseOrder {
		if got := entries[i].ID.String(); got != want {
			t.Errorf("Iter()[%d].ID = %q, want %q (canonical order)", i, got, want)
		}
		// The clause paired with each id is the one Clause(id) returns.
		looked, ok := program.Clause(entries[i].ID)
		if !ok {
			t.Errorf("Iter()[%d] id %q not found via Clause()", i, entries[i].ID.String())
			continue
		}
		if hex.EncodeToString(ClauseBytes(looked)) != hex.EncodeToString(ClauseBytes(entries[i].Clause)) {
			t.Errorf("Iter()[%d] clause for %q differs from Clause() lookup", i, entries[i].ID.String())
		}
	}
}

// TestMapProgramIterIsInsertionOrderIndependent asserts Iter is canonical regardless of
// the order clauses were inserted (a raw Go map range would be nondeterministic).
func TestMapProgramIterIsInsertionOrderIndependent(t *testing.T) {
	mk := func(order []string) *MapProgram {
		p := NewMapProgram()
		for _, id := range order {
			p.Insert(NewClauseId(id), Fact(NewGoal(id)))
		}
		return p
	}
	idsOf := func(p *MapProgram) []string {
		out := make([]string, 0, p.Len())
		for _, e := range p.Iter() {
			out = append(out, e.ID.String())
		}
		return out
	}
	a := idsOf(mk([]string{"z", "a", "m", "aa", "A"}))
	b := idsOf(mk([]string{"A", "aa", "m", "z", "a"}))
	want := []string{"A", "a", "aa", "m", "z"} // byte-lex: 'A'(0x41) < 'a'(0x61) < "aa" < 'm' < 'z'
	for i := range want {
		if a[i] != want[i] || b[i] != want[i] {
			t.Fatalf("Iter order not canonical/insertion-independent: a=%v b=%v want=%v", a, b, want)
		}
	}
}

// TestProgramSerdeIsInsertionOrderIndependent builds the SAME (id, clause) set in two
// different insertion orders; the canonical bytes must be byte-identical.
func TestProgramSerdeIsInsertionOrderIndependent(t *testing.T) {
	mk := func(order []string) *MapProgram {
		p := NewMapProgram()
		for _, id := range order {
			p.Insert(NewClauseId(id), Fact(NewGoal(id)))
		}
		return p
	}
	a := mk([]string{"z", "a", "m"})
	b := mk([]string{"a", "m", "z"})
	ba, err := ProgramBytes(a)
	if err != nil {
		t.Fatalf("ProgramBytes(a): %v", err)
	}
	bb, err := ProgramBytes(b)
	if err != nil {
		t.Fatalf("ProgramBytes(b): %v", err)
	}
	if hex.EncodeToString(ba) != hex.EncodeToString(bb) {
		t.Fatal("canonical bytes depend on insertion order")
	}
}

// TestProgramFromValueRejectsMalformed pins the partial-inverse error paths.
func TestProgramFromValueRejectsMalformed(t *testing.T) {
	// Not a tuple.
	if _, err := ProgramFromValue(core.NewAtom([]byte("x"))); err == nil {
		t.Error("expected error for non-tuple value")
	}
	// Wrong version tag.
	if _, err := ProgramFromValue(core.NewTuple(core.NewAtom([]byte("wrong")))); err == nil {
		t.Error("expected error for bad version tag")
	}
	// A non-tuple entry.
	bad := core.NewTuple(core.NewAtom(ProgramFormatTag()), core.NewAtom([]byte("bad")))
	if _, err := ProgramFromValue(bad); err == nil {
		t.Error("expected error for a non-tuple entry")
	}
	// An entry whose clause value is not a quoted clause term.
	badClause := core.NewTuple(
		core.NewAtom(ProgramFormatTag()),
		core.NewTuple(core.NewAtom([]byte("id")), core.NewAtom([]byte("not-a-clause"))),
	)
	if _, err := ProgramFromValue(badClause); err == nil {
		t.Error("expected error for a malformed clause value")
	}
	// A duplicate clause id (two entries share an id).
	one := ClauseValue(Fact(NewGoal("p")))
	dup := core.NewTuple(
		core.NewAtom(ProgramFormatTag()),
		core.NewTuple(core.NewAtom([]byte("same")), one),
		core.NewTuple(core.NewAtom([]byte("same")), one),
	)
	if _, err := ProgramFromValue(dup); err == nil {
		t.Error("expected error for a duplicate clause id")
	}
}

// TestProgramToValueRejectsReservedPredicate is the BLOCKER regression: a POSITIVE body
// literal whose predicate is the reserved negTag byte 0x00 with exactly one arg would
// encode byte-identically to a Neg literal — a silent Pos→Neg flip. The encoder MUST
// reject it (never emit ambiguous bytes), so the round-trip stays total over accepted
// programs. The HEAD is checked under the same uniform rule.
func TestProgramToValueRejectsReservedPredicate(t *testing.T) {
	// Body offender: p() :- <0x00>(a).
	reservedPred := NewGoal("\x00", Atom([]byte("a")))
	bodyOffender := NewMapProgram()
	bodyOffender.Insert(NewClauseId("c1"), NewClause(NewGoal("p"), reservedPred))
	if _, err := ProgramToValue(bodyOffender); !errors.Is(err, ErrProgramReservedPredicate) {
		t.Fatalf("body offender: want ErrProgramReservedPredicate, got %v", err)
	}
	if _, err := ProgramBytes(bodyOffender); !errors.Is(err, ErrProgramReservedPredicate) {
		t.Fatalf("ProgramBytes body offender: want ErrProgramReservedPredicate, got %v", err)
	}

	// Head offender: <0x00>(x).
	headOffender := NewMapProgram()
	headOffender.Insert(NewClauseId("c2"), Fact(NewGoal("\x00", Atom([]byte("x")))))
	if _, err := ProgramToValue(headOffender); !errors.Is(err, ErrProgramReservedPredicate) {
		t.Fatalf("head offender: want ErrProgramReservedPredicate, got %v", err)
	}
}
