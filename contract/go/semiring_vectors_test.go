// Go replay of the cross-core agreement vector vectors/semiring.json (ADR 0031 D1, D2, G3;
// v2 §14.3). The SAME file is replayed by Rust (contract/rs/tests/semiring_vectors.rs) and
// TS (contract/ts/test/semiring_vectors.test.ts). Every core builds the core semiring
// Counting and the four fixture semirings the vector's note defines, and must reproduce each
// semiring's declared identity, laws, computed identity digest, Zero and One; the element
// test; every Add/Mul row; and every audit verdict, witness included. The products sections
// (v2 §14.2, P9 I7) are replayed the same way over NewProductSemiring, built from each row's
// two members.

package contract

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"sort"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

type rvVectorFile struct {
	IdentityPrefix   string           `json:"identity_prefix"`
	LawBits          map[string]uint8 `json:"law_bits"`
	AuditOrder       []string         `json:"audit_order"`
	AuditSampleLimit int              `json:"audit_sample_limit"`
	Semirings        []rvSemiringRow  `json:"semirings"`
	Elements         []rvElementRow   `json:"elements"`
	Ops              []rvOpRow        `json:"ops"`
	Audits           []rvAuditRow     `json:"audits"`
	DecimalParts     []rvDecimalParts `json:"decimal_parts"`
	DecimalDecode    []rvDecimalCode  `json:"decimal_decode"`

	ProductIdentityPrefix string              `json:"product_identity_prefix"`
	Products              []rvProductRow      `json:"products"`
	ProductOps            []rvProductOpRow    `json:"product_ops"`
	ProductAudits         []rvProductAuditRow `json:"product_audits"`
}

type rvDecimalParts struct {
	Name     string          `json:"name"`
	Parts    [2]int64        `json:"parts"`
	Expected json.RawMessage `json:"expected"`
}

type rvDecimalCode struct {
	Name     string          `json:"name"`
	Value    json.RawMessage `json:"value"`
	Expected json.RawMessage `json:"expected"`
}

type rvDeclared struct {
	ID              string `json:"id"`
	Version         string `json:"version"`
	ConfigDigestHex string `json:"config_digest"`
}

type rvLaws struct {
	Idempotent         bool `json:"idempotent"`
	Bounded            bool `json:"bounded"`
	Monotone           bool `json:"monotone"`
	Commutative        bool `json:"commutative"`
	SupportsRetraction bool `json:"supports_retraction"`
}

type rvSemiringRow struct {
	Name              string          `json:"name"`
	Kind              string          `json:"kind"`
	Declared          rvDeclared      `json:"declared_identity"`
	Laws              rvLaws          `json:"laws"`
	LawsByte          uint8           `json:"laws_byte"`
	IdentityDigestHex string          `json:"identity_digest_hex"`
	Zero              json.RawMessage `json:"zero"`
	One               json.RawMessage `json:"one"`
}

type rvElementRow struct {
	Name     string          `json:"name"`
	Semiring string          `json:"semiring"`
	Value    json.RawMessage `json:"value"`
	Expected bool            `json:"expected"`
}

type rvOpRow struct {
	Name     string          `json:"name"`
	Semiring string          `json:"semiring"`
	Op       string          `json:"op"`
	A        json.RawMessage `json:"a"`
	B        json.RawMessage `json:"b"`
	Expected json.RawMessage `json:"expected"`
}

type rvAuditRow struct {
	Name     string            `json:"name"`
	Semiring string            `json:"semiring"`
	Samples  []json.RawMessage `json:"samples"`
	Verdict  rvVerdict         `json:"verdict"`
}

// rvProductRow is a products row: a semirings row, with the two members it is the product of and,
// for a fixture, the laws it declares beyond theirs.
type rvProductRow struct {
	rvSemiringRow
	Members      []string `json:"members"`
	DeclaresAlso []string `json:"declares_also"`
}

type rvProductOpRow struct {
	Name     string          `json:"name"`
	Product  string          `json:"product"`
	Op       string          `json:"op"`
	A        json.RawMessage `json:"a"`
	B        json.RawMessage `json:"b"`
	Expected json.RawMessage `json:"expected"`
}

type rvProductAuditRow struct {
	Name    string            `json:"name"`
	Product string            `json:"product"`
	Samples []json.RawMessage `json:"samples"`
	Verdict rvVerdict         `json:"verdict"`
}

type rvTally struct {
	Law       string `json:"law"`
	Decided   int    `json:"decided"`
	Undecided int    `json:"undecided"`
}

type rvVerdict struct {
	NoCounterexample *struct {
		Laws []rvTally `json:"laws"`
	} `json:"no_counterexample"`
	Vacuous *struct {
		Laws []rvTally `json:"laws"`
	} `json:"vacuous"`
	Counterexample *struct {
		Law     string            `json:"law"`
		Witness []json.RawMessage `json:"witness"`
	} `json:"counterexample"`
	SampleLimit *struct {
		Given int `json:"given"`
		Limit int `json:"limit"`
	} `json:"sample_limit"`
}

func loadSemiringVectors(t *testing.T) rvVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "semiring.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/semiring.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf rvVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// rvValue builds the ontos value an object of the vector's structural grammar denotes.
func rvValue(t *testing.T, raw json.RawMessage) core.Value {
	t.Helper()
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		t.Fatalf("value is not an object: %s", raw)
	}
	if n, ok := obj["int"]; ok {
		var i int64
		if err := json.Unmarshal(n, &i); err != nil {
			t.Fatalf("int is not an int64: %s", n)
		}
		return data.EncodeInt(big.NewInt(i))
	}
	if digits, ok := obj["bigint"]; ok {
		var s string
		if err := json.Unmarshal(digits, &s); err != nil {
			t.Fatalf("bigint is not a string: %s", digits)
		}
		n, ok := new(big.Int).SetString(s, 10)
		if !ok {
			t.Fatalf("bigint is not a decimal integer: %s", s)
		}
		return data.EncodeInt(n)
	}
	if raw, ok := obj["decimal"]; ok {
		var parts [2]int64
		if err := json.Unmarshal(raw, &parts); err != nil {
			t.Fatalf("decimal is not [mantissa, exponent]: %s", raw)
		}
		m, e := data.EncodeInt(big.NewInt(parts[0])), data.EncodeInt(big.NewInt(parts[1]))
		return core.NewTuple(core.NewAtom([]byte("decimal")), m, e)
	}
	if a, ok := obj["atom"]; ok {
		var s string
		if err := json.Unmarshal(a, &s); err != nil {
			t.Fatalf("atom is not a string: %s", a)
		}
		return core.NewAtom([]byte(s))
	}
	if items, ok := obj["tuple"]; ok {
		var raws []json.RawMessage
		if err := json.Unmarshal(items, &raws); err != nil {
			t.Fatalf("tuple is not an array: %s", items)
		}
		return core.NewTuple(rvValues(t, raws)...)
	}
	t.Fatalf("unrecognized value shape: %s", raw)
	return nil
}

func rvValues(t *testing.T, raws []json.RawMessage) []core.Value {
	t.Helper()
	out := make([]core.Value, 0, len(raws))
	for _, r := range raws {
		out = append(out, rvValue(t, r))
	}
	return out
}

func rvLawNames(laws []SemiringLaw) []string {
	out := make([]string, 0, len(laws))
	for _, l := range laws {
		out = append(out, string(l))
	}
	return out
}

func rvSameStrings(a, b []string) bool {
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

func rvSameValues(a, b []core.Value) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if !core.Equal(a[i], b[i]) {
			return false
		}
	}
	return true
}

// ---- the fixture semirings, as the vector's note defines them ----

func rvAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

// rvTruth reads atom false / atom true as a boolean, or ok=false outside the carrier.
func rvTruth(v core.Value) (bool, bool) {
	switch {
	case core.Equal(v, rvAtom("true")):
		return true, true
	case core.Equal(v, rvAtom("false")):
		return false, true
	}
	return false, false
}

func rvTruthValue(b bool) core.Value {
	if b {
		return rvAtom("true")
	}
	return rvAtom("false")
}

// rvBoolean is boolean (⊕ or), or left_add (⊕ the left projection), over {false, true}.
type rvBoolean struct {
	id      string
	leftAdd bool
}

func (s rvBoolean) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte(s.id), []byte("1"), [32]byte{})
}

func (rvBoolean) Laws() LawDeclaration {
	return LawDeclaration{Idempotent: true, Bounded: true, Monotone: true, Commutative: true}
}

func (rvBoolean) Zero() core.Value { return rvTruthValue(false) }

func (rvBoolean) One() core.Value { return rvTruthValue(true) }

func (rvBoolean) IsElement(v core.Value) bool {
	_, ok := rvTruth(v)
	return ok
}

func (s rvBoolean) Add(a, b core.Value) SemiringAnswer {
	x, okA := rvTruth(a)
	y, okB := rvTruth(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	if s.leftAdd {
		return SemiringElement{Value: rvTruthValue(x)}
	}
	return SemiringElement{Value: rvTruthValue(x || y)}
}

func (rvBoolean) Mul(a, b core.Value) SemiringAnswer {
	x, okA := rvTruth(a)
	y, okB := rvTruth(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return SemiringElement{Value: rvTruthValue(x && y)}
}

// rvStringSet is string_set: finite sets of atoms, a Tuple of Atoms strictly increasing by
// unsigned byte order.
type rvStringSet struct{}

func rvWords(v core.Value) ([][]byte, bool) {
	tup, ok := v.(core.Tuple)
	if !ok {
		return nil, false
	}
	items := tup.Items()
	out := make([][]byte, 0, len(items))
	for _, item := range items {
		a, ok := item.(core.Atom)
		if !ok {
			return nil, false
		}
		w := bytes.Clone(a.Bytes())
		if len(out) > 0 && bytes.Compare(out[len(out)-1], w) >= 0 {
			return nil, false
		}
		out = append(out, w)
	}
	return out, true
}

func rvWordSet(ws [][]byte) core.Value {
	sort.Slice(ws, func(i, j int) bool { return bytes.Compare(ws[i], ws[j]) < 0 })
	items := make([]core.Value, 0, len(ws))
	for i, w := range ws {
		if i > 0 && bytes.Equal(ws[i-1], w) {
			continue
		}
		items = append(items, core.NewAtom(w))
	}
	return core.NewTuple(items...)
}

func (rvStringSet) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("fixture/string-set-semiring"), []byte("1"), [32]byte{})
}

func (rvStringSet) Laws() LawDeclaration {
	return LawDeclaration{Idempotent: true, Monotone: true, Commutative: true}
}

func (rvStringSet) Zero() core.Value { return rvWordSet(nil) }

func (rvStringSet) One() core.Value { return rvWordSet([][]byte{{}}) }

func (rvStringSet) IsElement(v core.Value) bool {
	_, ok := rvWords(v)
	return ok
}

func (rvStringSet) Add(a, b core.Value) SemiringAnswer {
	x, okA := rvWords(a)
	y, okB := rvWords(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return SemiringElement{Value: rvWordSet(append(x, y...))}
}

func (rvStringSet) Mul(a, b core.Value) SemiringAnswer {
	x, okA := rvWords(a)
	y, okB := rvWords(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	out := make([][]byte, 0, len(x)*len(y))
	for _, p := range x {
		for _, q := range y {
			out = append(out, append(bytes.Clone(p), q...))
		}
	}
	return SemiringElement{Value: rvWordSet(out)}
}

// rvCountingVariant is counting_declared_idempotent (Counting with Idempotent also declared)
// or stopping (Counting's carrier, every operation on elements stopped at the capacity bound).
type rvCountingVariant struct {
	Semiring
	declaredIdempotent bool
	stopping           bool
}

func (v rvCountingVariant) DeclaredIdentity() ComponentIdentity {
	if v.stopping {
		return NewComponentIdentity([]byte("fixture/stopping-semiring"), []byte("1"), [32]byte{})
	}
	return v.Semiring.DeclaredIdentity()
}

func (v rvCountingVariant) Laws() LawDeclaration {
	laws := v.Semiring.Laws()
	laws.Idempotent = v.declaredIdempotent
	return laws
}

func (v rvCountingVariant) stopOr(counted SemiringAnswer) SemiringAnswer {
	if _, ok := counted.(SemiringElement); ok && v.stopping {
		return SemiringCapacity()
	}
	return counted
}

func (v rvCountingVariant) Add(a, b core.Value) SemiringAnswer { return v.stopOr(v.Semiring.Add(a, b)) }

func (v rvCountingVariant) Mul(a, b core.Value) SemiringAnswer { return v.stopOr(v.Semiring.Mul(a, b)) }

// rvUnit reads noisy_or's carrier: a canonical decimal in [0, 1].
func rvUnit(v core.Value) (bigDecimal, bool) {
	d, ok := decFromTerm(v)
	if !ok || d.isNegative() || d.cmp(decFromBigInt(big.NewInt(1))) > 0 {
		return bigDecimal{}, false
	}
	return d, true
}

// rvNoisyOr is noisy_or: decimals in [0, 1], ⊕ a + b - ab, ⊗ ab. Not distributive, so not a
// semiring.
type rvNoisyOr struct{}

func (rvNoisyOr) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("fixture/noisy-or-semiring"), []byte("1"), [32]byte{})
}

func (rvNoisyOr) Laws() LawDeclaration { return LawDeclaration{Monotone: true, Commutative: true} }

func (rvNoisyOr) Zero() core.Value { return decZero().toDecimalTerm() }

func (rvNoisyOr) One() core.Value { return decFromBigInt(big.NewInt(1)).toDecimalTerm() }

func (rvNoisyOr) IsElement(v core.Value) bool {
	_, ok := rvUnit(v)
	return ok
}

func (rvNoisyOr) Add(a, b core.Value) SemiringAnswer {
	x, okA := rvUnit(a)
	y, okB := rvUnit(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	sum, err := x.add(y)
	if err != decOK {
		return SemiringCapacity()
	}
	product, err := x.mul(y)
	if err != decOK {
		return SemiringCapacity()
	}
	return ringDecimalAnswer(sum.sub(product))
}

func (rvNoisyOr) Mul(a, b core.Value) SemiringAnswer {
	x, okA := rvUnit(a)
	y, okB := rvUnit(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return ringDecimalAnswer(x.mul(y))
}

// rvSemiring builds the semiring a vector row names from this core's own code: kind "core"
// is a contract semiring, "fixture" one of the test fixtures above.
func rvSemiring(t *testing.T, name, kind string) Semiring {
	t.Helper()
	switch kind + "/" + name {
	case "core/counting":
		return NewCountingSemiring()
	case "fixture/counting_declared_idempotent":
		return rvCountingVariant{Semiring: NewCountingSemiring(), declaredIdempotent: true}
	case "fixture/stopping":
		return rvCountingVariant{Semiring: NewCountingSemiring(), stopping: true}
	case "fixture/boolean":
		return rvBoolean{id: "fixture/boolean-semiring"}
	case "fixture/left_add":
		return rvBoolean{id: "fixture/left-projection-add", leftAdd: true}
	case "fixture/string_set":
		return rvStringSet{}
	case "core/tropical":
		return NewTropicalSemiring()
	case "core/probability":
		return NewProbabilitySemiring()
	case "core/provenance":
		return NewProvenanceSemiring()
	case "fixture/noisy_or":
		return rvNoisyOr{}
	}
	t.Fatalf("vectors/semiring.json names an unknown %s semiring %q", kind, name)
	return nil
}

func rvSemiringNamed(t *testing.T, vf rvVectorFile, name string) Semiring {
	t.Helper()
	for _, row := range vf.Semirings {
		if row.Name == name {
			return rvSemiring(t, row.Name, row.Kind)
		}
	}
	t.Fatalf("no semiring named %q", name)
	return nil
}

func TestSemiringVectorMetadata(t *testing.T) {
	vf := loadSemiringVectors(t)
	if !bytes.Equal([]byte(vf.IdentityPrefix), SemiringIdentityPrefix()) {
		t.Errorf("identity_prefix %q, want %q", vf.IdentityPrefix, SemiringIdentityPrefix())
	}
	if !bytes.Equal([]byte(vf.ProductIdentityPrefix), ProductSemiringPrefix()) {
		t.Errorf("product_identity_prefix %q, want %q", vf.ProductIdentityPrefix, ProductSemiringPrefix())
	}
	if vf.AuditSampleLimit != SemiringAuditSampleLimit {
		t.Errorf("audit_sample_limit %d, want %d", vf.AuditSampleLimit, SemiringAuditSampleLimit)
	}
	if got := rvLawNames(SemiringAuditOrder()); !rvSameStrings(got, vf.AuditOrder) {
		t.Errorf("audit_order: core %v, vector %v", got, vf.AuditOrder)
	}
	bits := map[string]uint8{
		"idempotent":          LawIdempotentBit,
		"bounded":             LawBoundedBit,
		"monotone":            LawMonotoneBit,
		"commutative":         LawCommutativeBit,
		"supports_retraction": LawSupportsRetractionBit,
	}
	if len(vf.LawBits) != len(bits) {
		t.Errorf("law_bits has %d laws, want %d", len(vf.LawBits), len(bits))
	}
	for law, bit := range bits {
		if vf.LawBits[law] != bit {
			t.Errorf("law_bits.%s = %d, want %d", law, vf.LawBits[law], bit)
		}
	}
}

func TestSemiringVectorIdentities(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.Semirings) == 0 {
		t.Fatal("the semirings table is empty")
	}
	for _, row := range vf.Semirings {
		rvCheckSemiringRow(t, rvSemiring(t, row.Name, row.Kind), row)
	}
}

// rvCheckSemiringRow checks s against a semirings or products row: its declared identity, laws,
// laws byte, computed identity, zero and one. It returns the computed identity digest, in hex.
func rvCheckSemiringRow(t *testing.T, s Semiring, row rvSemiringRow) string {
	t.Helper()
	declared := s.DeclaredIdentity()
	if string(declared.Id) != row.Declared.ID || string(declared.Version) != row.Declared.Version {
		t.Errorf("%s: declared %s@%s, want %s@%s", row.Name, declared.Id, declared.Version, row.Declared.ID, row.Declared.Version)
	}
	if got := hex.EncodeToString(declared.ConfigDigest[:]); got != row.Declared.ConfigDigestHex {
		t.Errorf("%s: declared config digest %s, want %s", row.Name, got, row.Declared.ConfigDigestHex)
	}
	laws := s.Laws()
	want := LawDeclaration{
		Idempotent:         row.Laws.Idempotent,
		Bounded:            row.Laws.Bounded,
		Monotone:           row.Laws.Monotone,
		Commutative:        row.Laws.Commutative,
		SupportsRetraction: row.Laws.SupportsRetraction,
	}
	if laws != want {
		t.Errorf("%s: laws %+v, want %+v", row.Name, laws, want)
	}
	if laws.Bits() != row.LawsByte {
		t.Errorf("%s: laws_byte %d, want %d", row.Name, laws.Bits(), row.LawsByte)
	}
	identity := SemiringIdentity(s)
	if !identity.Equal(SemiringIdentityOf(declared, laws)) {
		t.Errorf("%s: SemiringIdentity and SemiringIdentityOf disagree", row.Name)
	}
	if !bytes.Equal(identity.Id, declared.Id) || !bytes.Equal(identity.Version, declared.Version) {
		t.Errorf("%s: the identity must keep the declared id and version", row.Name)
	}
	digest := hex.EncodeToString(identity.ConfigDigest[:])
	if digest != row.IdentityDigestHex {
		t.Errorf("%s: identity digest %s, want %s", row.Name, digest, row.IdentityDigestHex)
	}
	if !core.Equal(s.Zero(), rvValue(t, row.Zero)) {
		t.Errorf("%s: zero mismatch", row.Name)
	}
	if !core.Equal(s.One(), rvValue(t, row.One)) {
		t.Errorf("%s: one mismatch", row.Name)
	}
	return digest
}

func TestSemiringVectorElements(t *testing.T) {
	vf := loadSemiringVectors(t)
	for _, row := range vf.Elements {
		s := rvSemiringNamed(t, vf, row.Semiring)
		if got := s.IsElement(rvValue(t, row.Value)); got != row.Expected {
			t.Errorf("%s: IsElement %v, want %v", row.Name, got, row.Expected)
		}
	}
}

func TestSemiringVectorOperations(t *testing.T) {
	vf := loadSemiringVectors(t)
	for _, row := range vf.Ops {
		s := rvSemiringNamed(t, vf, row.Semiring)
		got := rvApply(t, row.Name, row.Op, s, rvValue(t, row.A), rvValue(t, row.B))
		rvCheckAnswer(t, row.Name, got, row.Expected)
	}
}

// rvApply runs a row's op, add or mul, on s.
func rvApply(t *testing.T, name, op string, s Semiring, a, b core.Value) SemiringAnswer {
	t.Helper()
	switch op {
	case "add":
		return s.Add(a, b)
	case "mul":
		return s.Mul(a, b)
	}
	t.Fatalf("%s: unknown op %q", name, op)
	return nil
}

// rvCheckAnswer checks an operation's answer against a row's expected: the element,
// "not_an_element", or {"stopped": {kind, scope}}.
func rvCheckAnswer(t *testing.T, name string, got SemiringAnswer, expected json.RawMessage) {
	t.Helper()
	var word string
	if json.Unmarshal(expected, &word) == nil {
		if word != "not_an_element" {
			t.Fatalf("%s: unknown expected %q", name, word)
		}
		if _, ok := got.(SemiringNotAnElement); !ok {
			t.Errorf("%s: want not_an_element, got %#v", name, got)
		}
		return
	}
	var stop struct {
		Stopped *struct {
			Kind  string `json:"kind"`
			Scope string `json:"scope"`
		} `json:"stopped"`
	}
	if err := json.Unmarshal(expected, &stop); err == nil && stop.Stopped != nil {
		stopped, ok := got.(SemiringStopped)
		if !ok {
			t.Errorf("%s: want a stop, got %#v", name, got)
			return
		}
		if stopped.Cause.Kind().Tag() != stop.Stopped.Kind || stopped.Cause.Scope().Tag() != stop.Stopped.Scope {
			t.Errorf("%s: stop %s/%s, want %s/%s", name, stopped.Cause.Kind().Tag(), stopped.Cause.Scope().Tag(), stop.Stopped.Kind, stop.Stopped.Scope)
		}
		return
	}
	element, ok := got.(SemiringElement)
	if !ok || !core.Equal(element.Value, rvValue(t, expected)) {
		t.Errorf("%s: got %#v, want %s", name, got, expected)
	}
}

func rvTallies(laws []LawTally) []rvTally {
	out := make([]rvTally, 0, len(laws))
	for _, l := range laws {
		out = append(out, rvTally{Law: string(l.Law), Decided: l.Decided, Undecided: l.Undecided})
	}
	return out
}

func rvSameTallies(a, b []rvTally) bool {
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

func rvAnyVacuous(laws []LawTally) bool {
	for _, l := range laws {
		if l.IsVacuous() {
			return true
		}
	}
	return false
}

func TestSemiringVectorAudits(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.Audits) == 0 {
		t.Fatal("the audits table is empty")
	}
	for _, row := range vf.Audits {
		s := rvSemiringNamed(t, vf, row.Semiring)
		rvCheckVerdict(t, row.Name, AuditSemiring(s, rvValues(t, row.Samples)), row.Verdict)
	}
}

// rvCheckVerdict checks an audit's verdict against a row's: its kind, then its tallies, its law and
// witness, or its limit.
func rvCheckVerdict(t *testing.T, name string, got SemiringAudit, want rvVerdict) {
	t.Helper()
	switch {
	case want.NoCounterexample != nil:
		pass, ok := got.(SemiringNoCounterexample)
		if !ok {
			t.Errorf("%s: want no_counterexample, got %#v", name, got)
			return
		}
		if rvAnyVacuous(pass.Laws) {
			t.Errorf("%s: a no_counterexample verdict carries a vacuous law", name)
		}
		if tallies := rvTallies(pass.Laws); !rvSameTallies(tallies, want.NoCounterexample.Laws) {
			t.Errorf("%s: laws %+v, want %+v", name, tallies, want.NoCounterexample.Laws)
		}
	case want.Vacuous != nil:
		vacuous, ok := got.(SemiringVacuous)
		if !ok {
			t.Errorf("%s: want vacuous, got %#v", name, got)
			return
		}
		if !rvAnyVacuous(vacuous.Laws) {
			t.Errorf("%s: a vacuous verdict carries no vacuous law", name)
		}
		if tallies := rvTallies(vacuous.Laws); !rvSameTallies(tallies, want.Vacuous.Laws) {
			t.Errorf("%s: laws %+v, want %+v", name, tallies, want.Vacuous.Laws)
		}
	case want.Counterexample != nil:
		refuted, ok := got.(SemiringCounterexample)
		if !ok {
			t.Errorf("%s: want counterexample, got %#v", name, got)
			return
		}
		refutation := want.Counterexample
		if string(refuted.Law) != refutation.Law {
			t.Errorf("%s: law %s, want %s", name, refuted.Law, refutation.Law)
		}
		if !rvSameValues(refuted.Witness, rvValues(t, refutation.Witness)) {
			t.Errorf("%s: witness %v, want %v", name, refuted.Witness, rvValues(t, refutation.Witness))
		}
	case want.SampleLimit != nil:
		limit, ok := got.(SemiringSampleLimit)
		if !ok {
			t.Errorf("%s: want sample_limit, got %#v", name, got)
			return
		}
		bound := want.SampleLimit
		if limit.Given != bound.Given || limit.Limit != bound.Limit {
			t.Errorf("%s: sample limit %+v, want %+v", name, limit, *bound)
		}
	default:
		t.Fatalf("%s: unknown verdict", name)
	}
}

func TestSemiringVectorDecimalParts(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.DecimalParts) == 0 {
		t.Fatal("the decimal_parts table is empty")
	}
	for _, row := range vf.DecimalParts {
		d, ok := decFromParts(big.NewInt(row.Parts[0]), big.NewInt(row.Parts[1]))
		var word string
		if json.Unmarshal(row.Expected, &word) == nil {
			if word != "out_of_band" {
				t.Fatalf("%s: unknown expected %q", row.Name, word)
			}
			if ok {
				t.Errorf("%s: want out_of_band, got %v", row.Name, d.toDecimalTerm())
			}
			continue
		}
		if !ok || !core.Equal(d.toDecimalTerm(), rvValue(t, row.Expected)) {
			t.Errorf("%s: got ok=%v, want %s", row.Name, ok, row.Expected)
		}
	}
}

func TestSemiringVectorDecimalDecode(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.DecimalDecode) == 0 {
		t.Fatal("the decimal_decode table is empty")
	}
	for _, row := range vf.DecimalDecode {
		d, ok := decFromTerm(rvValue(t, row.Value))
		var word string
		if json.Unmarshal(row.Expected, &word) == nil {
			if word != "not_a_canonical_decimal" {
				t.Fatalf("%s: unknown expected %q", row.Name, word)
			}
			if ok {
				t.Errorf("%s: want no decimal, got %v", row.Name, d.toDecimalTerm())
			}
			continue
		}
		if !ok || !core.Equal(d.toDecimalTerm(), rvValue(t, row.Expected)) {
			t.Errorf("%s: got ok=%v, want %s", row.Name, ok, row.Expected)
		}
	}
}

// ---- the product semiring (v2 §14.2, P9 I7) ----

// rvDeclaresMore is a product fixture: the product's identity, carrier and operations, declaring
// its laws and also the ones its row's declares_also lists.
type rvDeclaresMore struct {
	Semiring
	also LawDeclaration
}

func (d rvDeclaresMore) Laws() LawDeclaration {
	laws := d.Semiring.Laws()
	return LawDeclaration{
		Idempotent:         laws.Idempotent || d.also.Idempotent,
		Bounded:            laws.Bounded || d.also.Bounded,
		Monotone:           laws.Monotone || d.also.Monotone,
		Commutative:        laws.Commutative || d.also.Commutative,
		SupportsRetraction: laws.SupportsRetraction || d.also.SupportsRetraction,
	}
}

// rvLawsNamed is the declaration of the named laws; an unknown law fails the replay.
func rvLawsNamed(t *testing.T, name string, laws []string) LawDeclaration {
	t.Helper()
	var out LawDeclaration
	for _, law := range laws {
		switch law {
		case "idempotent":
			out.Idempotent = true
		case "bounded":
			out.Bounded = true
		case "monotone":
			out.Monotone = true
		case "commutative":
			out.Commutative = true
		case "supports_retraction":
			out.SupportsRetraction = true
		default:
			t.Fatalf("%s: declares_also names an unknown law %q", name, law)
		}
	}
	return out
}

// rvProduct builds the product a products row names: NewProductSemiring over its two members, each
// a core semiring this core builds, and for the fixture a wrapper that declares the laws its
// declares_also lists. An unknown member, kind or fixture fails the replay; nothing is skipped.
func rvProduct(t *testing.T, row rvProductRow) Semiring {
	t.Helper()
	if len(row.Members) != 2 {
		t.Fatalf("%s: a product has two members, got %v", row.Name, row.Members)
	}
	first, second := rvSemiring(t, row.Members[0], "core"), rvSemiring(t, row.Members[1], "core")
	product := NewProductSemiring(first, second)
	switch row.Kind {
	case "core":
		if row.Name != row.Members[0]+"_x_"+row.Members[1] {
			t.Fatalf("%s: a core product is named for its members, %s_x_%s", row.Name, row.Members[0], row.Members[1])
		}
		if len(row.DeclaresAlso) != 0 {
			t.Fatalf("%s: a core product declares no law beyond its members'", row.Name)
		}
		return product
	case "fixture":
		if row.Name != "counting_x_tropical_declared_bounded" {
			t.Fatalf("vectors/semiring.json names an unknown fixture product %q", row.Name)
		}
		return rvDeclaresMore{Semiring: product, also: rvLawsNamed(t, row.Name, row.DeclaresAlso)}
	}
	t.Fatalf("%s: unknown product kind %q", row.Name, row.Kind)
	return nil
}

func rvProductNamed(t *testing.T, vf rvVectorFile, name string) Semiring {
	t.Helper()
	for _, row := range vf.Products {
		if row.Name == name {
			return rvProduct(t, row)
		}
	}
	t.Fatalf("no product named %q", name)
	return nil
}

func TestSemiringVectorProducts(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.Products) == 0 {
		t.Fatal("the products table is empty")
	}
	digests := map[[2]string]string{}
	for _, row := range vf.Products {
		digest := rvCheckSemiringRow(t, rvProduct(t, row), row.rvSemiringRow)
		if row.Kind != "core" {
			continue
		}
		pair := [2]string{row.Members[0], row.Members[1]}
		if _, seen := digests[pair]; seen {
			t.Errorf("%s: the ordered pair %s x %s has two rows", row.Name, pair[0], pair[1])
		}
		digests[pair] = digest
	}
	// The domain is the vector's own core semirings, so a core added there needs its products here.
	var cores []string
	for _, row := range vf.Semirings {
		if row.Kind == "core" {
			cores = append(cores, row.Name)
		}
	}
	if len(digests) != len(cores)*len(cores) {
		t.Errorf("products holds %d ordered core pairs, want %d (%d cores, the diagonal included)", len(digests), len(cores)*len(cores), len(cores))
	}
	for _, a := range cores {
		for _, b := range cores {
			digest, ok := digests[[2]string{a, b}]
			if !ok {
				t.Errorf("products lacks the ordered pair %s x %s", a, b)
				continue
			}
			if a != b && digest == digests[[2]string{b, a}] {
				t.Errorf("%s x %s and %s x %s share the identity digest %s: the order must be part of the identity", a, b, b, a, digest)
			}
		}
	}
}

func TestSemiringVectorProductOps(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.ProductOps) == 0 {
		t.Fatal("the product_ops table is empty")
	}
	for _, row := range vf.ProductOps {
		s := rvProductNamed(t, vf, row.Product)
		got := rvApply(t, row.Name, row.Op, s, rvValue(t, row.A), rvValue(t, row.B))
		rvCheckAnswer(t, row.Name, got, row.Expected)
	}
}

func TestSemiringVectorProductAudits(t *testing.T) {
	vf := loadSemiringVectors(t)
	if len(vf.ProductAudits) == 0 {
		t.Fatal("the product_audits table is empty")
	}
	for _, row := range vf.ProductAudits {
		s := rvProductNamed(t, vf, row.Product)
		rvCheckVerdict(t, row.Name, AuditSemiring(s, rvValues(t, row.Samples)), row.Verdict)
	}
}
