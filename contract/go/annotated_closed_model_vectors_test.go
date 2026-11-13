// Go replay of the hand-authored oracle vectors/annotated_closed_model.json (ADR 0031 D5; rulings
// Q14 and Q15 on #1821, P9 I5a). The SAME file is replayed by rs
// (contract/rs/tests/annotated_closed_model_vectors.rs) and ts
// (contract/ts/test/annotated_closed_model_vectors.test.ts).
//
// Each case builds the negation_v1 profile (the lt theory; EDB leaves = `extensional`, attesting the
// `edb` rows), the cert in negation.json's notation bound to the context derived from the live
// program, its annotations in semiring.json's value grammar, and the two semirings the case names,
// then runs CheckAnnotatedClosedModel. The vector compares the outcome kind, the code, the row where
// it gives one (none where it gives none), the law and the unattested tables. R3 re-runs every
// accepted case under each raised checker budget, and the verdict must not move.
package contract

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/internal/r3domain"
	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

type acmVectorFile struct {
	Profile     string                   `json:"profile"`
	Extensional []string                 `json:"extensional"`
	Edb         map[string][]negJSONLit  `json:"edb"`
	Program     map[string]negJSONClause `json:"program"`
	Cases       []acmCase                `json:"cases"`
}

type acmCase struct {
	Name         string          `json:"name"`
	Semiring     string          `json:"semiring"`
	CertSemiring string          `json:"cert_semiring"`
	Cert         negJSONCert     `json:"cert"`
	Annotations  []acmAnnotation `json:"annotations"`
	Outcome      string          `json:"outcome"`
	Expected     acmExpected     `json:"expected"`
}

type acmAnnotation struct {
	Pred     string            `json:"pred"`
	Elements []json.RawMessage `json:"elements"`
}

type acmExpected struct {
	Code       *string  `json:"code"`
	Row        *acmRow  `json:"row"`
	Law        *string  `json:"law"`
	Unattested []string `json:"unattested"`
}

type acmRow struct {
	Pred  string `json:"pred"`
	Index int    `json:"index"`
}

// acmFoldOrder is the vector's TEST semiring fold_order, never registered: declared identity
// (fixture/fold-order, 1, 32 zero bytes), no law declared, carrier every Atom, Zero and One the empty
// atom, and Add(x, y) and Mul(x, y) both the atom of x's bytes then y's bytes. Its Add is
// order-sensitive on purpose (#1821 Q15 condition 3), so the canonical grounding order is pinned.
type acmFoldOrder struct{}

func (acmFoldOrder) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("fixture/fold-order"), []byte("1"), [32]byte{})
}

func (acmFoldOrder) Laws() LawDeclaration { return LawDeclaration{} }

func (acmFoldOrder) Zero() core.Value { return core.NewAtom([]byte{}) }

func (acmFoldOrder) One() core.Value { return core.NewAtom([]byte{}) }

func (acmFoldOrder) IsElement(v core.Value) bool {
	_, ok := v.(core.Atom)
	return ok
}

func (acmFoldOrder) Add(a, b core.Value) SemiringAnswer { return acmConcat(a, b) }

func (acmFoldOrder) Mul(a, b core.Value) SemiringAnswer { return acmConcat(a, b) }

// acmConcat is the atom of a's bytes then b's bytes, or SemiringNotAnElement.
func acmConcat(a, b core.Value) SemiringAnswer {
	x, okA := a.(core.Atom)
	y, okB := b.(core.Atom)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return SemiringElement{Value: core.NewAtom(append(bytes.Clone(x.Bytes()), y.Bytes()...))}
}

// acmSemiring is the semiring a case names: counting, tropical and stopping are semiring.json's
// (stopping its fixture, built by the semiring replay's own constructor), fold_order this vector's.
func acmSemiring(t *testing.T, name string) Semiring {
	t.Helper()
	switch name {
	case "counting":
		return rvSemiring(t, "counting", "core")
	case "tropical":
		return rvSemiring(t, "tropical", "core")
	case "stopping":
		return rvSemiring(t, "stopping", "fixture")
	case "fold_order":
		return acmFoldOrder{}
	}
	t.Fatalf("vectors/annotated_closed_model.json names an unknown semiring %q", name)
	return nil
}

func loadAnnotatedClosedModelVectors(t *testing.T) acmVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "annotated_closed_model.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/annotated_closed_model.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf acmVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// acmFixture is what every case shares: the live program, the profile's leaves and the derived
// context.
type acmFixture struct {
	program     *MapProgram
	extensional *PredicateSet
	edb         map[string][]GroundLiteral
	derived     CertContext
}

func newAcmFixture(t *testing.T, vf acmVectorFile) acmFixture {
	t.Helper()
	if vf.Profile != "negation_v1" {
		t.Fatalf("the vector names profile %q; this replay builds negation_v1", vf.Profile)
	}
	program := NewMapProgram()
	for id, clause := range vf.Program {
		body := make([]BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build(t)
		}
		program.Insert(NewClauseId(id), NewClauseLits(clause.Head.buildGoal(t), body...))
	}
	extensional := NewPredicateSet()
	for _, p := range vf.Extensional {
		extensional.Insert(SymbolFromString(p))
	}
	edb := make(map[string][]GroundLiteral, len(vf.Edb))
	for pred, rows := range vf.Edb {
		grounds := make([]GroundLiteral, len(rows))
		for i, r := range rows {
			grounds[i] = r.buildGround(t)
		}
		edb[pred] = grounds
	}
	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))
	return acmFixture{program: program, extensional: extensional, edb: edb, derived: derived}
}

func (f acmFixture) profile() *CheckProfile[unitCtx] {
	return &CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: negVectorLeaves{extensional: f.extensional, edb: f.edb},
		Admit:  AlwaysAdmit[unitCtx]{},
		Limits: DefaultLimits(),
	}
}

// annotated builds a case's annotated certificate: its cert bound to the derived context, the
// identity of the semiring the case's cert names, and its annotations.
func (f acmFixture) annotated(t *testing.T, c acmCase) AnnotatedClosedModelCert {
	t.Helper()
	tables := make([]AnnotatedTable, len(c.Annotations))
	for i, a := range c.Annotations {
		tables[i] = AnnotatedTable{Pred: SymbolFromString(a.Pred), Elements: rvValues(t, a.Elements)}
	}
	return AnnotatedClosedModelCert{
		Cert:        c.Cert.build(t, f.derived),
		Semiring:    SemiringIdentity(acmSemiring(t, c.CertSemiring)),
		Annotations: tables,
	}
}

// acmRender renders a verdict as the vector compares it, and names its kind and code.
func acmRender(t *testing.T, out AnnotatedOutcome) (string, string) {
	t.Helper()
	switch o := out.(type) {
	case AnnotatedAccept:
		law := "null"
		if o.Law != nil {
			law = o.Law.Name()
		}
		names := make([]string, len(o.Unattested))
		for i, p := range o.Unattested {
			names[i] = p.String()
		}
		return fmt.Sprintf("accept law=%s unattested=[%s]", law, strings.Join(names, ",")), "accept"
	case AnnotatedCertReject:
		return "reject_cert code=" + o.Code.Code(), "reject_cert:" + o.Code.Code()
	case AnnotatedReject:
		row := "none"
		if o.Row != nil {
			row = fmt.Sprintf("%s/%d", o.Row.Pred.String(), o.Row.Index)
		}
		return fmt.Sprintf("reject code=%s row=%s", o.Code.Code(), row), "reject:" + o.Code.Code()
	}
	t.Fatalf("an AnnotatedOutcome of no known kind: %#v", out)
	return "", ""
}

// acmWant renders a case's expectation the way acmRender renders a verdict.
func acmWant(t *testing.T, c acmCase) (string, string) {
	t.Helper()
	code := func() string {
		if c.Expected.Code == nil {
			t.Fatalf("case %q: outcome %q carries no expected code", c.Name, c.Outcome)
		}
		return *c.Expected.Code
	}
	switch c.Outcome {
	case "accept":
		law := "null"
		if c.Expected.Law != nil {
			law = *c.Expected.Law
		}
		return fmt.Sprintf("accept law=%s unattested=[%s]", law, strings.Join(c.Expected.Unattested, ",")), "accept"
	case "reject_cert":
		return "reject_cert code=" + code(), "reject_cert:" + code()
	case "reject":
		row := "none"
		if c.Expected.Row != nil {
			row = fmt.Sprintf("%s/%d", c.Expected.Row.Pred, c.Expected.Row.Index)
		}
		return fmt.Sprintf("reject code=%s row=%s", code(), row), "reject:" + code()
	}
	t.Fatalf("case %q: unknown outcome %q", c.Name, c.Outcome)
	return "", ""
}

// acmAssertWireRoundTrip requires the annotated certificate's wire to decode to a certificate whose
// wire is byte-identical.
func acmAssertWireRoundTrip(t *testing.T, a AnnotatedClosedModelCert) {
	t.Helper()
	value, err := AnnotatedClosedModelCertAsValue(a)
	if err != nil {
		t.Fatalf("wire: %v", err)
	}
	back, err := AnnotatedClosedModelCertFromValue(value)
	if err != nil {
		t.Fatalf("decode: %v", err)
	}
	again, err := AnnotatedClosedModelCertAsValue(back)
	if err != nil {
		t.Fatalf("re-wire: %v", err)
	}
	if !bytes.Equal(codec.Encode(value), codec.Encode(again)) {
		t.Fatalf("the annotated wire does not round-trip byte-identically")
	}
	if !back.Semiring.Equal(a.Semiring) || len(back.Annotations) != len(a.Annotations) {
		t.Fatalf("the decoded identity or annotation count differs from the encoded one")
	}
}

// TestAnnotatedClosedModelVectors replays every case of vectors/annotated_closed_model.json through
// CheckAnnotatedClosedModel, and R3 (EachBudgetRaised) over the accepted ones.
func TestAnnotatedClosedModelVectors(t *testing.T) {
	vf := loadAnnotatedClosedModelVectors(t)
	if len(vf.Cases) < 14 {
		t.Fatalf("vectors/annotated_closed_model.json holds %d cases; the replay requires at least 14", len(vf.Cases))
	}
	fx := newAcmFixture(t, vf)
	names := make([]string, 0, len(vf.Cases))
	for _, c := range vf.Cases {
		names = append(names, c.Name)
	}
	domain := r3domain.Domain(t, "annotated_closed_model.json", names)
	raised := r3domain.Raised(t)
	if len(domain) == 0 {
		t.Fatal("R3's domain for annotated_closed_model.json is empty: the raised-budget check is vacuous")
	}
	wantNames, gotNames := map[string]bool{}, map[string]bool{}
	reRuns := 0
	for _, c := range vf.Cases {
		t.Run(c.Name, func(t *testing.T) {
			want, wantName := acmWant(t, c)
			wantNames[wantName] = true
			annotated := fx.annotated(t, c)
			acmAssertWireRoundTrip(t, annotated)
			profile := fx.profile()
			semiring := acmSemiring(t, c.Semiring)
			out := CheckAnnotatedClosedModel[unitCtx](fx.program, annotated, unitCtx{}, profile, fx.derived, semiring)
			got, gotName := acmRender(t, out)
			gotNames[gotName] = true
			if got != want {
				t.Fatalf("case %q: got %s, want %s (%#v)", c.Name, got, want, out)
			}
			if !domain[c.Name] {
				return
			}
			if c.Outcome != "accept" {
				t.Fatalf("case %q: R3's domain names a case whose outcome is %q", c.Name, c.Outcome)
			}
			// R3 (#2733, the checker's arm): an accepted case stays accepted, with the same law and the
			// same unattested tables, under each raised budget, alone and together.
			for _, rb := range EachBudgetRaised(profile.Limits, raised) {
				raisedProfile := *profile
				raisedProfile.Limits = rb.Limits
				again := CheckAnnotatedClosedModel[unitCtx](fx.program, annotated, unitCtx{}, &raisedProfile, fx.derived, semiring)
				if s, _ := acmRender(t, again); s != got {
					t.Fatalf("case %q: raising %s changed the verdict to %s", c.Name, rb.Name, s)
				}
				reRuns++
			}
		})
	}
	if reRuns == 0 {
		t.Fatal("R3 re-ran no accepted case: the raised-budget check is vacuous")
	}
	// Every expected kind and code occurred: set equality over the names that ran.
	if w, g := acmSortedNames(wantNames), acmSortedNames(gotNames); strings.Join(w, " ") != strings.Join(g, " ") {
		t.Fatalf("the verdicts that ran are %v; the vector expects %v", g, w)
	}
}

func acmSortedNames(set map[string]bool) []string {
	out := make([]string, 0, len(set))
	for name := range set {
		out = append(out, name)
	}
	sort.Strings(out)
	return out
}

// TestAnnotatedClosedModelCertDecodeIsClosed plants each shape the decoder must refuse: a wrong tag,
// a wrong arity, a config digest that is not a 64-character hex digest, a table that is not a pair and a predicate
// that is not an atom. The unplanted wire is the control: it decodes.
func TestAnnotatedClosedModelCertDecodeIsClosed(t *testing.T) {
	vf := loadAnnotatedClosedModelVectors(t)
	fx := newAcmFixture(t, vf)
	value, err := AnnotatedClosedModelCertAsValue(fx.annotated(t, vf.Cases[0]))
	if err != nil {
		t.Fatalf("wire: %v", err)
	}
	if _, err := AnnotatedClosedModelCertFromValue(value); err != nil {
		t.Fatalf("control: the unplanted wire is refused: %v", err)
	}
	items := value.(core.Tuple).Items()
	with := func(i int, v core.Value) core.Value {
		planted := append([]core.Value(nil), items...)
		planted[i] = v
		return core.NewTuple(planted...)
	}
	identity := items[2].(core.Tuple).Items()
	tables := items[3].(core.Tuple).Items()
	firstTable := tables[0].(core.Tuple).Items()
	withTable := func(table core.Value) core.Value {
		planted := append([]core.Value(nil), tables...)
		planted[0] = table
		return with(3, core.NewTuple(planted...))
	}
	for _, c := range []struct {
		name  string
		value core.Value
	}{
		{"a wrong tag", with(0, core.NewAtom([]byte("closed_model_cert")))},
		{"a wrong arity", core.NewTuple(items[:3]...)},
		{"a 31-byte config digest", with(2, core.NewTuple(identity[0], identity[1], core.NewAtom(make([]byte, 31))))},
		{"a table of arity 3", withTable(core.NewTuple(firstTable[0], firstTable[1], firstTable[1]))},
		{"a predicate that is not an atom", withTable(core.NewTuple(core.NewTuple(firstTable[0]), firstTable[1]))},
	} {
		_, err := AnnotatedClosedModelCertFromValue(c.value)
		var decodeErr *DecodeError
		if !errors.As(err, &decodeErr) {
			t.Errorf("%s: want a *DecodeError, got %v", c.name, err)
		}
	}
}
