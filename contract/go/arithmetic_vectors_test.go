// Go replay of the cross-core THEORY-DECISION agreement vector
// vectors/arithmetic.json (issue #95). The Rust ArithmeticTheory is the decision
// oracle; this test asserts the Go ArithmeticTheory reproduces every pinned outcome
// byte-for-byte. The SAME file is replayed in Rust (core/rs/tests/arithmetic_vectors.rs),
// so a single oracle pins both cores — the byte-parity proof the issue requires.
package contract

import (
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ----- the on-disk vector shape -----

type arithVectorFile struct {
	Identity  arithIdentity   `json:"identity"`
	Owns      arithOwns       `json:"owns"`
	Decisions []arithDecision `json:"decisions"`
	// DecimalSpellings (#2679) pins the literal parser against the value domain.
	DecimalSpellings struct {
		Rows []struct {
			Name   string  `json:"name"`
			Prefix string  `json:"prefix"`
			Zeros  int     `json:"zeros"`
			Suffix string  `json:"suffix"`
			Parses []int64 `json:"parses"`
		} `json:"rows"`
	} `json:"decimal_spellings"`
}

type arithIdentity struct {
	ID              string `json:"id"`
	Version         string `json:"version"`
	ConfigDigestHex string `json:"config_digest_hex"`
}

type arithOwns struct {
	Owned    []string `json:"owned"`
	NotOwned []string `json:"not_owned"`
}

type arithDecision struct {
	Name    string            `json:"name"`
	Pred    string            `json:"pred"`
	Args    []json.RawMessage `json:"args"`
	Outcome json.RawMessage   `json:"outcome"`
}

// loadArithVectors finds vectors/arithmetic.json by walking up from the test's
// working directory (contract/go) to the repo root, mirroring how the Rust replay
// includes it two levels up.
func loadArithVectors(t *testing.T) arithVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "arithmetic.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/arithmetic.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf arithVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// buildArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/arithmetic.json (and the Rust replay's builder):
//
//	{"int": N}                 -> the ontos-data int embedding of N
//	{"bigint": "<digits>"}     -> the int embedding of a value beyond JSON int range
//	{"decimal": "<d.dddd>"}    -> the ontos-data decimal embedding of that decimal literal (#331)
//	{"text": "<s>"}            -> the ontos-data utf8-text embedding
//	{"atom": "<utf8>"}         -> a bare Atom of those UTF-8 bytes
//	{"op": "<op>", "args": []} -> an operator compound Tuple(Atom(op), arg..)
//	{"list": [..]}             -> the ontos-data list embedding of the encoded children
//	{"tuple": [..]}            -> a raw Tuple of the encoded children
func buildArg(t *testing.T, raw json.RawMessage) core.Value {
	t.Helper()
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		t.Fatalf("arg is not an object: %s: %v", raw, err)
	}
	switch {
	case has(obj, "int"):
		var n int64
		if err := json.Unmarshal(obj["int"], &n); err != nil {
			t.Fatalf("bad int arg %s: %v", obj["int"], err)
		}
		return data.EncodeInt(big.NewInt(n))
	case has(obj, "bigint"):
		var s string
		if err := json.Unmarshal(obj["bigint"], &s); err != nil {
			t.Fatalf("bad bigint arg: %v", err)
		}
		n, ok := new(big.Int).SetString(s, 10)
		if !ok {
			t.Fatalf("bigint %q is not a base-10 integer", s)
		}
		return data.EncodeInt(n)
	case has(obj, "decimal"):
		var s string
		if err := json.Unmarshal(obj["decimal"], &s); err != nil {
			t.Fatalf("bad decimal arg: %v", err)
		}
		d, ok := decFromString(s)
		if !ok {
			t.Fatalf("decimal %q is not a decimal literal", s)
		}
		return d.toDecimalTerm()
	case has(obj, "text"):
		var s string
		if err := json.Unmarshal(obj["text"], &s); err != nil {
			t.Fatalf("bad text arg: %v", err)
		}
		// ontos v0.8.0 made EncodeText fallible (it rejects non-UTF-8).
		v, err := data.EncodeText(s)
		if err != nil {
			t.Fatalf("text arg %q does not encode: %v", s, err)
		}
		return v
	case has(obj, "atom"):
		var s string
		if err := json.Unmarshal(obj["atom"], &s); err != nil {
			t.Fatalf("bad atom arg: %v", err)
		}
		return core.NewAtom([]byte(s))
	case has(obj, "op"):
		var op string
		if err := json.Unmarshal(obj["op"], &op); err != nil {
			t.Fatalf("bad op arg: %v", err)
		}
		var args []json.RawMessage
		if err := json.Unmarshal(obj["args"], &args); err != nil {
			t.Fatalf("bad op args: %v", err)
		}
		items := make([]core.Value, 0, len(args)+1)
		items = append(items, core.NewAtom([]byte(op)))
		for _, a := range args {
			items = append(items, buildArg(t, a))
		}
		return core.NewTuple(items...)
	case has(obj, "list"):
		var children []json.RawMessage
		if err := json.Unmarshal(obj["list"], &children); err != nil {
			t.Fatalf("bad list arg: %v", err)
		}
		elems := make([]core.Value, 0, len(children))
		for _, c := range children {
			elems = append(elems, buildArg(t, c))
		}
		return data.EncodeList(elems)
	case has(obj, "tuple"):
		var children []json.RawMessage
		if err := json.Unmarshal(obj["tuple"], &children); err != nil {
			t.Fatalf("bad tuple arg: %v", err)
		}
		items := make([]core.Value, 0, len(children))
		for _, c := range children {
			items = append(items, buildArg(t, c))
		}
		return core.NewTuple(items...)
	default:
		t.Fatalf("unrecognized arg shape: %s", raw)
		return nil
	}
}

func has(m map[string]json.RawMessage, key string) bool {
	_, ok := m[key]
	return ok
}

// expectOutcome decodes the pinned outcome ("holds" | {"fails": "<code>"} | {"not_completed":
// "<kind>"}, #3126) and asserts the ground verdict matches it judgment-for-judgment.
func expectOutcome(t *testing.T, name string, raw json.RawMessage, ground completion.TheoryGround) {
	t.Helper()
	got := readGround(ground)
	// "holds"
	var s string
	if err := json.Unmarshal(raw, &s); err == nil {
		if s != "holds" {
			t.Fatalf("%s: unknown string outcome %q", name, s)
		}
		if got.arm != groundHolds {
			t.Errorf("%s: want Holds, got %#v", name, got)
		}
		return
	}
	// {"fails": "<code>"} or {"not_completed": "<kind>"}
	var obj map[string]string
	if err := json.Unmarshal(raw, &obj); err != nil || len(obj) != 1 {
		t.Fatalf("%s: outcome is none of \"holds\", {\"fails\": code}, {\"not_completed\": kind}: %s", name, raw)
	}
	if kind, ok := obj["not_completed"]; ok {
		if got.arm != groundNotDecided || got.cause.Kind().Tag() != kind {
			t.Errorf("%s: want NotCompleted(%s), got %#v", name, kind, got)
		}
		return
	}
	code, ok := obj["fails"]
	if !ok || code == "" {
		t.Fatalf("%s: outcome is none of \"holds\", {\"fails\": code}, {\"not_completed\": kind}: %s", name, raw)
	}
	if got.arm != groundFails {
		t.Errorf("%s: want Fails{%s}, got %#v", name, code, got)
		return
	}
	if got.code != code {
		t.Errorf("%s: want fail code %q, got %q", name, code, got.code)
	}
}

// ----- the replay -----

func TestArithmeticTheoryVectorDecisions(t *testing.T) {
	vf := loadArithVectors(t)
	theory := NewArithmeticTheory()
	if len(vf.Decisions) == 0 {
		t.Fatal("no decision vectors loaded")
	}
	for _, d := range vf.Decisions {
		args := make([]core.Value, 0, len(d.Args))
		for _, a := range d.Args {
			args = append(args, buildArg(t, a))
		}
		atom := GroundLiteral{Pred: SymbolFromString(d.Pred), Args: args}
		expectOutcome(t, d.Name, d.Outcome, DecideGround(theory, atom))
	}
}

func TestArithmeticTheoryVectorOwns(t *testing.T) {
	vf := loadArithVectors(t)
	theory := NewArithmeticTheory()
	for _, name := range vf.Owns.Owned {
		if !theory.Owns(SymbolFromString(name)) {
			t.Errorf("Owns(%q) = false, want true", name)
		}
	}
	for _, name := range vf.Owns.NotOwned {
		if theory.Owns(SymbolFromString(name)) {
			t.Errorf("Owns(%q) = true, want false", name)
		}
	}
}

func TestArithmeticTheoryVectorIdentity(t *testing.T) {
	vf := loadArithVectors(t)
	id := NewArithmeticTheory().Identity()
	if string(id.Id) != vf.Identity.ID {
		t.Errorf("identity Id = %q, want %q", id.Id, vf.Identity.ID)
	}
	if string(id.Version) != vf.Identity.Version {
		t.Errorf("identity Version = %q, want %q", id.Version, vf.Identity.Version)
	}
	if id.ConfigDigest != ([32]byte{}) {
		t.Errorf("identity ConfigDigest = %v, want zero", id.ConfigDigest)
	}
}

// TestDecimalSpellingsMatchTheParser (#2679, seat:caa's ruling (a)): decFromString returns through
// the one limit-checked constructor, so a spelling whose VALUE lies outside the domain is refused
// and one at the bound parses. The spellings are 65 KB, so the vector carries their recipe.
func TestDecimalSpellingsMatchTheParser(t *testing.T) {
	rows := loadArithVectors(t).DecimalSpellings.Rows
	if len(rows) != 5 {
		t.Fatalf("anti-vacuity: %d spelling rows, want 5", len(rows))
	}
	for _, row := range rows {
		spelling := row.Prefix + strings.Repeat("0", row.Zeros) + row.Suffix
		d, ok := decFromString(spelling)
		if row.Parses == nil {
			if ok {
				t.Errorf("%s: parsed, want refused", row.Name)
			}
			continue
		}
		want := data.EncodeDecimal(big.NewInt(row.Parses[0]), big.NewInt(row.Parses[1]))
		if !ok || !d.toDecimalTerm().Equal(want) {
			t.Errorf("%s: got (%v, ok=%v), want decimal(%d, %d)", row.Name, d, ok, row.Parses[0], row.Parses[1])
		}
	}
}
