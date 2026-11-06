// Go replay of vectors/reify.json (#3102): §2a's reify decision, pinned as a shared fact.
//
// Before #3102 go's Reify accepted a quoted variable whose name is not UTF-8 (Tuple[Atom(0x02),
// Atom(0xFF)] reified to a variable), while rs and ts refused it. The three cores decode one
// untrusted input, so their agreement is replayed here from one hand-authored file rather than
// claimed in a comment.
package contract

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

type reifyVectorRow struct {
	Name     string          `json:"name"`
	ValueHex string          `json:"value_hex"`
	Term     json.RawMessage `json:"term"`
}

func loadReifyVectors(t *testing.T) map[string]json.RawMessage {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "reify.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read %s: %v", candidate, readErr)
			}
			var file map[string]json.RawMessage
			if jsonErr := json.Unmarshal(raw, &file); jsonErr != nil {
				t.Fatalf("parse %s: %v", candidate, jsonErr)
			}
			return file
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/reify.json above %s", dir)
		}
		d = parent
	}
}

func reifyVectorSection(t *testing.T, file map[string]json.RawMessage, key string) []reifyVectorRow {
	t.Helper()
	var rows []reifyVectorRow
	if err := json.Unmarshal(file[key], &rows); err != nil {
		t.Fatalf("section %q: %v", key, err)
	}
	if len(rows) == 0 {
		t.Fatalf("section %q is empty: a replay over no rows proves nothing", key)
	}
	return rows
}

func reifyVectorValue(t *testing.T, row reifyVectorRow) ([]byte, Term, bool) {
	t.Helper()
	raw, err := hex.DecodeString(row.ValueHex)
	if err != nil {
		t.Fatalf("%s: value_hex: %v", row.Name, err)
	}
	value, err := codec.Decode(raw)
	if err != nil {
		t.Fatalf("%s: the value does not decode: %v", row.Name, err)
	}
	term, ok := Reify(value)
	return raw, term, ok
}

// reifyVectorTerm builds the term a row describes: {"var": name}, {"atom_hex": bytes} or
// {"tuple": [terms]}.
func reifyVectorTerm(t *testing.T, name string, raw json.RawMessage) Term {
	t.Helper()
	var desc map[string]json.RawMessage
	if err := json.Unmarshal(raw, &desc); err != nil || len(desc) != 1 {
		t.Fatalf("%s: a term is an object with one key, got %s", name, raw)
	}
	for kind, body := range desc {
		switch kind {
		case "var":
			var s string
			if err := json.Unmarshal(body, &s); err != nil {
				t.Fatalf("%s: var: %v", name, err)
			}
			return Var(s)
		case "atom_hex":
			var h string
			if err := json.Unmarshal(body, &h); err != nil {
				t.Fatalf("%s: atom_hex: %v", name, err)
			}
			b, err := hex.DecodeString(h)
			if err != nil {
				t.Fatalf("%s: atom_hex: %v", name, err)
			}
			return Atom(b)
		case "tuple":
			var kids []json.RawMessage
			if err := json.Unmarshal(body, &kids); err != nil {
				t.Fatalf("%s: tuple: %v", name, err)
			}
			children := make([]Term, len(kids))
			for i, k := range kids {
				children[i] = reifyVectorTerm(t, name, k)
			}
			return Tuple(children...)
		default:
			t.Fatalf("%s: unknown term kind %q", name, kind)
		}
	}
	panic("unreachable: the one key was returned above")
}

func TestReifyVectors3102(t *testing.T) {
	file := loadReifyVectors(t)
	for key := range file {
		switch key {
		case "spec", "note", "refused", "reifies", "var_names":
		default:
			t.Fatalf("vectors/reify.json carries a section %q this replay has no reader for", key)
		}
	}

	for _, row := range reifyVectorSection(t, file, "refused") {
		if _, term, ok := reifyVectorValue(t, row); ok {
			t.Errorf("refused/%s: reify ACCEPTED it as %s; the value is outside quote's image", row.Name, term)
		}
	}

	for _, row := range reifyVectorSection(t, file, "reifies") {
		raw, got, ok := reifyVectorValue(t, row)
		if !ok {
			t.Errorf("reifies/%s: reify refused a value in quote's image", row.Name)
			continue
		}
		want := reifyVectorTerm(t, row.Name, row.Term)
		if !got.Equal(want) {
			t.Errorf("reifies/%s: reify gave %s, want %s", row.Name, got, want)
		}
		if again := codec.Encode(Quote(got)); !bytes.Equal(again, raw) {
			t.Errorf("reifies/%s: quote re-encodes to %x, want %x", row.Name, again, raw)
		}
	}

	replayVarNames3115(t, file)
}

type varNameRow struct {
	Name     string `json:"name"`
	NameHex  string `json:"name_hex"`
	InDomain bool   `json:"in_domain"`
	UTF16    bool   `json:"utf16"`
}

// replayVarNames3115 replays the var_names section (#3115): a go string holds any bytes, so every row
// is expressible here, and ParseVarId must accept it iff in_domain, refusing BY NAME otherwise, with
// NewVarId panicking with the same error. An accepted name round-trips, and quote writes exactly its
// bytes.
func replayVarNames3115(t *testing.T, file map[string]json.RawMessage) {
	t.Helper()
	var rows []varNameRow
	if err := json.Unmarshal(file["var_names"], &rows); err != nil || len(rows) == 0 {
		t.Fatalf("var_names: %v (%d rows); a replay over no rows proves nothing", err, len(rows))
	}
	for _, row := range rows {
		b, err := hex.DecodeString(row.NameHex)
		if err != nil {
			t.Fatalf("var_names/%s: name_hex: %v", row.Name, err)
		}
		name := string(b)
		if utf8.ValidString(name) != row.InDomain {
			t.Errorf("var_names/%s: the row says in_domain=%v, but the bytes' UTF-8 validity is %v", row.Name, row.InDomain, !row.InDomain)
			continue
		}
		id, err := ParseVarId(name)
		if row.InDomain != (err == nil) {
			t.Errorf("var_names/%s: ParseVarId err=%v, want accepted=%v", row.Name, err, row.InDomain)
			continue
		}
		if !row.InDomain {
			var verr *VarIdError
			if !errors.As(err, &verr) || verr.Name != name {
				t.Errorf("var_names/%s: refused without a *VarIdError naming it: %v", row.Name, err)
			}
			if perr, panicked := mustVarIdPanic(func() { NewVarId(name) }); !panicked || perr == nil {
				t.Errorf("var_names/%s: NewVarId did not panic with a *VarIdError", row.Name)
			}
			continue
		}
		v := VarFromID(id)
		q := Quote(v)
		if back, ok := Reify(q); !ok || !back.Equal(v) {
			t.Errorf("var_names/%s: reify(quote(v)) != v", row.Name)
		}
		want := core.NewTuple(core.NewAtom([]byte{tagQuoteVar}), core.NewAtom(b))
		if !bytes.Equal(codec.Encode(q), codec.Encode(want)) {
			t.Errorf("var_names/%s: quote does not write exactly name_hex", row.Name)
		}
	}
}
