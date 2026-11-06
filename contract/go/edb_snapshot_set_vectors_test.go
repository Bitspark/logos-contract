// Go replay of vectors/edb_snapshot_set.json (#2279): EdbTableHash reads its rows as a SET.
// Every case is an equivalence over hashes, so no digest is authored in the vector.
package contract

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

type edbSnapshotSetFile struct {
	Pred  string              `json:"pred"`
	Arity uint32              `json:"arity"`
	Rows  map[string][]string `json:"rows"`
	Equal []struct {
		Name  string     `json:"name"`
		Lists [][]string `json:"lists"`
	} `json:"equal"`
	Differ []struct {
		Name  string     `json:"name"`
		Lists [][]string `json:"lists"`
	} `json:"differ"`
	TableAgrees [][]string `json:"table_agrees"`
}

func loadEdbSnapshotSet(t *testing.T) edbSnapshotSetFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "edb_snapshot_set.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read vector: %v", readErr)
			}
			var v edbSnapshotSetFile
			if err := json.Unmarshal(raw, &v); err != nil {
				t.Fatalf("parse vector: %v", err)
			}
			return v
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatalf("could not locate vectors/edb_snapshot_set.json")
		}
		dir = parent
	}
}

func (v edbSnapshotSetFile) rows(t *testing.T, names []string) []GroundLiteral {
	t.Helper()
	out := make([]GroundLiteral, 0, len(names))
	for _, n := range names {
		args, ok := v.Rows[n]
		if !ok {
			t.Fatalf("row %s is not in `rows`", n)
		}
		vals := make([]core.Value, len(args))
		for i, a := range args {
			vals[i] = core.NewAtom([]byte(a))
		}
		out = append(out, NewGroundLiteral(v.Pred, vals...))
	}
	return out
}

func (v edbSnapshotSetFile) hash(t *testing.T, names []string) Hash {
	t.Helper()
	return EdbTableHash(SymbolFromString(v.Pred), v.rows(t, names))
}

func TestEdbSnapshotSetEveryEqualGroupHashesEqual(t *testing.T) {
	v := loadEdbSnapshotSet(t)
	if len(v.Equal) == 0 {
		t.Fatal("the vector must carry equal groups")
	}
	for _, g := range v.Equal {
		first := v.hash(t, g.Lists[0])
		for _, list := range g.Lists[1:] {
			if v.hash(t, list) != first {
				t.Errorf("%s: %v hashes differently from %v", g.Name, list, g.Lists[0])
			}
		}
	}
}

func TestEdbSnapshotSetEveryDifferPairHashesDifferently(t *testing.T) {
	v := loadEdbSnapshotSet(t)
	if len(v.Differ) == 0 {
		t.Fatal("the vector must carry differ pairs, or a constant hash passes")
	}
	for _, p := range v.Differ {
		if v.hash(t, p.Lists[0]) == v.hash(t, p.Lists[1]) {
			t.Errorf("%s: %v and %v hash equal", p.Name, p.Lists[0], p.Lists[1])
		}
	}
}

func TestEdbSnapshotSetASnapshotEqualsTheHashOverItsSealedTable(t *testing.T) {
	v := loadEdbSnapshotSet(t)
	pred := SymbolFromString(v.Pred)
	for _, list := range v.TableAgrees {
		rows := v.rows(t, list)
		table := NewRelationTable(pred, v.Arity, rows)
		if !table.IsCanonical() {
			t.Errorf("%v: the sealed table is not canonical", list)
		}
		if EdbTableHash(pred, rows) != EdbTableHash(pred, table.Rows) {
			t.Errorf("%v: the snapshot of the rows and the hash over the table they seal differ", list)
		}
	}
}
