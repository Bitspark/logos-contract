package contract

// Go replay of vectors/account-v2-list.json (#2732 increment 1). The spec records the reify-aware
// account-v2 check as tri-core (docs/spec/logos-contract.md §9), yet until this file only rs replayed
// the vector. Like the rs oracle (conformance/rs/tests/list_reification_vectors.rs), each case is
// rebuilt from code and the committed file is checked against it: the file is checked, not trusted.
// The case NAMES are read from the file, so a case added there with no builder here fails, and a
// builder here with no case there fails.

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/internal/replayledger"
	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// avFile is this replay's vector file, as its ledger lines name it (#2732 increment 2).
const avFile = "account-v2-list.json"

type accountV2ListFile struct {
	Fixtures []struct {
		Name        string `json:"name"`
		ConsWireHex string `json:"cons_wire_hex"`
		ListWireHex string `json:"list_wire_hex"`
	} `json:"fixtures"`
	CheckCorrespondence struct {
		AccountEqual []struct {
			Case string `json:"case"`
		} `json:"account_equal"`
		AccountDistinct []struct {
			Case string `json:"case"`
		} `json:"account_distinct"`
	} `json:"check_correspondence"`
}

func loadAccountV2List(t *testing.T) accountV2ListFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "account-v2-list.json")
		if raw, err := os.ReadFile(candidate); err == nil {
			var f accountV2ListFile
			if err := json.Unmarshal(raw, &f); err != nil {
				t.Fatalf("parsing %s: %v", candidate, err)
			}
			return f
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/account-v2-list.json above %s", dir)
		}
		d = parent
	}
}

func avAtom(s string) core.Value { return core.NewAtom([]byte(s)) }
func avNil() core.Value          { return avAtom("[]") }
func avCons(head, tail core.Value) core.Value {
	return core.NewTuple(avAtom("."), head, tail)
}

// avConsList is a PROPER cons list, right-folded onto [].
func avConsList(elems ...core.Value) core.Value {
	acc := avNil()
	for i := len(elems) - 1; i >= 0; i-- {
		acc = avCons(elems[i], acc)
	}
	return acc
}

// avListEmbed is the `list` embedding Tuple[Atom("list"), e0, …], built directly so the
// correspondence oracle does not depend on the transform it checks.
func avListEmbed(elems ...core.Value) core.Value {
	return core.NewTuple(append([]core.Value{avAtom("list")}, elems...)...)
}

// avClaimWireHex is the account's reading of the ground claim p(arg): Tuple[Atom(p), quote(arg)].
func avClaimWireHex(arg core.Value) string {
	return hex.EncodeToString(codec.Encode(core.NewTuple(avAtom("p"), Quote(FromValue(arg)))))
}

func sortedNames[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

func TestAccountV2ListFixtures2732(t *testing.T) {
	f := loadAccountV2List(t)
	// Each fixture's argument, in its default cons form.
	builders := map[string]core.Value{
		"proper_pair":      avConsList(avAtom("a"), avAtom("b")),
		"proper_singleton": avConsList(avAtom("a")),
		"empty_nil":        avNil(),
		"improper_tail":    avCons(avAtom("a"), avAtom("b")),
		"nested_list":      avConsList(avConsList(avAtom("a")), avAtom("b")),
	}
	if len(f.Fixtures) != len(builders) {
		t.Fatalf("the file carries %d fixtures, the oracle builds %d (%v)", len(f.Fixtures), len(builders), sortedNames(builders))
	}
	for _, fx := range f.Fixtures {
		arg, ok := builders[fx.Name]
		if !ok {
			t.Fatalf("fixture %q has no builder here", fx.Name)
		}
		if got := avClaimWireHex(arg); got != fx.ConsWireHex {
			t.Errorf("[%s] cons wire hex: got %s, the file pins %s", fx.Name, got, fx.ConsWireHex)
		} else {
			replayledger.Observe(t, avFile, fx.Name, "cons_wire_hex", replayledger.Passed)
		}
		if got := avClaimWireHex(CanonicalizeLists(arg)); got != fx.ListWireHex {
			t.Errorf("[%s] canonicalized (list) wire hex: got %s, the file pins %s", fx.Name, got, fx.ListWireHex)
		} else {
			replayledger.Observe(t, avFile, fx.Name, "list_wire_hex", replayledger.Passed)
		}
	}
}

func TestAccountV2ListCheckCorrespondence2732(t *testing.T) {
	f := loadAccountV2List(t)
	ab := []core.Value{avAtom("a"), avAtom("b")}
	// account_equal: a cons form and its `list` embedding canonicalize to ONE value.
	equal := map[string][2]core.Value{
		"proper_pair_cons_vs_list": {avConsList(ab...), avListEmbed(ab...)},
		"singleton_cons_vs_list":   {avConsList(avAtom("a")), avListEmbed(avAtom("a"))},
		"nested_cons_vs_list": {
			avConsList(avConsList(avAtom("a")), avAtom("b")),
			avListEmbed(avListEmbed(avAtom("a")), avAtom("b")),
		},
	}
	// account_distinct: pairs that MUST NOT conflate.
	distinct := map[string][2]core.Value{
		"wrong_order":             {avListEmbed(ab...), avListEmbed(avAtom("b"), avAtom("a"))},
		"empty_nil_vs_empty_list": {avNil(), avListEmbed()},
		"proper_vs_improper":      {avListEmbed(ab...), avCons(avAtom("a"), avAtom("b"))},
	}
	enc := func(v core.Value) string { return hex.EncodeToString(codec.Encode(v)) }
	check := func(section string, cases []struct {
		Case string `json:"case"`
	}, oracle map[string][2]core.Value, wantEqual bool) {
		if len(cases) != len(oracle) {
			t.Fatalf("%s: the file carries %d cases, the oracle builds %d (%v)", section, len(cases), len(oracle), sortedNames(oracle))
		}
		for _, c := range cases {
			pair, ok := oracle[c.Case]
			if !ok {
				t.Fatalf("%s case %q has no builder here", section, c.Case)
			}
			// The presentation equivalence (#3022): two spellings present one list exactly when
			// their list normal forms are equal. check() no longer applies it: every certified
			// claim is exact, so an account_equal pair is two distinct terms to the checker.
			same := enc(CanonicalizeLists(pair[0])) == enc(CanonicalizeLists(pair[1]))
			held := true
			if same != wantEqual {
				t.Errorf("%s [%s]: canonicalized equal = %v, want %v", section, c.Case, same, wantEqual)
				held = false
			}
			if pair[0].Equal(pair[1]) {
				t.Errorf("%s [%s]: the two spellings are one term structurally; the pair pins nothing", section, c.Case)
				held = false
			}
			if held {
				replayledger.Observe(t, avFile, c.Case, "outcome", replayledger.Passed)
			}
		}
	}
	check("account_equal", f.CheckCorrespondence.AccountEqual, equal, true)
	check("account_distinct", f.CheckCorrespondence.AccountDistinct, distinct, false)
}
