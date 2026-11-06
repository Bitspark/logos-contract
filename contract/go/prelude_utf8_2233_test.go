// #2233: LoadPrelude refuses what encoding/json would silently repair. A lone UTF-16 surrogate
// escape and a byte that is not UTF-8 both became U+FFFD, so `p(X,Y) :- q(X), r(Y)` loaded as
// `p(V,V) :- q(V), r(V)` and the digest could not tell. The same witnesses are pinned in
// contract/rs and contract/ts.
package contract

import (
	"errors"
	"strings"
	"testing"
)

// utf8Clause is `p(X,Y) :- q(X), r(Y)` with the two variable names spliced in as raw JSON string
// contents, so escapes and raw bytes reach the loader unchanged.
func utf8Clause(x, y string) string {
	return `{"head":{"pred":"p","args":[{"var":"` + x + `"},{"var":"` + y + `"}]},` +
		`"body":[{"pred":"q","args":[{"var":"` + x + `"}]},{"pred":"r","args":[{"var":"` + y + `"}]}]}`
}

// utf8Load loads a one-clause bundle, pinning the digest the loader recomputes, so only a
// refusal BEFORE the digest check can fail it.
func utf8Load(clauseJSON string) (*PreludeBundle, error) {
	doc := `{"name":"t","version":"0.0.0","program_digest":"DIGEST","clauses":[{"clause":` + clauseJSON + `}]}`
	_, err := LoadPrelude([]byte(doc))
	var perr *PreludeError
	if !errors.As(err, &perr) || perr.Kind != PreludeDigestMismatch {
		return nil, err
	}
	return LoadPrelude([]byte(strings.Replace(doc, "DIGEST", perr.Recomputed, 1)))
}

func TestPrelude2233RefusesWhatJSONWouldRepair(t *testing.T) {
	refused := []struct{ name, x, y string }{
		{"PJ1 lone surrogate escapes", `\ud800`, `\udc00`},
		{"PJ2 raw bytes that are not UTF-8", "\xff", "\xfe"},
		{"a high surrogate followed by a non-surrogate escape", `\ud800\u0041`, `Y`},
		{"a lone low surrogate", `X`, `\udfff`},
	}
	for _, c := range refused {
		_, err := utf8Load(utf8Clause(c.x, c.y))
		var perr *PreludeError
		if !errors.As(err, &perr) || perr.Kind != PreludeMalformed {
			t.Errorf("%s: got %v, want a %s refusal", c.name, err, PreludeMalformed)
		}
	}
}

func TestPrelude2233WellFormedNamesStillLoadDistinct(t *testing.T) {
	loaded := []struct{ name, x, y string }{
		{"PJ0 control", "X", "Y"},
		{"a surrogate PAIR each (U+1F600, U+1F601)", `\ud83d\ude00`, `\ud83d\ude01`},
	}
	for _, c := range loaded {
		b, err := utf8Load(utf8Clause(c.x, c.y))
		if err != nil {
			t.Fatalf("%s: refused: %v", c.name, err)
		}
		head := b.Clauses[0].Clause.Head
		if len(head.Args) != 2 || head.Args[0].(VarTerm).ID().String() == head.Args[1].(VarTerm).ID().String() {
			t.Fatalf("%s: the two head variables merged: %v", c.name, head)
		}
	}
}
