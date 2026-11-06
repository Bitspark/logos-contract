// VARIANT-ADDITION TRIPWIRE for go (#996) — the go half of the forcer #991 gave rust.
//
// WHY GO NEEDS ITS OWN MECHANISM. rust forces at COMPILE TIME: `BodyLit` is an enum and the
// polarity-switching methods are arm-less `match`es, so adding a variant does not build.
// ts forces at compile time too — `Polarity` is a string-literal union, so a `Record<Polarity, …>`
// stops tsc. Go can do NEITHER: `Polarity` is `int` + `iota`, the compiler does not check switch
// exhaustiveness, and there is no reflection over consts. A fourth const appended after `Count` is
// invisible to every in-language check.
//
// So this file gets its forcing from the one place go leaves open: it PARSES ITS OWN SOURCE at
// test time and counts the declared polarities. Adding a const without adding a corpus sample
// moves the count and fails the test, naming both numbers.
package contract

import (
	"go/ast"
	"go/parser"
	"go/token"
	"testing"
)

// declaredPolarityNames parses program.go and returns the names declared as `Polarity` consts,
// in declaration order. This is the denominator every guard below prints.
//
// It reads the SOURCE rather than the values deliberately: `Polarity(3)` is constructible whether
// or not anyone declared it, so counting values would count nothing. Counting declarations is what
// makes "a maintainer added a polarity" observable at all in this language.
func declaredPolarityNames(t *testing.T) []string {
	t.Helper()
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "program.go", nil, 0)
	if err != nil {
		t.Fatalf("parsing program.go for the polarity declarations: %v — this guard cannot run "+
			"without its source; do not skip it, fix the path", err)
	}

	var names []string
	var lastType string
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.CONST {
			continue
		}
		for _, spec := range gen.Specs {
			vs, ok := spec.(*ast.ValueSpec)
			if !ok {
				continue
			}
			// `Pos Polarity = iota` names the type; `Neg` / `Count` inherit it implicitly.
			if id, ok := vs.Type.(*ast.Ident); ok {
				lastType = id.Name
			} else if len(vs.Values) > 0 {
				lastType = "" // a fresh initialiser of some other type ends the run
			}
			if lastType != "Polarity" {
				continue
			}
			for _, n := range vs.Names {
				if n.Name != "_" {
					names = append(names, n.Name)
				}
			}
		}
	}
	if len(names) == 0 {
		t.Fatal("parsed program.go and found ZERO Polarity consts — the guard would pass " +
			"vacuously, so it fails instead. The declaration shape changed; fix this parser.")
	}
	return names
}

// TestPolarityCorpusCoversEveryDeclaredPolarity is the tripwire.
//
// It fails the moment a polarity is DECLARED without a matching sample in
// bodyLitPolarityCases() — the case rust catches with a compile error and go otherwise cannot
// catch at all. Both numbers are in the message: a verdict without its denominator is not
// auditable.
//
// HONEST BOUND, stated so nobody reads more into it: this proves the corpus has as many samples
// as there are declared polarities. It does not prove they are the RIGHT ones — TestBodyLitPolarityPartition
// covers that, and it can only cover what the corpus lists. Together: this guard makes the corpus
// complete, the partition guard makes it correct.
func TestPolarityCorpusCoversEveryDeclaredPolarity(t *testing.T) {
	declared := declaredPolarityNames(t)
	corpus := bodyLitPolarityCases()

	if len(corpus) != len(declared) {
		t.Fatalf("polarity corpus is INCOMPLETE: %d declared %v but bodyLitPolarityCases() has "+
			"%d sample(s) %v — every guard in this package iterates that corpus, so the missing "+
			"polarity passes them ALL vacuously. Add a sample (and see #996: until you do, the "+
			"new polarity is answered by the `default` arm of BindingTerms/RequiredTerms/Dependency).",
			len(declared), declared, len(corpus), keysOf(corpus))
	}
	t.Logf("polarity corpus complete: %d declared %v, %d samples", len(declared), declared, len(corpus))
}

func keysOf(m map[string]BodyLit) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	return out
}

// TestUnknownPolarityFailsClosed pins caa's #996 ruling on all three structural surfaces.
//
// THE DEFECT THIS REPLACES. `default:` used to be an ALIAS for the Pos case — commented
// `// Pos` — on BindingTerms, RequiredTerms and Dependency. That aliasing turned "a polarity we
// have never seen" into "the most permissive polarity we have", at three surfaces that feed range
// restriction and stratification. MEASURED before the fix, for Polarity(3):
//
//	BindingTerms()  = 2 terms          (claimed it BINDS its arguments)
//	RequiredTerms() = 0 terms          (claimed it requires NOTHING already bound)
//	Dependency()    = (p, false)       (told the stratifier there is NO barrier)
//
// An unknown polarity must instead bind nothing, require everything, and force a barrier — deny in
// every direction — so a program using one fails range restriction or gets a conservative
// stratification rather than a silently permissive one.
//
// REACHABILITY (the severity question, measured for #996): an unknown polarity CANNOT arrive from
// outside the process. bodyLitFromTerm constructs only through PosLit/NegLit/CountLitBody, so
// there is no byte path to an arbitrary Polarity value. This is a development-time guard: it
// catches a maintainer adding a variant, not an attacker sending one.
func TestUnknownPolarityFailsClosed(t *testing.T) {
	// One past the last declared polarity — exactly what the next `iota` const would be.
	unknown := Polarity(len(declaredPolarityNames(t)))
	bl := BodyLit{Polarity: unknown, Lit: NewGoal("p", Var("X"), Var("Y"))}

	if bl.IsPos() {
		t.Errorf("IsPos() = true for unknown polarity %d — the whitelist must deny", unknown)
	}
	if _, ok := bl.AsInner(); ok {
		t.Errorf("AsInner() ok = true for unknown polarity %d — the whitelist must deny", unknown)
	}
	if got := bl.BindingTerms(); len(got) != 0 {
		t.Errorf("BindingTerms() = %d term(s) for unknown polarity %d, want 0 — an unknown "+
			"literal must be assumed to bind NOTHING (it returned Lit.Args when `default` "+
			"aliased Pos)", len(got), unknown)
	}
	if got, want := bl.RequiredTerms(), bl.Lit.Args; len(got) != len(want) {
		t.Errorf("RequiredTerms() = %d term(s) for unknown polarity %d, want %d (all args) — an "+
			"unknown literal must be assumed to evaluate NOTHING on its own, so range "+
			"restriction demands its arguments already bound", len(got), unknown, len(want))
	}
	if _, nonMonotone := bl.Dependency(); !nonMonotone {
		t.Errorf("Dependency() nonMonotone = false for unknown polarity %d — an unknown literal "+
			"must be assumed to break monotonicity so the stratifier keeps its barrier; false "+
			"here is what let an unseen polarity through with no stratum at all", unknown)
	}
}

// TestEveryDeclaredPolarityHasASampleOfThatPolarity closes the last unforced step for go.
//
// TestPolarityCorpusCoversEveryDeclaredPolarity proves the corpus has as many samples as there are
// declared polarities. It does not prove they are the RIGHT ones: adding a second "pos" sample under
// a new label satisfies the count while leaving the new polarity untested. caa named this residue on
// #991 as the last unforced step in the chain.
//
// It closes here because the AST gives us DECLARATION ORDER, and declaration order IS the iota
// value. So the i-th declared polarity must have a sample carrying Polarity(i) — which forces the
// corpus to contain one literal of each actual polarity, not merely N literals.
func TestEveryDeclaredPolarityHasASampleOfThatPolarity(t *testing.T) {
	declared := declaredPolarityNames(t)
	corpus := bodyLitPolarityCases()

	present := make(map[Polarity]string, len(corpus))
	for label, bl := range corpus {
		if prev, dup := present[bl.Polarity]; dup {
			t.Errorf("corpus samples %q and %q BOTH carry polarity %d — a duplicate satisfies the "+
				"count while leaving another polarity untested", prev, label, bl.Polarity)
		}
		present[bl.Polarity] = label
	}

	for i, name := range declared {
		// Declaration order is the iota value: the i-th const IS Polarity(i).
		if label, ok := present[Polarity(i)]; !ok {
			t.Errorf("declared polarity %s (= Polarity(%d)) has NO sample carrying that polarity — "+
				"the corpus has %d sample(s) covering %v, so %s passes every guard in this package "+
				"vacuously", name, i, len(corpus), present, name)
		} else {
			t.Logf("%s (Polarity(%d)) ← sample %q", name, i, label)
		}
	}
}
