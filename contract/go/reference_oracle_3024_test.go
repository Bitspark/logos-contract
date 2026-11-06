package contract

// #3024 part 2 (research 0028, advice section 5, row A17): an INDEPENDENT reference semantics for
// tiny generated programs, used as an oracle for Check's support and closure verdicts. It is
// deliberately slow and shares nothing with the checker's matcher or join: it grounds every rule by
// enumerating every assignment of the rule's variables over the domain, and tests each body literal
// by membership in its own string-keyed sets. It only BUILDS the checker's types (a program, two
// certificates, a one-node derivation) from the model it computed, then asks Check three questions:
//
//   - accept: the certificate carrying the reference least model is accepted;
//   - closure: the same certificate with one derived row (and its support edge) removed is refused
//     cert_not_closed. The row is one no other support edge cites, so closure is the only defect;
//   - support: the same certificate with a non-derivable row added, and no edge for it, is refused.
//
// Each program is stratified the way stacked certificates admit it (stacked_2258_m1's shape): cert 1
// (level 2) seals the positively read EDB relations e1/1 and e2/2 and the derived p/1, q/2 and r/1;
// cert 0 (level 1) seals f1/1, the only relation a rule negates. Every rule is safe.

import (
	"fmt"
	"math/rand/v2"
	"sort"
	"strings"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

var oracleDomain3024 = []string{"a", "b", "c"}

type oracleLit3024 struct {
	pred string
	args []string // variable names
	neg  bool
}

type oracleRule3024 struct {
	id   string
	head oracleLit3024
	body []oracleLit3024
}

var oracleArity3024 = map[string]int{"e1": 1, "e2": 2, "f1": 1, "p": 1, "q": 2, "r": 1}

// oracleProgram3024 generates one small safe, stratified program and its EDB.
func oracleProgram3024(rng *rand.Rand) ([]oracleRule3024, map[string][][]string) {
	edb := map[string][][]string{}
	for _, pred := range []string{"e1", "e2", "f1"} {
		for _, tuple := range oracleTuples3024(oracleArity3024[pred]) {
			if rng.IntN(2) == 0 {
				edb[pred] = append(edb[pred], tuple)
			}
		}
	}
	vars := []string{"X", "Y", "Z"}
	positive := []string{"e1", "e2", "p", "q", "r"}
	derived := []string{"p", "q", "r"}
	var rules []oracleRule3024
	for i, n := 0, 2+rng.IntN(3); i < n; i++ {
		var body []oracleLit3024
		bound := map[string]bool{}
		for k, m := 0, 1+rng.IntN(2); k < m; k++ {
			pred := positive[rng.IntN(len(positive))]
			lit := oracleLit3024{pred: pred}
			for a := 0; a < oracleArity3024[pred]; a++ {
				v := vars[rng.IntN(len(vars))]
				lit.args = append(lit.args, v)
				bound[v] = true
			}
			body = append(body, lit)
		}
		var boundVars []string
		for v := range bound {
			boundVars = append(boundVars, v)
		}
		sort.Strings(boundVars)
		if rng.IntN(2) == 0 {
			body = append(body, oracleLit3024{pred: "f1", args: []string{boundVars[rng.IntN(len(boundVars))]}, neg: true})
		}
		headPred := derived[rng.IntN(len(derived))]
		head := oracleLit3024{pred: headPred}
		for a := 0; a < oracleArity3024[headPred]; a++ {
			head.args = append(head.args, boundVars[rng.IntN(len(boundVars))])
		}
		rules = append(rules, oracleRule3024{id: fmt.Sprintf("oracle_r%d", i), head: head, body: body})
	}
	return rules, edb
}

func oracleTuples3024(arity int) [][]string {
	out := [][]string{{}}
	for i := 0; i < arity; i++ {
		var next [][]string
		for _, prefix := range out {
			for _, v := range oracleDomain3024 {
				next = append(next, append(append([]string(nil), prefix...), v))
			}
		}
		out = next
	}
	return out
}

func oracleKey3024(pred string, tuple []string) string {
	return pred + "(" + strings.Join(tuple, ",") + ")"
}

// oracleEdge3024 is one support edge of the reference model: the rule, its full assignment, and the
// rank of the iteration that first derived the fact.
type oracleEdge3024 struct {
	pred  string
	tuple []string
	rule  oracleRule3024
	asg   map[string]string
	rank  uint32
}

// oracleModel3024 is the reference least model, by naive Jacobi iteration: in iteration i every
// rule is grounded under EVERY assignment of its variables, and a positive derived literal counts
// only if it held before iteration i. A fact's rank is the first iteration that derived it, so every
// same-stratum literal an edge cites has a strictly lower rank.
func oracleModel3024(rules []oracleRule3024, edb map[string][][]string) (map[string]uint32, []oracleEdge3024) {
	edbSet := map[string]bool{}
	for pred, rows := range edb {
		for _, row := range rows {
			edbSet[oracleKey3024(pred, row)] = true
		}
	}
	rank := map[string]uint32{}
	var edges []oracleEdge3024
	for iter := uint32(1); ; iter++ {
		before := map[string]bool{}
		for k := range rank {
			before[k] = true
		}
		added := false
		for _, rule := range rules {
			var names []string
			seen := map[string]bool{}
			for _, lit := range append([]oracleLit3024{rule.head}, rule.body...) {
				for _, v := range lit.args {
					if !seen[v] {
						seen[v] = true
						names = append(names, v)
					}
				}
			}
			for _, values := range oracleTuples3024(len(names)) {
				asg := map[string]string{}
				for i, n := range names {
					asg[n] = values[i]
				}
				ground := func(l oracleLit3024) []string {
					out := make([]string, len(l.args))
					for i, v := range l.args {
						out[i] = asg[v]
					}
					return out
				}
				holds := true
				for _, lit := range rule.body {
					key := oracleKey3024(lit.pred, ground(lit))
					var in bool
					if lit.pred == "e1" || lit.pred == "e2" || lit.pred == "f1" {
						in = edbSet[key]
					} else {
						in = before[key]
					}
					if in == lit.neg {
						holds = false
						break
					}
				}
				headTuple := ground(rule.head)
				headKey := oracleKey3024(rule.head.pred, headTuple)
				if !holds || before[headKey] {
					continue
				}
				if _, done := rank[headKey]; done {
					continue
				}
				rank[headKey] = iter
				edges = append(edges, oracleEdge3024{pred: rule.head.pred, tuple: headTuple, rule: rule, asg: asg, rank: iter})
				added = true
			}
		}
		if !added {
			return rank, edges
		}
	}
}

func oracleAtomValue3024(s string) core.Value {
	v, ok := Atom([]byte(s)).EraseGround()
	if !ok {
		panic("an atom is ground")
	}
	return v
}

func oracleGround3024(pred string, tuple []string) GroundLiteral {
	args := make([]core.Value, len(tuple))
	for i, s := range tuple {
		args[i] = oracleAtomValue3024(s)
	}
	return NewGroundLiteral(pred, args...)
}

func oracleGoal3024(l oracleLit3024) Goal {
	args := make([]Term, len(l.args))
	for i, v := range l.args {
		args[i] = Var(v)
	}
	return Goal{Pred: SymbolFromString(l.pred), Args: args}
}

// oracleCert3024 builds the level-2 certificate over rows (derived facts, keyed) and edges.
func oracleCert3024(derived CertContext, edb map[string][][]string, rows map[string][]string, rank map[string]uint32, edges []oracleEdge3024) ClosedModelCert {
	domain := make([]core.Value, len(oracleDomain3024))
	for i, s := range oracleDomain3024 {
		domain[i] = oracleAtomValue3024(s)
	}
	tables := map[string][]GroundLiteral{"e1": nil, "e2": nil, "p": nil, "q": nil, "r": nil}
	for _, pred := range []string{"e1", "e2"} {
		for _, row := range edb[pred] {
			tables[pred] = append(tables[pred], oracleGround3024(pred, row))
		}
	}
	for key, tuple := range rows {
		pred := key[:strings.Index(key, "(")]
		tables[pred] = append(tables[pred], oracleGround3024(pred, tuple))
	}
	preds := []string{"e1", "e2", "p", "q", "r"}
	var extensions []RelationTable
	var scope []Symbol
	var facts uint64
	for _, pred := range preds {
		scope = append(scope, SymbolFromString(pred))
		extensions = append(extensions, NewRelationTable(SymbolFromString(pred), uint32(oracleArity3024[pred]), tables[pred]))
		facts += uint64(len(tables[pred]))
	}
	var supports []SupportEdge
	for _, e := range edges {
		subst := Subst{}
		for v, val := range e.asg {
			subst[NewVarId(v)] = Atom([]byte(val))
		}
		var refs []SupportRef
		for _, lit := range e.rule.body {
			tuple := make([]string, len(lit.args))
			for i, v := range lit.args {
				tuple[i] = e.asg[v]
			}
			atom := oracleGround3024(lit.pred, tuple)
			switch {
			case lit.neg:
				refs = append(refs, NegLowerRef{Cert: NewCertId(0), Atom: atom})
			case lit.pred == "e1" || lit.pred == "e2":
				refs = append(refs, LowerStratumRef{Cert: NewCertId(1), Atom: atom})
			default:
				refs = append(refs, SameStratumRef{Fact: atom, Rank: rank[oracleKey3024(lit.pred, tuple)]})
			}
		}
		supports = append(supports, SupportEdge{Fact: oracleGround3024(e.pred, e.tuple), Clause: NewClauseId(e.rule.id),
			Subst: subst, BodyRefs: refs, Rank: e.rank})
	}
	limits := DefaultLimits()
	cert := ClosedModelCert{
		Scope:       NewStratumPrefix(2, scope),
		ProgramHash: derived.ProgramHash, ProfileHash: derived.ProfileHash, CtxHash: derived.CtxHash,
		TheoryConfigHash: derived.TheoryConfigHash,
		Domains:          []FiniteDomain{NewFiniteDomain(SymbolFromString("d"), domain)},
		Extensions:       extensions,
		Supports:         SupportWitness{Edges: supports},
		LimitsDecl: CertSizeDecl{CertFacts: facts, DomainValues: uint64(len(domain)), SupportEdges: uint64(len(supports)),
			RuleGroundings: uint64(limits.MaxRuleGroundings), JoinSteps: uint64(limits.MaxJoinSteps),
			CertBytes: uint64(limits.MaxCertBytes)},
	}
	return cert
}

func TestAReferenceSemanticsAgreesWithCheckOnGeneratedPrograms3024(t *testing.T) {
	rng := rand.New(rand.NewPCG(3024, 28))
	const programs = 400
	var accepted, closure, support, recursive, negating int
	for n := 0; n < programs; n++ {
		rules, edb := oracleProgram3024(rng)
		rank, edges := oracleModel3024(rules, edb)

		// The claim: \+ P(t) for the first derived-relation atom the reference model does not hold.
		var claimPred string
		var claimTuple []string
		var absent [][2]string
		for _, pred := range []string{"p", "q", "r"} {
			for _, tuple := range oracleTuples3024(oracleArity3024[pred]) {
				if _, in := rank[oracleKey3024(pred, tuple)]; !in {
					absent = append(absent, [2]string{pred, strings.Join(tuple, ",")})
					if claimPred == "" {
						claimPred, claimTuple = pred, tuple
					}
				}
			}
		}
		if claimPred == "" {
			continue // every derived atom holds; there is nothing to negate
		}

		program := NewMapProgram()
		for _, rule := range rules {
			body := make([]BodyLit, len(rule.body))
			for i, lit := range rule.body {
				if lit.neg {
					body[i] = NegLit(oracleGoal3024(lit))
				} else {
					body[i] = PosLit(oracleGoal3024(lit))
				}
			}
			program.Insert(NewClauseId(rule.id), NewClauseLits(oracleGoal3024(rule.head), body...))
		}
		claimArgs := make([]Term, len(claimTuple))
		for i, s := range claimTuple {
			claimArgs[i] = Atom([]byte(s))
		}
		program.Insert(NewClauseId("oracle_q"), NewClauseLits(Goal{Pred: SymbolFromString("oracle_q")},
			NegLit(Goal{Pred: SymbolFromString(claimPred), Args: claimArgs})))

		extensional := NewPredicateSet()
		edbRows := map[string][]GroundLiteral{}
		for _, pred := range []string{"e1", "e2", "f1"} {
			extensional.Insert(SymbolFromString(pred))
			for _, row := range edb[pred] {
				edbRows[pred] = append(edbRows[pred], oracleGround3024(pred, row))
			}
		}
		derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))
		profile := &CheckProfile[unitCtx]{Theory: ltTheory{}, Leaves: negVectorLeaves{extensional: extensional, edb: edbRows},
			Admit: AlwaysAdmit[unitCtx]{}, Limits: DefaultLimits()}
		domain := make([]core.Value, len(oracleDomain3024))
		for i, s := range oracleDomain3024 {
			domain[i] = oracleAtomValue3024(s)
		}
		limits := DefaultLimits()
		cert0 := ClosedModelCert{
			Scope:       NewStratumPrefix(1, []Symbol{SymbolFromString("f1")}),
			ProgramHash: derived.ProgramHash, ProfileHash: derived.ProfileHash, CtxHash: derived.CtxHash,
			TheoryConfigHash: derived.TheoryConfigHash,
			Domains:          []FiniteDomain{NewFiniteDomain(SymbolFromString("d"), domain)},
			Extensions:       []RelationTable{NewRelationTable(SymbolFromString("f1"), 1, edbRows["f1"])},
			LimitsDecl: CertSizeDecl{CertFacts: uint64(len(edbRows["f1"])), DomainValues: uint64(len(domain)),
				RuleGroundings: uint64(limits.MaxRuleGroundings), JoinSteps: uint64(limits.MaxJoinSteps),
				CertBytes: uint64(limits.MaxCertBytes)},
		}
		claim := NewGroundLiteral("oracle_q")
		verdict := func(rows map[string][]string, edgeSet []oracleEdge3024) Outcome {
			cert1 := oracleCert3024(derived, edb, rows, rank, edgeSet)
			node := RuleNode{Conc: claim, Clause: NewClauseId("oracle_q"), Subst: Subst{}, Premises: []Premise{
				NegPremise{Atom: oracleGround3024(claimPred, claimTuple), Cert: NewCertId(1), Nonmember: DirectLookup}}, Meta: NoMeta()}
			deriv := NewDerivationWithClosedWorld([]Node{node}, 0, []ClosedModelCert{cert0, cert1})
			return CheckWithCertContext[unitCtx](program, claim, deriv, unitCtx{}, profile, derived)
		}
		describe := func() string {
			var b strings.Builder
			for _, r := range rules {
				fmt.Fprintf(&b, "\n    %s: %v :- %v", r.id, r.head, r.body)
			}
			fmt.Fprintf(&b, "\n    edb %v\n    model %v", edb, rank)
			return b.String()
		}

		rows := map[string][]string{}
		for _, e := range edges {
			rows[oracleKey3024(e.pred, e.tuple)] = e.tuple
			if e.rank > 1 {
				recursive++
			}
			for _, lit := range e.rule.body {
				if lit.neg {
					negating++
					break
				}
			}
		}

		// accept: the reference least model.
		if got := verdict(rows, edges); !got.IsAccept() {
			t.Fatalf("program %d: the reference model is refused %s: %s%s", n, got.Code().Code(), got.Detail(), describe())
		}
		accepted++

		// closure: drop one derived row no other edge cites, with its edge.
		cited := map[string]bool{}
		for _, e := range edges {
			for _, lit := range e.rule.body {
				if !lit.neg && lit.pred != "e1" && lit.pred != "e2" {
					tuple := make([]string, len(lit.args))
					for i, v := range lit.args {
						tuple[i] = e.asg[v]
					}
					cited[oracleKey3024(lit.pred, tuple)] = true
				}
			}
		}
		for i, e := range edges {
			key := oracleKey3024(e.pred, e.tuple)
			if cited[key] {
				continue
			}
			fewer := map[string][]string{}
			for k, v := range rows {
				if k != key {
					fewer[k] = v
				}
			}
			rest := append(append([]oracleEdge3024(nil), edges[:i]...), edges[i+1:]...)
			if got := verdict(fewer, rest); got.IsAccept() || got.Code() != CertNotClosed {
				t.Fatalf("program %d: dropping the derivable %s gave %s, want cert_not_closed%s", n, key, negOutcomeString(got), describe())
			}
			closure++
			break
		}

		// support: add one non-derivable row, other than the claim's atom, with no edge.
		for _, a := range absent {
			tuple := strings.Split(a[1], ",")
			if a[0] == claimPred && a[1] == strings.Join(claimTuple, ",") {
				continue
			}
			more := map[string][]string{oracleKey3024(a[0], tuple): tuple}
			for k, v := range rows {
				more[k] = v
			}
			if got := verdict(more, edges); got.IsAccept() {
				t.Fatalf("program %d: the non-derivable %s with no support edge was accepted%s", n, oracleKey3024(a[0], tuple), describe())
			}
			support++
			break
		}
	}
	t.Logf("reference oracle over %d generated programs: %d accepted, %d closure refusals, %d support refusals; %d edges of rank > 1, %d edges through a negation",
		programs, accepted, closure, support, recursive, negating)
	// Floors: an oracle that stopped generating recursion, negation or either perturbation must not
	// pass by having nothing to compare.
	// Today (seed 3024/28): 400 accepted, 187 closure, 400 support, 119 rank > 1 edges, 210 negation edges.
	if accepted < 350 || closure < 150 || support < 350 || recursive < 100 || negating < 150 {
		t.Fatalf("the oracle's coverage fell under its floors: accepted %d (350), closure %d (150), support %d (350), rank>1 edges %d (100), negation edges %d (150)",
			accepted, closure, support, recursive, negating)
	}
}
