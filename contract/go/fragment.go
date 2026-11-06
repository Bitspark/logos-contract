package contract

// #2759 (seat:caa's design gate; research 0028 row A15): the CONSTRUCTOR-ACYCLIC fragment's cycle
// test, in the checker's tier so there is ONE computation. check runs it over a certificate's
// sealed scope (checkScopeDownwardClosed's constructor-acyclic gate), and the kernel's resolver
// runs it over the certifying producer's seal plan (kernel/go/runtime sealedCompounds) to derive
// the function-symbol level at admission. The Go twin of rs logos_contract::fragment::ScopeGraph.
//
// A CONSTRUCTING rule's head carries an OPEN compound (IsOpenCompound): it wraps a variable in a
// function symbol. It lies on a dependency cycle when its head predicate is reachable from one of
// its own body predicates through the scope's clauses. What acyclicity discharges is FINITENESS of
// the relevant model (row A9), nothing else.

// ScopeGraph is the dependency graph of a scope, built one clause at a time: an edge from each
// in-scope clause's head to every body literal predicate (positive or negated) that is in scope. A
// count reads a relation a strictly lower certificate seals, never one of its own scope, so it adds
// no edge. Keyed by name, as a certificate's scope is.
type ScopeGraph struct {
	edges map[string]map[string]bool
}

// NewScopeGraph is an empty graph.
func NewScopeGraph() *ScopeGraph { return &ScopeGraph{edges: map[string]map[string]bool{}} }

// Add adds one clause of the program. A clause whose head is out of scope adds nothing.
func (g *ScopeGraph) Add(clause Clause, inScope func(Symbol) bool) {
	if !inScope(clause.Head.Pred) {
		return
	}
	head := string(clause.Head.Pred.Bytes())
	out, ok := g.edges[head]
	if !ok {
		out = map[string]bool{}
		g.edges[head] = out
	}
	for _, bl := range clause.Body {
		if goal, ok := bl.AsInner(); ok && inScope(goal.Pred) {
			out[string(goal.Pred.Bytes())] = true
		}
	}
}

// Constructs reports whether clause CONSTRUCTS: its head carries an open compound.
func (*ScopeGraph) Constructs(clause Clause) bool {
	for _, t := range clause.Head.Args {
		if IsOpenCompound(t) {
			return true
		}
	}
	return false
}

// CycleThrough is the first body predicate of clause, in body order, from which the clause's own
// head predicate is reachable in the graph (itself included): the clause lies on a dependency
// cycle through it. ok is false when the clause is on no cycle.
func (g *ScopeGraph) CycleThrough(clause Clause) (Symbol, bool) {
	head := string(clause.Head.Pred.Bytes())
	for _, bl := range clause.Body {
		goal, ok := bl.AsInner()
		if !ok {
			continue
		}
		if g.reaches(string(goal.Pred.Bytes()), head) {
			return goal.Pred, true
		}
	}
	return Symbol{}, false
}

// reaches reports whether to is reachable from from along the edges, from itself included.
func (g *ScopeGraph) reaches(from, to string) bool {
	seen := map[string]bool{}
	work := []string{from}
	for len(work) > 0 {
		pred := work[len(work)-1]
		work = work[:len(work)-1]
		if pred == to {
			return true
		}
		if seen[pred] {
			continue
		}
		seen[pred] = true
		for next := range g.edges[pred] {
			work = append(work, next)
		}
	}
	return false
}

// SealContext is the context a sealed clause is classified in (#3067, research 0028 row A15;
// seat:caa's ruling Q2): the relations its certificate seals, and the relations it reads from a
// strictly lower certificate. ONE type: check builds it from a certificate and the lower
// certificates it resolves. The Go twin of rs logos_contract::fragment::SealContext.
type SealContext struct {
	Seals      map[Symbol]bool
	ReadsLower map[Symbol]bool
}

// NewSealContext is the context whose certificate seals seals and reads readsLower from strictly
// lower certificates.
func NewSealContext(seals, readsLower []Symbol) SealContext {
	ctx := SealContext{Seals: map[Symbol]bool{}, ReadsLower: map[Symbol]bool{}}
	for _, s := range seals {
		ctx.Seals[s] = true
	}
	for _, s := range readsLower {
		ctx.ReadsLower[s] = true
	}
	return ctx
}

// OutsideKind names the gate a sealed clause fails.
type OutsideKind int

const (
	// OutsideCountNotLower: a count over a relation no strictly lower certificate seals.
	OutsideCountNotLower OutsideKind = iota + 1
	// OutsideCountOpenCompound: a count whose filter or result carries an open compound.
	OutsideCountOpenCompound
	// OutsideConstructorCycle: the head constructs an open compound on a dependency cycle.
	OutsideConstructorCycle
	// OutsideUnserved: a body literal over a relation neither sealed, theory-owned nor read lower.
	OutsideUnserved
	// OutsideIntraScopeNegation: a \+ over a relation the clause's own certificate seals.
	OutsideIntraScopeNegation
	// OutsideUnboundCountFilter: a count filter variable no positive sealed literal binds.
	OutsideUnboundCountFilter
	// OutsideUnboundVariable: a variable no positive sealed literal, nor a count's result, binds.
	OutsideUnboundVariable
)

// Outside is why a sealed clause is outside the certifiable fragment: the FIRST gate it fails, in
// the one order ClassifySealedClause declares, with that gate's subject. Pred is the relation of a
// count, read or negation; SameScope, for OutsideCountNotLower, is true when the clause's own
// certificate seals Pred (the table under construction); Through is the cycle's body predicate;
// Var the unbound variable. The Go twin of rs logos_contract::fragment::Outside.
type Outside struct {
	Kind      OutsideKind
	Pred      Symbol
	SameScope bool
	Through   Symbol
	Var       VarId
}

// CountHasOpenCompound reports whether a count's filter or result carries an OPEN compound (the
// function-free count gate, #2294).
func CountHasOpenCompound(count CountLit) bool {
	if IsOpenCompound(count.Count) {
		return true
	}
	for _, e := range count.Filter {
		if IsOpenCompound(e.Term) {
			return true
		}
	}
	return false
}

// ClassifySealedClause is THE classification of one sealed clause (#3067; seat:caa's rulings Q1 to
// Q3): ok is false inside the certifiable fragment, else Outside names the first gate it fails.
// graph is the scope's dependency graph (built over the program with ctx.Seals as its scope).
//
// The theory is read in TWO directions (seat:caa's ruling on #3067 increment 2, Q1): servedBy says
// which relations a theory decides live, for the read gate, and bindsNothing which relations bind no
// variable, for range restriction. check and a producer pass the bound theory's ownership for both;
// a caller that sees only part of the theory passes what it knows for each reading (the kernel's
// resolver reads the theories the kernel ships, and the certifying provider decides, #3211).
//
// The gates run in ONE order, the checker's, declared here and never restated by a caller:
//  1. the count gate, per count literal in body order: it reads a strictly lower certificate, and
//     its terms carry no open compound;
//  2. the constructor-cycle gate (ScopeGraph);
//  3. the read gate, per body literal in body order: the relation is sealed, served by a theory
//     (servedBy) or read lower, and a \+ never reads this certificate's own table;
//  4. range restriction: every count filter variable, count by count in body order, then every
//     variable of the clause, is bound by a positive literal over a relation the certificate seals
//     or reads lower and that binds (not bindsNothing); a count then binds its result. Where
//     several variables are unbound it names the first in name order.
//
// The Go twin of rs logos_contract::fragment::classify_sealed_clause, whose comments carry each
// gate's reason.
func ClassifySealedClause(clause Clause, ctx SealContext, graph *ScopeGraph, servedBy, bindsNothing func(Symbol) bool) (Outside, bool) {
	for _, b := range clause.Body {
		if !b.IsCount() {
			continue
		}
		pred := b.CountVal.Pred.Pred
		if !ctx.ReadsLower[pred] {
			return Outside{Kind: OutsideCountNotLower, Pred: pred, SameScope: ctx.Seals[pred]}, true
		}
		if CountHasOpenCompound(b.CountVal) {
			return Outside{Kind: OutsideCountOpenCompound, Pred: pred}, true
		}
	}
	if graph.Constructs(clause) {
		if through, cyclic := graph.CycleThrough(clause); cyclic {
			return Outside{Kind: OutsideConstructorCycle, Through: through}, true
		}
	}
	for _, b := range clause.Body {
		g, ok := b.AsInner()
		if !ok {
			continue
		}
		sealed := ctx.Seals[g.Pred]
		if !sealed && !servedBy(g.Pred) && !ctx.ReadsLower[g.Pred] {
			return Outside{Kind: OutsideUnserved, Pred: g.Pred}, true
		}
		if b.IsNeg() && sealed {
			return Outside{Kind: OutsideIntraScopeNegation, Pred: g.Pred}, true
		}
	}
	bound := map[VarId]struct{}{}
	for _, b := range clause.Body {
		if b.IsNeg() {
			continue
		}
		g, ok := b.AsInner()
		if !ok {
			continue
		}
		if (ctx.Seals[g.Pred] || ctx.ReadsLower[g.Pred]) && !bindsNothing(g.Pred) {
			collectVarsGoal(g, bound)
		}
	}
	for _, b := range clause.Body {
		if !b.IsCount() {
			continue
		}
		filter := map[VarId]struct{}{}
		for _, e := range b.CountVal.Filter {
			collectVarsTerm(e.Term, filter)
		}
		for _, v := range sortedVarIds(filter) {
			if _, ok := bound[v]; !ok {
				return Outside{Kind: OutsideUnboundCountFilter, Pred: b.CountVal.Pred.Pred, Var: v}, true
			}
		}
	}
	for _, b := range clause.Body {
		if b.IsCount() {
			collectVarsTerm(b.CountVal.Count, bound)
		}
	}
	all := map[VarId]struct{}{}
	collectVarsGoal(clause.Head, all)
	for _, b := range clause.Body {
		if g, ok := b.AsInner(); ok {
			collectVarsGoal(g, all)
		} else if b.IsCount() {
			for _, e := range b.CountVal.Filter {
				collectVarsTerm(e.Term, all)
			}
			collectVarsTerm(b.CountVal.Count, all)
		}
	}
	for _, v := range sortedVarIds(all) {
		if _, ok := bound[v]; !ok {
			return Outside{Kind: OutsideUnboundVariable, Var: v}, true
		}
	}
	return Outside{}, false
}
