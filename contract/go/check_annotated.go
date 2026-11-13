// ADR 0031 D5: the check of an annotated closed-model certificate, relative to its semiring's
// identity (rulings Q14 and Q15 on #1821). [PROPOSED] The Go sibling of
// contract/rs/src/check/annotated.rs; the ts binding's checkAnnotatedClosedModel is the third.
//
// The boolean check is unchanged and runs first. On a certificate it accepts, every intensional
// row's element is recomputed as the least solution of the ground system the closure join meets:
// each IDB row is the fold, with Add from Zero, over its groundings in canonical order, of the fold,
// with Mul from One, over each grounding's positive non-theory body literals in body order. The
// groundings are the closure join's own (checkCertClosure's joinGroundings with a recording hook),
// never a second join. An extensional row's element is a PREMISE: the certificate binds it, the
// check reads it, and nothing attests it (#1821 Q15 condition 1), so the verdict names those tables.

package contract

import (
	"bytes"
	"fmt"
	"sort"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// AnnotationLaw is the law an accepted annotated certificate's verdict relied on (ADR 0031 D5).
type AnnotationLaw int

const (
	// AnnotationLawKleeneLeastFixpoint: the ground system is cyclic, so it may have several
	// solutions, and the claimed elements are its LEAST one, reached by Kleene iteration from Zero.
	AnnotationLawKleeneLeastFixpoint AnnotationLaw = iota
)

// Name is the law's wire name.
func (l AnnotationLaw) Name() string {
	switch l {
	case AnnotationLawKleeneLeastFixpoint:
		return "kleene_least_fixpoint"
	}
	panic(fmt.Sprintf("contract: an AnnotationLaw with no name: %d", l))
}

// AnnotationCode names why CheckAnnotatedClosedModel refused an annotated certificate whose boolean
// check passed (ADR 0031 D5). A refusal of the boolean check itself is AnnotatedCertReject, with its
// RejectionCode unchanged; RejectionCode gains no member.
type AnnotationCode int

const (
	// AnnotationIdentityMismatch: the checker's semiring identity is not the one the certificate
	// names.
	AnnotationIdentityMismatch AnnotationCode = iota
	// AnnotationUnsupported: the certificate is outside what the check can annotate: a partial
	// scope (ADR 0030), a negated or count literal in a scope clause, or a grounding whose body is
	// not decided.
	AnnotationUnsupported
	// AnnotationShape: a sealed table is not annotated in order with one element per row, or a
	// claimed element is not an element of the semiring.
	AnnotationShape
	// AnnotationNotConverged: the iteration reached no fixed point within its bound (IDB rows + 1
	// rounds).
	AnnotationNotConverged
	// AnnotationMismatch: an intensional row's claimed element differs from the least solution.
	AnnotationMismatch
	// AnnotationNotAnElement: an Add or Mul answered SemiringNotAnElement.
	AnnotationNotAnElement
	// AnnotationStopped: an Add or Mul answered SemiringStopped: not decided, never false.
	AnnotationStopped
	// AnnotationBudgetExceeded: the Add and Mul calls exceeded the profile's MaxJoinSteps.
	AnnotationBudgetExceeded
)

// Code is the code's wire name.
func (c AnnotationCode) Code() string {
	switch c {
	case AnnotationIdentityMismatch:
		return "annotation_identity_mismatch"
	case AnnotationUnsupported:
		return "annotation_unsupported"
	case AnnotationShape:
		return "annotation_shape"
	case AnnotationNotConverged:
		return "annotation_not_converged"
	case AnnotationMismatch:
		return "annotation_mismatch"
	case AnnotationNotAnElement:
		return "semiring_not_an_element"
	case AnnotationStopped:
		return "semiring_stopped"
	case AnnotationBudgetExceeded:
		return "annotation_budget_exceeded"
	}
	panic(fmt.Sprintf("contract: an AnnotationCode with no name: %d", c))
}

// AnnotatedRow names one sealed row: the table's predicate and the row's index in it.
type AnnotatedRow struct {
	// Pred is the table's predicate.
	Pred Symbol
	// Index is the row's index in the table's row order.
	Index int
}

// AnnotatedOutcome is CheckAnnotatedClosedModel's verdict: AnnotatedAccept, AnnotatedCertReject or
// AnnotatedReject.
type AnnotatedOutcome interface {
	isAnnotatedOutcome()
}

// AnnotatedAccept: the boolean check passed and every intensional row's claimed element is the least
// solution, relative to the semiring identity the certificate names. It does NOT attest the
// extensional elements: Unattested names the tables whose elements were premises.
type AnnotatedAccept struct {
	// Law is the law the verdict relied on: AnnotationLawKleeneLeastFixpoint when the ground
	// dependency graph over the intensional rows has a cycle, nil when it is acyclic (its solution
	// is then unique).
	Law *AnnotationLaw
	// Unattested is the predicates of the extensional tables, in the certificate's table order:
	// premises the certificate binds and the verdict never attests (#1821 Q15 condition 1).
	Unattested []Symbol
}

// AnnotatedCertReject: the boolean check refused the certificate, with its code and detail
// unchanged.
type AnnotatedCertReject struct {
	// Code is the boolean check's code.
	Code RejectionCode
	// Detail is the boolean check's detail.
	Detail string
}

// AnnotatedReject: the annotated check refused a certificate whose boolean check passed, or (for
// AnnotationIdentityMismatch) before running it.
type AnnotatedReject struct {
	// Code names the refusal.
	Code AnnotationCode
	// Row is the row the refusal names, or nil.
	Row *AnnotatedRow
	// Detail is free text for a reader.
	Detail string
}

func (AnnotatedAccept) isAnnotatedOutcome()     {}
func (AnnotatedCertReject) isAnnotatedOutcome() {}
func (AnnotatedReject) isAnnotatedOutcome()     {}

// CheckAnnotatedClosedModel checks an annotated closed-model certificate (ADR 0031 D5; #1821 Q14 and
// Q15), RELATIVE TO THE SEMIRING'S IDENTITY: a verdict says the elements are the least solution in
// the semiring SemiringIdentity names, and nothing about another. It takes CheckClosedModelChain's
// parameters plus the semiring, and the first failing step is the verdict:
//
//  1. IDENTITY: SemiringIdentity(semiring) equals annotated.Semiring, else
//     AnnotationIdentityMismatch.
//  2. THE BOOLEAN CHECK: CheckClosedModelChain over the one-certificate world; a refusal is
//     AnnotatedCertReject, unchanged.
//  3. SUPPORTED: no partial scope, and no clause whose head the scope seals has a negated or count
//     body literal; else AnnotationUnsupported.
//  4. SHAPE: one AnnotatedTable per sealed table, in order, each with one element per row, else
//     AnnotationShape with no row; then each element IsElement, in table and row order, else
//     AnnotationShape naming the row.
//  5. GROUNDINGS: for each clause the scope seals whose head is not extensional, the closure join's
//     body-true groundings (a grounding whose body is not decided is AnnotationUnsupported).
//     Within a head row they are ordered by the codec bytes of Tuple[Atom(clause id),
//     Tuple[Tuple[Atom(var), value]...]], the variables in ascending byte order.
//  6. LEAST SOLUTION: Jacobi rounds from Zero, at most (IDB rows + 1) of them; each Add and Mul is
//     one step against the profile's MaxJoinSteps (AnnotationBudgetExceeded); a non-element or a
//     stop answer is AnnotationNotAnElement or AnnotationStopped naming the row being computed;
//     no fixed point within the bound is AnnotationNotConverged.
//  7. MISMATCH: the first intensional row whose claimed element differs, by encoded bytes.
//  8. ACCEPT, with the law relied on and the unattested extensional tables.
//
// The verdict does not attest extensional elements. They are premises, bound by the certificate.
func CheckAnnotatedClosedModel[C any](program Program, annotated AnnotatedClosedModelCert, ctx C, profile *CheckProfile[C], certContext CertContext, semiring Semiring) AnnotatedOutcome {
	captured := *profile
	profile = &captured
	// Own the certificate and its annotations before any consumer code runs.
	cert := cloneWorld([]ClosedModelCert{annotated.Cert})[0]
	annotations := make([]AnnotatedTable, len(annotated.Annotations))
	for i, table := range annotated.Annotations {
		annotations[i] = AnnotatedTable{Pred: table.Pred, Elements: append([]core.Value(nil), table.Elements...)}
	}

	// 1. IDENTITY.
	if !SemiringIdentity(semiring).Equal(annotated.Semiring) {
		return AnnotatedReject{Code: AnnotationIdentityMismatch,
			Detail: "the checker's semiring identity is not the identity the annotated certificate names"}
	}

	// 2. THE BOOLEAN CHECK, unchanged, over a one-certificate world.
	if out := CheckClosedModelChain(program, []ClosedModelCert{cert}, ctx, profile, certContext); !out.IsAccept() {
		return AnnotatedCertReject{Code: out.Verdict.Code(), Detail: out.Verdict.Detail()}
	}

	// 3. SUPPORTED.
	if cert.PartialScope != nil {
		return annotationUnsupported("the certificate seals a partial scope (ADR 0030): a lower bound has no least annotation")
	}
	complete := worldProgram(program)()
	if complete == nil {
		return annotationUnsupported("the program does not supply complete clause enumeration")
	}
	var refused AnnotatedOutcome
	complete.ForEachClause(func(id ClauseId, clause Clause) {
		if refused != nil || !cert.Scope.Seals(clause.Head.Pred) {
			return
		}
		for _, bl := range clause.Body {
			if !bl.IsPos() {
				refused = annotationUnsupported(fmt.Sprintf(
					"scope clause %q has a negated or count body literal, which no semiring combination is ruled for", id.String()))
				return
			}
		}
	})
	if refused != nil {
		return refused
	}

	// 4. SHAPE.
	if out := checkAnnotationShape(cert, annotations, semiring); out != nil {
		return out
	}

	// 5. GROUNDINGS, from the closure join.
	extensional := profile.Leaves.Extensional()
	system := newAnnotatedSystem(cert, annotations, extensional, profile.Theory)
	groundings, joins := 0, 0
	complete.ForEachClause(func(id ClauseId, clause Clause) {
		if refused != nil || !cert.Scope.Seals(clause.Head.Pred) || extensional.Contains(clause.Head.Pred) {
			return
		}
		view := ownView(cert)
		view.record = func(subst Subst, decided bool) {
			if refused == nil {
				refused = system.add(id, clause, subst, decided)
			}
		}
		if e := joinGroundings(clause, view, profile.Theory, profile.Limits, &groundings, &joins); e != nil && refused == nil {
			// Unreachable: step 2 ran this join in full over the same certificate and passed.
			refused = AnnotatedCertReject{Code: e.code, Detail: e.detail}
		}
	})
	if refused != nil {
		return refused
	}
	system.order()

	// 6. THE LEAST SOLUTION.
	solution, out := system.solve(semiring, profile.Limits.MaxJoinSteps)
	if out != nil {
		return out
	}

	// 7. MISMATCH.
	for t, ref := range system.idb {
		claimed := annotations[ref.table].Elements[ref.row]
		if !bytes.Equal(codec.Encode(claimed), solution[t]) {
			return AnnotatedReject{Code: AnnotationMismatch, Row: system.rowOf(t),
				Detail: "the claimed element differs from the least solution"}
		}
	}

	// 8. ACCEPT.
	var law *AnnotationLaw
	if annotatedCyclic(system.edges) {
		kleene := AnnotationLawKleeneLeastFixpoint
		law = &kleene
	}
	unattested := make([]Symbol, 0, len(cert.Extensions))
	for _, table := range cert.Extensions {
		if extensional.Contains(table.Pred) {
			unattested = append(unattested, table.Pred)
		}
	}
	return AnnotatedAccept{Law: law, Unattested: unattested}
}

func annotationUnsupported(detail string) AnnotatedOutcome {
	return AnnotatedReject{Code: AnnotationUnsupported, Detail: detail}
}

// checkAnnotationShape is step 4: the annotations follow the sealed tables, and every element is an
// element of the semiring. nil when they do.
func checkAnnotationShape(cert ClosedModelCert, annotations []AnnotatedTable, semiring Semiring) AnnotatedOutcome {
	if len(annotations) != len(cert.Extensions) {
		return AnnotatedReject{Code: AnnotationShape, Detail: fmt.Sprintf(
			"%d table annotations for %d sealed tables", len(annotations), len(cert.Extensions))}
	}
	for i, table := range cert.Extensions {
		if !annotations[i].Pred.Equal(table.Pred) {
			return AnnotatedReject{Code: AnnotationShape, Detail: fmt.Sprintf(
				"annotation %d names predicate %q, the sealed table at that place is %q", i, annotations[i].Pred.String(), table.Pred.String())}
		}
		if len(annotations[i].Elements) != len(table.Rows) {
			return AnnotatedReject{Code: AnnotationShape, Detail: fmt.Sprintf(
				"table %q has %d rows and %d elements", table.Pred.String(), len(table.Rows), len(annotations[i].Elements))}
		}
	}
	for i, table := range cert.Extensions {
		for r, element := range annotations[i].Elements {
			if element == nil || !semiring.IsElement(element) {
				return AnnotatedReject{Code: AnnotationShape, Row: &AnnotatedRow{Pred: table.Pred, Index: r},
					Detail: "the claimed element is not an element of the semiring"}
			}
		}
	}
	return nil
}

// annotatedRef is one sealed row: its table's index in the certificate and its index in the table.
type annotatedRef struct{ table, row int }

// annotatedFactor is one factor of a grounding's product: the previous round's value of IDB row
// idb, or, when idb is negative, an extensional row's claimed element (a premise).
type annotatedFactor struct {
	// idb is the IDB row read, or -1 for a premise.
	idb int
	// premise is the extensional element read when idb is -1.
	premise core.Value
}

// annotatedGrounding is one grounding the closure join emitted: its canonical key and its factors in
// body order.
type annotatedGrounding struct {
	// key is the codec bytes the groundings of one head row are ordered by.
	key []byte
	// factors are the grounding's positive non-theory body literals, in body order.
	factors []annotatedFactor
}

// annotatedSystem is the ground system step 6 solves.
type annotatedSystem struct {
	// cert is the certificate the system is read from.
	cert ClosedModelCert
	// annotations are the claimed elements, one table per sealed table.
	annotations []AnnotatedTable
	// theory owns the literals that are filters, never factors.
	theory Theory
	// where locates a sealed row by its GroundKey.
	where map[string]annotatedRef
	// idb lists the IDB rows, in table order then row order.
	idb []annotatedRef
	// idbIndex is, per table and row, the row's IDB index, or -1 for an extensional row.
	idbIndex [][]int
	// groundings holds each IDB row's groundings.
	groundings [][]annotatedGrounding
	// edges is the ground dependency graph: from each IDB row to the IDB rows its groundings read.
	edges [][]int
}

func newAnnotatedSystem(cert ClosedModelCert, annotations []AnnotatedTable, extensional *PredicateSet, theory Theory) *annotatedSystem {
	s := &annotatedSystem{cert: cert, annotations: annotations, theory: theory, where: map[string]annotatedRef{}}
	s.idbIndex = make([][]int, len(cert.Extensions))
	for i, table := range cert.Extensions {
		s.idbIndex[i] = make([]int, len(table.Rows))
		isIDB := !extensional.Contains(table.Pred)
		for r, row := range table.Rows {
			s.where[string(GroundKey(row))] = annotatedRef{table: i, row: r}
			s.idbIndex[i][r] = -1
			if isIDB {
				s.idbIndex[i][r] = len(s.idb)
				s.idb = append(s.idb, annotatedRef{table: i, row: r})
			}
		}
	}
	s.groundings = make([][]annotatedGrounding, len(s.idb))
	s.edges = make([][]int, len(s.idb))
	return s
}

// rowOf names IDB row t.
func (s *annotatedSystem) rowOf(t int) *AnnotatedRow {
	ref := s.idb[t]
	return &AnnotatedRow{Pred: s.cert.Extensions[ref.table].Pred, Index: ref.row}
}

// locate is the sealed row lit is, if any.
func (s *annotatedSystem) locate(lit GroundLiteral) (annotatedRef, bool) {
	ref, ok := s.where[string(GroundKey(lit))]
	return ref, ok
}

// add records one grounding of clause id that the closure join emitted under subst. The values it
// keeps are read from subst before the join moves on.
func (s *annotatedSystem) add(id ClauseId, clause Clause, subst Subst, decided bool) AnnotatedOutcome {
	if !decided {
		return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q has a body that is not decided", id.String()))
	}
	key, ok := annotatedGroundingKey(id, subst)
	if !ok {
		return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q binds a variable to a term that is not ground", id.String()))
	}
	// Steps 2 and 5 make every lookup below succeed: the boolean check found the head in E, and
	// every positive non-theory literal is a binder the join matched against a sealed row.
	head, ok := clause.Head.Substitute(subst).AsGround()
	if !ok {
		return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q has a head that is not ground", id.String()))
	}
	ref, ok := s.locate(head)
	if !ok || s.idbIndex[ref.table][ref.row] < 0 {
		return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q has a head that is no intensional row", id.String()))
	}
	h := s.idbIndex[ref.table][ref.row]
	var factors []annotatedFactor
	for _, bl := range clause.Body {
		goal, ok := bl.AsInner()
		if !ok || !bl.IsPos() || s.theory.Owns(goal.Pred) {
			continue
		}
		lit, ok := goal.Substitute(subst).AsGround()
		if !ok {
			return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q has a body literal that is not ground", id.String()))
		}
		at, ok := s.locate(lit)
		if !ok {
			return annotationUnsupported(fmt.Sprintf("a grounding of scope clause %q reads a row no sealed table holds", id.String()))
		}
		if i := s.idbIndex[at.table][at.row]; i >= 0 {
			factors = append(factors, annotatedFactor{idb: i})
			s.edges[h] = append(s.edges[h], i)
			continue
		}
		factors = append(factors, annotatedFactor{idb: -1, premise: s.annotations[at.table].Elements[at.row]})
	}
	s.groundings[h] = append(s.groundings[h], annotatedGrounding{key: key, factors: factors})
	return nil
}

// annotatedGroundingKey is a grounding's canonical key: the codec bytes of Tuple[Atom(clause id),
// Tuple[Tuple[Atom(var), Quote(image)], ...]], the variables in ascending byte order of their names
// and each image in the certificate wire's term reading. ok=false when an image is not ground.
func annotatedGroundingKey(id ClauseId, subst Subst) ([]byte, bool) {
	vars := make([]VarId, 0, len(subst))
	for v := range subst {
		vars = append(vars, v)
	}
	sort.Slice(vars, func(i, j int) bool { return vars[i].String() < vars[j].String() })
	bindings := make([]core.Value, len(vars))
	for i, v := range vars {
		if _, ok := subst[v].EraseGround(); !ok {
			return nil, false
		}
		bindings[i] = core.NewTuple(StrAtom(v.String()), Quote(subst[v]))
	}
	return codec.Encode(core.NewTuple(StrAtom(id.String()), core.NewTuple(bindings...))), true
}

// order sorts each IDB row's groundings by their keys, ascending.
func (s *annotatedSystem) order() {
	for _, gs := range s.groundings {
		sort.SliceStable(gs, func(i, j int) bool { return bytes.Compare(gs[i].key, gs[j].key) < 0 })
	}
}

// solve is step 6: Jacobi rounds from Zero, at most (IDB rows + 1), each Add and Mul one step against
// budget. It returns the fixed point's encoded values, one per IDB row, or the refusal.
func (s *annotatedSystem) solve(semiring Semiring, budget int) ([][]byte, AnnotatedOutcome) {
	n := len(s.idb)
	zero, one := semiring.Zero(), semiring.One()
	zeroBytes := codec.Encode(zero)
	prev := make([]core.Value, n)
	prevBytes := make([][]byte, n)
	for t := range prev {
		prev[t], prevBytes[t] = zero, zeroBytes
	}
	steps := 0
	for round := 1; round <= n+1; round++ {
		next := make([]core.Value, n)
		nextBytes := make([][]byte, n)
		converged := true
		for t := 0; t < n; t++ {
			acc := zero
			for _, g := range s.groundings[t] {
				p := one
				for _, f := range g.factors {
					v := f.premise
					if f.idb >= 0 {
						v = prev[f.idb]
					}
					var out AnnotatedOutcome
					if p, out = s.apply(semiring.Mul, "Mul", p, v, t, &steps, budget); out != nil {
						return nil, out
					}
				}
				var out AnnotatedOutcome
				if acc, out = s.apply(semiring.Add, "Add", acc, p, t, &steps, budget); out != nil {
					return nil, out
				}
			}
			next[t], nextBytes[t] = acc, codec.Encode(acc)
			if !bytes.Equal(nextBytes[t], prevBytes[t]) {
				converged = false
			}
		}
		if converged {
			return nextBytes, nil
		}
		prev, prevBytes = next, nextBytes
	}
	return nil, AnnotatedReject{Code: AnnotationNotConverged, Detail: fmt.Sprintf(
		"no fixed point within %d rounds over %d intensional rows", n+1, n)}
}

// apply charges one step and runs one semiring operation for IDB row t.
func (s *annotatedSystem) apply(op func(a, b core.Value) SemiringAnswer, name string, a, b core.Value, t int, steps *int, budget int) (core.Value, AnnotatedOutcome) {
	*steps++
	if *steps > budget {
		return nil, AnnotatedReject{Code: AnnotationBudgetExceeded, Detail: fmt.Sprintf(
			"counted semiring operations %d exceed max_join_steps %d", *steps, budget)}
	}
	switch answer := op(a, b).(type) {
	case SemiringElement:
		return answer.Value, nil
	case SemiringNotAnElement:
		return nil, AnnotatedReject{Code: AnnotationNotAnElement, Row: s.rowOf(t),
			Detail: name + " answered that an operand is not an element"}
	case SemiringStopped:
		return nil, AnnotatedReject{Code: AnnotationStopped, Row: s.rowOf(t),
			Detail: name + " stopped: " + answer.Cause.Kind().Tag()}
	}
	// A nil answer, or a foreign type embedding SemiringAnswer, establishes no element: not decided.
	return nil, AnnotatedReject{Code: AnnotationStopped, Row: s.rowOf(t),
		Detail: name + " answered no SemiringAnswer a constructor builds"}
}

// annotatedCyclic reports whether the ground dependency graph has a cycle, a self-loop included.
func annotatedCyclic(edges [][]int) bool {
	// state: 0 unvisited, 1 on the current path, 2 finished.
	state := make([]uint8, len(edges))
	type frame struct{ node, next int }
	for root := range edges {
		if state[root] != 0 {
			continue
		}
		state[root] = 1
		stack := []frame{{node: root}}
		for len(stack) > 0 {
			top := &stack[len(stack)-1]
			if top.next == len(edges[top.node]) {
				state[top.node] = 2
				stack = stack[:len(stack)-1]
				continue
			}
			succ := edges[top.node][top.next]
			top.next++
			if state[succ] == 1 {
				return true
			}
			if state[succ] == 0 {
				state[succ] = 1
				stack = append(stack, frame{node: succ})
			}
		}
	}
	return false
}
