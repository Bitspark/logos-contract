package contract

import (
	"fmt"
	"sort"
)

// #2258 (a): STACKED certificates. A sealed clause may read a predicate its own certificate does
// not seal when a certificate at a STRICTLY LOWER scope level seals it: uniquely, exactly (not in
// that certificate's PartialScope, ADR 0030 D2), and Valid. The citing certificate then reads
// that lower table: a negated literal is true iff the atom is absent from it, a positive literal
// binds over its rows.
//
// Soundness rests on the order verificationOrder fixes: a certificate is verified only after
// every certificate at a lower level, so a lower table is read only once its own support, closure
// and EDB obligations have made it the exact least model of its predicate. References go strictly
// down in level, so the citation graph is acyclic by construction, and an invalid certificate
// nothing resolves against stays inert (seat:caa's C3 amendment). Mirrors rs check/cert_stack.rs.

// verificationOrder is the order the certificates of a ClosedWorld are verified in: ascending
// scope level, ties by index. Every certificate a cert at level L can resolve against sits at a
// level below L, so its status is final before that cert is verified.
func verificationOrder(world []ClosedModelCert) []int {
	order := make([]int, len(world))
	for i := range order {
		order[i] = i
	}
	sort.SliceStable(order, func(a, b int) bool {
		return world[order[a]].Scope.Level < world[order[b]].Scope.Level
	})
	return order
}

// lowerSeal is the strictly lower certificate a predicate resolved to: its ClosedWorld index and
// the certificate.
type lowerSeal struct {
	index int
	cert  ClosedModelCert
}

// certView is one certificate's view of the tables its sealed clauses read: its OWN sealed
// tables, and each predicate it reads from a strictly lower certificate, resolved to that
// certificate. The closure join, the body-literal evaluation and the support gate all read
// tables through it. Mirrors rs CertView.
type certView struct {
	cert  ClosedModelCert
	lower map[Symbol]lowerSeal
}

// ownView reads only the certificate's own tables: every certificate before #2258 (a).
func ownView(cert ClosedModelCert) certView { return certView{cert: cert} }

// table is the table a sealed clause reads for pred: the certificate's own if it seals pred,
// else the resolved lower certificate's.
func (v certView) table(pred Symbol) (RelationTable, bool) {
	if v.cert.Scope.Seals(pred) {
		return v.cert.Table(pred)
	}
	if l, ok := v.lower[pred]; ok {
		return l.cert.Table(pred)
	}
	return RelationTable{}, false
}

// readsLower reports whether pred is read from a strictly lower certificate.
// sealContext is the context this certificate's sealed clauses are classified in (#3067, research
// 0028 row A15): the relations it seals, and the relations it reads from a strictly lower
// certificate. Mirrors rs CertView::seal_context.
func (v certView) sealContext() SealContext {
	lower := make([]Symbol, 0, len(v.lower))
	for pred := range v.lower {
		lower = append(lower, pred)
	}
	return NewSealContext(v.cert.Scope.Predicates, lower)
}

func (v certView) readsLower(pred Symbol) bool {
	_, ok := v.lower[pred]
	return ok
}

// lowerIndex is the ClosedWorld index of the lower certificate pred resolved to, if any.
func (v certView) lowerIndex(pred Symbol) (int, bool) {
	l, ok := v.lower[pred]
	return l.index, ok
}

// resolveLowerSeals resolves every predicate the certificate at own reads without sealing it: a
// body literal of a defining clause of one of its sealed predicates, on a predicate it does not
// seal and no theory owns. For each, the certificates at a strictly lower level that seal it:
// none leaves it unresolved (the scope gate refuses the literal, as it always has); more than
// one is cert_scope_incomplete, ambiguous (decided on structure alone); one sealing it in its
// PartialScope is cert_scope_incomplete (a lower bound read by a sealed clause makes that
// clause's closure, or its negation, vacuous); one Invalid invalidates this cert with that
// certificate's own code, the detail naming the chain; one exact and Valid resolves.
//
// status/verified hold the statuses computed so far; verificationOrder makes every lower one
// final first. Mirrors rs resolve_lower_seals.
func resolveLowerSeals(cert ClosedModelCert, own int, world []ClosedModelCert, status []certStatus, verified []bool, program Program, theory Theory) (certView, *certErr) {
	view := certView{cert: cert, lower: map[Symbol]lowerSeal{}}
	var err *certErr
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		if err != nil || !cert.Scope.Seals(clause.Head.Pred) {
			return
		}
		for _, bl := range clause.Body {
			// #2258 L3.3b: a count's counted predicate resolves like any other literal's, so a
			// count over a strictly lower seal is readable and the scope gate can admit it.
			pred := bl.Pred()
			if cert.Scope.Seals(pred) || theory.Owns(pred) || view.readsLower(pred) {
				continue
			}
			var sealers []int
			for j := range world {
				if world[j].Scope.Level < cert.Scope.Level && world[j].Scope.Seals(pred) {
					sealers = append(sealers, j)
				}
			}
			switch len(sealers) {
			case 0:
			case 1:
				j := sealers[0]
				if world[j].IsPartial(pred) {
					err = &certErr{CertScopeIncomplete, fmt.Sprintf(
						"certificate %d reads predicate %q, which certificate %d seals PARTIAL (a lower bound cannot be read by a sealed clause, ADR 0030 D2)",
						own, pred.String(), j)}
					return
				}
				if !verified[j] {
					// The verification order makes every lower status final first; a missing
					// one is a checker defect, refused rather than read as Valid.
					err = &certErr{CertScopeIncomplete, fmt.Sprintf(
						"certificate %d would read predicate %q from certificate %d before it is verified",
						own, pred.String(), j)}
					return
				}
				if !status[j].valid {
					err = &certErr{status[j].code, fmt.Sprintf(
						"certificate %d rests on certificate %d for predicate %q, which is invalid: %s",
						own, j, pred.String(), status[j].detail)}
					return
				}
				view.lower[pred] = lowerSeal{index: j, cert: world[j]}
			default:
				err = &certErr{CertScopeIncomplete, fmt.Sprintf(
					"predicate %q is sealed by more than one strictly lower certificate (%v); a stacked read needs a unique lower seal",
					pred.String(), sealers)}
				return
			}
		}
	})
	return view, err
}
