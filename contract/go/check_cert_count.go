package contract

import (
	"fmt"
	"math/big"

	data "github.com/bitspark/ontos/data/go"
)

// #2258 lane 3's L3.3b: a COUNT (ADR 0023) inside a sealed clause, over a relation a strictly
// lower certificate seals. Admission is the NegLower rule (seat:caa's Q2): the counted predicate
// must resolve to the unique, exact, Valid certificate at a strictly lower level that seals it.
// The closure evaluates it as a count stage (it binds or tests its result, one join step per lower
// row it scans), and a CountLowerRef support ref recomputes it against that table. min/max over no
// matching row has no value (the count literal is false); a non-integer column is unserved,
// count_attr_out_of_range. Mirrors rs contract/rs/src/check/cert_count.rs.

// aggregateOver folds count over table under the ground filter: the counted relation's arity must
// agree with the table's, and every filter position and the projected column must lie inside it
// (count_attr_out_of_range, the structural checks verifyCountPremise runs before its fold).
func aggregateOver(count CountLit, filter []GroundFilterEntry, table RelationTable) (*big.Int, *certErr) {
	arity := table.Arity
	if count.Pred.Arity != arity {
		return nil, &certErr{CountAttrOutOfRange, fmt.Sprintf("count predicate arity %d does not match the sealed table arity %d", count.Pred.Arity, arity)}
	}
	for _, e := range filter {
		if e.Pos >= arity {
			return nil, &certErr{CountAttrOutOfRange, fmt.Sprintf("count filter position %d is outside predicate arity %d", e.Pos, arity)}
		}
	}
	if count.Project.HasColumn() && count.Project.Attr >= arity {
		return nil, &certErr{CountAttrOutOfRange, fmt.Sprintf("aggregate projection attr %d is outside predicate arity %d", count.Project.Attr, arity)}
	}
	return evaluateAggregate(table.Rows, filter, count.Project)
}

// groundCountFilter is the count's filter under subst, each value ground, or false if one is not.
func groundCountFilter(count CountLit, subst Subst) ([]GroundFilterEntry, bool) {
	filter := make([]GroundFilterEntry, 0, len(count.Filter))
	for _, e := range count.Filter {
		v, ok := e.Term.Substitute(subst).EraseGround()
		if !ok {
			return nil, false
		}
		filter = append(filter, GroundFilterEntry{Pos: e.Pos, Value: v})
	}
	return filter, true
}

// countLowerTable is the lower table a count reads, or cert_scope_incomplete: the scope gate
// admits a count only over a predicate resolved to a strictly lower certificate.
func countLowerTable(count CountLit, view certView) (RelationTable, *certErr) {
	pred := count.Pred.Pred
	if !view.readsLower(pred) {
		return RelationTable{}, &certErr{CertScopeIncomplete, fmt.Sprintf("count over predicate %q, which no strictly lower certificate seals", pred.String())}
	}
	t, ok := view.table(pred)
	if !ok {
		return RelationTable{}, &certErr{CertScopeIncomplete, fmt.Sprintf("count over predicate %q, whose lower certificate has no sealed extension", pred.String())}
	}
	return t, nil
}

// countStage runs one CLOSURE COUNT STAGE at its evaluation point: charge one join step per row
// of the lower table it scans, fold, then bind the result variable (recorded in newly) or test a
// result already ground. False when the count has no value (agg_empty_undefined) or differs from
// a ground result; a filter not ground here is cert_scope_incomplete, never a silent false.
func countStage(count CountLit, subst Subst, view certView, limits CheckLimits, joins *int, newly *[]VarId) (bool, *certErr) {
	table, e := countLowerTable(count, view)
	if e != nil {
		return false, e
	}
	for range table.Rows {
		if e := countJoinStep(joins, view.cert, limits); e != nil {
			return false, e
		}
	}
	filter, ok := groundCountFilter(count, subst)
	if !ok {
		return false, &certErr{CertScopeIncomplete, fmt.Sprintf(
			"closure count over predicate %q has a filter that is not ground at its evaluation point (unsafe existential)", count.Pred.Pred.String())}
	}
	n, e := aggregateOver(count, filter, table)
	if e != nil {
		if e.code == AggEmptyUndefined {
			return false, nil
		}
		return false, e
	}
	folded := data.EncodeInt(n)
	switch slot := count.Count.Substitute(subst).(type) {
	case VarTerm:
		subst[slot.ID()] = FromValue(folded)
		*newly = append(*newly, slot.ID())
		return true, nil
	case AtomTerm, TupleTerm:
		v, ok := slot.EraseGround()
		return ok && v.Equal(folded), nil
	default:
		// The slot is the program's count term, filled with values the join built (#3074:
		// internal, so an unknown kind panics by name).
		panic(fmt.Sprintf("contract: countStage: unknown Term %T", slot))
	}
}

// resolveCountLower resolves a support edge's CountLowerRef for body literal k, a count: cited must
// be the strictly lower certificate the counted predicate resolved to (its own certificate is
// refused), the filter and the result must be ground under subst, and the aggregate recomputed
// over the lower table must equal the result. A count with no value supports nothing.
func resolveCountLower(k int, count CountLit, cited CertId, subst Subst, view certView, place certPlace) *certErr {
	unsupported := func(detail string) *certErr { return &certErr{CertUnsupported, detail} }
	pred := count.Pred.Pred
	lower, e := checkSupportRefCert(k, cited, pred, view, place)
	if e != nil {
		return e
	}
	if lower == nil {
		return unsupported(fmt.Sprintf(
			"support body ref %d: CountLower cites its own certificate for predicate %q (a count must read a strictly lower certificate)", k, pred.String()))
	}
	filter, ok := groundCountFilter(count, subst)
	if !ok {
		return unsupported(fmt.Sprintf("support body ref %d: count filter not ground under subst", k))
	}
	claimed, ok := count.Count.Substitute(subst).EraseGround()
	if !ok {
		return unsupported(fmt.Sprintf("support body ref %d: count result not ground under subst", k))
	}
	n, e := aggregateOver(count, filter, lower.table)
	if e != nil {
		if e.code == AggEmptyUndefined {
			return unsupported(fmt.Sprintf("support body ref %d: the count has no value over certificate %d's table (%s)", k, lower.index, e.detail))
		}
		return e
	}
	if c, err := data.ReadInt(claimed); err == nil && c.Cmp(n) == 0 {
		return nil
	}
	return unsupported(fmt.Sprintf(
		"support body ref %d: count result does not equal the aggregate recomputed over certificate %d's table (%s)", k, lower.index, n.String()))
}
