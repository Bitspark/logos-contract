package contract

import (
	"fmt"
	"math/big"

	codec "github.com/bitspark/ontos/codec/go"
	data "github.com/bitspark/ontos/data/go"
)

// evaluateAggregate folds the rows that match filter under project, in ONE linear scan — ADR
// 0023's one aggregate semantics, the Go twin of rs `crate::aggregate::evaluate_aggregate`:
//
//	Rows              the number of matching rows
//	Distinct{attr}    the number of distinct values of column attr, by canonical encoding,
//	                  EXCLUDING null()
//	Sum{attr}         the integer sum of column attr; empty sums to 0
//	Min/Max{attr}     the integer extreme of column attr; empty is UNDEFINED
//
// rows are read as a SET (a sealed table is sorted and deduplicated). A filter position or a
// projection column outside a row's arity simply does not match; checking both against the
// relation's arity is the caller's. The errors are the checker's own codes: count_attr_out_of_range
// for a non-int column under sum/min/max (v1 folds are integer-only), agg_empty_undefined for
// min/max over no matching row. It is the fold verifyCountPremise recomputes a claimed aggregate
// with, and (#2258 L3.3b) the one a closure count stage and a CountLower support ref evaluate.
func evaluateAggregate(rows []GroundLiteral, filter []GroundFilterEntry, project ProjectSpec) (*big.Int, *certErr) {
	matches := func(row GroundLiteral) bool {
		for _, e := range filter {
			if int(e.Pos) >= len(row.Args) || !row.Args[e.Pos].Equal(e.Value) {
				return false
			}
		}
		return true
	}
	switch project.Kind {
	case ProjectDistinct:
		seen := map[string]struct{}{}
		for _, row := range rows {
			if !matches(row) || int(project.Attr) >= len(row.Args) {
				continue
			}
			projected := row.Args[project.Attr]
			if isNullValue(projected) {
				continue // count_distinct EXCLUDES null() (ADR 0023 Phase 0).
			}
			seen[string(codec.Encode(projected))] = struct{}{}
		}
		return big.NewInt(int64(len(seen))), nil
	case ProjectSum, ProjectMin, ProjectMax:
		sum := big.NewInt(0)
		var extremum *big.Int // tracks min/max; nil until the first matching row
		var rowsSeen int
		for _, row := range rows {
			if !matches(row) || int(project.Attr) >= len(row.Args) {
				continue
			}
			// v1 sum/min/max are integer-only: a non-int column value (including null()) is
			// count_attr_out_of_range, as rs's fold, which does not special-case null.
			v, err := data.ReadInt(row.Args[project.Attr])
			if err != nil {
				return nil, &certErr{CountAttrOutOfRange, fmt.Sprintf("aggregate column %d is not a sealed numeric (int) value — v1 sum/min/max are integer-only", project.Attr)}
			}
			rowsSeen++
			switch project.Kind {
			case ProjectRows, ProjectDistinct:
				panic(fmt.Sprintf("contract: evaluateAggregate: %d reached the sum/min/max fold", int(project.Kind)))
			case ProjectSum:
				sum.Add(sum, v)
			case ProjectMin:
				if extremum == nil || v.Cmp(extremum) < 0 {
					extremum = v
				}
			case ProjectMax:
				if extremum == nil || v.Cmp(extremum) > 0 {
					extremum = v
				}
			}
		}
		if project.Kind == ProjectSum {
			return sum, nil // empty sum ⇒ 0
		}
		if rowsSeen == 0 {
			return nil, &certErr{AggEmptyUndefined, "min/max of an empty set is undefined"}
		}
		return extremum, nil
	case ProjectRows:
		var n int64
		for _, row := range rows {
			if matches(row) {
				n++
			}
		}
		return big.NewInt(n), nil
	default:
		// The kind is the program's (#3074: internal, so an unknown one panics by name).
		panic(fmt.Sprintf("contract: evaluateAggregate: unknown ProjectKind %d", int(project.Kind)))
	}
}
