package contract

// G4, the completeness gate's set comparison, as one contract operation (design 0008 section 1.4.4;
// research 0028 row A16, seat:caa's ruling on #3023). Each kernel's gate calls it after G2 and G3,
// and vectors/exact_answer_set.json replays it in all three cores. rs answer_set.rs.
//
// The emitted answers must be exactly the sealed rows that are instances of the goal. A row is an
// instance when one binding of the goal's variables makes the goal structurally equal to it, where a
// repeated variable binds one value. Two answers are one answer exactly when they are structurally
// equal (GroundKey).
//
// The precedence is normative: the first emitted answer that is not a sealed instance, in claim
// order; otherwise the first sealed instance that was not emitted, in GroundKey order.

import (
	"fmt"
	"sort"

	core "github.com/bitspark/ontos/core/go"
)

// AnswerSetMismatchKind is how an answer set fails G4. Its zero value is no kind: a mismatch always
// names one of the two.
type AnswerSetMismatchKind int

const (
	// AnswerSetExtra is an emitted answer that is not a sealed row matching the goal: the first, in
	// claim order.
	AnswerSetExtra AnswerSetMismatchKind = iota + 1
	// AnswerSetMissing is a sealed row matching the goal that was not emitted: the first, in
	// GroundKey order.
	AnswerSetMissing
)

// AnswerSetMismatch is how an answer set fails G4, and the literal that shows it. These are exactly
// the two ways a set comparison fails (seat:caa's ruling on #3023): a third kind would be a contract
// v2 item.
type AnswerSetMismatch struct {
	Kind    AnswerSetMismatchKind
	Literal GroundLiteral
}

// CheckAnswerSet is G4: nil when claims is exactly the set of sealed rows that are instances of
// goal, and otherwise the first difference by the normative precedence.
func CheckAnswerSet(goal Goal, sealed, claims []GroundLiteral) *AnswerSetMismatch {
	instances := map[string]GroundLiteral{}
	for _, row := range sealed {
		if isInstance(goal, row) {
			instances[string(GroundKey(row))] = row
		}
	}
	emitted := map[string]bool{}
	for _, claim := range claims {
		key := string(GroundKey(claim))
		if _, ok := instances[key]; !ok {
			return &AnswerSetMismatch{Kind: AnswerSetExtra, Literal: claim}
		}
		emitted[key] = true
	}
	keys := make([]string, 0, len(instances))
	for k := range instances {
		keys = append(keys, k)
	}
	sort.Strings(keys) // byte order, as rs's BTreeMap orders the keys
	for _, k := range keys {
		if !emitted[k] {
			return &AnswerSetMismatch{Kind: AnswerSetMissing, Literal: instances[k]}
		}
	}
	return nil
}

// isInstance reports whether row is an instance of goal: the same predicate and arity, and one
// binding of the goal's variables under which every argument matches. The walk is an explicit
// stack of pairs, never one native frame per nesting level (#3036).
func isInstance(goal Goal, row GroundLiteral) bool {
	if !goal.Pred.Equal(row.Pred) || len(goal.Args) != len(row.Args) {
		return false
	}
	type pair struct {
		term  Term
		value core.Value
	}
	work := make([]pair, 0, len(goal.Args))
	for i := len(goal.Args) - 1; i >= 0; i-- {
		work = append(work, pair{goal.Args[i], row.Args[i]})
	}
	bound := map[string]core.Value{}
	for len(work) > 0 {
		p := work[len(work)-1]
		work = work[:len(work)-1]
		switch t := p.term.(type) {
		case VarTerm:
			name := t.ID().String()
			if prior, ok := bound[name]; ok {
				if !prior.Equal(p.value) {
					return false
				}
				continue
			}
			bound[name] = p.value
		case AtomTerm:
			ground, _ := t.EraseGround()
			if !ground.Equal(p.value) {
				return false
			}
		case TupleTerm:
			tuple, ok := p.value.(core.Tuple)
			if !ok {
				return false
			}
			children, items := t.Children(), tuple.Items()
			if len(children) != len(items) {
				return false
			}
			for i := len(children) - 1; i >= 0; i-- {
				work = append(work, pair{children[i], items[i]})
			}
		default:
			// The goal is the caller's query, never untrusted input (#3074): an unknown kind is a
			// defect, and it panics by name.
			panic(fmt.Sprintf("contract: CheckAnswerSet: %T is none of the known term kinds", p.term))
		}
	}
	return true
}
