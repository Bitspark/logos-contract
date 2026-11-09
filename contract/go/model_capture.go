package contract

import (
	"fmt"
	"math"
)

// NativeModelError identifies data outside the closed native account algebra.
type NativeModelError struct{ Detail string }

func (e *NativeModelError) Error() string { return e.Detail }

// CaptureGroundLiteral detaches a persistent fact. Only immutable native Ontos
// values can be shared. A dataset has no checker profile or term-depth policy.
func CaptureGroundLiteral(lit GroundLiteral) (GroundLiteral, error) {
	if why := wellFormedLiteral(lit, math.MaxInt, "fact"); why != "" {
		return GroundLiteral{}, &NativeModelError{why}
	}
	return lit.detached(), nil
}

func goalShape(g Goal) error {
	for i, arg := range g.Args {
		if why := wellFormedTerm(arg, math.MaxInt, fmt.Sprintf("goal argument %d", i)); why != "" {
			return &NativeModelError{why}
		}
	}
	return nil
}

// CaptureClause reads the native head and the active payload of each body
// literal. It retains no editable term or unused host representation field.
func CaptureClause(c Clause) (Clause, error) {
	if err := goalShape(c.Head); err != nil {
		return Clause{}, err
	}
	owned := CloneClause(c)
	for i, lit := range owned.Body {
		switch lit.Polarity {
		case Pos, Neg:
			if err := goalShape(lit.Lit); err != nil {
				return Clause{}, err
			}
			owned.Body[i].CountVal = CountLit{}
		case Count:
			count := lit.CountVal
			for _, entry := range count.Filter {
				if why := wellFormedTerm(entry.Term, math.MaxInt, "count filter"); why != "" {
					return Clause{}, &NativeModelError{why}
				}
			}
			if why := wellFormedTerm(count.Count, math.MaxInt, "count result"); why != "" {
				return Clause{}, &NativeModelError{why}
			}
			owned.Body[i].Lit = Goal{}
		default:
			return Clause{}, &NativeModelError{fmt.Sprintf("unknown polarity at body literal %d", i)}
		}
	}
	return owned, nil
}
