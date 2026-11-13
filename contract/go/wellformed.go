package contract

// The boundary pass of #3088 (seat:caa's ruling). The derivation is untrusted, and in Go an interface
// value can be nil, or a type the checker does not know that satisfies the interface by embedding
// it. Such a value used to reach a method call (node.Conclusion() in the depth pass, the byte
// measurement's encoder, an Equal) before any switch could refuse it, and the trusted verifier
// panicked. This pass reads every interface value the checker itself reads, in the derivation's
// nodes and certificates, before any node or certificate is inspected, and refuses the first one of unknown or
// absent kind as unknown_node_kind, naming the component. Every later pass then reads a derivation
// whose every value is one of the known kinds.
//
// It is iterative (an explicit stack) and descends no deeper than limits.MaxTermDepth: a value
// nested deeper is refused term_too_deep by the depth pass, whose own walk stops at the same level
// without reading what lies below it.

import (
	"fmt"

	core "github.com/bitspark/ontos/core/go"
)

// checkWellFormed refuses the first derivation component of unknown or absent kind.
func checkWellFormed(deriv Derivation, limits CheckLimits) Verdict {
	max := limits.MaxTermDepth
	for i, node := range deriv.Nodes {
		if d := wellFormedNode(node, max); d != "" {
			return reject(UnknownNodeKind, fmt.Sprintf("node %d: %s", i, d))
		}
	}
	for i, cert := range deriv.ClosedWorld {
		if d := wellFormedCert(cert, max); d != "" {
			return reject(UnknownNodeKind, fmt.Sprintf("certificate %d: %s", i, d))
		}
	}
	return Accept()
}

// unknownKind describes a component that is none of its interface's known kinds.
func unknownKind(what string, v any) string {
	if v == nil {
		return what + " is absent (nil)"
	}
	return fmt.Sprintf("%s is of unknown kind %T", what, v)
}

func wellFormedNode(node Node, max int) string {
	switch n := node.(type) {
	case RuleNode:
		if d := wellFormedLiteral(n.Conc, max, "conclusion"); d != "" {
			return d
		}
		for v, term := range n.Subst {
			if d := wellFormedTerm(term, max, "subst image of "+v.String()); d != "" {
				return d
			}
		}
		for k, p := range n.Premises {
			if d := wellFormedPremise(p, max, fmt.Sprintf("premise %d", k)); d != "" {
				return d
			}
		}
		// Meta is opaque to the core (only a consumer's RuleAdmissibility reads it), so it is not
		// this pass's to refuse: the checker never calls a method on it.
		return ""
	case LeafNode:
		// Evidence is opaque to the core too (only a LeafVerifier reads it).
		return wellFormedLiteral(n.Conc, max, "conclusion")
	case BuiltinNode:
		return wellFormedLiteral(n.Conc, max, "conclusion")
	default:
		return unknownKind("the node", node)
	}
}

func wellFormedPremise(p Premise, max int, what string) string {
	switch pr := p.(type) {
	case PosPremise:
		return ""
	case NegPremise:
		return wellFormedLiteral(pr.Atom, max, what+" atom")
	case CountPremise:
		for i, e := range pr.Filter {
			if d := wellFormedValue(e.Value, max, fmt.Sprintf("%s filter %d", what, i)); d != "" {
				return d
			}
		}
		return wellFormedValue(pr.K, max, what+" k")
	default:
		return unknownKind(what, p)
	}
}

func wellFormedCert(cert ClosedModelCert, max int) string {
	for i, dom := range cert.Domains {
		for j, v := range dom.Values {
			if d := wellFormedValue(v, max, fmt.Sprintf("domain %d value %d", i, j)); d != "" {
				return d
			}
		}
	}
	for i, table := range cert.Extensions {
		for j, row := range table.Rows {
			if d := wellFormedLiteral(row, max, fmt.Sprintf("extension %d row %d", i, j)); d != "" {
				return d
			}
		}
	}
	for i, edge := range cert.Supports.Edges {
		where := fmt.Sprintf("support edge %d", i)
		if d := wellFormedLiteral(edge.Fact, max, where+" fact"); d != "" {
			return d
		}
		for v, term := range edge.Subst {
			if d := wellFormedTerm(term, max, where+" subst image of "+v.String()); d != "" {
				return d
			}
		}
		for k, ref := range edge.BodyRefs {
			if d := wellFormedSupportRef(ref, max, fmt.Sprintf("%s ref %d", where, k)); d != "" {
				return d
			}
		}
	}
	return ""
}

func wellFormedSupportRef(ref SupportRef, max int, what string) string {
	switch r := ref.(type) {
	case SameStratumRef:
		return wellFormedLiteral(r.Fact, max, what+" fact")
	case LowerStratumRef:
		return wellFormedLiteral(r.Atom, max, what+" atom")
	case BuiltinRef:
		return wellFormedLiteral(r.Atom, max, what+" atom")
	case NegLowerRef:
		return wellFormedLiteral(r.Atom, max, what+" atom")
	case CountLowerRef:
		return ""
	default:
		return unknownKind(what, ref)
	}
}

func wellFormedLiteral(lit GroundLiteral, max int, what string) string {
	for i, v := range lit.Args {
		if d := wellFormedValue(v, max, fmt.Sprintf("%s argument %d", what, i)); d != "" {
			return d
		}
	}
	return ""
}

// wellFormedValue walks an ontos value, whose known kinds are core.Atom and core.Tuple.
func wellFormedValue(value core.Value, max int, what string) string {
	type item struct {
		value core.Value
		level int
	}
	work := []item{{value: value, level: 1}}
	for len(work) > 0 {
		it := work[len(work)-1]
		work = work[:len(work)-1]
		if it.level > max {
			continue // too deep: the depth pass refuses it without reading it
		}
		switch v := it.value.(type) {
		case core.Atom:
		case core.Tuple:
			for _, c := range v.Items() {
				work = append(work, item{value: c, level: it.level + 1})
			}
		default:
			return unknownKind(what+" (a value)", it.value)
		}
	}
	return ""
}

// wellFormedTerm walks a term, whose known kinds are VarTerm, AtomTerm and TupleTerm.
func wellFormedTerm(term Term, max int, what string) string {
	type item struct {
		term  Term
		level int
	}
	work := []item{{term: term, level: 1}}
	for len(work) > 0 {
		it := work[len(work)-1]
		work = work[:len(work)-1]
		if it.level > max {
			continue // too deep: the depth pass refuses it without reading it
		}
		switch t := it.term.(type) {
		case VarTerm, AtomTerm:
		case TupleTerm:
			for _, c := range t.Children() {
				work = append(work, item{term: c, level: it.level + 1})
			}
		default:
			return unknownKind(what+" (a term)", it.term)
		}
	}
	return ""
}
