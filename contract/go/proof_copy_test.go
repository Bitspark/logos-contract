package contract_test

import (
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	core "github.com/bitspark/ontos/core/go"
)

func TestCloneDerivationOwnsNativeContainers(t *testing.T) {
	x := contract.NewVarId("X")
	id := contract.NewClauseId(string([]byte{0xff}))
	atom := core.NewAtom([]byte("a"))
	fact := contract.NewGroundLiteral("p", atom)
	proof := contract.Derivation{
		Nodes: []contract.Node{contract.RuleNode{
			Conc: fact, Clause: id, Subst: contract.Subst{x: contract.Atom([]byte("a"))},
		}},
		ClosedWorld: []contract.ClosedModelCert{{
			Supports: contract.SupportWitness{Edges: []contract.SupportEdge{{
				Clause: id, BodyRefs: []contract.SupportRef{contract.LowerStratumRef{Atom: fact}},
			}}},
		}},
	}
	copy := contract.CloneDerivation(proof)
	delete(proof.Nodes[0].(contract.RuleNode).Subst, x)
	proof.ClosedWorld[0].Supports.Edges[0].BodyRefs[0].(contract.LowerStratumRef).Atom.Args[0] = core.NewAtom(nil)
	node := copy.Nodes[0].(contract.RuleNode)
	if node.Clause != id || len(node.Subst) != 1 || node.Premises != nil {
		t.Fatal("copy lost a native handle, binding or nil premise list")
	}
	edge := copy.ClosedWorld[0].Supports.Edges[0]
	if edge.Clause != id || !core.Equal(edge.BodyRefs[0].(contract.LowerStratumRef).Atom.Args[0], atom) {
		t.Fatal("copy lost the support handle or retained the caller's support arguments")
	}
	node.Conc.Args[0] = core.NewAtom([]byte("copied"))
	if core.Equal(node.Conc.Args[0], proof.Nodes[0].(contract.RuleNode).Conc.Args[0]) {
		t.Fatal("writing through the copy changed the original")
	}
	if zero := contract.CloneDerivation(contract.Derivation{}); zero.Nodes != nil || zero.ClosedWorld != nil {
		t.Fatal("copy changed the native zero-value representation")
	}
}

// Embedding an interface can produce a foreign Node in Go. Copying native model
// data must not traverse its private domain or convert it to the embedded node.
type foreignCopyNode struct {
	contract.Node
	link *foreignCopyNode
}

func TestCloneDerivationPreservesAnUnrecognizedNodeAsUntrusted(t *testing.T) {
	foreign := &foreignCopyNode{Node: contract.LeafNode{}}
	foreign.link = foreign
	copy := contract.CloneDerivation(contract.NewDerivation([]contract.Node{foreign}, 0))
	if copy.Nodes[0] != foreign {
		t.Fatal("copying a foreign node changed its identity or interpreted its private payload")
	}
}
