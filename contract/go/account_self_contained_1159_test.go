package contract

import "testing"

// Derivation.IsSelfContained — §8.2's first portability arm (#1159, P4).
//
// The account-side mirror of the kernel seam's CheckContext.IsTrivial. BOTH directions are
// pinned, because a predicate that is constant passes a one-armed test: an all-positive
// account is self-contained, one carrying a ClosedModelCert is not, and the two must DIFFER.

// anyCert is a structurally minimal cert. Never verified here — IsSelfContained reads only
// ClosedWorld's length, so the cert's CONTENTS are deliberately irrelevant, and a valid one
// would be testing something this predicate does not do.
func anyCert() ClosedModelCert { return ClosedModelCert{} }

func selfContainedNode() Node {
	return BuiltinNode{Conc: NewGroundLiteral("p")}
}

func TestAllPositiveAccountIsSelfContained(t *testing.T) {
	d := NewDerivation([]Node{selfContainedNode()}, 0)
	if !d.IsSelfContained() {
		t.Fatal("an all-positive account cites no closure, so it needs no context — §8.2's first arm")
	}
}

func TestCertifyingAccountIsNotSelfContained(t *testing.T) {
	d := NewDerivationWithClosedWorld([]Node{selfContainedNode()}, 0, []ClosedModelCert{anyCert()})
	if d.IsSelfContained() {
		t.Fatal("an account carrying a ClosedModelCert is a CERTIFYING check: it needs a bound cert context")
	}
}

// The vacuity guard. Each test above passes on a predicate hard-coded to its own answer;
// only the DIFFERENCE shows the predicate reads anything at all.
func TestSelfContainedPredicateIsNotConstant(t *testing.T) {
	positive := NewDerivation([]Node{selfContainedNode()}, 0)
	certifying := NewDerivationWithClosedWorld([]Node{selfContainedNode()}, 0, []ClosedModelCert{anyCert()})
	if positive.IsSelfContained() == certifying.IsSelfContained() {
		t.Fatal("the two arms must DIFFER — a constant predicate satisfies both one-armed tests")
	}
}

// The one thing the doc promises beyond the body: it tracks ClosedWorld and nothing else,
// so node count and shape must not move it.
func TestSelfContainmentTracksClosedWorldOnly(t *testing.T) {
	one := NewDerivation([]Node{selfContainedNode()}, 0)
	many := NewDerivation([]Node{selfContainedNode(), selfContainedNode(), selfContainedNode()}, 0)
	if !one.IsSelfContained() || !many.IsSelfContained() {
		t.Fatal("node count must not affect self-containment")
	}
	certifyingMany := NewDerivationWithClosedWorld(
		[]Node{selfContainedNode(), selfContainedNode(), selfContainedNode()},
		0,
		[]ClosedModelCert{anyCert()},
	)
	if certifyingMany.IsSelfContained() {
		t.Fatal("a non-empty ClosedWorld must flip it regardless of node count")
	}
}
