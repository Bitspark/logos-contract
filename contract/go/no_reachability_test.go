// §4 core obligation 6 — **no reachability requirement** (frozen; downstream-load-bearing).
//
// Go twin of contract/rs/tests/no_reachability.rs (issue #710): Check verifies
// obligations 1–5 — each node locally valid, the root concluding the claim — and
// nothing about node connectivity beyond the per-Rule premise edges. A locally-valid
// node the root does not transitively cite is neither rejected nor required. This
// *absence* is consumed as law by a downstream verifier (thesmos CD-015,
// "reach-as-non-op / enforcement-by-absence"), so it is pinned here as a CI guard:
// **adding** a reachability check to Check fails this suite, not the consumer's
// shipped law. Named frozen in docs/spec/logos-contract.md §4 (PR #705, the
// load-bearing register / consumer change gate).
//
// Two halves, both load-bearing:
//  1. ACCEPT — an extra, locally-valid, root-UNREACHABLE node does not reject.
//  2. REJECT — an extra root-unreachable node is still LOCALLY verified (obligations
//     1–5 range over *every* node, cited or not): an invalid uncited node rejects.
//     "No reachability requirement" means unreachable ≠ exempt, not unreachable ≠ seen.
package contract

import (
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
)

// noReachTheory owns nothing — this suite needs no builtins.
// test-double: consumer(owns no predicate)
type noReachTheory struct{}

func (noReachTheory) Owns(_ Symbol) bool { return false }
func (noReachTheory) DecideGround(_ GroundLiteral) completion.TheoryGround {
	return completion.TheoryGroundDisowned()
}

// noReachLeaves declares `grant`/`audit` extensional and admits any leaf.
// test-double: consumer(admits grant and audit leaves)
type noReachLeaves struct {
	ext *PredicateSet
}

func (l noReachLeaves) Extensional() *PredicateSet { return l.ext }
func (l noReachLeaves) Verify(_ GroundLiteral, _ Evidence, _ struct{}) LeafOutcome {
	return LeafAdmit{}
}

func noReachProfile() *CheckProfile[struct{}] {
	return &CheckProfile[struct{}]{
		Theory: noReachTheory{},
		Leaves: noReachLeaves{ext: PredicateSetOf("grant", "audit")},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
}

const clausePermit = "permit_rule"

// noReachProgram is `permit(S) :- grant(S).` — `grant`/`audit` are extensional (leaves).
func noReachProgram() *MapProgram {
	return NewMapProgram().With(NewClauseId(clausePermit), NewClause(
		NewGoal("permit", Var("S")),
		NewGoal("grant", Var("S")),
	))
}

func noReachAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

// noReachDerivation builds nodes [0] leaf grant(s1) ← cited, [1] rule permit(s1) = root.
// `extra` (if non-nil) is appended as node [2]: present in the DAG, **cited by nothing,
// unreachable from root**.
func noReachDerivation(extra Node) Derivation {
	nodes := []Node{
		LeafNode{
			Conc:     NewGroundLiteral("grant", noReachAtom("s1")),
			Evidence: NoEvidence(),
		},
		RuleNode{
			Conc:     NewGroundLiteral("permit", noReachAtom("s1")),
			Clause:   NewClauseId(clausePermit),
			Subst:    Subst{NewVarId("S"): Atom([]byte("s1"))},
			Premises: PosPremises(0),
			Meta:     NoMeta(),
		},
	}
	if extra != nil {
		nodes = append(nodes, extra)
	}
	return NewDerivation(nodes, 1)
}

// TestNoReachability_AcceptBaseline: the two-node derivation (no extra node) accepts.
func TestNoReachability_AcceptBaseline(t *testing.T) {
	out := Check[struct{}](
		noReachProgram(),
		NewGroundLiteral("permit", noReachAtom("s1")),
		noReachDerivation(nil),
		struct{}{},
		noReachProfile(),
	)
	if !out.IsAccept() {
		t.Fatalf("baseline must accept, got %v", out)
	}
}

// TestNoReachability_AcceptLocallyValidRootUnreachableNode — THE FROZEN ABSENCE
// (obligation 6): a locally-valid extensional leaf the root never cites — node [2]
// audit(x9), reachable from nothing — must NOT cause rejection. A future reachability
// requirement in Check turns this test red before it turns thesmos CD-015 wrong.
func TestNoReachability_AcceptLocallyValidRootUnreachableNode(t *testing.T) {
	extra := LeafNode{
		Conc:     NewGroundLiteral("audit", noReachAtom("x9")),
		Evidence: NoEvidence(),
	}
	out := Check[struct{}](
		noReachProgram(),
		NewGroundLiteral("permit", noReachAtom("s1")),
		noReachDerivation(extra),
		struct{}{},
		noReachProfile(),
	)
	if !out.IsAccept() {
		t.Fatalf(
			"a locally-valid, root-unreachable node must be neither rejected nor required "+
				"(§4 obligation 6, frozen; thesmos CD-015 rests on this) — got %v", out,
		)
	}
}

// TestNoReachability_RejectLocallyInvalidRootUnreachableNode — the other half:
// unreachable does NOT mean exempt. Obligations 1–5 range over every node — an
// *invalid* uncited node (a Leaf concluding the intensional `permit`, the §4.2 sealing
// violation) still rejects, even though the root never cites it.
func TestNoReachability_RejectLocallyInvalidRootUnreachableNode(t *testing.T) {
	extra := LeafNode{
		Conc:     NewGroundLiteral("permit", noReachAtom("x9")), // intensional head as a leaf → sealed_violation
		Evidence: NoEvidence(),
	}
	out := Check[struct{}](
		noReachProgram(),
		NewGroundLiteral("permit", noReachAtom("s1")),
		noReachDerivation(extra),
		struct{}{},
		noReachProfile(),
	)
	if out.IsAccept() {
		t.Fatal("an invalid (sealing-violating) uncited node must still reject")
	}
	if out.Verdict.Code() != SealedViolation {
		t.Fatalf("an invalid uncited node must reject with its own local error (sealed_violation), got %s", out.Verdict.Code().Code())
	}
}
