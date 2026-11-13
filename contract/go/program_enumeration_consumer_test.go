package contract_test

import (
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

// test-double: consumer(lookup over the application's own clause store)
type lookupOnlyProgram func(contract.ClauseId) (contract.Clause, bool)

func (p lookupOnlyProgram) Clause(id contract.ClauseId) (contract.Clause, bool) { return p(id) }

// test-double: consumer(complete inventory in stable clause-handle order)
type completeClauses []contract.ClauseEntry

func (p completeClauses) Clause(id contract.ClauseId) (contract.Clause, bool) {
	for _, entry := range p {
		if entry.ID == id {
			return entry.Clause, true
		}
	}
	return contract.Clause{}, false
}

func (p completeClauses) ForEachClause(visit func(contract.ClauseId, contract.Clause)) {
	for _, entry := range p {
		visit(entry.ID, entry.Clause)
	}
}

var _ contract.Program = lookupOnlyProgram(nil)
var _ contract.CompleteProgram = completeClauses(nil)

func TestLookupOnlyProgramChecksACitedPositiveRule(t *testing.T) {
	id := contract.NewClauseId("published")
	p := completeClauses{{ID: id, Clause: contract.Fact(contract.NewGoal("published"))}}
	claim := contract.NewGroundLiteral("published")
	proof := contract.NewDerivation([]contract.Node{contract.RuleNode{Conc: claim, Clause: id}}, 0)
	got := contract.Check(lookupOnlyProgram(p.Clause), claim, proof, struct{}{}, bindingContext().profile)
	if !got.IsAccept() {
		t.Fatalf("positive rule lookup: %s %s", got.Verdict.Code().Code(), got.Verdict.Detail())
	}
}

func TestClosureRequiresTheCompleteTrustedClauseSet(t *testing.T) {
	empty := completeClauses{}
	withFact := completeClauses{{
		ID:     contract.NewClauseId("independent-definition"),
		Clause: contract.Fact(contract.NewGoal("sealed", contract.Atom([]byte("a")))),
	}}
	outside := completeClauses{{
		ID:     contract.NewClauseId("outside-scope"),
		Clause: contract.NewClause(contract.NewGoal("sealed", contract.Atom([]byte("a"))), contract.NewGoal("outside")),
	}}
	emptyHash := contract.ProgramDigestOf(empty)
	if emptyHash != contract.ProgramDigest(nil) {
		t.Fatal("an explicitly complete empty inventory must name the canonical empty program")
	}
	for _, tc := range []struct {
		name    string
		program contract.Program
		hash    contract.Hash
		accept  bool
		code    contract.RejectionCode
	}{
		{name: "lookup only", program: lookupOnlyProgram(empty.Clause), hash: emptyHash, code: contract.CertScopeIncomplete},
		{name: "complete empty", program: empty, hash: emptyHash, accept: true},
		{name: "dependency outside scope", program: outside, hash: contract.ProgramDigestOf(outside), code: contract.CertScopeIncomplete},
		{name: "changed complete program", program: withFact, hash: emptyHash, code: contract.CertContextMismatch},
		{name: "uncited defining clause", program: withFact, hash: contract.ProgramDigestOf(withFact), code: contract.CertNotClosed},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := bindingContext()
			cert := f.proof.ClosedWorld[0]
			cert.DecompositionWitness = nil
			cert.ProgramHash = tc.hash
			cx := contract.NewCertContext(tc.hash, f.context.ProfileHash, f.context.CtxHash, f.context.TheoryConfigHash)
			out := contract.CheckClosedModelChain(tc.program, []contract.ClosedModelCert{cert}, struct{}{}, f.profile, cx)
			if out.IsAccept() != tc.accept || (!tc.accept && out.Verdict.Code() != tc.code) {
				t.Fatalf("accept=%v, code=%s, detail=%s", out.IsAccept(), out.Verdict.Code().Code(), out.Verdict.Detail())
			}
		})
	}
}

// test-double: consumer(a complete store counts the traversals of its current read view)
type observedInventory struct {
	completeClauses
	visits int
}

func (p *observedInventory) ForEachClause(visit func(contract.ClauseId, contract.Clause)) {
	p.visits++
	p.completeClauses.ForEachClause(visit)
}

func TestWholeChainConsultsOneTrustedInventoryPerCall(t *testing.T) {
	p := &observedInventory{}
	f := bindingContext()
	cert := f.proof.ClosedWorld[0]
	cert.DecompositionWitness = nil
	cert.ProgramHash = contract.ProgramDigest(nil)
	cx := contract.NewCertContext(cert.ProgramHash, f.context.ProfileHash, f.context.CtxHash, f.context.TheoryConfigHash)
	for call := 1; call <= 2; call++ {
		out := contract.CheckClosedModelChain(p, []contract.ClosedModelCert{cert, cert}, struct{}{}, f.profile, cx)
		if !out.IsAccept() || p.visits != call {
			t.Fatalf("call %d: %v after %d inventory reads", call, out, p.visits)
		}
	}
}
