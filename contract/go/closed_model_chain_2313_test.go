// #2313 (design 0008 §1.4.3): CheckClosedModelChain verifies a closed-model certificate chain
// that no derivation cites, by the verification a Neg-cited cert already passes in
// CheckWithCertContext. Go twin of contract/rs/tests/closed_model_chain_2313.rs.
//
// The replay below reuses vectors/negation.json, the oracle all three cores already agree on. It
// makes two claims per case, and counts both so neither can pass vacuously:
//   - a case the oracle ACCEPTS verifies its closed_world as a chain;
//   - a case the oracle rejects with a code only verifyCert produces rejects the chain with the
//     SAME code.
//
// Other rejections (a node, a premise, a cert index a Neg premise names) are about the derivation,
// not the chain, and are skipped by name.
package contract

import (
	"strings"
	"testing"
)

// The codes only verifyCert can produce. A case rejected with one of these was rejected because
// a cited certificate is invalid.
var chainCertInternalCodes = map[string]bool{
	"cert_budget_exceeded":       true,
	"cert_size_exceeded":         true,
	"cert_decl_mismatch":         true,
	"cert_context_mismatch":      true,
	"cert_unsupported":           true,
	"cert_not_closed":            true,
	"cert_scope_incomplete":      true,
	"cert_edb_mismatch":          true,
	"cert_partial_scope_invalid": true,
}

type chainVectorCase struct {
	name    string
	want    string
	program Program
	certs   []ClosedModelCert
	profile *CheckProfile[unitCtx]
	cx      CertContext
}

// chainVectorCases builds each negation vector's program, closed_world, profile and context
// exactly as TestNegationVectors does.
func chainVectorCases(t *testing.T) []chainVectorCase {
	t.Helper()
	vf := loadNegVectors(t)
	program := NewMapProgram()
	for id, clause := range vf.Program {
		body := make([]BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build(t)
		}
		program.Insert(NewClauseId(id), NewClauseLits(clause.Head.buildGoal(t), body...))
	}
	extensional := NewPredicateSet()
	for _, p := range vf.Extensional {
		extensional.Insert(SymbolFromString(p))
	}
	edb := make(map[string][]GroundLiteral, len(vf.Edb))
	for pred, rows := range vf.Edb {
		grounds := make([]GroundLiteral, len(rows))
		for i, r := range rows {
			grounds[i] = r.buildGround(t)
		}
		edb[pred] = grounds
	}
	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))

	var out []chainVectorCase
	for _, c := range vf.Cases {
		if c.PlainCheck {
			continue // a plain check runs under the zero context by design; not a chain case
		}
		certs := make([]ClosedModelCert, len(c.Derivation.ClosedWorld))
		for i, cj := range c.Derivation.ClosedWorld {
			certs[i] = cj.build(t, derived)
		}
		limits := DefaultLimits()
		if c.Limits != nil {
			setLimitIf(&limits.MaxNodes, c.Limits.MaxNodes)
			setLimitIf(&limits.MaxDepth, c.Limits.MaxDepth)
			setLimitIf(&limits.MaxTermDepth, c.Limits.MaxTermDepth)
			setLimitIf(&limits.MaxCertBytes, c.Limits.MaxCertBytes)
			setLimitIf(&limits.MaxCertFacts, c.Limits.MaxCertFacts)
			setLimitIf(&limits.MaxDomainValues, c.Limits.MaxDomainValues)
			setLimitIf(&limits.MaxSupportEdges, c.Limits.MaxSupportEdges)
			setLimitIf(&limits.MaxRuleGroundings, c.Limits.MaxRuleGroundings)
			setLimitIf(&limits.MaxJoinSteps, c.Limits.MaxJoinSteps)
		}
		cx := derived
		if c.CertContext != nil {
			if c.CertContext.ProgramHash != nil {
				cx.ProgramHash = negHashFromHex(t, *c.CertContext.ProgramHash)
			}
			if c.CertContext.ProfileHash != nil {
				cx.ProfileHash = negHashFromHex(t, *c.CertContext.ProfileHash)
			}
			if c.CertContext.CtxHash != nil {
				cx.CtxHash = negHashFromHex(t, *c.CertContext.CtxHash)
			}
			if c.CertContext.TheoryConfigHash != nil {
				cx.TheoryConfigHash = negHashFromHex(t, *c.CertContext.TheoryConfigHash)
			}
			if c.CertContext.DecompositionWitness != nil {
				cx = cx.WithDecomposition(negHashFromHex(t, *c.CertContext.DecompositionWitness))
			}
		}
		out = append(out, chainVectorCase{
			name:    c.Name,
			want:    expectedOutcome(t, c.Outcome),
			program: program,
			certs:   certs,
			profile: &CheckProfile[unitCtx]{
				Theory: ltTheory{},
				Leaves: negVectorLeaves{extensional: extensional, edb: edb},
				Admit:  AlwaysAdmit[unitCtx]{},
				Limits: limits,
			},
			cx: cx,
		})
	}
	return out
}

func TestClosedModelChainReplaysTheNegationVectors2313(t *testing.T) {
	accepted, certRejected := 0, 0
	for _, c := range chainVectorCases(t) {
		if len(c.certs) == 0 {
			continue // an all-positive case cites no cert; there is no chain to verify
		}
		got := CheckClosedModelChain[unitCtx](c.program, c.certs, unitCtx{}, c.profile, c.cx)
		switch {
		case c.want == "accept":
			accepted++
			if !got.IsAccept() {
				t.Errorf("case %q: the oracle accepts it, so its closed_world must verify as a chain; got %s (%s)", c.name, got.Code().Code(), got.Detail())
			}
		case chainCertInternalCodes[strings.TrimPrefix(c.want, "reject:")]:
			certRejected++
			want := strings.TrimPrefix(c.want, "reject:")
			if got.IsAccept() || got.Code().Code() != want {
				t.Errorf("case %q: the oracle rejects a cited cert with %s, so the chain must too; got accept=%v %s", c.name, want, got.IsAccept(), got.Detail())
			}
		}
	}
	// ANTI-VACUITY: both halves must have run over real cases.
	if accepted == 0 || certRejected == 0 {
		t.Fatalf("the replay is vacuous: %d accepted and %d cert-rejected cases", accepted, certRejected)
	}
	t.Logf("chain replay: %d accepted, %d cert-rejected cases", accepted, certRejected)
}

func TestClosedModelChainEmptyIsRefusedByName2313(t *testing.T) {
	cases := chainVectorCases(t)
	c := cases[0]
	got := CheckClosedModelChain[unitCtx](c.program, nil, unitCtx{}, c.profile, c.cx)
	if got.IsAccept() || got.Code() != CertOutOfRange || !strings.Contains(got.Detail(), "empty certificate chain") {
		t.Fatalf("an empty chain must be refused cert_out_of_range, never accepted vacuously; got accept=%v %s", got.IsAccept(), got.Detail())
	}
}

func TestClosedModelChainUnboundContextIsRefused2313(t *testing.T) {
	for _, c := range chainVectorCases(t) {
		if c.want != "accept" || len(c.certs) == 0 {
			continue
		}
		got := CheckClosedModelChain[unitCtx](c.program, c.certs, unitCtx{}, c.profile, ZeroCertContext())
		if got.IsAccept() || got.Code() != CertContextUnbound {
			t.Fatalf("case %q under the zero context must be refused cert_context_unbound; got accept=%v %s", c.name, got.IsAccept(), got.Detail())
		}
		return
	}
	t.Fatal("no accepted case with a closed_world to test the unbound context against")
}
