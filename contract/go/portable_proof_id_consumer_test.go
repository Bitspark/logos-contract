package contract_test

import (
	"bytes"
	"errors"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
	core "github.com/bitspark/ontos/core/go"
)

type proofHandles struct {
	program *contract.MapProgram
	context contract.CertContext
	claim   contract.GroundLiteral
	rule    contract.Derivation
	support contract.Derivation
}

func evidenceForHandle(handle string) proofHandles {
	a := core.NewAtom([]byte("a"))
	claim := contract.NewGroundLiteral("proved", a)
	clause := contract.Fact(contract.NewGoal("proved", contract.Atom([]byte("a"))))
	id, alternate := contract.NewClauseId(handle), contract.NewClauseId("second-witness")
	program := contract.NewMapProgram().With(id, clause).With(alternate, clause)
	pin := contract.Hash{1}
	cx := contract.NewCertContext(contract.ProgramDigestOf(program), pin, pin, pin)
	cert := contract.ClosedModelCert{
		Scope:       contract.NewStratumPrefix(0, []contract.Symbol{claim.Pred}),
		ProgramHash: cx.ProgramHash, ProfileHash: cx.ProfileHash, CtxHash: cx.CtxHash, TheoryConfigHash: cx.TheoryConfigHash,
		Domains:    []contract.FiniteDomain{contract.NewFiniteDomain(contract.SymbolFromString("domain"), []core.Value{a})},
		Extensions: []contract.RelationTable{contract.NewRelationTable(claim.Pred, 1, []contract.GroundLiteral{claim})},
		Supports:   contract.SupportWitness{Edges: []contract.SupportEdge{{Fact: claim, Clause: id}}},
		LimitsDecl: contract.CertSizeDecl{CertFacts: 4, DomainValues: 4, SupportEdges: 4, RuleGroundings: 20, JoinSteps: 20, CertBytes: 8192},
	}
	cert.LimitsDecl.CertBytes = contract.CertEncodedBytes(cert)
	return proofHandles{
		program: program, context: cx, claim: claim,
		rule:    contract.NewDerivation([]contract.Node{contract.RuleNode{Conc: claim, Clause: id}}, 0),
		support: contract.NewDerivationWithClosedWorld([]contract.Node{contract.RuleNode{Conc: claim, Clause: alternate}}, 0, []contract.ClosedModelCert{cert}),
	}
}

func TestPortableProofHandlesRoundTrip(t *testing.T) {
	for _, handle := range []string{"", "A\ufffd", "A\U0001f600B", "\ufeffid"} {
		f := evidenceForHandle(handle)
		for _, proof := range []contract.Derivation{f.rule, f.support} {
			wire, err := contract.EncodeDerivationWireV1(proof)
			if err != nil {
				t.Fatal(err)
			}
			decoded, err := contract.DecodeDerivationWireV1(wire)
			if err != nil {
				t.Fatal(err)
			}
			actual := decoded.Nodes[0].(contract.RuleNode).Clause
			if len(decoded.ClosedWorld) > 0 {
				actual = decoded.ClosedWorld[0].Supports.Edges[0].Clause
			}
			if actual.String() != handle {
				t.Fatalf("clause ID %q decoded as %q", handle, actual.String())
			}
			again, err := contract.EncodeDerivationWireV1(decoded)
			if err != nil || !bytes.Equal(wire, again) {
				t.Fatalf("%q: proof bytes changed after a round trip: %v", handle, err)
			}
		}
	}
}

func TestNativeProofHandlesRefusePortableWriting(t *testing.T) {
	profile := &contract.CheckProfile[struct{}]{
		Theory: contract.NewStandardTheory(), Leaves: clauseIDLeaves{},
		Admit: contract.AlwaysAdmit[struct{}]{}, Limits: contract.DefaultLimits(),
	}
	for _, handle := range []string{"A\xff", "A\xed\xa0\x80"} {
		f := evidenceForHandle(handle)
		if out := contract.Check(f.program, f.claim, f.rule, struct{}{}, profile); !out.IsAccept() {
			t.Fatalf("native rule check: %v", out.Verdict.Detail())
		}
		if out := contract.CheckClosedModelChain(f.program, f.support.ClosedWorld, struct{}{}, profile, f.context); !out.IsAccept() {
			t.Fatalf("native support check: %v", out.Verdict.Detail())
		}
		under := f.support.ClosedWorld[0]
		under.LimitsDecl.CertBytes--
		short := contract.CheckClosedModelChain(f.program, []contract.ClosedModelCert{under}, struct{}{}, profile, f.context)
		if short.IsAccept() || short.Verdict.Code().Code() != "cert_decl_mismatch" {
			t.Fatalf("a native certificate declared one byte short: %v", short.Verdict.Detail())
		}
		memo := contract.NewWorldMemo(f.program, profile, struct{}{}, f.context)
		for range 2 {
			if out := contract.CheckWithWorldMemo(memo, f.claim, f.support); !out.IsAccept() {
				t.Fatalf("native memo check: %v", out.Verdict.Detail())
			}
		}
		cert := f.support.ClosedWorld[0]
		if memo.CertificatesVerified() != 1 || contract.CertEncodedBytes(cert) == 0 {
			t.Fatal("the native verifier must account for the certificate and reuse an equal world")
		}
		requireID := func(err error) {
			t.Helper()
			var e *contract.ClauseIdEncodingError
			if !errors.As(err, &e) || e.ClauseID.String() != handle {
				t.Fatalf("expected the original handle %q, got %v", handle, err)
			}
		}
		value, err := contract.ClosedModelCertAsValue(cert)
		requireID(err)
		if value != nil {
			t.Fatal("the refused certificate produced a value")
		}
		for _, proof := range []contract.Derivation{f.rule, f.support} {
			for _, project := range []func(contract.Derivation) (core.Value, error){
				contract.DerivationAsValue, contract.DerivationWirePayloadV1ToValue, contract.DerivationWireV1ToValue,
			} {
				value, err := project(proof)
				requireID(err)
				if value != nil {
					t.Fatal("the refused proof produced a value")
				}
			}
			wire, err := contract.EncodeDerivationWireV1(proof)
			requireID(err)
			if wire != nil {
				t.Fatal("the refused proof produced bytes")
			}
		}
	}
}
