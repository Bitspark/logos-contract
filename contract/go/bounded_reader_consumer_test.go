package contract_test

import (
	"errors"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

func boundedTestFrame(count int) []byte {
	leaf := contract.LeafNode{Conc: contract.NewGroundLiteral("fact")}
	certs := make([]contract.ClosedModelCert, count)
	return mustWire(contract.EncodeDerivationWireV1(contract.NewDerivationWithClosedWorld([]contract.Node{leaf}, 0, certs)))
}

func TestBoundedReaderOwnsItsV1Path(t *testing.T) {
	frame := boundedTestFrame(2)
	path := contract.DerivationWireV1CertPath()
	spans, err := contract.CertWireSpans(frame, path)
	if err != nil || len(spans) != 2 {
		t.Fatalf("two certificate spans: %v, %v", spans, err)
	}
	policy := contract.DefaultLimits()
	policy.MaxCertBytes = max(spans[0], spans[1]) - int(contract.CertBytesSlack())
	if d, err := contract.DecodeDerivationWireV1Bounded(frame, policy); err != nil || len(d.ClosedWorld) != 2 {
		t.Fatalf("at the encoded span boundary: %v", err)
	}
	policy.MaxCertBytes--
	requireLimit := func() {
		t.Helper()
		_, err := contract.DecodeDerivationWireV1Bounded(frame, policy)
		var failure *contract.BoundedWireError
		if !errors.As(err, &failure) || failure.Kind != contract.BoundedWireOverBudget || failure.MaxCertBytes != policy.MaxCertBytes {
			t.Fatalf("the oversized certificate was not refused under %d: %v", policy.MaxCertBytes, err)
		}
	}
	requireLimit()
	original := path[1]
	path[1] = 99
	t.Cleanup(func() { path[1] = original })
	if spans, err := contract.CertWireSpans(frame, path); err != nil || len(spans) != 0 {
		t.Fatalf("the independently chosen absent path: %v, %v", spans, err)
	}
	requireLimit()
	policy.MaxCertBytes = 0
	requireLimit()
	if d, err := contract.DecodeDerivationWireV1Bounded(boundedTestFrame(0), policy); err != nil || len(d.ClosedWorld) != 0 {
		t.Fatalf("positive proof under a zero certificate budget: %v", err)
	}
}

func TestBoundedReaderRejectsInvalidConfigurationBeforeFrameInput(t *testing.T) {
	policy := contract.DefaultLimits()
	for _, budget := range policy.Budgets() {
		t.Run(budget.Name, func(t *testing.T) {
			original := *budget.Value
			*budget.Value = -1
			t.Cleanup(func() { *budget.Value = original })
			for _, frame := range [][]byte{nil, boundedTestFrame(1)} {
				_, err := contract.DecodeDerivationWireV1Bounded(frame, policy)
				var refusal *contract.BoundedWireError
				var invalid *contract.CheckLimitError
				if !errors.As(err, &refusal) || refusal.Kind != contract.BoundedWireInvalidLimits ||
					!errors.As(err, &invalid) || invalid.Field != budget.Name {
					t.Fatalf("invalid %s misclassified: %v", budget.Name, err)
				}
			}
		})
	}
}

func TestWireFailureNameIsIndependentOfAnEarlierError(t *testing.T) {
	var first contract.CertWireError
	if err := contract.CertWireWalk(nil); !errors.As(err, &first) || first.Name() != "truncated" {
		t.Fatalf("unexpected truncated wire: %v", err)
	}
	first = contract.CertWireError("another caller")
	_, err := contract.DecodeDerivationWireV1Bounded(nil, contract.DefaultLimits())
	var next contract.CertWireError
	if !errors.As(err, &next) || next.Name() != "truncated" || next == first {
		t.Fatalf("a different reader lost the truncated classification: %v", err)
	}
}

func TestPortableCertificateSpanBoundaries(t *testing.T) {
	for _, maxBytes := range []uint64{1<<32 - 1, 1 << 32, 1<<53 - 1} {
		cap, err := contract.NewProofBudgetCount("max_cert_bytes", maxBytes)
		if err != nil {
			t.Fatal(err)
		}
		at := cap.Uint64() + contract.CertBytesSlack()
		if contract.CertSpanOverBudget(at, cap) || !contract.CertSpanOverBudget(at+1, cap) {
			t.Fatalf("certificate span boundary moved at %d", maxBytes)
		}
	}
}

// These fixtures contain portable evidence. An encoding error fails the test at its call site.
func mustWire[T any](value T, err error) T {
	if err != nil {
		panic(err)
	}
	return value
}
