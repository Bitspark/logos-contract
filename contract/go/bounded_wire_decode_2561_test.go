// #2561 (seat:caa's ruling): DecodeDerivationWireV1Bounded holds a derivation wire's certificates to
// the caller's CheckLimits BEFORE decoding. The wires are the real producer derivations of
// vectors/cert_encoded_bytes.json (#2524), which rs and ts decode in their twins.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"

	codec "github.com/bitspark/ontos/codec/go"
)

func boundedWire(t *testing.T, name string) []byte {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	var raw []byte
	for {
		if b, err := os.ReadFile(filepath.Join(dir, "vectors", "cert_encoded_bytes.json")); err == nil {
			raw = b
			break
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("could not locate vectors/cert_encoded_bytes.json")
		}
		dir = parent
	}
	var v struct {
		Cases []struct {
			Name           string `json:"name"`
			DerivationWire string `json:"derivation_wire"`
		} `json:"cases"`
	}
	if err := json.Unmarshal(raw, &v); err != nil {
		t.Fatal(err)
	}
	for _, c := range v.Cases {
		if c.Name == name {
			b, err := hex.DecodeString(c.DerivationWire)
			if err != nil {
				t.Fatal(err)
			}
			return b
		}
	}
	t.Fatalf("no case %q", name)
	return nil
}

func limitsAt(maxCertBytes int) CheckLimits {
	l := DefaultLimits()
	l.MaxCertBytes = maxCertBytes
	return l
}

func boundedKind(err error) string {
	var be *BoundedWireError
	if errors.As(err, &be) {
		return be.Kind
	}
	return ""
}

func TestACertificateOverTheCallersBudgetIsRefusedBeforeDecoding2561(t *testing.T) {
	for _, name := range []string{"permit_one_certificate", "stacked_two_certificates"} {
		b := boundedWire(t, name)
		spans, err := CertWireSpans(b, DerivationWireV1CertPath)
		if err != nil || len(spans) == 0 {
			t.Fatalf("%s: the wire carries certificates: %v %v", name, spans, err)
		}
		largest := 0
		for _, s := range spans {
			largest = max(largest, s)
		}
		at := largest - int(CertBytesSlack())
		d, err := DecodeDerivationWireV1Bounded(b, limitsAt(at))
		if err != nil || len(d.ClosedWorld) != len(spans) {
			t.Fatalf("%s: CONTROL: read at max + slack, got %v", name, err)
		}
		_, err = DecodeDerivationWireV1Bounded(b, limitsAt(at-1))
		var be *BoundedWireError
		if !errors.As(err, &be) || be.Kind != BoundedWireOverBudget || be.Span != largest {
			t.Fatalf("%s: one byte past max + slack is refused undecoded, got %v", name, err)
		}
	}
}

func TestBytesTheWalkCannotReadAreRefusedAndAPositiveWireNeedsNoBudget2561(t *testing.T) {
	b := boundedWire(t, "permit_one_certificate")
	if _, err := DecodeDerivationWireV1Bounded(b[:len(b)/2], DefaultLimits()); boundedKind(err) != BoundedWireUnreadable {
		t.Fatalf("a truncated wire is unreadable, got %v", err)
	}
	trailing := append(append([]byte{}, b...), 0x00)
	_, err := DecodeDerivationWireV1Bounded(trailing, DefaultLimits())
	var we *CertWireError
	if boundedKind(err) != BoundedWireUnreadable || !errors.As(err, &we) || we.Name != "trailing_bytes" {
		t.Fatalf("trailing bytes are unreadable, got %v", err)
	}
	notAWire := []byte{0x01, 0x02, 0x00, 0x01, 'x', 0x01, 0x00}
	if _, err := DecodeDerivationWireV1Bounded(notAWire, DefaultLimits()); boundedKind(err) != BoundedWireDecode {
		t.Fatalf("a readable value that is not a wire is the decoder's refusal, got %v", err)
	}
	// A codec capacity stop is the codec's own error, never the shape refusal (#2734 3c).
	nested := make([]byte, 0, 4002)
	for range 2000 {
		nested = append(nested, 0x01, 0x01)
	}
	nested = append(nested, 0x00, 0x00)
	_, err = DecodeDerivationWireV1Bounded(nested, DefaultLimits())
	var de *codec.DecodeError
	if boundedKind(err) != BoundedWireStopped || !errors.As(err, &de) || de.Code != "limit_exceeded" {
		t.Fatalf("a value past the codec's decode depth stops the codec, got %v", err)
	}
	if _, err := DecodeDerivationWireV1Bounded(b, limitsAt(0)); err == nil || !strings.HasPrefix(err.Error(), "cert_wire_over_budget") {
		t.Fatalf("the refusal names are the hosts', got %v", err)
	}
}
