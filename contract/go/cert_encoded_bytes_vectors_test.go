// Go replay of vectors/cert_encoded_bytes.json (#2524): a certificate's size in bytes is its
// canonical encoding with LimitsDecl.CertBytes zeroed. Every case decodes one derivation wire and
// measures its ClosedWorld certificates, which must equal the numbers the rs generator measured.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

type certEncodedBytesFile struct {
	Cases []struct {
		Name           string   `json:"name"`
		Produced       bool     `json:"produced"`
		CertBytes      []uint64 `json:"cert_bytes"`
		DerivationWire string   `json:"derivation_wire"`
	} `json:"cases"`
}

func loadCertEncodedBytes(t *testing.T) certEncodedBytesFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "cert_encoded_bytes.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read vector: %v", readErr)
			}
			var v certEncodedBytesFile
			if err := json.Unmarshal(raw, &v); err != nil {
				t.Fatalf("parse vector: %v", err)
			}
			return v
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatalf("could not locate vectors/cert_encoded_bytes.json")
		}
		dir = parent
	}
}

func TestCertEncodedBytesVectors2524(t *testing.T) {
	v := loadCertEncodedBytes(t)
	if len(v.Cases) != 7 {
		t.Fatalf("the vector's seven cases, got %d", len(v.Cases))
	}
	for _, c := range v.Cases {
		wire, err := hex.DecodeString(c.DerivationWire)
		if err != nil {
			t.Fatalf("%s: hex: %v", c.Name, err)
		}
		d, err := DecodeDerivationWireV1(wire)
		if err != nil {
			t.Fatalf("%s: decode: %v", c.Name, err)
		}
		// #2605: the value reading is byte-identical to the one the generator wrote.
		if rt := hex.EncodeToString(mustWire(EncodeDerivationWireV1(d))); rt != c.DerivationWire {
			t.Errorf("%s: the derivation wire does not re-encode byte-identically", c.Name)
		}
		if len(d.ClosedWorld) == 0 || len(d.ClosedWorld) != len(c.CertBytes) {
			t.Fatalf("%s: %d certificates for %d pinned measures", c.Name, len(d.ClosedWorld), len(c.CertBytes))
		}
		for i, cert := range d.ClosedWorld {
			got := CertEncodedBytes(cert)
			assertLengthReading2605(t, c.Name, cert)
			if got != c.CertBytes[i] {
				t.Errorf("%s: certificate %d measures %d, the vector pins %d", c.Name, i, got, c.CertBytes[i])
			}
			if c.Produced && cert.LimitsDecl.CertBytes != got {
				t.Errorf("%s: certificate %d declares %d but measures %d", c.Name, i, cert.LimitsDecl.CertBytes, got)
			}
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
