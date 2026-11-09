// Go replay of vectors/cert_wire_spans.json (#2528, #2561): CertWireSpansAt walks each guest-to-host
// frame's tags and uvarints WITHOUT decoding it, and must report the rs walk's certificates (their
// concrete paths and spans), tag, walk verdict, budget verdict and refusal names; an all-index path
// must give CertWireSpans the same spans.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	codec "github.com/bitspark/ontos/codec/go"
)

type certWireSpansFile struct {
	CertBytesSlack uint64 `json:"cert_bytes_slack"`
	Cases          []struct {
		Name         string            `json:"name"`
		Path         []json.RawMessage `json:"path"`
		Tag          *string           `json:"tag"`
		At           [][]int           `json:"at"`
		Spans        []int             `json:"spans"`
		Starts       []int             `json:"starts"`
		Measures     []uint64          `json:"measures"`
		Refused      *string           `json:"refused"`
		MaxCertBytes *int              `json:"max_cert_bytes"`
		OverBudget   [][]int           `json:"over_budget"`
		Walk         string            `json:"walk"`
		Frame        string            `json:"frame"`
	} `json:"cases"`
}

func loadCertWireSpans(t *testing.T) certWireSpansFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for {
		candidate := filepath.Join(dir, "vectors", "cert_wire_spans.json")
		if _, statErr := os.Stat(candidate); statErr == nil {
			raw, readErr := os.ReadFile(candidate)
			if readErr != nil {
				t.Fatalf("read vector: %v", readErr)
			}
			var v certWireSpansFile
			if err := json.Unmarshal(raw, &v); err != nil {
				t.Fatalf("parse vector: %v", err)
			}
			return v
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatalf("could not locate vectors/cert_wire_spans.json")
		}
		dir = parent
	}
}

// vectorSteps reads a case's path: an index, or "*" for every element. indices is the same path as
// indices when every step is one (the index-only walker's input), else nil.
func vectorSteps(t *testing.T, name string, raw []json.RawMessage) (steps []PathStep, indices []uint64) {
	t.Helper()
	indices = []uint64{}
	for _, r := range raw {
		var i uint64
		if err := json.Unmarshal(r, &i); err == nil {
			steps = append(steps, PathIndex(i))
			if indices != nil {
				indices = append(indices, i)
			}
			continue
		}
		var star string
		if err := json.Unmarshal(r, &star); err != nil || star != "*" {
			t.Fatalf("%s: a path step %s is neither an index nor \"*\"", name, r)
		}
		steps = append(steps, PathEach())
		indices = nil
	}
	return steps, indices
}

func TestCertWireSpansVectors2528(t *testing.T) {
	v := loadCertWireSpans(t)
	if v.CertBytesSlack != CertBytesSlack() {
		t.Fatalf("slack: go %d, the vector %d", CertBytesSlack(), v.CertBytesSlack)
	}
	if len(v.Cases) < 10 {
		t.Fatalf("the vector's cases: %d", len(v.Cases))
	}
	measured, each, budgeted := 0, 0, 0
	for _, c := range v.Cases {
		frame, err := hex.DecodeString(c.Frame)
		if err != nil {
			t.Fatalf("%s: hex: %v", c.Name, err)
		}
		tag, _ := CertWireTag(frame)
		if (c.Tag == nil) != (tag == nil) || (c.Tag != nil && *c.Tag != string(tag)) {
			t.Errorf("%s: tag %q, the vector %v", c.Name, tag, c.Tag)
		}
		walk := "ok"
		if err := CertWireWalk(frame); err != nil {
			var we CertWireError
			if !errors.As(err, &we) {
				t.Fatalf("%s: the walk alone: %v", c.Name, err)
			}
			walk = we.Name()
		}
		if walk != c.Walk {
			t.Errorf("%s: the walk alone %q, the vector %q", c.Name, walk, c.Walk)
		}
		steps, indices := vectorSteps(t, c.Name, c.Path)
		if indices == nil {
			each++
		}
		certs, err := CertWireSpansAt(frame, steps)
		if c.Refused != nil {
			var we CertWireError
			if !errors.As(err, &we) || we.Name() != *c.Refused {
				t.Errorf("%s: want refused %q, got %v (certificates %v)", c.Name, *c.Refused, err, certs)
			}
			if indices != nil {
				if _, err := CertWireSpans(frame, indices); !errors.As(err, &we) || we.Name() != *c.Refused {
					t.Errorf("%s: the index-only walker: want refused %q, got %v", c.Name, *c.Refused, err)
				}
			}
			continue
		}
		if err != nil {
			t.Fatalf("%s: walk: %v", c.Name, err)
		}
		at := [][]int{}
		spans := []int{}
		starts := []int{}
		for _, cert := range certs {
			at = append(at, cert.Path)
			spans = append(spans, cert.Span)
			starts = append(starts, cert.Start)
		}
		if !reflect.DeepEqual(at, c.At) || !reflect.DeepEqual(spans, c.Spans) || !reflect.DeepEqual(starts, c.Starts) {
			t.Errorf("%s: at %v spans %v starts %v, the vector at %v spans %v starts %v", c.Name, at, spans, starts, c.At, c.Spans, c.Starts)
		}
		if indices != nil {
			if got, err := CertWireSpans(frame, indices); err != nil || !reflect.DeepEqual(got, spans) {
				t.Errorf("%s: the index-only walker: %v %v, want %v", c.Name, got, err, spans)
			}
		}
		if c.MaxCertBytes != nil {
			budget, err := ProofBudgetCountFromInt64("max_cert_bytes", int64(*c.MaxCertBytes))
			if err != nil {
				t.Fatal(err)
			}
			over := [][]int{}
			for _, cert := range certs {
				if CertSpanOverBudget(uint64(cert.Span), budget) {
					over = append(over, cert.Path)
				}
			}
			if !reflect.DeepEqual(over, c.OverBudget) {
				t.Errorf("%s: over budget %v, the vector %v", c.Name, over, c.OverBudget)
			}
			budgeted++
		}
		for i, m := range c.Measures {
			if uint64(spans[i]) < m || uint64(spans[i])-m > CertBytesSlack() {
				t.Errorf("%s: certificate %d spans %d over measure %d, beyond the slack", c.Name, i, spans[i], m)
			}
			measured++
		}
	}
	if measured < 4 {
		t.Fatalf("the vector measures real certificates: %d", measured)
	}
	if each < 3 || budgeted < 1 {
		t.Fatalf("the vector walks * paths (%d) and holds a case to a budget (%d)", each, budgeted)
	}
}

func TestCertWireWalkRefusesWhatTheCodecRefuses2528(t *testing.T) {
	// A padded arity uvarint (0x81 0x00 for 1) is the codec's non_canonical_uvarint.
	padded := []byte{0x01, 0x81, 0x00, 0x00, 0x01, 'a'}
	if _, err := codec.Decode(padded); err == nil {
		t.Fatal("CONTROL: the codec must refuse the padded uvarint")
	}
	var we CertWireError
	if _, err := CertWireSpans(padded, nil); !errors.As(err, &we) || we.Name() != "non_canonical_uvarint" {
		t.Fatalf("want non_canonical_uvarint, got %v", err)
	}
	frame := []byte{0x01, 0x01, 0x00, 0x01, 'a'}
	for cut := 0; cut < len(frame); cut++ {
		if _, err := CertWireSpans(frame[:cut], nil); !errors.As(err, &we) || we.Name() != "truncated" {
			t.Fatalf("cut %d: want truncated, got %v", cut, err)
		}
	}
	if spans, err := CertWireSpans(frame, []uint64{3}); err != nil || len(spans) != 0 {
		t.Fatalf("an absent slot has no certificates, got %v %v", spans, err)
	}
}

func TestCertBytesSlackBoundsEveryDeclaration2528(t *testing.T) {
	slack := CertBytesSlack()
	zero := len(codec.Encode(U64Atom(0)))
	for _, n := range []uint64{0, 1, 255, 256, 1 << 20, 1 << 40, ^uint64(0)} {
		if growth := uint64(len(codec.Encode(U64Atom(n))) - zero); growth > slack {
			t.Fatalf("%d grows %d over the slack %d", n, growth, slack)
		}
	}
	if !CertSpanOverBudget(100+slack+1, ProofBudgetCountFromUint32(100)) || CertSpanOverBudget(100+slack, ProofBudgetCountFromUint32(100)) {
		t.Fatal("the bound is span > max + slack")
	}
}

func TestCertWireWalkAloneReadsAnyValue2561(t *testing.T) {
	if err := CertWireWalk([]byte{0x00, 0x01, 'x'}); err != nil {
		t.Fatalf("an atom root is a readable frame: %v", err)
	}
	var we CertWireError
	if err := CertWireWalk([]byte{0x00, 0x01, 'x', 0x00}); !errors.As(err, &we) || we.Name() != "trailing_bytes" {
		t.Fatalf("want trailing_bytes, got %v", err)
	}
	if err := CertWireWalk([]byte{0x01, 0x02, 0x00, 0x00}); !errors.As(err, &we) || we.Name() != "truncated" {
		t.Fatalf("want truncated, got %v", err)
	}
}
