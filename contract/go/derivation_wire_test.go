package contract

import (
	"encoding/hex"
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

type derivationWireFile struct {
	Positive []struct {
		Name    string `json:"name"`
		WireHex string `json:"wire_hex"`
	} `json:"positive"`
	Malformed []struct {
		Name    string `json:"name"`
		WireHex string `json:"wire_hex"`
		Refusal string `json:"refusal"`
	} `json:"malformed"`
	Decodes []struct {
		Name    string `json:"name"`
		WireHex string `json:"wire_hex"`
		Root    uint64 `json:"root"`
		Nodes   int    `json:"nodes"`
	} `json:"decodes"`
}

func loadDerivationWireVectors(t *testing.T) derivationWireFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "derivation_wire.json")
		if _, err := os.Stat(candidate); err == nil {
			raw, err := os.ReadFile(candidate)
			if err != nil {
				t.Fatalf("read %s: %v", candidate, err)
			}
			var vf derivationWireFile
			if err := json.Unmarshal(raw, &vf); err != nil {
				t.Fatalf("unmarshal %s: %v", candidate, err)
			}
			return vf
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/derivation_wire.json above %s", dir)
		}
		d = parent
	}
}

func dwAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

func dwLit(pred string, args ...string) GroundLiteral {
	values := make([]core.Value, len(args))
	for i, arg := range args {
		values[i] = dwAtom(arg)
	}
	return NewGroundLiteral(pred, values...)
}

func dwZeroHash() Hash { return Hash{} }

func dwClosedCert() ClosedModelCert {
	pred := SymbolFromString("sealed")
	return ClosedModelCert{
		Scope:             NewStratumPrefix(0, []Symbol{pred}),
		ProgramHash:       dwZeroHash(),
		ProfileHash:       dwZeroHash(),
		CtxHash:           dwZeroHash(),
		TheoryConfigHash:  dwZeroHash(),
		EdbSnapshotHashes: nil,
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("entity"), []core.Value{dwAtom("a")})},
		Extensions:        []RelationTable{NewRelationTable(pred, 1, []GroundLiteral{dwLit("sealed", "a")})},
		Supports:          SupportWitness{},
		Closure:           ClosureWitness{},
		LimitsDecl: CertSizeDecl{
			CertFacts:      1,
			DomainValues:   1,
			SupportEdges:   0,
			RuleGroundings: 0,
			JoinSteps:      0,
			CertBytes:      0,
		},
	}
}

func dwFixture(t *testing.T, name string) Derivation {
	t.Helper()
	switch name {
	case "leaf":
		return NewDerivation([]Node{LeafNode{Conc: dwLit("edge", "a", "b"), Evidence: NoEvidence()}}, 0)
	case "builtin":
		return NewDerivation([]Node{BuiltinNode{Conc: dwLit("=", "a", "a")}}, 0)
	case "rule":
		return NewDerivation([]Node{
			LeafNode{Conc: dwLit("edge", "a", "b"), Evidence: NoEvidence()},
			RuleNode{
				Conc:     dwLit("path", "a", "b"),
				Clause:   NewClauseId("path#edge"),
				Subst:    Subst{},
				Premises: []Premise{PosNode(0)},
				Meta:     NoMeta(),
			},
		}, 1)
	case "closed_world_count":
		return NewDerivationWithClosedWorld([]Node{
			RuleNode{
				Conc:   dwLit("has_count", "a"),
				Clause: NewClauseId("count#sealed"),
				Subst:  Subst{},
				Premises: []Premise{
					CountPremise{
						Pred:    NewPredicateRef(SymbolFromString("sealed"), 1),
						Filter:  []GroundFilterEntry{{Pos: 0, Value: dwAtom("a")}},
						Project: Rows(),
						K:       data.EncodeInt(bigOne()),
						Cert:    NewCertId(0),
					},
				},
				Meta: NoMeta(),
			},
		}, 0, []ClosedModelCert{dwClosedCert()})
	case "closed_world_count_partial":
		// ADR 0030 D4: the twelve-element cert — the D10 witness at slot 11 AND a partial
		// sub-scope at slot 12. Byte-identical to the RED-first malformed entry of b1d3d5a7;
		// a WIRE fixture only (the level-1 partial scope over a level-0 seal is not checkable).
		cert := dwClosedCert()
		var w Hash
		for i := range w {
			w[i] = 0xd1
		}
		cert.DecompositionWitness = &w
		ps := NewStratumPrefix(1, []Symbol{SymbolFromString("sealed")})
		cert.PartialScope = &ps
		return NewDerivationWithClosedWorld([]Node{
			RuleNode{
				Conc:   dwLit("has_count", "a"),
				Clause: NewClauseId("count#sealed"),
				Subst:  Subst{},
				Premises: []Premise{
					CountPremise{
						Pred:    NewPredicateRef(SymbolFromString("sealed"), 1),
						Filter:  []GroundFilterEntry{{Pos: 0, Value: dwAtom("a")}},
						Project: Rows(),
						K:       data.EncodeInt(bigOne()),
						Cert:    NewCertId(0),
					},
				},
				Meta: NoMeta(),
			},
		}, 0, []ClosedModelCert{cert})
	default:
		t.Fatalf("unknown derivation_wire fixture %s", name)
		return Derivation{}
	}
}

func bigOne() *big.Int {
	return big.NewInt(1)
}

func TestDerivationWirePositiveVectors(t *testing.T) {
	vf := loadDerivationWireVectors(t)
	for _, c := range vf.Positive {
		deriv := dwFixture(t, c.Name)
		got := hex.EncodeToString(mustWire(EncodeDerivationWireV1(deriv)))
		if got != c.WireHex {
			t.Fatalf("%s wire bytes\n got  %s\n want %s", c.Name, got, c.WireHex)
		}
		decoded, err := DecodeDerivationWireV1(mustWire(EncodeDerivationWireV1(deriv)))
		if err != nil {
			t.Fatalf("%s decode: %v", c.Name, err)
		}
		if rt := hex.EncodeToString(mustWire(EncodeDerivationWireV1(decoded))); rt != c.WireHex {
			t.Fatalf("%s round-trip bytes\n got  %s\n want %s", c.Name, rt, c.WireHex)
		}
	}
}

func TestDerivationWireMalformedVectorsReject(t *testing.T) {
	vf := loadDerivationWireVectors(t)
	if len(vf.Malformed) == 0 {
		t.Fatal("the vector has no malformed rows")
	}
	for _, c := range vf.Malformed {
		raw, err := hex.DecodeString(c.WireHex)
		if err != nil {
			t.Fatalf("%s hex: %v", c.Name, err)
		}
		_, err = DecodeDerivationWireV1(raw)
		if err == nil {
			t.Fatalf("%s unexpectedly decoded", c.Name)
		}
		// #2630: the one decoder's refusal text, byte-identical in all three cores.
		if c.Refusal == "" {
			t.Fatalf("%s states no refusal", c.Name)
		}
		if err.Error() != c.Refusal {
			t.Fatalf("%s refusal\n got  %q\n want %q", c.Name, err.Error(), c.Refusal)
		}
	}
}

// #2630 (seat:caa's ruling on #2645): wires the decoder must ACCEPT. A root that indexes no node
// passes through (check refuses it as root_out_of_range), and a subst in canonical order decodes;
// each re-encodes byte for byte.
func TestDerivationWireDecodesVectorsAreAcceptedAndRoundTrip(t *testing.T) {
	vf := loadDerivationWireVectors(t)
	if len(vf.Decodes) == 0 {
		t.Fatal("the vector has no decodes rows")
	}
	for _, c := range vf.Decodes {
		raw, err := hex.DecodeString(c.WireHex)
		if err != nil {
			t.Fatalf("%s hex: %v", c.Name, err)
		}
		d, err := DecodeDerivationWireV1(raw)
		if err != nil {
			t.Fatalf("%s was refused: %v", c.Name, err)
		}
		if d.Root != c.Root || len(d.Nodes) != c.Nodes {
			t.Fatalf("%s: root %d over %d nodes, want root %d over %d", c.Name, d.Root, len(d.Nodes), c.Root, c.Nodes)
		}
		if rt := hex.EncodeToString(mustWire(EncodeDerivationWireV1(d))); rt != c.WireHex {
			t.Fatalf("%s re-encodes\n got  %s\n want %s", c.Name, rt, c.WireHex)
		}
	}
}
