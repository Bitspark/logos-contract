// #3057: the injective escape is Symbol's canonical rendering, so it lives beside Symbol in the
// contract tier (seat:caa's ruling on #2984, site 3). This replays vectors/identity_bytes.json's
// escaped_name section against contract.EscapedName directly, so the contract tier's own code can
// render a name injectively without the kernel. kernel/go/runtime/identity_bytes_test.go replays
// the same rows through seam.EscapedName, which delegates here. The same rows are replayed at the
// contract tier in rs (contract/rs/tests/escaped_name_3057.rs) and ts
// (contract/ts/test/escaped_name_3057.test.ts).
package contract

import (
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

type escapedNameCase struct {
	Name         string `json:"name"`
	BytesHex     string `json:"bytes_hex"`
	Rendered     string `json:"rendered"`
	CollidesWith string `json:"collides_with"`
}

// loadEscapedNameCases finds vectors/identity_bytes.json by walking up from contract/go to the
// repo root, mirroring loadTextVectors.
func loadEscapedNameCases(t *testing.T) []escapedNameCase {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	for d := dir; ; {
		raw, err := os.ReadFile(filepath.Join(d, "vectors", "identity_bytes.json"))
		if err == nil {
			var file struct {
				EscapedName struct {
					Cases []escapedNameCase `json:"cases"`
				} `json:"escaped_name"`
			}
			if err := json.Unmarshal(raw, &file); err != nil {
				t.Fatalf("parse identity_bytes.json: %v", err)
			}
			return file.EscapedName.Cases
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/identity_bytes.json above %s", dir)
		}
		d = parent
	}
}

// Every row renders to exactly `rendered`, and a row naming collides_with renders differently
// from that row, where a lossy render gave both U+FFFD.
func TestEscapedNameVectorAtTheContractTier3057(t *testing.T) {
	cases := loadEscapedNameCases(t)
	if len(cases) == 0 {
		t.Fatal("the escaped_name section carries no rows")
	}
	rendered := map[string]string{}
	for _, c := range cases {
		b, err := hex.DecodeString(c.BytesHex)
		if err != nil {
			t.Fatalf("[escaped_name/%s] row hex: %v", c.Name, err)
		}
		got := EscapedName(b)
		if got != c.Rendered {
			t.Errorf("[escaped_name/%s] rendered %q, want %q", c.Name, got, c.Rendered)
		}
		rendered[c.Name] = got
	}
	for _, c := range cases {
		if c.CollidesWith != "" && rendered[c.Name] == rendered[c.CollidesWith] {
			t.Errorf("[escaped_name/%s] renders as %s does", c.Name, c.CollidesWith)
		}
	}
}
