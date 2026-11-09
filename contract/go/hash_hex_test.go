package contract_test

import (
	"strings"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

func TestParseHashHex(t *testing.T) {
	canonical := strings.Repeat("01ab", 16)
	hash, ok := contract.ParseHashHex(canonical)
	if !ok {
		t.Fatal("canonical hash refused")
	}
	for i := 0; i < len(hash); i += 2 {
		if hash[i] != 1 || hash[i+1] != 0xab {
			t.Fatalf("decoded wrong bytes at %d", i)
		}
	}
	if zero, ok := contract.ParseHashHex(strings.Repeat("00", 32)); !ok || zero != (contract.Hash{}) {
		t.Fatal("valid zero hash refused")
	}
	for _, text := range []string{"fg" + canonical[2:], canonical[2:], canonical + "0f", strings.ToUpper(canonical)} {
		if _, ok := contract.ParseHashHex(text); ok {
			t.Fatalf("accepted malformed hash %q", text)
		}
	}
}

func TestHashFromBytes(t *testing.T) {
	for _, size := range []int{0, 31, 32, 33} {
		input := make([]byte, size)
		hash, ok := contract.HashFromBytes(input)
		if ok != (size == 32) {
			t.Fatalf("HashFromBytes(%d bytes): got %v", size, ok)
		}
		if ok {
			input[0] = 255
			if hash != (contract.Hash{}) {
				t.Fatal("source mutation changed the zero hash")
			}
			fresh, ok := contract.HashFromBytes(input)
			if !ok || fresh[0] != 255 {
				t.Fatal("a valid nonzero octet was lost")
			}
		}
	}
}
