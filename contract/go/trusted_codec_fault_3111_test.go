package contract

import (
	"errors"
	"testing"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
)

// Checker SPI v2, ADR 0036 D8 change 4 (#3111; #2734 ruling C): the trusted decoder's codec stop is
// its own FAULT kind, carrying the codec's error, and a decoded value of the wrong shape is still the
// shape refusal. Twin of rs's trusted_codec_fault_3111 module; ts pins the same text.
func TestACodecStopOnTrustedBytesIsACodecFaultNotAShape3111(t *testing.T) {
	_, err := DecodeDerivationWireV1([]byte{})
	var de *DecodeError
	if !errors.As(err, &de) {
		t.Fatalf("expected a *DecodeError, got %T: %v", err, err)
	}
	if de.Kind != DecodeCodecFault {
		t.Fatalf("expected the codec fault kind, got %d: %v", de.Kind, de)
	}
	var ce *codec.DecodeError
	if !errors.As(err, &ce) || ce.Code != "unexpected_eof" {
		t.Fatalf("the codec's own error must unwrap, code unexpected_eof; got %v", err)
	}
	if got, want := err.Error(), "decode derivation wire v1 bytes: codec fault: unexpected_eof"; got != want {
		t.Fatalf("rendering: got %q, want %q", got, want)
	}
}

// CONTROL: the bytes ARE a value (an atom), so the codec did not stop; the wire reading refuses it,
// and that is not the fault kind.
func TestAValueOfTheWrongShapeIsStillAShapeRefusal3111(t *testing.T) {
	_, err := DecodeDerivationWireV1(codec.Encode(core.NewAtom([]byte("not-a-wire"))))
	var de *DecodeError
	if !errors.As(err, &de) {
		t.Fatalf("expected a *DecodeError, got %T: %v", err, err)
	}
	if de.Kind == DecodeCodecFault {
		t.Fatalf("a decoded value is never a codec fault: %v", de)
	}
}
