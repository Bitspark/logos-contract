// Language-local unit tests for the ComponentIdentity / Identified seam (ADR 0004 D4
// · tri-core parity with the Rust binding's ComponentIdentity + defaulted identity()).
// Identity is exposed for attestation only; the bindings compute NO digest.
package contract

import (
	"bytes"
	"testing"
)

func TestUnidentifiedComponentIsStable(t *testing.T) {
	a := UnidentifiedComponent()
	b := UnidentifiedComponent()
	if !bytes.Equal(a.Id, []byte("unidentified")) {
		t.Errorf("Id = %q, want %q", a.Id, "unidentified")
	}
	if len(a.Version) != 0 {
		t.Errorf("Version = %q, want empty", a.Version)
	}
	if a.ConfigDigest != ([32]byte{}) {
		t.Errorf("ConfigDigest = %v, want zero", a.ConfigDigest)
	}
	// Two calls produce the same identity.
	if !bytes.Equal(a.Id, b.Id) || !bytes.Equal(a.Version, b.Version) || a.ConfigDigest != b.ConfigDigest {
		t.Error("UnidentifiedComponent() is not stable across calls")
	}
}

func TestNewComponentIdentityRoundTrips(t *testing.T) {
	digest := [32]byte{}
	digest[0] = 0xAB
	digest[31] = 0xCD
	id := NewComponentIdentity([]byte("some/component"), []byte("2.1.0"), digest)
	if !bytes.Equal(id.Id, []byte("some/component")) {
		t.Errorf("Id = %q", id.Id)
	}
	if !bytes.Equal(id.Version, []byte("2.1.0")) {
		t.Errorf("Version = %q", id.Version)
	}
	if id.ConfigDigest != digest {
		t.Errorf("ConfigDigest = %v, want %v", id.ConfigDigest, digest)
	}
}

func TestAlwaysAdmitImplementsIdentified(t *testing.T) {
	// AlwaysAdmit is a component, so it can be type-asserted to Identified exactly as
	// a kernel-side consumer would do.
	var component any = AlwaysAdmit[any]{}
	c, ok := component.(Identified)
	if !ok {
		t.Fatal("AlwaysAdmit should implement Identified")
	}
	id := c.Identity()
	if !bytes.Equal(id.Id, []byte("core/always-admit")) {
		t.Errorf("Id = %q, want %q", id.Id, "core/always-admit")
	}
	if !bytes.Equal(id.Version, []byte("1.0.0")) {
		t.Errorf("Version = %q, want %q", id.Version, "1.0.0")
	}
	if id.ConfigDigest != ([32]byte{}) {
		t.Errorf("ConfigDigest = %v, want zero", id.ConfigDigest)
	}
}

// unidentifiedFixture is a Theory that does NOT implement Identified — the common
// case (an impl predating, or simply not opting into, the identity seam).
// test-double: adversarial(relies on the default identity: the unidentified fallback under test)
type unidentifiedFixture struct{}

func (unidentifiedFixture) Owns(_ Symbol) bool                   { return false }
func (unidentifiedFixture) Decide(_ GroundLiteral) TheoryOutcome { return TheoryNotMine{} }

func TestComponentWithoutIdentifiedFallsBackToUnidentified(t *testing.T) {
	var component any = unidentifiedFixture{}
	// The kernel-side resolution pattern: type-assert, else Unidentified.
	id := UnidentifiedComponent()
	if c, ok := component.(Identified); ok {
		id = c.Identity()
		t.Fatal("fixture unexpectedly implements Identified")
	}
	if !bytes.Equal(id.Id, []byte("unidentified")) {
		t.Errorf("Id = %q, want %q", id.Id, "unidentified")
	}
	// Sanity: the fixture really is usable as a Theory (interface unchanged).
	var _ Theory = unidentifiedFixture{}
}
