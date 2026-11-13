package contract

import "testing"

// #2735: a protocol index is an INTEGER, not a host offset. It is held as uint64 on every platform,
// becomes an offset only through IndexOffset after a range check, and an index past its collection
// reaches check, which refuses it by name. #2682's per-platform decode refusal
// (DecodeIndexBeyondPlatform) is gone: on a 32-bit build, a root past 2^32 - 1 is still an integer
// the decoder holds, and check refuses it as root_out_of_range, like any other root past the nodes.
func TestProtocolIndexIsAnIntegerNotAnOffset2735(t *testing.T) {
	const past32 = uint64(1)<<32 + 5 // in the contract domain (<= IndexMax), past a 32-bit int
	if past32 > IndexMax {
		t.Fatal("CONTROL: the probe index must be inside the contract's domain")
	}
	// The offset step is the range check and nothing else.
	if o, ok := IndexOffset(2, 3); !ok || o != 2 {
		t.Fatalf("CONTROL: an in-range index is its offset: %d %v", o, ok)
	}
	for _, c := range []struct {
		i uint64
		n int
	}{{3, 3}, {past32, 3}, {IndexMax, 3}, {0, 0}} {
		if _, ok := IndexOffset(c.i, c.n); ok {
			t.Fatalf("index %d is no offset into %d elements", c.i, c.n)
		}
	}
	// A derivation whose root is past 2^32 - 1 is held whole, and check refuses it by its FIRM code.
	claim := NewGroundLiteral("p", pmAtom("a"))
	d := NewDerivation([]Node{LeafNode{Conc: claim, Evidence: NoEvidence()}}, past32)
	if d.Root != past32 {
		t.Fatalf("the root was not held as an integer: %d", d.Root)
	}
	if _, ok := d.RootOffset(); ok {
		t.Fatal("a root past the nodes has no offset")
	}
	profile := &CheckProfile[struct{}]{
		Theory: NewStandardTheory(),
		Leaves: pmLeaves{PredicateSetOf("p"), []GroundLiteral{claim}},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	out := Check(NewMapProgram(), claim, d, struct{}{}, profile)
	if got := out.Verdict.Code().Code(); got != "root_out_of_range" {
		t.Fatalf("want root_out_of_range, got %q", got)
	}
}
