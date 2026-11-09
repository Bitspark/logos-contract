package contract_test

import (
	"fmt"
	"reflect"
	"testing"

	contract "github.com/Bitspark/logos-contract/contract/go"
)

func TestWireSelectorCountsBeforeTraversal(t *testing.T) {
	frames := [][]byte{{1, 0}, {1, 1, 1, 0}, nil}
	for _, index := range []uint64{1 << 53, 1<<53 + 1, ^uint64(0)} {
		t.Run(fmt.Sprint(index), func(t *testing.T) {
			for _, frame := range frames {
				if _, err := contract.CertWireSpans(frame, []uint64{index}); err == nil || err.Error() != "cert wire: invalid_path" {
					t.Errorf("index-only selector on %x: %v", frame, err)
				}
				for _, steps := range [][]contract.PathStep{
					{contract.PathIndex(index)},
					{contract.PathEach(), contract.PathIndex(index)},
					{contract.PathIndex(99), contract.PathIndex(index)},
				} {
					if _, err := contract.CertWireSpansAt(frame, steps); err == nil || err.Error() != "cert wire: invalid_path" {
						t.Errorf("composed selector on %x: %v", frame, err)
					}
				}
			}
		})
	}
}

func TestWireSelectorAbsentSlotAndConcreteCoordinates(t *testing.T) {
	// Root[tag, list[item[empty, certificates[a]], item[empty, certificates[bc]]]].
	frame := []byte{1, 2, 0, 3, 't', 'a', 'g', 1, 2, 1, 2, 1, 0, 1, 1, 0, 1, 'a', 1, 2, 1, 0, 1, 1, 0, 2, 'b', 'c'}
	for _, index := range []uint64{2, 1<<31 - 1, 1 << 31, 1<<32 - 1, 1 << 32, 1<<53 - 1} {
		spans, err := contract.CertWireSpans(frame, []uint64{index})
		if err != nil || len(spans) != 0 {
			t.Errorf("valid absent index %d: %v, %v", index, spans, err)
		}
	}
	spans, err := contract.CertWireSpansAt(frame, []contract.PathStep{
		contract.PathIndex(1), contract.PathEach(), contract.PathIndex(1),
	})
	if err != nil || len(spans) != 2 {
		t.Fatalf("composed selector: %v, %v", spans, err)
	}
	for i, expected := range []struct {
		path  []int
		bytes []byte
	}{
		{[]int{1, 0, 1, 0}, []byte{0, 1, 'a'}},
		{[]int{1, 1, 1, 0}, []byte{0, 2, 'b', 'c'}},
	} {
		span := spans[i]
		if !reflect.DeepEqual(span.Path, expected.path) || !reflect.DeepEqual(frame[span.Start:span.Start+span.Span], expected.bytes) {
			t.Errorf("selected element %d: %v", i, span)
		}
	}
}

func TestWireSelectorInspectionPreservesZeroAndEach(t *testing.T) {
	for _, index := range []uint64{0, 1, 1<<32 - 1, 1 << 32, 1<<53 - 1} {
		step := contract.PathIndex(index)
		got, ok := step.Index()
		if !ok || got != index || step.IsEach() {
			t.Fatalf("index %d: %d, %v, %v", index, got, ok, step.IsEach())
		}
	}
	each := contract.PathEach()
	if _, ok := each.Index(); ok || !each.IsEach() {
		t.Fatal("each step was reported as an index")
	}
}
