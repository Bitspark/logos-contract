package contract

// #3151 (research 0030 rows 3 and 4): FromValue's frame carries an operation whose zero value is
// invalid, and an assemble checks the children above the base it recorded. Each malformed frame is
// refused by name. These frames can only come from this package's own code, so the refusal is an
// invariant panic, never a verdict on input (#3074's "the source decides").

import (
	"fmt"
	"strings"
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

func frameRefusal3151(t *testing.T, work []fromValueFrame) (msg string) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("fromValueRun accepted a malformed frame")
		}
		msg = fmt.Sprint(r)
	}()
	fromValueRun(work)
	return ""
}

func TestAZeroValuedFrameIsRefusedByName3151(t *testing.T) {
	msg := frameRefusal3151(t, []fromValueFrame{{}})
	if !strings.Contains(msg, "a frame with no operation") {
		t.Fatalf("a zero-valued frame was refused, but not by name: %q", msg)
	}
}

func TestAnOutOfRangeFrameOperationIsRefusedByName3151(t *testing.T) {
	msg := frameRefusal3151(t, []fromValueFrame{{op: 7}})
	if !strings.Contains(msg, "frame operation 7 is neither enter nor assemble") {
		t.Fatalf("an unknown frame operation was refused, but not by name: %q", msg)
	}
}

func TestAnAssembleThatFindsTheWrongNumberOfChildrenIsRefusedByName3151(t *testing.T) {
	msg := frameRefusal3151(t, []fromValueFrame{assembleFrame(2, 0)})
	if !strings.Contains(msg, "an assemble of 2 children above 0 finds 0 terms") {
		t.Fatalf("an assemble with its children missing was refused, but not by name: %q", msg)
	}
}

// The control: the constructors still lift every shape, and EraseGround inverts the lift.
func TestFromValueStillLiftsEveryShape3151(t *testing.T) {
	a := func(s string) core.Value { return core.NewAtom([]byte(s)) }
	deep := a("x")
	for i := 0; i < 2000; i++ {
		deep = core.NewTuple(deep, a("y"))
	}
	for _, v := range []core.Value{
		a("p"),
		core.NewTuple(),
		core.NewTuple(a("p"), core.NewTuple(a("q"), core.NewTuple()), a("r")),
		deep,
	} {
		back, ok := FromValue(v).EraseGround()
		if !ok || !back.Equal(v) {
			t.Fatalf("FromValue then EraseGround did not round-trip %v", v)
		}
	}
}
