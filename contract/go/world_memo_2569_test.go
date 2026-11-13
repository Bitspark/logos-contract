package contract

// #2569, the go rung of #2565 term 1: WorldMemo verifies a closed world once for a run of
// derivations citing it, and every verdict through it is the fresh CheckWithCertContext verdict.
// Ported from contract/rs/tests/negation.rs `world_memo_2565`, on the aggregation fixture, plus the
// two cases go adds: an in-place edit of the checked derivation, and a limit changed through the
// profile the memo is bound to.

import (
	"reflect"
	"testing"
	"time"

	core "github.com/bitspark/ontos/core/go"
)

func memoClaim() GroundLiteral { return NewGroundLiteral("eligible_count", aggV("o1")) }

func memoDeriv(cert ClosedModelCert) Derivation {
	return aggCountDerivation(cEligibleCount, "eligible_count", Rows(), 4, cert)
}

func memoFresh(program CompleteProgram, prof *CheckProfile[struct{}], claim GroundLiteral, deriv Derivation) Outcome {
	return CheckWithCertContext[struct{}](program, claim, deriv, struct{}{}, prof, aggBoundContext(program))
}

// memoMutations is one change each to the valid certificate: a table row, a domain value, a pin,
// a size declaration.
func memoMutations() []struct {
	what string
	cert ClosedModelCert
} {
	row := aggValidCert()
	rows := obsEdb()
	rows[0] = aggObs("o1", "p1", aggV("y"))
	row.Extensions[0] = NewRelationTable(aggSym("obs"), 3, rows)

	domain := aggValidCert()
	domain.Domains[0] = NewFiniteDomain(aggSym("u"), []core.Value{
		aggV("o1"), aggV("o2"), aggV("p1"), aggV("p2"), aggV("p3"), aggV("p4"),
		aggV("x"), aggV("y"), nullValue(),
	})

	pin := aggValidCert()
	pin.ProgramHash[0] ^= 1

	size := aggValidCert()
	size.LimitsDecl.CertFacts = 6

	return []struct {
		what string
		cert ClosedModelCert
	}{
		{"a table row", row},
		{"a domain value", domain},
		{"a pin", pin},
		{"a size declaration", size},
	}
}

func TestWorldMemoVerifiesAWorldCitedByManyAnswersOnce2569(t *testing.T) {
	program := aggBaseProgram()
	memo := NewWorldMemo[struct{}](program, aggProfile(), struct{}{}, aggBoundContext(program))
	deriv := memoDeriv(aggValidCert())
	for i := 0; i < 5; i++ {
		if out := CheckWithWorldMemo(memo, memoClaim(), deriv); !out.IsAccept() {
			t.Fatalf("answer %d: %s", i, out)
		}
	}
	if got := memo.CertificatesVerified(); got != 1 {
		t.Fatalf("five answers citing one certificate verified %d certificates, want 1", got)
	}
}

// test-double: consumer(attests its fixed EDB and retains the producer's input)
type editingSnapshot struct {
	*aggLeaves
	edit func()
}

func (s editingSnapshot) EdbSnapshot(pred Symbol, ctx struct{}) (Hash, bool) {
	s.edit()
	return s.aggLeaves.EdbSnapshot(pred, ctx)
}

func TestWorldMemoBindsTheWorldBeforeCallingTheVerifier(t *testing.T) {
	program := aggBaseProgram()
	deriv := memoDeriv(aggValidCert())
	profile := aggProfile()
	profile.Leaves = editingSnapshot{profile.Leaves.(*aggLeaves), func() {
		// The attestor still attests the same EDB. Only the producer's proposed
		// certificate changes during the callback, after context validation.
		deriv.ClosedWorld[0].ProfileHash[0] = 0
		deriv.ClosedWorld[0].Extensions[0] = NewRelationTable(aggSym("obs"), 3, nil)
	}}
	memo := NewWorldMemo(program, profile, struct{}{}, aggBoundContext(program))
	if first := CheckWithWorldMemo(memo, memoClaim(), deriv); !first.IsAccept() {
		t.Fatalf("the original verified table should discharge the original count: %s", first)
	}
	fresh := memoFresh(program, aggProfile(), memoClaim(), deriv)
	if fresh.IsAccept() || fresh.Verdict.Code() != CertContextMismatch {
		t.Fatalf("control: the changed input should fail the context check: %s", fresh)
	}
	if got := CheckWithWorldMemo(memo, memoClaim(), deriv); got.String() != fresh.String() || memo.CertificatesVerified() != 2 {
		t.Fatalf("the changed world needs a fresh verification: %s, verified %d", got, memo.CertificatesVerified())
	}
}

func TestWorldMemoCanBeReenteredDuringCertificateVerification(t *testing.T) {
	program := aggBaseProgram()
	profile := aggProfile()
	deriv := memoDeriv(aggValidCert())
	var memo *WorldMemo[struct{}]
	entered, innerOK := false, false
	profile.Leaves = editingSnapshot{profile.Leaves.(*aggLeaves), func() {
		if !entered {
			entered = true
			innerOK = CheckWithWorldMemo(memo, memoClaim(), deriv).IsAccept()
		}
	}}
	memo = NewWorldMemo(program, profile, struct{}{}, aggBoundContext(program))
	done := make(chan bool, 1)
	go func() {
		first := CheckWithWorldMemo(memo, memoClaim(), deriv)
		repeated := CheckWithWorldMemo(memo, memoClaim(), deriv)
		done <- first.IsAccept() && innerOK && repeated.IsAccept() && memo.CertificatesVerified() == 2
	}()
	select {
	case ok := <-done:
		if !ok {
			t.Fatal("the overlapping misses must both verify and the subsequent hit must reuse their result")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("world verification held the cache lock across its callback")
	}
}

func TestWorldMemoPublishesOverlappingVerifiedWorlds(t *testing.T) {
	program := aggBaseProgram()
	profile := aggProfile()
	entered := make(chan struct{}, 2)
	release := make(chan struct{})
	profile.Leaves = editingSnapshot{profile.Leaves.(*aggLeaves), func() {
		select {
		case <-release:
			return
		default:
		}
		entered <- struct{}{}
		<-release
	}}
	memo := NewWorldMemo(program, profile, struct{}{}, aggBoundContext(program))
	deriv := memoDeriv(aggValidCert())
	results := make(chan Outcome, 2)
	for range 2 {
		go func() { results <- CheckWithWorldMemo(memo, memoClaim(), deriv) }()
	}
	for range 2 {
		select {
		case <-entered:
		case <-time.After(5 * time.Second):
			close(release)
			t.Fatal("both misses must be able to enter the verifier")
		}
	}
	close(release)
	for range 2 {
		if out := <-results; !out.IsAccept() {
			t.Fatal(out)
		}
	}
	if out := CheckWithWorldMemo(memo, memoClaim(), deriv); !out.IsAccept() || memo.CertificatesVerified() != 2 {
		t.Fatalf("overlapping misses then reuse: %v, verified %d", out, memo.CertificatesVerified())
	}
}

func TestWorldMemoAChangedCertificateIsAMissWithTheFreshVerdict2569(t *testing.T) {
	program := aggBaseProgram()
	prof := aggProfile()
	memo := NewWorldMemo[struct{}](program, prof, struct{}{}, aggBoundContext(program))
	valid := memoDeriv(aggValidCert())
	if out := CheckWithWorldMemo(memo, memoClaim(), valid); !out.IsAccept() {
		t.Fatalf("the valid world: %s", out)
	}
	// The control, exact: which single changes a fresh check rejects. The size declaration above
	// the real size is a change the checker ACCEPTS, and it must miss all the same: the memo keys
	// on the certificate, never on the verdict.
	rejecting := map[string]bool{"a table row": true, "a domain value": true, "a pin": true}
	for _, m := range memoMutations() {
		before := memo.CertificatesVerified()
		deriv := memoDeriv(m.cert)
		got := CheckWithWorldMemo(memo, memoClaim(), deriv)
		want := memoFresh(program, prof, memoClaim(), deriv)
		if got.String() != want.String() {
			t.Fatalf("%s: the memo gave %s, the fresh check %s", m.what, got, want)
		}
		if memo.CertificatesVerified() != before+1 {
			t.Fatalf("%s: a changed certificate must miss (verified %d -> %d)", m.what, before, memo.CertificatesVerified())
		}
		if !want.IsAccept() != rejecting[m.what] {
			t.Fatalf("%s: the control's expected verdict is %s", m.what, want)
		}
		if back := CheckWithWorldMemo(memo, memoClaim(), valid); !back.IsAccept() {
			t.Fatalf("%s: the valid world after it: %s", m.what, back)
		}
	}
}

// Go has no borrow checker, so a caller can edit the derivation it just checked. The memo must
// have taken its own copy: an edit in place, at the top of a certificate or deep inside one, is a
// miss with the fresh verdict, never a hit against the stale world it shares memory with.
func TestWorldMemoAnInPlaceEditOfTheCheckedDerivationIsAMiss2569(t *testing.T) {
	program := aggBaseProgram()
	prof := aggProfile()
	edits := []struct {
		what string
		edit func(*Derivation)
	}{
		{"a pin, in the world's own element", func(d *Derivation) { d.ClosedWorld[0].ProgramHash[0] ^= 1 }},
		{"a table row, inside a nested slice", func(d *Derivation) {
			rows := obsEdb()
			rows[0] = aggObs("o1", "p1", aggV("y"))
			d.ClosedWorld[0].Extensions[0] = NewRelationTable(aggSym("obs"), 3, rows)
		}},
		{"a domain, inside a nested slice", func(d *Derivation) {
			d.ClosedWorld[0].Domains[0] = NewFiniteDomain(aggSym("u"), []core.Value{aggV("o1")})
		}},
	}
	for _, e := range edits {
		memo := NewWorldMemo[struct{}](program, prof, struct{}{}, aggBoundContext(program))
		deriv := memoDeriv(aggValidCert())
		if out := CheckWithWorldMemo(memo, memoClaim(), deriv); !out.IsAccept() {
			t.Fatalf("%s: the valid world: %s", e.what, out)
		}
		e.edit(&deriv)
		want := memoFresh(program, prof, memoClaim(), deriv)
		if want.IsAccept() {
			t.Fatalf("%s: control, the edited world must be rejected fresh", e.what)
		}
		if got := CheckWithWorldMemo(memo, memoClaim(), deriv); got.String() != want.String() {
			t.Fatalf("%s: the memo gave %s, the fresh check %s", e.what, got, want)
		}
		if got := memo.CertificatesVerified(); got != 2 {
			t.Fatalf("%s: an in-place edit must miss (verified %d, want 2)", e.what, got)
		}
	}
}

// Limits are the one bound input checked rather than assumed: a limit changed through the profile
// the memo holds re-verifies, and so does changing it back.
func TestWorldMemoALimitChangedThroughTheProfileIsAMiss2569(t *testing.T) {
	program := aggBaseProgram()
	prof := aggProfile()
	memo := NewWorldMemo[struct{}](program, prof, struct{}{}, aggBoundContext(program))
	deriv := memoDeriv(aggValidCert())
	if out := CheckWithWorldMemo(memo, memoClaim(), deriv); !out.IsAccept() {
		t.Fatalf("the loose limits: %s", out)
	}
	loose := prof.Limits
	prof.Limits.MaxCertFacts = 4 // the valid certificate seals five facts
	tightFresh := memoFresh(program, prof, memoClaim(), deriv)
	if tightFresh.IsAccept() {
		t.Fatal("control: the tighter limit must reject")
	}
	if got := CheckWithWorldMemo(memo, memoClaim(), deriv); got.String() != tightFresh.String() {
		t.Fatalf("tightened: the memo gave %s, the fresh check %s", got, tightFresh)
	}
	prof.Limits = loose
	if out := CheckWithWorldMemo(memo, memoClaim(), deriv); !out.IsAccept() {
		t.Fatalf("loosened again: %s", out)
	}
	if got := memo.CertificatesVerified(); got != 3 {
		t.Fatalf("each change of limits re-verifies: verified %d, want 3", got)
	}
}

func TestWorldMemoAMixedSequenceIsTheFreshSequence2569(t *testing.T) {
	program := aggBaseProgram()
	prof := aggProfile()
	memo := NewWorldMemo[struct{}](program, prof, struct{}{}, aggBoundContext(program))
	row := aggObs("o1", "p1", aggV("x"))
	positive := NewDerivation([]Node{LeafNode{Conc: row, Evidence: NoEvidence()}}, 0)
	valid := memoDeriv(aggValidCert())
	muts := memoMutations()
	tableRow, domain, pin := memoDeriv(muts[0].cert), memoDeriv(muts[1].cert), memoDeriv(muts[2].cert)
	steps := []struct {
		claim GroundLiteral
		deriv Derivation
	}{
		{memoClaim(), valid},    // miss 1
		{row, positive},         // no world: the slot is not touched
		{memoClaim(), valid},    // hit
		{memoClaim(), tableRow}, // miss 2
		{memoClaim(), valid},    // miss 3
		{row, positive},         // no world
		{memoClaim(), domain},   // miss 4
		{memoClaim(), domain},   // hit
		{memoClaim(), valid},    // miss 5
		{memoClaim(), pin},      // miss 6
		{memoClaim(), valid},    // miss 7
	}
	for i, s := range steps {
		got := CheckWithWorldMemo(memo, s.claim, s.deriv)
		if want := memoFresh(program, prof, s.claim, s.deriv); got.String() != want.String() {
			t.Fatalf("step %d: the memo gave %s, the fresh check %s", i, got, want)
		}
	}
	if out := memoFresh(program, prof, row, positive); !out.IsAccept() {
		t.Fatalf("control: the positive answer accepts, got %s", out)
	}
	if got := memo.CertificatesVerified(); got != 7 {
		t.Fatalf("seven misses, two hits, positive answers never evict: verified %d, want 7", got)
	}
}

// sharedUnderDeepCopy names every path in t that deepCopy (world_memo.go) would leave SHARED with
// the caller: an unexported field whose type reaches a slice, a map or a pointer. deepCopy cannot
// set an unexported field, so it copies it whole, and any container inside it keeps the caller's
// memory, which is the stale-hit hazard the copy exists to prevent. Exported fields are walked
// into. Interfaces are not: their dynamic values (Term, core.Value) are immutable by contract, and
// no type walk can see them. visited counts the struct types reached, so an empty result can be
// told from a walk that never got anywhere.
func sharedUnderDeepCopy(t reflect.Type, path string, seen map[reflect.Type]bool, visited *int) []string {
	switch t.Kind() {
	case reflect.Slice, reflect.Array, reflect.Pointer:
		return sharedUnderDeepCopy(t.Elem(), path+"[]", seen, visited)
	case reflect.Map:
		out := sharedUnderDeepCopy(t.Key(), path+"{key}", seen, visited)
		return append(out, sharedUnderDeepCopy(t.Elem(), path+"{value}", seen, visited)...)
	case reflect.Struct:
		if seen[t] {
			return nil
		}
		seen[t] = true
		*visited++
		var out []string
		for i := 0; i < t.NumField(); i++ {
			f := t.Field(i)
			at := path + "." + f.Name
			if !f.IsExported() {
				if reachesContainer(f.Type, map[reflect.Type]bool{}) {
					out = append(out, at+" ("+f.Type.String()+")")
				}
				continue
			}
			out = append(out, sharedUnderDeepCopy(f.Type, at, seen, visited)...)
		}
		return out
	}
	return nil
}

// reachesContainer reports whether a value of type t holds a slice, a map or a pointer, directly or
// inside an array or struct (not through an interface; see sharedUnderDeepCopy).
func reachesContainer(t reflect.Type, seen map[reflect.Type]bool) bool {
	switch t.Kind() {
	case reflect.Slice, reflect.Map, reflect.Pointer:
		return true
	case reflect.Array:
		return reachesContainer(t.Elem(), seen)
	case reflect.Struct:
		if seen[t] {
			return false
		}
		seen[t] = true
		for i := 0; i < t.NumField(); i++ {
			if reachesContainer(t.Field(i).Type, seen) {
				return true
			}
		}
	}
	return false
}

// seat:caa's condition on #2598: deepCopy's correctness rests on no container being reachable only
// through an unexported field of a certificate. It holds today; this keeps it held. The mutation
// control first: a type with an unexported slice, and one hiding a slice inside an unexported
// struct field, must both be named, or the walk proves nothing about ClosedModelCert.
func TestWorldMemoDeepCopyReachesEveryContainer2569(t *testing.T) {
	type hiddenInner struct{ bytes []byte }
	type probe struct {
		Rows   []GroundLiteral
		hidden []int
		inner  hiddenInner
		n      int
		label  string
	}
	var probeVisited int
	got := sharedUnderDeepCopy(reflect.TypeOf(probe{}), "probe", map[reflect.Type]bool{}, &probeVisited)
	want := []string{"probe.hidden ([]int)", "probe.inner (contract.hiddenInner)"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("control: the walk named %v, want %v", got, want)
	}

	var visited int
	shared := sharedUnderDeepCopy(reflect.TypeOf(ClosedModelCert{}), "ClosedModelCert", map[reflect.Type]bool{}, &visited)
	if len(shared) != 0 {
		t.Fatalf("deepCopy would leave these shared with the caller (unexported, reaching a container): %v", shared)
	}
	if visited < 8 {
		t.Fatalf("the walk reached only %d struct types under ClosedModelCert: it did not get far enough to mean anything", visited)
	}
}
