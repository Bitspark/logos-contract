package typed

import (
	"reflect"
	"testing"
)

func trusted(dependencies ...string) Policy {
	return Policy{Foundation: Foundation, Checker: Checker, Dependencies: dependencies}
}

func statement(expected Expr, declarations ...Declaration) Statement {
	return Statement{Foundation: Foundation, Declarations: declarations, Expected: expected}
}

func require(t *testing.T, result Outcome, status Status, code Code) {
	t.Helper()
	if result.Status() != status || result.Code() != code {
		t.Fatalf("got %s/%s (%s) at %+v, want %s/%s", result.Status(), result.Code(), result.Detail(), result.Location(), status, code)
	}
}

func TestFoundationRules(t *testing.T) {
	identity := Lam(Nat(), Var(0))
	pairType := Sigma(Nat(), ID(Nat(), Var(0), Var(0)))
	pair := Pair(pairType, Zero(), Refl(Nat(), Zero()))
	motive := Lam(Nat(), Nat())
	step := Lam(Nat(), Lam(Nat(), Succ(Var(0))))
	cases := []struct {
		name       string
		typ, proof Expr
	}{
		{"identity", Pi(Nat(), Nat()), identity},
		{"application", Nat(), App(identity, Succ(Zero()))},
		{"dependent-pair", pairType, pair},
		{"dependent-second", ID(Nat(), Fst(pair), Fst(pair)), Snd(pair)},
		{"nat-elimination", Nat(), NatElim(motive, Zero(), step, Succ(Succ(Zero())))},
		{"bool-elimination", Nat(), BoolElim(Lam(Bool(), Nat()), Zero(), Succ(Zero()), True())},
		{"transport", Nat(), Transport(Nat(), Zero(), Zero(), Refl(Nat(), Zero()), motive, Succ(Zero()))},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			require(t, Check(statement(c.typ), c.proof, trusted(), DefaultLimits()), AcceptedStatus, "")
		})
	}
}

func TestCaptureAvoidingSubstitution(t *testing.T) {
	// The inner lambda ignores its bool parameter and returns the free Nat from
	// the enclosing context. Substituting that free value must lift it under Bool.
	s := statement(Pi(Bool(), Nat()))
	s.Context = []Expr{Nat()}
	proof := App(Lam(Nat(), Lam(Bool(), Var(1))), Var(0))
	require(t, Check(s, proof, trusted(), DefaultLimits()), AcceptedStatus, "")
	wrong := App(Lam(Nat(), Lam(Bool(), Var(0))), Var(0))
	require(t, Check(s, wrong, trusted(), DefaultLimits()), InvalidStatus, TypeMismatch)
	closed := statement(Pi(Nat(), Nat()))
	require(t, Check(closed, Lam(Nat(), Var(1)), trusted(), DefaultLimits()), InvalidStatus, EscapedVariable)
}

func TestWrongEndpointsAndUniverseCapacity(t *testing.T) {
	proof := Transport(Nat(), Zero(), Succ(Zero()), Refl(Nat(), Zero()), Lam(Nat(), Nat()), Zero())
	require(t, Check(statement(Nat()), proof, trusted(), DefaultLimits()), InvalidStatus, TypeMismatch)
	require(t, Check(statement(Sort(MaxNatural)), Sort(MaxNatural-1), trusted(), DefaultLimits()), IncompleteStatus, UniverseCapacity)
	require(t, Check(statement(Sort(0)), Sort(0), trusted(), DefaultLimits()), InvalidStatus, TypeMismatch)
}

func TestReachableDependenciesAndCurrentPolicy(t *testing.T) {
	declarations := []Declaration{
		Assume("a", Nat(), "source.a"),
		Assume("unused", Nat(), "source.unused"),
		Define("a-definition", Nat(), Const("a")),
	}
	proof := App(Lam(Nat(), Zero()), Const("a-definition"))
	result := Check(statement(Nat(), declarations...), proof, trusted("source.a", "allowed.unused"), DefaultLimits())
	require(t, result, AcceptedStatus, "")
	accepted, ok := result.Accepted()
	if !ok || !reflect.DeepEqual(accepted.Dependencies(), []string{"source.a"}) {
		t.Fatalf("incorrect reachable basis: %v", accepted.Dependencies())
	}
	if !reflect.DeepEqual(accepted.UsedConstants(), []string{"a", "a-definition"}) {
		t.Fatalf("incorrect constants: %v", accepted.UsedConstants())
	}
	require(t, Check(statement(Nat(), declarations...), proof, trusted(), DefaultLimits()), UnsupportedStatus, UnadmittedDependency)
	// Unused declarations are still checked: a forward reference cannot hide in
	// an otherwise unused signature entry.
	bad := append(declarations, Define("bad", Nat(), Const("later")))
	result = Check(statement(Nat(), bad...), Zero(), trusted(), DefaultLimits())
	require(t, result, InvalidStatus, UnknownConstant)
	if result.Location() != (Location{Phase: DeclarationPhase, Index: 3, HasIndex: true}) {
		t.Fatal(result.Location())
	}
}

func TestStatementAndResultAreImmutable(t *testing.T) {
	deps := []string{"source"}
	d := Assume("a", Nat(), deps...)
	deps[0] = "changed-before-check"
	s := statement(Nat(), d)
	proof := Const("a")
	policy := trusted("source", "unused", "unused")
	result := Check(s, proof, policy, DefaultLimits())
	require(t, result, AcceptedStatus, "")
	a, _ := result.Accepted()
	policy.Dependencies[0] = "changed-after-check"
	policy.Foundation = "other-foundation"
	policyView := a.Policy()
	policyView.Dependencies[0] = "changed-returned-policy"
	policyView.Checker = "other-checker"
	admitted := a.Policy()
	if admitted.Foundation != Foundation || admitted.Checker != Checker || !reflect.DeepEqual(admitted.Dependencies, []string{"source", "unused", "unused"}) {
		t.Fatal("accepted policy was mutated")
	}
	s.Declarations[0] = Assume("different", Bool(), "different")
	s.Expected = Bool()
	copy := a.Statement()
	copy.Declarations[0] = d
	copy.Expected = Bool()
	copy.Declarations[0].Dependencies()[0] = "tampered"
	got := a.Statement()
	if got.Expected.Kind() != NatKind || got.Declarations[0].Name() != "a" || got.Declarations[0].Dependencies()[0] != "source" {
		t.Fatal("accepted statement was mutated")
	}
	returnedDeps := a.Dependencies()
	returnedDeps[0] = "tampered"
	if a.Dependencies()[0] != "source" {
		t.Fatal("dependency slice escaped")
	}
	if (Outcome{}).IsAccepted() {
		t.Fatal("zero outcome accepted")
	}
	if _, ok := (Outcome{}).Accepted(); ok {
		t.Fatal("zero outcome minted acceptance")
	}
	if (&Acceptance{}).Valid() || (&Acceptance{}).Foundation() != "" {
		t.Fatal("zero acceptance appeared minted")
	}
}

func TestIdentityBytesConsumeWorkBeforeScanning(t *testing.T) {
	// The string already exists as caller input. Check must refuse its byte cost
	// before UTF-8 scanning or inserting it into a signature map.
	name := make([]byte, 2048)
	for i := range name {
		name[i] = 'a'
	}
	limits := DefaultLimits()
	limits.NameBytes = 4096
	limits.Work = 100
	require(t, Check(statement(Nat(), Assume(string(name), Nat(), "source")), Zero(), trusted("source"), limits), IncompleteStatus, Work)
}

func TestMalformedAndResourceOutcomes(t *testing.T) {
	require(t, Check(statement(Nat()), Expr{}, trusted(), DefaultLimits()), InvalidStatus, MalformedInput)
	require(t, Check(statement(Nat(), Declaration{}), Zero(), trusted(), DefaultLimits()), InvalidStatus, EmptyConstantName)
	cycle := &expression{kind: SuccKind}
	cycle.args = []Expr{{cycle}}
	require(t, Check(statement(Nat()), Expr{cycle}, trusted(), DefaultLimits()), InvalidStatus, MalformedInput)
	wrong := Expr{&expression{kind: NatKind, args: []Expr{Zero()}}}
	require(t, Check(statement(Nat()), wrong, trusted(), DefaultLimits()), InvalidStatus, MalformedInput)
	for _, test := range []struct {
		code   Code
		change func(*Limits)
	}{
		{InputNodes, func(l *Limits) { l.InputNodes = 0 }},
		{InputDepth, func(l *Limits) { l.InputDepth = 0 }},
		{NameBytes, func(l *Limits) { l.NameBytes = 0 }},
		{Work, func(l *Limits) { l.Work = 0 }},
		{Depth, func(l *Limits) { l.Depth = 0 }},
	} {
		limits := DefaultLimits()
		test.change(&limits)
		require(t, Check(statement(Nat()), Zero(), trusted(), limits), IncompleteStatus, test.code)
	}
	limits := DefaultLimits()
	limits.CollectionEntries = 0
	require(t, Check(statement(Nat(), Assume("a", Nat(), "source")), Zero(), trusted(), limits), IncompleteStatus, CollectionEntries)
	deep := Nat()
	for i := 0; i < 140; i++ {
		deep = Pi(Nat(), deep)
	}
	limits = DefaultLimits()
	limits.InputDepth = MaxNatural
	require(t, Check(statement(deep), Zero(), trusted(), limits), IncompleteStatus, InputDepth)
	require(t, Check(statement(Nat(), Assume("a", Nat())), Zero(), trusted(), DefaultLimits()), InvalidStatus, MissingAssumptions)
}

func TestExpectedAndCandidateLocations(t *testing.T) {
	badExpected := Check(statement(Zero()), Zero(), trusted(), DefaultLimits())
	require(t, badExpected, InvalidStatus, ExpectedUniverse)
	if badExpected.Location().Phase != ExpectedPhase {
		t.Fatal(badExpected.Location())
	}
	badProof := Check(statement(Nat()), True(), trusted(), DefaultLimits())
	require(t, badProof, InvalidStatus, TypeMismatch)
	if badProof.Location().Phase != CandidatePhase {
		t.Fatal(badProof.Location())
	}
	p := trusted()
	p.Checker = "another-checker"
	require(t, Check(statement(Nat()), Zero(), p, DefaultLimits()), UnsupportedStatus, UnadmittedChecker)
}

func TestIdentitiesUseExactUTF8AndDependenciesUseByteOrder(t *testing.T) {
	// These names look alike but have different UTF-8 encodings. The dependency
	// order below also distinguishes UTF-8 ordering from UTF-16 code-unit order.
	composed, decomposed := "\u00e9", "e\u0301"
	first, second := "\ue000", "\U00010000"
	pairType := Sigma(Nat(), Nat())
	s := statement(pairType,
		Assume(composed, Nat(), second),
		Assume(decomposed, Nat(), first),
	)
	proof := Pair(pairType, Const(composed), Const(decomposed))
	policy := trusted(second, first, first)
	result := Check(s, proof, policy, DefaultLimits())
	require(t, result, AcceptedStatus, "")
	a, _ := result.Accepted()
	if !reflect.DeepEqual(a.Dependencies(), []string{first, second}) {
		t.Fatalf("wrong byte order: %q", a.Dependencies())
	}
	if len(a.UsedConstants()) != 2 {
		t.Fatal("normalized distinct identities")
	}
	limits := DefaultLimits()
	limits.CollectionEntries = 6 // two declarations + two basis entries + three policy entries
	require(t, Check(s, proof, policy, limits), IncompleteStatus, CollectionEntries)
	invalidName := string([]byte{0xff})
	require(t, Check(statement(Nat(), Assume(invalidName, Nat(), "basis")), Zero(), trusted("basis"), DefaultLimits()), InvalidStatus, MalformedInput)
	require(t, Check(statement(Nat()), Var(MaxNatural), trusted(), DefaultLimits()), InvalidStatus, EscapedVariable)
}

func TestRepeatedChecksHaveDeterministicWorkAtAcceptanceBoundary(t *testing.T) {
	dependencies := []string{"z", "a-longer", "m", "c-much-longer", "b", "n-third", "q", "r-fourth"}
	s := statement(Nat(), Assume("value", Nat(), dependencies...))
	p := trusted(dependencies...)
	proof := Const("value")
	baseline := Check(s, proof, p, DefaultLimits())
	require(t, baseline, AcceptedStatus, "")
	for _, work := range []uint32{baseline.Steps(), baseline.Steps() - 1} {
		limits := DefaultLimits()
		limits.Work = work
		first := Check(s, proof, p, limits)
		if work == baseline.Steps() {
			require(t, first, AcceptedStatus, "")
		} else {
			require(t, first, IncompleteStatus, Work)
		}
		for i := 0; i < 100; i++ {
			actual := Check(s, proof, p, limits)
			if actual.Status() != first.Status() || actual.Code() != first.Code() || actual.Steps() != first.Steps() || actual.Location() != first.Location() {
				t.Fatalf("repeat %d changed %s/%s work %d to %s/%s work %d", i, first.Status(), first.Code(), first.Steps(), actual.Status(), actual.Code(), actual.Steps())
			}
		}
	}
}

func TestMapReservationsHaveDeterministicExhaustion(t *testing.T) {
	set := map[string]struct{}{"z": {}, "a-longer": {}, "m": {}, "c-much-longer": {}, "b": {}, "n-third": {}, "q": {}, "r-fourth": {}}
	for i := 0; i < 100; i++ {
		// Metadata fits but aggregate identity cost does not. No partially
		// consumed name may make the reported work depend on map iteration.
		b := &budget{remaining: 20}
		if mergeNames(make(map[string]struct{}), set, b) || b.err == nil || b.err.code != Work || b.spent != uint32(len(set)) {
			t.Fatalf("nondeterministic closure exhaustion: %+v", b)
		}
		b = &budget{remaining: 20}
		if sortedKeys(set, b) != nil || b.err == nil || b.err.code != Work || b.spent != uint32(len(set)) {
			t.Fatalf("nondeterministic sort exhaustion: %+v", b)
		}
	}
}
