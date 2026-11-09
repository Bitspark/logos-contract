package typed_test

import (
	"reflect"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/typed"
)

// External-package qualification of declaration/proof composition, independent
// of the TextBox/Page fixtures. The observation and logical contribution use only
// public constructors. This test owns their explicit selection and the requested
// statement; the unchanged checker owns formation, conversion and acceptance.
func TestIndependentPublicTypedComposition(t *testing.T) {
	policy := typed.Policy{Foundation: typed.Foundation, Checker: typed.Checker}
	theoremType, theoremProof := predicateTransport()
	theoremResult := typed.Check(typed.Statement{
		Foundation: typed.Foundation, Expected: theoremType,
	}, theoremProof, policy, typed.DefaultLimits())
	theorem, ok := theoremResult.Accepted()
	if !ok {
		t.Fatalf("transport theorem: %s/%s (%s)", theoremResult.Status(), theoremResult.Code(), theoremResult.Detail())
	}
	if len(theorem.Dependencies()) != 0 {
		t.Fatal("derived transport unexpectedly relies on assumptions")
	}

	observation := observationAtZero("fixture.measurement")
	other := observationAtZero("fixture.other-measurement")
	declarations := append([]typed.Declaration(nil), observation.declarations...)
	declarations = append(declarations, other.declarations...)
	// Reuse by checked definition, never by assuming an earlier accepted report.
	declarations = append(declarations, typed.Define("fixture.transport", theorem.Statement().Expected, theorem.Candidate()))
	policy.Dependencies = append([]string(nil), observation.dependencies...)
	// The receiver chooses a computed index. The transport contribution does not
	// inspect its representation or learn the observation predicate's identity.
	computedZero := typed.NatElim(
		typed.Lam(typed.Nat(), typed.Nat()), typed.Zero(),
		typed.Lam(typed.Nat(), typed.Lam(typed.Nat(), typed.Var(0))),
		typed.Succ(typed.Succ(typed.Zero())),
	)
	expected := typed.App(observation.predicate, computedZero)
	s := typed.Statement{Foundation: typed.Foundation, Declarations: declarations, Expected: expected}
	proof := applyTransport(typed.Const("fixture.transport"), typed.Nat(), observation.predicate,
		typed.Zero(), computedZero, typed.Refl(typed.Nat(), typed.Zero()), observation.witness)
	result := typed.Check(s, proof, policy, typed.DefaultLimits())
	accepted, ok := result.Accepted()
	if !ok {
		t.Fatalf("composition: %s/%s (%s)", result.Status(), result.Code(), result.Detail())
	}
	if !reflect.DeepEqual(accepted.Statement().Expected, expected) || !reflect.DeepEqual(accepted.Candidate(), proof) {
		t.Fatal("composition lost the receiver's exact statement or candidate")
	}
	if !reflect.DeepEqual(accepted.Dependencies(), observation.dependencies) {
		t.Fatalf("wrong composed basis: %v", accepted.Dependencies())
	}

	// A further application consumes the composed proof through the same contract.
	nested := applyTransport(typed.Const("fixture.transport"), typed.Nat(), observation.predicate,
		computedZero, typed.Zero(), typed.Refl(typed.Nat(), typed.Zero()), accepted.Candidate())
	nestedStatement := s
	nestedStatement.Expected = typed.App(observation.predicate, typed.Zero())
	nestedResult := typed.Check(nestedStatement, nested, policy, typed.DefaultLimits())
	nestedAccepted, ok := nestedResult.Accepted()
	if !ok || !reflect.DeepEqual(nestedAccepted.Dependencies(), observation.dependencies) {
		t.Fatalf("nested composition: %s/%s", nestedResult.Status(), nestedResult.Code())
	}

	check := func(t *testing.T, statement typed.Statement, candidate typed.Expr, currentPolicy typed.Policy, limits typed.Limits, status typed.Status, code typed.Code) {
		t.Helper()
		outcome := typed.Check(statement, candidate, currentPolicy, limits)
		if outcome.Status() != status || outcome.Code() != code {
			t.Fatalf("got %s/%s (%s), want %s/%s", outcome.Status(), outcome.Code(), outcome.Detail(), status, code)
		}
		if _, minted := outcome.Accepted(); minted {
			t.Fatal("failed composition minted acceptance")
		}
	}
	t.Run("different-subject", func(t *testing.T) {
		wrong := s
		wrong.Expected = typed.App(other.predicate, computedZero)
		check(t, wrong, proof, policy, typed.DefaultLimits(), typed.InvalidStatus, typed.TypeMismatch)
	})
	t.Run("wrong-equality", func(t *testing.T) {
		wrong := s
		wrong.Expected = typed.App(observation.predicate, typed.Succ(typed.Zero()))
		candidate := applyTransport(typed.Const("fixture.transport"), typed.Nat(), observation.predicate,
			typed.Zero(), typed.Succ(typed.Zero()), typed.Refl(typed.Nat(), typed.Zero()), observation.witness)
		check(t, wrong, candidate, policy, typed.DefaultLimits(), typed.InvalidStatus, typed.TypeMismatch)
	})
	t.Run("withdrawn-observation", func(t *testing.T) {
		narrow := policy
		narrow.Dependencies = []string{observation.dependencies[0]}
		check(t, s, accepted.Candidate(), narrow, typed.DefaultLimits(), typed.UnsupportedStatus, typed.UnadmittedDependency)
	})
	t.Run("missing-contribution", func(t *testing.T) {
		missing := s
		missing.Declarations = declarations[:len(declarations)-1]
		check(t, missing, proof, policy, typed.DefaultLimits(), typed.InvalidStatus, typed.UnknownConstant)
	})
	t.Run("changed-definition", func(t *testing.T) {
		changed := s
		changed.Declarations = append([]typed.Declaration(nil), declarations...)
		changed.Declarations[len(declarations)-1] = typed.Define("fixture.transport", theoremType, typed.Zero())
		check(t, changed, proof, policy, typed.DefaultLimits(), typed.InvalidStatus, typed.TypeMismatch)
	})
	t.Run("bounded-checking", func(t *testing.T) {
		limits := typed.DefaultLimits()
		limits.Work = 0
		check(t, s, proof, policy, limits, typed.IncompleteStatus, typed.Work)
	})
}
