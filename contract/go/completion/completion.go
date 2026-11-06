// Package completion is the completion algebra: an outcome that keeps "established false" apart
// from "did not finish", and the three-valued Not/And/Or over it (research 0031 row 15, #3164).
// It is PROPOSED: additive, and ratified by the ADR for research 0030 and 0031 (#3147). Since #3126
// the Theory SPI answers through it: a theory's DecideGround returns a TheoryGround, and checker SPI
// v2 (ADR 0036 D8) makes that method required. The Rust original is
// contract/rs/src/completion.rs, which carries the full rationale; this is its Go twin, and
// vectors/completion_algebra.json pins all three cores.
//
// A decider that stops before it establishes a fact must not report that fact as false. A
// Completion is Completed(value), LimitExceeded(limit) or NotCompleted(cause). A ground literal's
// outcome is a GroundOutcome, Completion[Decision, L], where a Decision is Holds or Fails(code).
// The layer that sets a caller's limit owns its vocabulary, so the algebra is generic over L and
// only carries it.
//
// A non-completion is a STOP or a FAULT (seat:caa's ruling on #3179). A stop's evidence is only
// incomplete, so it carries the scope its effect reaches: capacity, work_cap and instantiation at
// any scope, host_refusal and reply_unreadable at request scope only. A fault (inconsistent_theory,
// malformed_outcome) says the evidence is invalid and carries no scope. NewCause refuses any other
// pair.
//
// Not, And and Or are strong Kleene (¬U = U, F ∧ U = F, H ∨ U = H), with scoped absorption: a stop
// local to one literal, branch or enumeration may be absorbed by an independently decided operand,
// but a stop at dependency, theory-snapshot or request scope, and a caller's limit, are dominant
// and never absorbed, and a fault outranks even those. And/Or return the operand of the highest
// class, the leftmost on a tie:
//
//	and   Holds < absorbable stop < Fails < dominant stop or limit < fault
//	or    Fails < absorbable stop < Holds < dominant stop or limit < fault
//
// Go values have a zero state, and research 0031 requires that it is never read as an answer. Every
// type here has an invalid zero value, and every eliminator (Match, MatchOutcome, Not, And, Or)
// reports a value no constructor could have built (a zero value, an unknown code, a fault with a
// scope, a stop without one) as the fault malformed_outcome: never a logical answer.
package completion

import "fmt"

// CauseScope is how far a stop's effect reaches, which decides whether another operand may absorb
// it.
type CauseScope uint8

const (
	// NoScope is the absent scope: a fault's, and the zero value.
	NoScope CauseScope = iota
	// ScopeLiteral: one ground literal's decision stopped.
	ScopeLiteral
	// ScopeBranch: one alternative of a search or a disjunction stopped.
	ScopeBranch
	// ScopeEnumeration: an enumeration inside one literal stopped.
	ScopeEnumeration
	// ScopeDependency: a lower certificate or table this result depends on was not established.
	ScopeDependency
	// ScopeTheorySnapshot: the theory's snapshot could not be read completely.
	ScopeTheorySnapshot
	// ScopeRequest: the whole request stopped.
	ScopeRequest
)

// Absorbable reports whether a stop at this scope may be absorbed by an independently established
// operand. Only a stop local to one literal, branch or enumeration can.
func (s CauseScope) Absorbable() bool {
	switch s {
	case ScopeLiteral, ScopeBranch, ScopeEnumeration:
		return true
	case ScopeDependency, ScopeTheorySnapshot, ScopeRequest, NoScope:
		return false
	default:
		return false
	}
}

// Tag is the scope's stable name, as vectors/completion_algebra.json spells it; "" for NoScope or
// an unknown scope.
func (s CauseScope) Tag() string {
	switch s {
	case ScopeLiteral:
		return "literal"
	case ScopeBranch:
		return "branch"
	case ScopeEnumeration:
		return "enumeration"
	case ScopeDependency:
		return "dependency"
	case ScopeTheorySnapshot:
		return "theory_snapshot"
	case ScopeRequest:
		return "request"
	case NoScope:
		return ""
	default:
		return ""
	}
}

// NonCompletionKind is why a producer did not decide. The zero value is invalid.
type NonCompletionKind uint8

const (
	kindInvalid NonCompletionKind = iota
	// KindCapacity: a stop, an implementation capacity such as native stack depth. Any scope.
	KindCapacity
	// KindWorkCap: a stop, an internal bounded-work cap the language does not define as failure.
	// Any scope.
	KindWorkCap
	// KindInstantiation: a stop, an argument not instantiated enough for the decider. Any scope.
	KindInstantiation
	// KindHostRefusal: a stop, a host refused to answer. Request scope: the refusal channel is
	// sticky for the run.
	KindHostRefusal
	// KindReplyUnreadable: a stop, a host's reply could not be read. Request scope.
	KindReplyUnreadable
	// KindInconsistentTheory: a fault, a decider disowned a literal it was routed.
	KindInconsistentTheory
	// KindMalformedOutcome: a fault, a value no constructor could have built.
	KindMalformedOutcome
)

// IsFault reports whether the kind is a fault: the evidence is invalid, not merely incomplete.
func (k NonCompletionKind) IsFault() bool {
	switch k {
	case KindInconsistentTheory, KindMalformedOutcome:
		return true
	case KindCapacity, KindWorkCap, KindInstantiation, KindHostRefusal, KindReplyUnreadable, kindInvalid:
		return false
	default:
		return false
	}
}

// Tag is the kind's stable name, as vectors/completion_algebra.json spells it; "" if invalid.
func (k NonCompletionKind) Tag() string {
	switch k {
	case KindCapacity:
		return "capacity"
	case KindWorkCap:
		return "work_cap"
	case KindInstantiation:
		return "instantiation"
	case KindHostRefusal:
		return "host_refusal"
	case KindReplyUnreadable:
		return "reply_unreadable"
	case KindInconsistentTheory:
		return "inconsistent_theory"
	case KindMalformedOutcome:
		return "malformed_outcome"
	case kindInvalid:
		return ""
	default:
		return ""
	}
}

// NonCompletion is why a producer did not decide: a stop with the scope its effect reaches, or a
// fault. The zero value is invalid.
type NonCompletion struct {
	kind  NonCompletionKind
	scope CauseScope
}

// legal reports whether a kind and scope form a NonCompletion.
func legal(kind NonCompletionKind, scope CauseScope) bool {
	switch kind {
	case KindCapacity, KindWorkCap, KindInstantiation:
		return scope.Tag() != ""
	case KindHostRefusal, KindReplyUnreadable:
		return scope == ScopeRequest
	case KindInconsistentTheory, KindMalformedOutcome:
		return scope == NoScope
	case kindInvalid:
		return false
	default:
		return false
	}
}

// NewCause is the checked constructor, for a decoder: the cause a kind and scope name (NoScope for
// a fault), or an error naming the pair when they do not form one: a fault with a scope, a
// request-wide stop at a narrower scope, or a stop without one.
func NewCause(kind NonCompletionKind, scope CauseScope) (NonCompletion, error) {
	if !legal(kind, scope) {
		return NonCompletion{}, fmt.Errorf("illegal_cause: kind %d (%q) at scope %d (%q)", kind, kind.Tag(), scope, scope.Tag())
	}
	return NonCompletion{kind: kind, scope: scope}, nil
}

// Capacity is a capacity stop reaching scope. An absent or unknown scope yields a value every
// eliminator reads as malformed; NewCause refuses it instead.
func Capacity(scope CauseScope) NonCompletion { return NonCompletion{kind: KindCapacity, scope: scope} }

// WorkCap is a bounded-work stop reaching scope, with Capacity's rule for a bad scope.
func WorkCap(scope CauseScope) NonCompletion { return NonCompletion{kind: KindWorkCap, scope: scope} }

// Instantiation is an instantiation stop reaching scope, with Capacity's rule for a bad scope.
func Instantiation(scope CauseScope) NonCompletion {
	return NonCompletion{kind: KindInstantiation, scope: scope}
}

// HostRefusal is a host refusal, request-wide.
func HostRefusal() NonCompletion { return NonCompletion{kind: KindHostRefusal, scope: ScopeRequest} }

// ReplyUnreadable is an unreadable host reply, request-wide.
func ReplyUnreadable() NonCompletion {
	return NonCompletion{kind: KindReplyUnreadable, scope: ScopeRequest}
}

// InconsistentTheory is the fault that a theory contradicts its own routing.
func InconsistentTheory() NonCompletion { return NonCompletion{kind: KindInconsistentTheory} }

// MalformedOutcome is the fault that a value is none a constructor could have built.
func MalformedOutcome() NonCompletion { return NonCompletion{kind: KindMalformedOutcome} }

// Kind is why the producer did not decide.
func (c NonCompletion) Kind() NonCompletionKind { return c.kind }

// Scope is how far a stop reaches; NoScope for a fault, whose reach is everything.
func (c NonCompletion) Scope() CauseScope { return c.scope }

func (c NonCompletion) valid() bool { return legal(c.kind, c.scope) }

// malformed is how every eliminator reports a value no constructor could have built.
var malformed = NonCompletion{kind: KindMalformedOutcome}

// FalseCode is why the language says a literal is false. No conversion from a NonCompletion
// exists. The zero value is invalid.
type FalseCode uint8

const (
	falseCodeInvalid FalseCode = iota
	// FalseUnsatisfied: the relation was evaluated and does not hold.
	FalseUnsatisfied
)

// Tag is the code's stable name, as vectors/completion_algebra.json spells it; "" if invalid.
func (c FalseCode) Tag() string {
	switch c {
	case FalseUnsatisfied:
		return "unsatisfied"
	case falseCodeInvalid:
		return ""
	default:
		return ""
	}
}

type decisionArm uint8

const (
	decisionInvalid decisionArm = iota
	decisionHolds
	decisionFails
)

// Decision is the language's decision on a ground literal: Holds, or Fails with a code. The zero
// value is invalid.
type Decision struct {
	arm  decisionArm
	code FalseCode
}

// Holds is the decision that the literal holds.
func Holds() Decision { return Decision{arm: decisionHolds} }

// Fails is the decision that the literal is false, for the reason code gives.
func Fails(code FalseCode) Decision { return Decision{arm: decisionFails, code: code} }

func (d Decision) valid() bool {
	switch d.arm {
	case decisionHolds:
		return d.code == falseCodeInvalid
	case decisionFails:
		return d.code.Tag() != ""
	case decisionInvalid:
		return false
	default:
		return false
	}
}

type completionArm uint8

const (
	armInvalid completionArm = iota
	armCompleted
	armLimitExceeded
	armNotCompleted
)

// Completion is a producer's result: the value, a caller's limit reached, or a stop before the
// value was established. L is the caller's limit vocabulary. The zero value is invalid.
type Completion[T, L any] struct {
	arm   completionArm
	value T
	limit L
	cause NonCompletion
}

// Completed is the result that the value was established.
func Completed[T, L any](value T) Completion[T, L] {
	return Completion[T, L]{arm: armCompleted, value: value}
}

// LimitExceeded is the result that a caller's limit was reached.
func LimitExceeded[T, L any](limit L) Completion[T, L] {
	return Completion[T, L]{arm: armLimitExceeded, limit: limit}
}

// NotCompleted is the result that the producer did not establish the value.
func NotCompleted[T, L any](cause NonCompletion) Completion[T, L] {
	return Completion[T, L]{arm: armNotCompleted, cause: cause}
}

// Cases eliminates a Completion. Adding an arm adds a method, so every implementation must
// change: the closed-enumeration guarantee a Go type switch does not give.
type Cases[T, L, R any] interface {
	Completed(value T) R
	LimitExceeded(limit L) R
	NotCompleted(cause NonCompletion) R
}

// Match eliminates a Completion. A value no constructor could have built, or one carrying an
// illegal cause, reaches NotCompleted as the fault malformed_outcome.
func Match[T, L, R any](c Completion[T, L], cases Cases[T, L, R]) R {
	switch c.arm {
	case armCompleted:
		return cases.Completed(c.value)
	case armLimitExceeded:
		return cases.LimitExceeded(c.limit)
	case armNotCompleted:
		if c.cause.valid() {
			return cases.NotCompleted(c.cause)
		}
		return cases.NotCompleted(malformed)
	case armInvalid:
		return cases.NotCompleted(malformed)
	default:
		return cases.NotCompleted(malformed)
	}
}

// GroundOutcome is a ground literal's outcome: decided true or false, a caller's limit, or not
// decided.
type GroundOutcome[L any] = Completion[Decision, L]

// OutcomeCases eliminates a GroundOutcome, one method per case.
type OutcomeCases[L, R any] interface {
	Holds() R
	Fails(code FalseCode) R
	LimitExceeded(limit L) R
	NotCompleted(cause NonCompletion) R
}

// MatchOutcome eliminates a GroundOutcome. A value no constructor could have built reaches
// NotCompleted as the fault malformed_outcome.
func MatchOutcome[L, R any](o GroundOutcome[L], cases OutcomeCases[L, R]) R {
	o = normalize(o)
	switch o.arm {
	case armCompleted:
		if o.value.arm == decisionHolds {
			return cases.Holds()
		}
		return cases.Fails(o.value.code)
	case armLimitExceeded:
		return cases.LimitExceeded(o.limit)
	case armNotCompleted:
		return cases.NotCompleted(o.cause)
	case armInvalid:
		return cases.NotCompleted(malformed)
	default:
		return cases.NotCompleted(malformed)
	}
}

// normalize maps a value no constructor could have built to NotCompleted(malformed_outcome), and
// returns every valid value unchanged.
func normalize[L any](o GroundOutcome[L]) GroundOutcome[L] {
	switch o.arm {
	case armCompleted:
		if o.value.valid() {
			return o
		}
	case armLimitExceeded:
		return o
	case armNotCompleted:
		if o.cause.valid() {
			return o
		}
	case armInvalid:
	default:
	}
	return NotCompleted[Decision, L](malformed)
}

// class orders the operands And and Or choose between.
type class uint8

const (
	classHolds class = iota
	classFails
	classAbsorbable
	classDominant
	classFault
)

// classOf is the class of a normalized outcome.
func classOf[L any](o GroundOutcome[L]) class {
	switch o.arm {
	case armCompleted:
		if o.value.arm == decisionHolds {
			return classHolds
		}
		return classFails
	case armNotCompleted:
		if o.cause.kind.IsFault() {
			return classFault
		}
		if o.cause.scope.Absorbable() {
			return classAbsorbable
		}
		return classDominant
	case armLimitExceeded:
		return classDominant
	case armInvalid:
		return classFault
	default:
		return classFault
	}
}

func andRank(c class) int {
	switch c {
	case classHolds:
		return 0
	case classAbsorbable:
		return 1
	case classFails:
		return 2
	case classDominant:
		return 3
	case classFault:
		return 4
	default:
		return 4
	}
}

func orRank(c class) int {
	switch c {
	case classFails:
		return 0
	case classAbsorbable:
		return 1
	case classHolds:
		return 2
	case classDominant:
		return 3
	case classFault:
		return 4
	default:
		return 4
	}
}

// higher returns the operand of the higher rank, a on a tie.
func higher[L any](a, b GroundOutcome[L], rank func(class) int) GroundOutcome[L] {
	a, b = normalize(a), normalize(b)
	if rank(classOf(b)) > rank(classOf(a)) {
		return b
	}
	return a
}

// Not is strong-Kleene negation: ¬H = F, ¬F = H, and an undecided outcome or a limit is returned
// unchanged (¬U = U).
func Not[L any](a GroundOutcome[L]) GroundOutcome[L] {
	a = normalize(a)
	switch classOf(a) {
	case classHolds:
		return Completed[Decision, L](Fails(FalseUnsatisfied))
	case classFails:
		return Completed[Decision, L](Holds())
	case classAbsorbable, classDominant, classFault:
		return a
	default:
		return a
	}
}

// And is strong-Kleene conjunction with scoped absorption: F ∧ U = F only when U is an absorbable
// stop; a dominant stop or a limit is never absorbed, and a fault outranks both. It returns the
// higher-class operand, a on a tie.
func And[L any](a, b GroundOutcome[L]) GroundOutcome[L] { return higher(a, b, andRank) }

// Or is strong-Kleene disjunction with scoped absorption: H ∨ U = H only when U is an absorbable
// stop; a dominant stop or a limit is never absorbed, and a fault outranks both. It returns the
// higher-class operand, a on a tie.
func Or[L any](a, b GroundOutcome[L]) GroundOutcome[L] { return higher(a, b, orRank) }

// TheoryDecision is a theory's decision on a ground literal (#3126, seat:caa's ruling (C)): what a
// theory's DecideGround returns inside a Completion. Two vocabularies, each with one owner:
// FalseCode is the LANGUAGE's closed vocabulary, and the combinators fold over it; a theory's Fails
// code is an OPEN value space every theory and consumer owns, and check carries it as the
// builtin_failed detail. So the theory's code rides here as data, and DecisionOf is the one way into
// the algebra. Rust's completion::TheoryDecision. The zero value is invalid.
type TheoryDecision struct {
	arm  decisionArm
	code string
}

// TheoryHolds is the theory's decision that the atom holds.
func TheoryHolds() TheoryDecision { return TheoryDecision{arm: decisionHolds} }

// TheoryFails is the theory's decision that the atom does not hold; code is the theory's own name
// for why.
func TheoryFails(code string) TheoryDecision { return TheoryDecision{arm: decisionFails, code: code} }

// NoCallerLimit is the limit vocabulary of a producer no caller's limit reaches (Rust's
// uninhabited engine::NoCallerLimit). Go cannot express an empty type, so every eliminator here
// reads a LimitExceeded over it as the fault malformed_outcome: no constructor a theory is meant to
// call builds one.
type NoCallerLimit struct{}

// TheoryGround is what a theory's DecideGround returns: its decision, or not completed.
type TheoryGround = Completion[TheoryDecision, NoCallerLimit]

// TheoryCases eliminates a theory's answer, one method per case.
type TheoryCases[L, R any] interface {
	Holds() R
	Fails(code string) R
	LimitExceeded(limit L) R
	NotCompleted(cause NonCompletion) R
}

// MatchTheory eliminates a theory's answer. A value no constructor could have built reaches
// NotCompleted as the fault malformed_outcome.
func MatchTheory[L, R any](o Completion[TheoryDecision, L], cases TheoryCases[L, R]) R {
	switch o.arm {
	case armCompleted:
		switch o.value.arm {
		case decisionHolds:
			if o.value.code == "" {
				return cases.Holds()
			}
			return cases.NotCompleted(malformed)
		case decisionFails:
			return cases.Fails(o.value.code)
		case decisionInvalid:
			return cases.NotCompleted(malformed)
		default:
			return cases.NotCompleted(malformed)
		}
	case armLimitExceeded:
		return cases.LimitExceeded(o.limit)
	case armNotCompleted:
		if o.cause.valid() {
			return cases.NotCompleted(o.cause)
		}
		return cases.NotCompleted(malformed)
	case armInvalid:
		return cases.NotCompleted(malformed)
	default:
		return cases.NotCompleted(malformed)
	}
}

// DecisionOf is the ONE conversion from a theory's answer to the algebra's GroundOutcome (#3126,
// seat:caa's ruling (C)). A theory's false code is the theory's own, so it becomes the language's
// FalseUnsatisfied. A non-completion and a limit pass through unchanged: nothing here turns "not
// decided" into a decision. Every site that folds a theory's answer with Not/And/Or calls it; a
// reader that reports the theory's code (check's builtin_failed detail) reads the TheoryDecision
// before converting. Rust's completion::decision_of.
func DecisionOf[L any](o Completion[TheoryDecision, L]) GroundOutcome[L] {
	return MatchTheory[L, GroundOutcome[L]](o, decisionOfCases[L]{})
}

type decisionOfCases[L any] struct{}

func (decisionOfCases[L]) Holds() GroundOutcome[L] { return Completed[Decision, L](Holds()) }
func (decisionOfCases[L]) Fails(string) GroundOutcome[L] {
	return Completed[Decision, L](Fails(FalseUnsatisfied))
}
func (decisionOfCases[L]) LimitExceeded(limit L) GroundOutcome[L] {
	return LimitExceeded[Decision, L](limit)
}
func (decisionOfCases[L]) NotCompleted(cause NonCompletion) GroundOutcome[L] {
	return NotCompleted[Decision, L](cause)
}
