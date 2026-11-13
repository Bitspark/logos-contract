package contract

// completion.go — #3142 (research 0031 row 13; seat:caa's rulings on #3124 item 2, on #3142, and
// on #3189 Q3/Q4): whether a decider's Fails on a predicate it owns is always a decided false.
// The go form of Rust's DecisionCompletion and its defaulted Theory::completion.
//
// A decider that stops before it decides can surface the stop as Fails, and a closure check
// reads that false as knowledge, so a sealed table can miss a derivable row and still pass as
// exhaustive. #3313 landed the typed outcome channel (DecideGround), on which a stop is
// NotCompleted, never Fails. The certifying kernel refuses at admission every seal whose
// clauses reach a decider that does not declare DecisionStopsAreTyped: host builtins until the host's
// own decider declares its completion (#3506; #3374 typed only the guest's side, seat:caa's ruling on
// #3390), and any decider on the v1 Decide alone. It retires at v2
// (ADR 0036 D8). The admission itself runs in the wasm guest (the rs seal plan's guard); a go theory
// carries the declaration because it decides the same atoms at check, and
// vectors/decider_completion.json pins that every core's standard theories declare alike.

// DecisionCompletion is a decider's declaration about its own decisions on an owned predicate. A
// closed sum type via an unexported marker method (mirroring Rust's enum).
type DecisionCompletion interface {
	isDecisionCompletion()
}

// DecisionStopsAreTyped: every non-decision on the predicate reaches readers as DecideGround's typed
// NotCompleted, so a Fails is always a decided false. A decider that never stops satisfies it
// trivially; one that stops satisfies it when every stop is typed (arithmetic's work cap, #3313).
// Named for the claim the guard needs, never "completes": a decider here may stop.
type DecisionStopsAreTyped struct{}

// DecisionMayNotComplete: a decision may stop without deciding and still answer Fails (a
// capacity, a bounded-work cap, a host refusal, an unreadable reply). Decider is the deciding
// component as it attests itself; Cause says why, in its words.
type DecisionMayNotComplete struct {
	Decider ComponentIdentity
	Cause   string
}

// DecisionUndeclared: the decider declared nothing. Admission reads it as DecisionMayNotComplete
// (fail closed, seat:caa on #3142); the census names it.
type DecisionUndeclared struct {
	Decider ComponentIdentity
}

func (DecisionStopsAreTyped) isDecisionCompletion()  {}
func (DecisionMayNotComplete) isDecisionCompletion() {}
func (DecisionUndeclared) isDecisionCompletion()     {}

// CompletionOf reports t's declaration for pred: its own when it implements CompletionDeclared,
// otherwise DecisionUndeclared naming it (fail closed, never a borrowed DecisionStopsAreTyped).
func CompletionOf(t Theory, pred Symbol) DecisionCompletion {
	if d, ok := t.(CompletionDeclared); ok {
		return d.Completion(pred)
	}
	return DecisionUndeclared{Decider: identityOf(t)}
}

// DecisionCompletionTag is the stable tag the census and a refusal name a declaration by, tri-core.
func DecisionCompletionTag(d DecisionCompletion) string {
	switch d.(type) {
	case DecisionStopsAreTyped:
		return "stops_are_typed"
	case DecisionMayNotComplete:
		return "may_not_complete"
	case DecisionUndeclared:
		return "undeclared"
	default:
		panic("contract: DecisionCompletionTag over an unknown DecisionCompletion")
	}
}

// StopsAreTyped reports whether admission may rest a certified claim on this declaration: only
// DecisionStopsAreTyped.
func StopsAreTyped(d DecisionCompletion) bool {
	return DecisionCompletionTag(d) == "stops_are_typed"
}

// Completion: #3142, PER THEORY (seat:caa's rulings on #3142 and on #3189, Q3). Every arithmetic
// stop is typed: its one stop, decimal alignment past maxDecimalScaleShift (#3126; #3123 removed the
// depth capacity), is DecideGround's NotCompleted(work_cap), never Fails (#3313), and check
// refuses it by name. Arithmetic still stops, so it is not "complete".
func (ArithmeticTheory) Completion(Symbol) DecisionCompletion { return DecisionStopsAreTyped{} }

// Completion: #3142, a text decision never stops (a byte comparison of two ground atoms), so its
// stops are typed trivially.
func (TextTheory) Completion(Symbol) DecisionCompletion { return DecisionStopsAreTyped{} }

// Completion: #3142, a term decision never stops (the recognizers, univ, and the standard order, an
// explicit-stack walk since #2275), so its stops are typed trivially.
func (TermTheory) Completion(Symbol) DecisionCompletion { return DecisionStopsAreTyped{} }

// Completion: #3142, a list decision never stops (a direct destructuring of the list embedding), so
// its stops are typed trivially.
func (ListTheory) Completion(Symbol) DecisionCompletion { return DecisionStopsAreTyped{} }

// Completion: #3142, the declaration of the member that decides pred, routed as DecideGround routes
// (the first owner). A predicate no member owns reads DecisionUndeclared naming the compound.
func (c CompoundTheory) Completion(pred Symbol) DecisionCompletion {
	for _, t := range c.theories {
		if t.Owns(pred) {
			return CompletionOf(t, pred)
		}
	}
	return DecisionUndeclared{Decider: c.Identity()}
}

// compile-time proofs that the standard theories declare (#3142).
var (
	_ CompletionDeclared = ArithmeticTheory{}
	_ CompletionDeclared = TextTheory{}
	_ CompletionDeclared = TermTheory{}
	_ CompletionDeclared = ListTheory{}
	_ CompletionDeclared = CompoundTheory{}
)
