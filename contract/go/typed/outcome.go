package typed

// Status keeps evidence rejection, checking limitations and acceptance distinct.
type Status string

const (
	AcceptedStatus    Status = "accepted"
	InvalidStatus     Status = "invalid"
	IncompleteStatus  Status = "incomplete"
	UnsupportedStatus Status = "unsupported"
)

type Code string

const (
	MalformedInput        Code = "malformed-input"
	EscapedVariable       Code = "escaped-variable"
	UnknownConstant       Code = "unknown-constant"
	DuplicateConstant     Code = "duplicate-constant"
	MissingAssumptions    Code = "missing-assumptions"
	EmptyConstantName     Code = "empty-constant-name"
	ExpectedUniverse      Code = "expected-universe"
	ExpectedFunction      Code = "expected-function"
	ExpectedSigma         Code = "expected-sigma"
	TypeMismatch          Code = "type-mismatch"
	InputNodes            Code = "input-nodes"
	InputDepth            Code = "input-depth"
	CollectionEntries     Code = "collection-entries"
	NameBytes             Code = "name-bytes"
	Work                  Code = "work"
	Depth                 Code = "depth"
	UniverseCapacity      Code = "universe-capacity"
	IndexCapacity         Code = "index-capacity"
	UnsupportedFoundation Code = "foundation"
	UnadmittedFoundation  Code = "unadmitted-foundation"
	UnadmittedChecker     Code = "unadmitted-checker"
	UnadmittedDependency  Code = "unadmitted-dependency"
)

type Phase string

const (
	PreflightPhase   Phase = "preflight"
	DeclarationPhase Phase = "declaration"
	ContextPhase     Phase = "context"
	ExpectedPhase    Phase = "expected"
	CandidatePhase   Phase = "candidate"
	PolicyPhase      Phase = "policy"
	SnapshotPhase    Phase = "snapshot"
)

// Location identifies a checking phase and, where applicable, a zero-based
// declaration/context index. It contains no consumer-specific source addresses.
type Location struct {
	Phase    Phase
	Index    uint32
	HasIndex bool
}

// Outcome cannot be constructed as accepted by a consumer. A zero value has no
// status and no acceptance. A serialized outcome carries no checking authority.
type Outcome struct {
	status   Status
	code     Code
	detail   string
	steps    uint32
	accepted *acceptanceState
	location Location
}

func (o Outcome) Status() Status     { return o.status }
func (o Outcome) Code() Code         { return o.code }
func (o Outcome) Detail() string     { return o.detail }
func (o Outcome) Steps() uint32      { return o.steps }
func (o Outcome) Location() Location { return o.location }
func (o Outcome) IsAccepted() bool {
	return o.status == AcceptedStatus && o.accepted != nil && o.accepted.valid
}
func (o Outcome) Accepted() (Acceptance, bool) {
	if !o.IsAccepted() {
		return Acceptance{}, false
	}
	return Acceptance{state: o.accepted}, true
}

// Acceptance is a value handle over the exact checked statement and immutable
// proof. Replacing a caller's handle cannot replace the Outcome's retained state.
// Accessors copy all mutable collections. Expr and Declaration themselves are
// immutable values, so their nodes may safely be shared across these copies.
type Acceptance struct {
	state *acceptanceState
}

type acceptanceState struct {
	valid        bool
	statement    Statement
	candidate    Expr
	policy       Policy
	used         []string
	dependencies []string
	steps        uint32
}

// Valid is false for zero-value placeholders. Only Check can mint a
// valid acceptance; constructing an empty Acceptance does not do so.
func (a Acceptance) Valid() bool { return a.state != nil && a.state.valid }

func (a Acceptance) Statement() Statement {
	if !a.Valid() {
		return Statement{}
	}
	return Statement{
		Foundation:   a.state.statement.Foundation,
		Declarations: append([]Declaration(nil), a.state.statement.Declarations...),
		Context:      append([]Expr(nil), a.state.statement.Context...),
		Expected:     a.state.statement.Expected,
	}
}
func (a Acceptance) Candidate() Expr {
	if !a.Valid() {
		return Expr{}
	}
	return a.state.candidate
}

// Policy returns the exact admitted receiver policy, including unused allowances
// and their supplied order. Actual dependencies are reported separately.
func (a Acceptance) Policy() Policy {
	if !a.Valid() {
		return Policy{}
	}
	return Policy{
		Foundation:   a.state.policy.Foundation,
		Checker:      a.state.policy.Checker,
		Dependencies: append([]string(nil), a.state.policy.Dependencies...),
	}
}
func (a Acceptance) UsedConstants() []string {
	if !a.Valid() {
		return nil
	}
	return append([]string(nil), a.state.used...)
}
func (a Acceptance) Dependencies() []string {
	if !a.Valid() {
		return nil
	}
	return append([]string(nil), a.state.dependencies...)
}
func (a Acceptance) Steps() uint32 {
	if !a.Valid() {
		return 0
	}
	return a.state.steps
}
func (a Acceptance) Foundation() string {
	if !a.Valid() {
		return ""
	}
	return Foundation
}
func (a Acceptance) Checker() string {
	if !a.Valid() {
		return ""
	}
	return Checker
}

type failure struct {
	status   Status
	code     Code
	detail   string
	location Location
}

func invalid(code Code) *failure    { return &failure{status: InvalidStatus, code: code} }
func incomplete(code Code) *failure { return &failure{status: IncompleteStatus, code: code} }
func unsupported(code Code, detail string) *failure {
	return &failure{status: UnsupportedStatus, code: code, detail: detail}
}
