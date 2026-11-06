// Package typed checks supplied proofs in dependent-fragment-1. It performs no
// search and has no language-specific or solver callbacks. Receiver declarations
// are assumptions or checked definitions, never facts authenticated by a name.
// See docs/spec/typed-check-only.md for the resource and authority boundaries.
package typed

// Kind identifies one of the selected rulebook's 21 expression constructors.
type Kind string

const (
	SortKind      Kind = "sort"
	VarKind       Kind = "var"
	ConstKind     Kind = "const"
	PiKind        Kind = "pi"
	LamKind       Kind = "lam"
	AppKind       Kind = "app"
	SigmaKind     Kind = "sigma"
	PairKind      Kind = "pair"
	FstKind       Kind = "fst"
	SndKind       Kind = "snd"
	NatKind       Kind = "nat"
	ZeroKind      Kind = "zero"
	SuccKind      Kind = "succ"
	NatElimKind   Kind = "nat-elim"
	BoolKind      Kind = "bool"
	FalseKind     Kind = "false"
	TrueKind      Kind = "true"
	BoolElimKind  Kind = "bool-elim"
	IDKind        Kind = "id"
	ReflKind      Kind = "refl"
	TransportKind Kind = "transport"
)

// Expr is immutable syntax. Its zero value is malformed, not an empty proof.
// Constructors allocate caller-owned syntax; these allocations precede Check's
// resource boundary. Only Check establishes a typing judgment.
type Expr struct{ node *expression }

type expression struct {
	kind  Kind
	index uint32
	name  string
	args  []Expr
}

func expr(kind Kind, args ...Expr) Expr {
	return Expr{&expression{kind: kind, args: append([]Expr(nil), args...)}}
}

func Sort(level uint32) Expr              { return Expr{&expression{kind: SortKind, index: level}} }
func Var(index uint32) Expr               { return Expr{&expression{kind: VarKind, index: index}} }
func Const(name string) Expr              { return Expr{&expression{kind: ConstKind, name: name}} }
func Pi(domain, body Expr) Expr           { return expr(PiKind, domain, body) }
func Lam(domain, body Expr) Expr          { return expr(LamKind, domain, body) }
func App(fun, arg Expr) Expr              { return expr(AppKind, fun, arg) }
func Sigma(domain, body Expr) Expr        { return expr(SigmaKind, domain, body) }
func Pair(sigma, first, second Expr) Expr { return expr(PairKind, sigma, first, second) }
func Fst(pair Expr) Expr                  { return expr(FstKind, pair) }
func Snd(pair Expr) Expr                  { return expr(SndKind, pair) }
func Nat() Expr                           { return expr(NatKind) }
func Zero() Expr                          { return expr(ZeroKind) }
func Succ(value Expr) Expr                { return expr(SuccKind, value) }
func NatElim(motive, zero, step, scrutinee Expr) Expr {
	return expr(NatElimKind, motive, zero, step, scrutinee)
}
func Bool() Expr  { return expr(BoolKind) }
func False() Expr { return expr(FalseKind) }
func True() Expr  { return expr(TrueKind) }
func BoolElim(motive, onFalse, onTrue, scrutinee Expr) Expr {
	return expr(BoolElimKind, motive, onFalse, onTrue, scrutinee)
}
func ID(typ, lhs, rhs Expr) Expr { return expr(IDKind, typ, lhs, rhs) }
func Refl(typ, value Expr) Expr  { return expr(ReflKind, typ, value) }
func Transport(typ, from, to, equality, motive, value Expr) Expr {
	return expr(TransportKind, typ, from, to, equality, motive, value)
}

func (e Expr) Kind() Kind {
	if e.node == nil {
		return ""
	}
	return e.node.kind
}

// Index reports the natural operand of sort/var; it is zero for other nodes.
func (e Expr) Index() uint32 {
	if e.node == nil {
		return 0
	}
	return e.node.index
}

// Name reports a constant identity; it is empty for other nodes.
func (e Expr) Name() string {
	if e.node == nil {
		return ""
	}
	return e.node.name
}

// Operands returns a defensive copy of the ordered operand list.
func (e Expr) Operands() []Expr {
	if e.node == nil {
		return nil
	}
	return append([]Expr(nil), e.node.args...)
}

type declarationKind uint8

const (
	assumed declarationKind = iota + 1
	defined
)

// Declaration is immutable receiver-supplied signature data. Assume does not
// validate its proposition or authorize the named assumptions; Check does both.
type Declaration struct {
	kind         declarationKind
	name         string
	typ          Expr
	value        Expr
	dependencies []string
}

func Assume(name string, typ Expr, dependencies ...string) Declaration {
	return Declaration{kind: assumed, name: name, typ: typ, dependencies: append([]string(nil), dependencies...)}
}

func Define(name string, typ, value Expr) Declaration {
	return Declaration{kind: defined, name: name, typ: typ, value: value}
}

func (d Declaration) Name() string             { return d.name }
func (d Declaration) Type() Expr               { return d.typ }
func (d Declaration) IsAssumption() bool       { return d.kind == assumed }
func (d Declaration) Definition() (Expr, bool) { return d.value, d.kind == defined }
func (d Declaration) Dependencies() []string   { return append([]string(nil), d.dependencies...) }

// Statement is fixed by the receiver independently of candidate evidence.
// Do not mutate its slices concurrently with Check.
type Statement struct {
	Foundation   string
	Declarations []Declaration
	Context      []Expr
	Expected     Expr
}

type Policy struct {
	Foundation   string
	Checker      string
	Dependencies []string
}

const Foundation = "logos/dependent-fragment-1/edition-1"
const Checker = "logos/typed-check-only-v1/go"

// Limits uses exact uint32 capacities in every binding. Raising depth above the
// fixed implementation capacities does not remove those capacities.
type Limits struct {
	InputNodes        uint32
	InputDepth        uint32
	CollectionEntries uint32
	NameBytes         uint32
	Work              uint32
	Depth             uint32
}

func DefaultLimits() Limits {
	return Limits{100000, 128, 4096, 256, 1000000, 512}
}
