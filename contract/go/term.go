// Package contract is the Go binding of logos-contract: the FIRM proof account
// (Term/Literal/Clause/Derivation) + the STABLE-v1 checker SPI
// (check/Theory/LeafVerifier/RuleAdmissibility) over ontos. It is a faithful,
// idiomatic-Go mirror of the Rust crate in contract/rs; both bindings replay the
// shared conformance vectors (vectors/check.json) and must agree judgment for
// judgment. The rejection-code strings are normative and byte-identical across
// {rs,go}. See docs/spec/logos-contract.md.
//
// This file is §1 Term — an ontos value, with holes. [FIRM]
//
// A term mirrors ontos's Atom(bytes) | Tuple(children) exactly, but a tuple child
// may be a Var, so holes can appear at any depth:
//
//	Term = Atom(Bytes) | Tuple(Term*) | Var(VarId)
//
// This is full term algebra with holes (e.g. pair(X, "a")), not Datalog's
// variables-as-whole-arguments. A *ground* term (no Var) corresponds exactly to an
// ontos Value — a bijection witnessed by EraseGround / FromValue. Var is logos's
// sole addition and is deliberately NOT an ontos value under a reserved label;
// reification to ground data is the explicit quote (§2a).
package contract

import (
	"fmt"
	"strings"
	"unicode/utf8"

	core "github.com/bitspark/ontos/core/go"
)

// MaxTermDepthDefault is the default cap on single-term nesting depth in the trusted
// check/decode path (issue #253). A pathologically deep term — f(f(f(…))) nested tens
// of thousands deep, or a deep cons-chain — would otherwise overflow the goroutine
// stack during the recursive term traversals (Substitute / EraseGround / structural
// Equal / the account quote), aborting the trusted checker (a DoS).
//
// Distinct from CheckLimits.MaxDepth, which bounds DAG/premise-chain depth: a single
// node's term can be arbitrarily deep within one node, so the node/depth caps do not
// bound it. Tri-core-consistent with contract/{rs,ts} (256). Go's default goroutine
// stack grows, but the trusted path keeps the SAME structural bound so a derivation
// accepted by one core is accepted by all three (and a deep one refused by all three).
const MaxTermDepthDefault = 256

// ValueTooDeep is the one name for "a term nests deeper than this build can represent" (#2425):
// contract/rs's VALUE_TOO_DEEP. A representation refusal's reason begins with it, whichever bound
// applied. go has no core bound of its own (its stacks grow); its guest-backed provider refuses
// past the guest's served depth (#2366).
const ValueTooDeep = "value_too_deep"

// VarId is an opaque variable identity (§1): a name or index. Its only contract is
// equality and freshness (the ability to rename apart). logos imposes no
// numeric/quotient equality — that stays a consumer/theory concern. It is a
// comparable value type so it can be a map key (mirroring Rust's deriving Ord/Hash).
//
// Its name is UTF-8 text (§2a, #3115), the domain rs's String holds by type. A Go string can hold
// any bytes, so every construction checks validVarName: ParseVarId refuses by name, and NewVarId
// and Var panic by name. The zero VarId (the empty name) is in the domain.
type VarId struct {
	name string
}

// validVarName is the ONE go test of a VarId's domain (#3115, seat:caa's ruling): the name is
// valid UTF-8. ParseVarId (and through it NewVarId and Var), Reify and the decoders that build a
// VarId (SubstFromValue's subst.var, the prelude loader) all call it, and nothing else decides it.
func validVarName(name string) bool { return utf8.ValidString(name) }

// VarIdError is ParseVarId's named refusal: Name is not UTF-8 text, so it is not a VarId's name
// (§2a). NewVarId and Var panic with it.
type VarIdError struct {
	Name string
}

func (e *VarIdError) Error() string {
	return fmt.Sprintf("contract: VarId name %q is not UTF-8 text (§2a)", e.Name)
}

// ParseVarId is the named ingress for a variable's name from outside (#3115): the VarId, or a
// *VarIdError when name is not valid UTF-8. Use it for any name this process did not write itself.
func ParseVarId(name string) (VarId, error) {
	if !validVarName(name) {
		return VarId{}, &VarIdError{Name: name}
	}
	return VarId{name: name}, nil
}

// NewVarId is ParseVarId's Must form (the regexp.MustCompile idiom): for literals and names already
// validated. It panics with the *VarIdError on a name that is not UTF-8 text.
func NewVarId(name string) VarId {
	id, err := ParseVarId(name)
	if err != nil {
		panic(err)
	}
	return id
}

// String returns the variable's name.
func (v VarId) String() string { return v.name }

// Subst is a grounding substitution (§3): a map from variable identity to a
// replacement term. On a Rule node it grounds the cited clause's head and body. A
// well-formed grounding Subst is *resolved* (idempotent — its values are themselves
// ground), so a single substitution pass suffices; check does not assume this and
// simply verifies the substituted result is ground and matches the node's
// conclusion.
type Subst map[VarId]Term

// Term is a term: an ontos value with holes (§1). The unexported marker method
// keeps the sum type closed — only Atom, Tuple, and Var in this package implement
// it (mirroring Rust's enum and ontos's core.Value interface).
//
// Identity is structural and extends ontos identity with Var(a) == Var(b) iff
// a == b — exactly what Equal provides.
type Term interface {
	// Equal reports structural identity with other.
	Equal(other Term) bool
	// IsGround reports whether the term contains no Var (normative, §1).
	IsGround() bool
	// EraseGround returns the corresponding ontos Value, defined iff the term is
	// ground (normative, §1). The second result is false for a non-ground term.
	EraseGround() (core.Value, bool)
	// Substitute applies a grounding substitution (one pass). A Var with no binding
	// is left in place (so the result is non-ground and a subsequent ground check
	// fails).
	Substitute(subst Subst) Term
	// String renders a diagnostic form (not a canonical encoding).
	String() string

	isTerm()
}

// AtomTerm holds the same bytes as an ontos Atom.
type AtomTerm struct {
	bytes []byte
}

// TupleTerm holds the same ordered shape as an ontos Tuple, but children may
// contain Var.
type TupleTerm struct {
	children []Term
}

// VarTerm is the unknown — logos's sole addition.
type VarTerm struct {
	id VarId
}

func (AtomTerm) isTerm()  {}
func (TupleTerm) isTerm() {}
func (VarTerm) isTerm()   {}

// Atom builds an AtomTerm from a defensive copy of bytes.
func Atom(bytes []byte) Term {
	cp := make([]byte, len(bytes))
	copy(cp, bytes)
	return AtomTerm{bytes: cp}
}

// Tuple builds a TupleTerm from the given children.
func Tuple(children ...Term) Term {
	cp := make([]Term, len(children))
	copy(cp, children)
	return TupleTerm{children: cp}
}

// Var builds a VarTerm from a variable name. Like NewVarId it panics with a *VarIdError on a name
// that is not UTF-8 text; build from ParseVarId and VarFromID for a name from outside.
func Var(name string) Term { return VarTerm{id: NewVarId(name)} }

// VarFromID builds a VarTerm from a VarId.
func VarFromID(id VarId) Term { return VarTerm{id: id} }

// Bytes returns a defensive copy of the atom term's bytes.
func (a AtomTerm) Bytes() []byte {
	cp := make([]byte, len(a.bytes))
	copy(cp, a.bytes)
	return cp
}

// Children returns a defensive copy of the tuple term's children.
func (t TupleTerm) Children() []Term {
	cp := make([]Term, len(t.children))
	copy(cp, t.children)
	return cp
}

// ID returns the variable's identity.
func (v VarTerm) ID() VarId { return v.id }

// ---- IsGround ----

// IsGround: an atom is always ground.
func (AtomTerm) IsGround() bool { return true }

// IsGround: a var is never ground.
func (VarTerm) IsGround() bool { return false }

// IsGround: a tuple is ground iff every child is ground.
func (t TupleTerm) IsGround() bool {
	for _, c := range t.children {
		if !c.IsGround() {
			return false
		}
	}
	return true
}

// IsOpenCompound reports whether t is an OPEN compound: a tuple containing a variable at any
// depth (#2294, ruled seat:caa). It is THE classification of "compound" the function-free
// fragment excludes. A GROUND term, compound or not, is a constant: it carries no variable, so no
// variable can bind a strict sub-term of it. A string, an int, a ground list and f(a) are all
// constants. Mirrors rs Term::is_open_compound.
func IsOpenCompound(t Term) bool {
	tuple, ok := t.(TupleTerm)
	return ok && !tuple.IsGround()
}

// ---- EraseGround ----

// EraseGround: an atom term erases to an ontos atom.
func (a AtomTerm) EraseGround() (core.Value, bool) {
	return core.NewAtom(a.bytes), true
}

// EraseGround: a var has no ground erasure.
func (VarTerm) EraseGround() (core.Value, bool) { return nil, false }

// EraseGround: a tuple erases iff all children do.
func (t TupleTerm) EraseGround() (core.Value, bool) {
	out := make([]core.Value, 0, len(t.children))
	for _, c := range t.children {
		v, ok := c.EraseGround()
		if !ok {
			return nil, false
		}
		out = append(out, v)
	}
	return core.NewTuple(out...), true
}

// FromValue is the inverse of EraseGround on ground terms: lift an ontos Value into
// the (always ground) corresponding Term.
//
// Non-recursive (issue #253). Built with an explicit work stack so a pathologically
// deep Value cannot overflow the goroutine stack here at the decode boundary — this is
// the one term traversal that must remain total even for an over-deep input (the depth
// guard runs after a term is in hand, so constructing it must not itself crash). The
// post-order assembly reproduces the recursive shape exactly.
func FromValue(value core.Value) Term {
	return fromValueRun([]fromValueFrame{enterFrame(value)})
}

// frameOp is a FromValue work item's operation. Its zero value is frameInvalid, so a frame built
// without a constructor is refused by name, and never read as "enter" (#3151; research 0030 row 4).
// Before it, #3094's `assemble bool` met "a payload cannot select control" but not this stronger
// form: its zero value silently meant enter.
type frameOp uint8

const (
	frameInvalid frameOp = iota
	frameEnter
	frameAssemble
)

// fromValueFrame is one FromValue work item. Only its constructors build it: kernel/go's census
// reds a composite literal of it anywhere else.
//
// vocabcensus:constructors enterFrame assembleFrame
type fromValueFrame struct {
	op frameOp
	// value is the value an enter frame lifts.
	value core.Value
	// arity is how many built children an assemble frame pops, and base is the output stack's length
	// when its tuple was entered (research 0030 row 3): the assemble checks that exactly `arity`
	// terms sit above `base`, so a child that built none, or two, is refused by name instead of
	// stealing a sibling.
	arity, base int
}

// enterFrame lifts value.
func enterFrame(value core.Value) fromValueFrame {
	return fromValueFrame{op: frameEnter, value: value}
}

// assembleFrame pops arity built children, which sit above base, into one tuple.
func assembleFrame(arity, base int) fromValueFrame {
	return fromValueFrame{op: frameAssemble, arity: arity, base: base}
}

// fromValueRun is FromValue's walk, an explicit work stack: no native frame per nesting level.
func fromValueRun(work []fromValueFrame) Term {
	var out []Term
	for len(work) > 0 {
		f := work[len(work)-1]
		work = work[:len(work)-1]
		switch f.op {
		case frameAssemble:
			if len(out) != f.base+f.arity {
				panic(fmt.Sprintf("contract: FromValue: an assemble of %d children above %d finds %d terms",
					f.arity, f.base, len(out)))
			}
			children := make([]Term, f.arity)
			copy(children, out[f.base:])
			out = out[:f.base]
			out = append(out, TupleTerm{children: children})
		case frameEnter:
			switch v := f.value.(type) {
			case core.Atom:
				out = append(out, AtomTerm{bytes: v.Bytes()})
			case core.Tuple:
				items := v.Items()
				// Schedule the assemble first, then the children (LIFO: the children are built before
				// the assemble, leaving exactly `arity` terms above the base recorded now).
				work = append(work, assembleFrame(len(items), len(out)))
				for i := len(items) - 1; i >= 0; i-- {
					work = append(work, enterFrame(items[i]))
				}
			default:
				panic(fmt.Sprintf("contract: FromValue: unknown core.Value implementation %T", f.value))
			}
		case frameInvalid:
			panic("contract: FromValue: a frame with no operation (the zero frameOp); build frames with enterFrame or assembleFrame")
		default:
			panic(fmt.Sprintf("contract: FromValue: frame operation %d is neither enter nor assemble", f.op))
		}
	}
	if len(out) != 1 {
		panic(fmt.Sprintf("contract: FromValue: the walk ends with %d terms, not one root", len(out)))
	}
	return out[0]
}

// TermDepthLE reports whether `t` nests no deeper than `max` levels — measured
// ITERATIVELY with an early cutoff (issue #253), so checking a pathologically deep
// term's depth does NOT itself overflow the stack (a recursive depth-measure would
// defeat the purpose). An Atom/Var has depth 1; a Tuple has depth 1 + max(child
// depth). Returns false as soon as a path exceeds `max`, without descending further.
func TermDepthLE(t Term, max int) bool {
	return termDepthCapped(t, max) <= max
}

// termDepthCapped is the depth TermDepthLE measures, by the same walk and the same cutoff: the
// term's depth when it is at most max, else max + 1, the first level past max, where the walk
// stops. check reports the deepest term it measured (#3111, max_term_depth_reached), so the
// measurement is read rather than only compared. rs Term::depth_capped.
func termDepthCapped(t Term, max int) int {
	type item struct {
		term  Term
		level int
	}
	deepest := 0
	work := []item{{term: t, level: 1}}
	for len(work) > 0 {
		it := work[len(work)-1]
		work = work[:len(work)-1]
		if it.level > max {
			return it.level
		}
		if it.level > deepest {
			deepest = it.level
		}
		if tup, ok := it.term.(TupleTerm); ok {
			for _, c := range tup.children {
				work = append(work, item{term: c, level: it.level + 1})
			}
		}
	}
	return deepest
}

// ValueDepthLE reports whether the ontos `value` nests no deeper than `max` levels —
// the TermDepthLE analogue for a ground core.Value (a GroundLiteral's args are Values,
// not Terms). Iterative with an early cutoff (issue #253): the recursive Value
// traversals on the trusted path (structural Equal against the claim, the canonical
// codec encode, etc.) would overflow on a pathologically deep value, so the trusted
// checker measures depth without recursing and rejects an over-deep value first.
func ValueDepthLE(value core.Value, max int) bool {
	return valueDepthCapped(value, max) <= max
}

// valueDepthCapped is the depth ValueDepthLE measures, by the same walk and the same cutoff: the
// value's depth when it is at most max, else max + 1, where the walk stops (termDepthCapped's
// analogue, #3111). rs value_depth_capped.
func valueDepthCapped(value core.Value, max int) int {
	type item struct {
		value core.Value
		level int
	}
	deepest := 0
	work := []item{{value: value, level: 1}}
	for len(work) > 0 {
		it := work[len(work)-1]
		work = work[:len(work)-1]
		if it.level > max {
			return it.level
		}
		if it.level > deepest {
			deepest = it.level
		}
		if tup, ok := it.value.(core.Tuple); ok {
			for _, c := range tup.Items() {
				work = append(work, item{value: c, level: it.level + 1})
			}
		}
	}
	return deepest
}

// ===========================================================================
// account-v2 list canonicalization (cons ↔ `list`) — the BIJECTION on ground
// proper lists used by the reify-aware account-equality (#277). [FIRM]
//
// Go sibling of contract/rs/src/term.rs::canonicalize_lists. The logos surface lowers
// list syntax to Prolog-style cons cells ([] = Atom("[]"), [H|T] = Tuple[Atom("."),
// H, T]); the ontos/data L2 profile carries a sequence as the flat `list` embedding
// Tuple[Atom("list"), e0, …] (ontos-data §5.5). These are two spellings of the SAME
// datum; the opt-in account-emit reification (rust-only reify_lists, #159) rewrites
// cons → `list`. #277 made Check treat the two spellings as account-equal; #3022 withdrew
// that: every certified literal claim is exact, Check compares structurally, and this
// canonicalization is the PRESENTATION equivalence, never a certification equivalence.
//
// CanonicalizeLists is the single canonical retraction Check applies to BOTH sides of a
// comparison: it maps every ground PROPER cons-list to its `list` embedding (and leaves
// the `list` embedding fixed), so a cons-form clause head and a reified `list()`
// conclusion canonicalize to the same value and compare equal — while NEVER conflating
// two terms that denote different data.
//
// THE BIJECTION. On ground proper lists, cons-form [e0,…,e_{n-1}] and the `list`
// embedding list(e0,…,e_{n-1}) are in one-to-one correspondence (a proper cons-chain has
// a unique element sequence; list(…) has a unique child sequence). CanonicalizeLists
// chooses the `list` embedding as the canonical representative and is the IDENTITY on
// every other value. It is idempotent (a retraction); it conflates two values ONLY when
// they are the cons and `list` spellings of the SAME sequence (the intended account
// equality); distinct sequences have distinct element tuples, hence distinct canonical
// forms; a non-list value is untouched.
//
// EDGE CASES (each kept distinct): a bare nil Atom("[]") is an ATOM, not a `.`/2 cell, so
// it is LEFT as Atom("[]") (never rewritten to list()); the empty `list` embedding
// Tuple[Atom("list")] is likewise left fixed — so [] and list() are DISTINCT. An improper
// .(a, b) (tail not []) is NOT a proper list → kept as the cons tuple. A partial [a|X]
// cannot occur (a Value has no Var). An existing Tuple[Atom("list"), …] is headed by
// `list`, not `.`, so it is never a cons cell (children canonicalized, no double-wrap).
// ===========================================================================

// consLabel is the cons functor "." (a [H|T] cell head).
const consLabel = "."

// nilLabel is the nil atom "[]" (the cons-chain terminator).
const nilLabel = "[]"

// listLabel is the ontos/data `list` embedding label (Tuple[Atom("list"), …]).
const listLabel = "list"

// CanonicalizeLists canonicalizes every ground PROPER cons-list anywhere inside value to
// the ontos/data flat `list` embedding (Tuple[Atom("list"), e0, …]), bottom-up — the
// single canonical retraction of the presentation equivalence (#277; since #3022 Check never
// applies it). The IDENTITY on every non-(proper-cons-list) value. See the block
// note above for the bijection / no-conflation argument and edge cases. Total and
// deterministic; the spine walk is iterative (no per-cell recursion), and element/child
// recursion is bounded by the term-nesting depth the trusted path already gated
// (MaxTermDepth) before this runs.
func CanonicalizeLists(value core.Value) core.Value {
	// A proper cons-list anywhere is canonicalized to the flat `list` embedding. The
	// test runs on the RAW value (before any child rewrite): the spine threads through
	// `.`/`[]` cells, so canonicalizing a child first would dissolve the spine the top of
	// the chain must walk. We collect the raw element values off the intact spine, then
	// canonicalize EACH element (so nested lists are normalized too).
	if elems, ok := collectProperConsList(value); ok {
		items := make([]core.Value, 0, len(elems)+1)
		items = append(items, core.NewAtom([]byte(listLabel)))
		for _, e := range elems {
			items = append(items, CanonicalizeLists(e))
		}
		return core.NewTuple(items...)
	}
	switch v := value.(type) {
	case core.Tuple:
		// A non-list tuple (an ordinary compound, an existing list(…) embedding): keep the
		// shape, canonicalize each child.
		children := v.Items()
		out := make([]core.Value, len(children))
		for i, c := range children {
			out[i] = CanonicalizeLists(c)
		}
		return core.NewTuple(out...)
	case core.Atom:
		// An Atom (including the bare nil "[]"): identity.
		return value
	default:
		// A value of no known kind is not a proper cons list, and the retraction is the identity on
		// everything that is not one. Presentation only since #3022, so there is no refusal channel;
		// check's boundary refuses such a value before any gate reads it (#3088). (#3074)
		return value
	}
}

// collectProperConsList: if value is a cons cell Tuple[Atom("."), H, T] whose spine is a
// PROPER list (ends in the nil atom "[]"), return the RAW (un-canonicalized) element
// values in order and true; otherwise nil, false. Iterative over the tail (no spine
// recursion) so a long list does not grow the stack.
func collectProperConsList(value core.Value) ([]core.Value, bool) {
	// A standalone nil atom "[]" is NOT a list — only an actual `.`/2 cons cell starts a
	// list. (Canonicalizing a bare "[]" to list() would re-encode a legitimate atom and
	// break the empty-list edge case.)
	if t, ok := value.(core.Tuple); !ok || !isConsCell(t.Items()) {
		return nil, false
	}
	cursor := value
	var elems []core.Value
	for {
		switch c := cursor.(type) {
		case core.Atom:
			// Proper terminator: the spine ends in the nil atom "[]".
			if string(c.Bytes()) == nilLabel {
				return elems, true
			}
			// A non-"[]" atom before reaching "[]": improper.
			return nil, false
		case core.Tuple:
			if isConsCell(c.Items()) {
				items := c.Items()
				elems = append(elems, items[1])
				cursor = items[2]
				continue
			}
			// A non-cons tuple before reaching "[]": improper / not a list.
			return nil, false
		default:
			return nil, false
		}
	}
}

// isConsCell reports whether items are exactly the items of a cons cell: arity 3, headed
// by Atom(".").
func isConsCell(items []core.Value) bool {
	if len(items) != 3 {
		return false
	}
	a, ok := items[0].(core.Atom)
	return ok && string(a.Bytes()) == consLabel
}

// ---- Substitute ----

// Substitute: an atom term is unchanged (returns a fresh copy for immutability).
func (a AtomTerm) Substitute(Subst) Term {
	return AtomTerm{bytes: a.Bytes()}
}

// Substitute: a var is replaced by its binding, or left in place if unbound.
func (v VarTerm) Substitute(subst Subst) Term {
	if t, ok := subst[v.id]; ok {
		return t
	}
	return v
}

// Substitute: a tuple substitutes each child.
func (t TupleTerm) Substitute(subst Subst) Term {
	children := make([]Term, len(t.children))
	for i, c := range t.children {
		children[i] = c.Substitute(subst)
	}
	return TupleTerm{children: children}
}

// ---- Equal ----

// Equal: an atom term equals another atom term with the exact same bytes.
func (a AtomTerm) Equal(other Term) bool {
	b, ok := other.(AtomTerm)
	if !ok {
		return false
	}
	if len(a.bytes) != len(b.bytes) {
		return false
	}
	for i := range a.bytes {
		if a.bytes[i] != b.bytes[i] {
			return false
		}
	}
	return true
}

// Equal: a tuple term equals another tuple term of the same arity whose children
// are elementwise equal in order.
func (t TupleTerm) Equal(other Term) bool {
	u, ok := other.(TupleTerm)
	if !ok {
		return false
	}
	if len(t.children) != len(u.children) {
		return false
	}
	for i := range t.children {
		if !t.children[i].Equal(u.children[i]) {
			return false
		}
	}
	return true
}

// Equal: a var term equals another var term with the same identity.
func (v VarTerm) Equal(other Term) bool {
	w, ok := other.(VarTerm)
	if !ok {
		return false
	}
	return v.id == w.id
}

// TermEqual is the package-level structural identity relation for terms.
func TermEqual(left, right Term) bool { return left.Equal(right) }

// ---- String ----

func (a AtomTerm) String() string {
	var b strings.Builder
	b.WriteString("Atom(0x")
	for _, by := range a.bytes {
		const hexdigits = "0123456789abcdef"
		b.WriteByte(hexdigits[by>>4])
		b.WriteByte(hexdigits[by&0x0f])
	}
	b.WriteString(")")
	return b.String()
}

func (t TupleTerm) String() string {
	var b strings.Builder
	b.WriteString("Tuple(")
	for i, c := range t.children {
		if i != 0 {
			b.WriteString(", ")
		}
		b.WriteString(c.String())
	}
	b.WriteString(")")
	return b.String()
}

func (v VarTerm) String() string { return "Var(" + v.id.name + ")" }
