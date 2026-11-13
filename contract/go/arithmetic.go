// ArithmeticTheory — the Go binding of logos-core's exact-integer arithmetic
// Theory, a judgment-for-judgment mirror of the Rust ArithmeticTheory in
// core/rs/src/builtins.rs. [STABLE-v1 Theory impl]
//
// This lifts the positive-Datalog-only scope of host-side certification: a program
// that uses the arithmetic relations (is / =:= / =\= / < / > / >= / =<) can now be
// CHECKED in Go, because the same decide() that the Rust core uses is reproduced
// here byte-for-byte. The two cores agree on EVERY ground arithmetic atom — the §7
// dual-conformance law and the issue-#95 byte-parity requirement.
//
// # The home (why contract/go)
//
// Rust's ArithmeticTheory lives in logos-core (core/rs). Go has no core tier; the
// checker SPI is tri-core in contract/go, and the reusable Theory/RuleAdmissibility
// impls a consumer binds (e.g. AlwaysAdmit) live HERE, beside the SPI. So this is
// where a Go consumer binds arithmetic — alongside AlwaysAdmit — exactly as a Rust
// consumer binds logos_core::builtins::ArithmeticTheory beside the contract.
//
// # The numeric domain (frozen ontos-data int, NOT a re-invented parse)
//
// Every integer is the FROZEN ontos-data §5.1 `int` embedding
// Tuple(Atom("int"), Atom(sign‖big-endian-minimal-magnitude)). This file reads and
// builds those values through ontos/data's ReadInt / EncodeInt over math/big.Int —
// the SAME canonical bytes the Rust intval module delegates to
// (ontos_data::read_int / encode_int). The domain is unbounded (math/big), matching
// Rust's hand-rolled unbounded BigInt: no fixed-width overflow, no float.
//
// # Judgments (mirroring Rust exactly)
//
// owns(pred): by NAME only (any arity) for the seven arithmetic relations. The
// expression operators (+ - * / // mod abs min max) are never goals, so they are
// NOT owned. decide(atom) on a ground atom:
//   - non-UTF-8 predicate            -> Fails{arith_unknown_predicate}
//   - owned name, unregistered arity -> Fails{arith_bad_arity}   (e.g. is/3, </1)
//   - registered, evaluates to true  -> Holds
//   - registered, evaluates to false
//     OR an unevaluable expression
//     (unbound never occurs in a ground
//     atom; non-int atom / unknown op /
//     div-by-zero make the goal FAIL) -> Fails{arith_does_not_hold}
//
// (The Rust arm Fails{arith_unevaluable} is reachable only on an internal
// arity-mismatch inside evaluate(), which the registry lookup already prevents, and
// Fails{arith_unknown_predicate} only on a non-UTF-8 predicate. Both are preserved
// here for byte-identical codes on those defensive paths.)
package contract

import (
	"fmt"
	"math/big"
	"unicode/utf8"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// arithmeticPredicates is the set of relation names ArithmeticTheory owns, mirroring
// Rust's ARITHMETIC_PREDICATES. Owned by name only — an unregistered arity routes
// here and Fails (a malformed arithmetic goal), never panics.
var arithmeticPredicates = map[string]struct{}{
	"is":   {},
	"=:=":  {},
	"=\\=": {},
	"<":    {},
	">":    {},
	">=":   {},
	"=<":   {},
}

// num is a numeric value the arithmetic evaluator produces and applyOperator combines:
// an exact integer OR an exact decimal (#331), mirroring Rust's arithmetic::Num. The two
// are DISTINCT sorts — int(5) and decimal(5,0) are different terms, so `5 is 2+3.0` FAILS
// while `5.0 is 2+3.0` HOLDS (toTerm keeps the sort). But the comparisons order by VALUE
// across sorts (cmpValue), so `2 =:= 2.0` HOLDS. An all-integer expression stays integer
// (byte-identical to the pre-decimal path); a decimal operand promotes the expression.
type num struct {
	isDec bool
	i     *big.Int   // the integer value when !isDec
	d     bigDecimal // the decimal value when isDec
}

func numInt(i *big.Int) num   { return num{i: i} }
func numDec(d bigDecimal) num { return num{isDec: true, d: d} }

// toTerm lowers to the canonical embedding of the value's sort — int(…) or decimal(…).
func (n num) toTerm() core.Value {
	if n.isDec {
		return n.d.toDecimalTerm()
	}
	return data.EncodeInt(n.i)
}

// cmpValue is the total VALUE order across sorts (so `2 =:= 2.0`): a mixed pair promotes
// the integer to a decimal. Returns -1/0/+1.
func (n num) cmpValue(o num) int {
	switch {
	case !n.isDec && !o.isDec:
		return n.i.Cmp(o.i)
	case n.isDec && o.isDec:
		return n.d.cmp(o.d)
	case !n.isDec && o.isDec:
		return decFromBigInt(n.i).cmp(o.d)
	default:
		return n.d.cmp(decFromBigInt(o.i))
	}
}

// toDecimal promotes to the decimal domain (for a mixed-sort binary operator).
func (n num) toDecimal() bigDecimal {
	if n.isDec {
		return n.d
	}
	return decFromBigInt(n.i)
}

func (n num) negate() num {
	if n.isDec {
		return numDec(n.d.negate())
	}
	return numInt(new(big.Int).Neg(n.i))
}

func (n num) abs() num {
	if n.isDec {
		return numDec(n.d.abs())
	}
	return numInt(new(big.Int).Abs(n.i))
}

// ArithmeticTheory is the config-pinned §5 Theory that owns the arithmetic relations
// (is/2, =:= =\= < > >= =<) and decides a GROUND arithmetic atom by exact-integer
// evaluation over the frozen ontos-data int embedding. Pure / total / deterministic
// / config-free — a faithful mirror of Rust's logos_core::builtins::ArithmeticTheory.
type ArithmeticTheory struct{}

// NewArithmeticTheory builds the standard arithmetic Theory (no configuration).
func NewArithmeticTheory() ArithmeticTheory { return ArithmeticTheory{} }

// compile-time proofs that the theory satisfies the SPI seam (Theory + the optional
// Identified seam), exactly like AlwaysAdmit's parity with the Rust binding.
var (
	_ Theory     = ArithmeticTheory{}
	_ Identified = ArithmeticTheory{}
)

// Owns reports whether pred names an owned arithmetic relation. Mirrors
// Rust's ArithmeticTheory::owns / owns_name — by name, at any arity.
func (ArithmeticTheory) Owns(pred Symbol) bool {
	_, ok := arithmeticPredicates[string(pred.Bytes())]
	return ok
}

// Identity reports this theory's canonical component identity,
// logos-core/arithmetic-theory@1.0.0 with a zero config digest — byte-identical to
// the Rust theory's identity(), so a CheckProfile binding it derives the same
// theory binding (and thus the same stamped digest) tri-core.
func (ArithmeticTheory) Identity() ComponentIdentity {
	return NewComponentIdentity(
		[]byte("logos-core/arithmetic-theory"),
		[]byte("1.0.0"),
		[32]byte{},
	)
}

// DecideGround decides an owned GROUND arithmetic atom, byte-identically to the Rust
// ArithmeticTheory::decide_ground (#3126). A ground arithmetic relation binds nothing, so it
// Holds, Fails with a pinned host-band sub-code (a domainError is the language's false), or is not
// decided (an evaluation past a work cap, never a false).
func (t ArithmeticTheory) DecideGround(atom GroundLiteral) completion.TheoryGround {
	// Not one of ours: check routes by Owns, so this is the theory contradicting its own routing,
	// the named inconsistent_theory fault. Stay total. Mirrors Rust.
	if !t.Owns(atom.Pred) {
		return completion.TheoryGroundDisowned()
	}
	// A Go Symbol holds arbitrary bytes; an owned name is always valid UTF-8 (the
	// names are ASCII), but mirror Rust's std::str::from_utf8 guard so the non-UTF-8
	// defensive arm carries the identical code on every path.
	predBytes := atom.Pred.Bytes()
	if !utf8.Valid(predBytes) {
		return arithFails("arith_unknown_predicate")
	}
	name := string(predBytes)

	switch name {
	case "is":
		return decideIs(atom.Args)
	case "=:=":
		return decideCompare(atom.Args, func(c int) bool { return c == 0 })
	case "=\\=":
		return decideCompare(atom.Args, func(c int) bool { return c != 0 })
	case "<":
		return decideCompare(atom.Args, func(c int) bool { return c < 0 })
	case ">":
		return decideCompare(atom.Args, func(c int) bool { return c > 0 })
	case ">=":
		return decideCompare(atom.Args, func(c int) bool { return c >= 0 })
	case "=<":
		return decideCompare(atom.Args, func(c int) bool { return c <= 0 })
	default:
		// Owned name routed here but not handled above — unreachable (the name set
		// is exactly the switch arms), but stay total.
		return arithFails(arithDoesNotHold)
	}
}

// arithDoesNotHold is the code a false arithmetic relation names: a relation over values that does
// not hold, or an expression with no value (domainError.code).
const arithDoesNotHold = "arith_does_not_hold"

// arithFails is the false arm with code.
func arithFails(code string) completion.TheoryGround {
	return completion.TheoryGroundFails(code)
}

// arithHoldsIf is Holds when holds, else the relation's false.
func arithHoldsIf(holds bool) completion.TheoryGround {
	if holds {
		return completion.TheoryGroundHolds()
	}
	return arithFails(arithDoesNotHold)
}

// domainError is why an arithmetic expression has no value in the language (#3161), Rust's
// DomainError: every failure ADR 0022 defines. The goal over it is false, a decided answer. A work
// cap is not here: it is an evaluation's stop, because the value exists and was not computed. The
// zero value is invalid.
type domainError uint8

const (
	domainErrorInvalid domainError = iota
	// domainNotANumber: a leaf that is not a number (a bare atom, a non-number embedding, a
	// compound whose head is not an operator atom).
	domainNotANumber
	// domainUnknownOperator: an operator compound whose op/arity is not one of the operators.
	domainUnknownOperator
	// domainDivisionByZero: a zero divisor for /, // or mod.
	domainDivisionByZero
	// domainInexactDivision: an integer / whose operands do not divide evenly (7 / 2).
	domainInexactDivision
	// domainNonTerminating: a decimal / whose exact quotient does not terminate (1.0 / 3).
	domainNonTerminating
	// domainOutsideDomain: a decimal result outside the value domain.
	domainOutsideDomain
)

// code is the false code this failure names in DecideGround (seat:caa's condition on #3126): the
// ONE function a domain failure's code comes from. Every domain failure names arith_does_not_hold,
// the code a false arithmetic relation has always named in vectors/arithmetic.json. Rust's
// DomainError::code.
func (e domainError) code() string {
	switch e {
	case domainNotANumber, domainUnknownOperator, domainDivisionByZero, domainInexactDivision,
		domainNonTerminating, domainOutsideDomain:
		return arithDoesNotHold
	case domainErrorInvalid:
		panic("arithmetic: a domain error nobody built")
	default:
		panic(fmt.Sprintf("arithmetic: domain error %d is not a failure", e))
	}
}

// evalArm is which of an evaluation's three results it holds.
type evalArm uint8

const (
	evalInvalid evalArm = iota
	// evalValue: the expression's value.
	evalValue
	// evalNoValue: the language's answer that it has none (a domainError): a goal over it is false.
	evalNoValue
	// evalStopped: the evaluator stopped before it knew (a work cap): a goal over it is not decided.
	evalStopped
)

// evaluation is what evaluating an arithmetic expression establishes (#3161, research 0031 row 3),
// Rust's Evaluation. No path converts a stop into a domainError.
type evaluation struct {
	arm   evalArm
	value num
	err   domainError
	cause completion.NonCompletion
}

func valueOf(n num) evaluation                       { return evaluation{arm: evalValue, value: n} }
func noValue(e domainError) evaluation               { return evaluation{arm: evalNoValue, err: e} }
func evalStop(c completion.NonCompletion) evaluation { return evaluation{arm: evalStopped, cause: c} }

// decimalStep is a decimal operation's result as an evaluation: the ONE place a decimalError is
// sorted into the language's failure or the implementation's stop. The alignment cap is the only
// stop.
func decimalStep(n num, err decimalError) evaluation {
	switch err {
	case decOK:
		return valueOf(n)
	case decDivisionByZero:
		return noValue(domainDivisionByZero)
	case decNonTerminating:
		return noValue(domainNonTerminating)
	case decOutsideDomain:
		return noValue(domainOutsideDomain)
	case decAlignmentCap:
		return evalStop(completion.WorkCap(completion.ScopeLiteral))
	default:
		panic(fmt.Sprintf("arithmetic: decimal error %d is not one", err))
	}
}

// settle is an operand's value (ok), or the decision its evaluation already settles: a
// domainError is the relation's false, named by its code; a stop is not decided.
func settle(e evaluation) (num, completion.TheoryGround, bool) {
	switch e.arm {
	case evalValue:
		return e.value, completion.TheoryGround{}, true
	case evalNoValue:
		return num{}, arithFails(e.err.code()), false
	case evalStopped:
		return num{}, completion.NotCompleted[completion.TheoryDecision, completion.NoCallerLimit](e.cause), false
	case evalInvalid:
		panic("arithmetic: an evaluation nobody built")
	default:
		panic(fmt.Sprintf("arithmetic: evaluation arm %d is not one", e.arm))
	}
}

// decideIs decides `is/2`: evaluate the RHS expression and compare the LHS (a ground value) to
// the canonical embedding of its value. Mirrors Rust's decide_is.
//
//   - wrong arity (not 2)   -> Fails{arith_bad_arity}    (no is/N builtin)
//   - RHS has no value      -> the domainError's code, arith_does_not_hold (the goal fails)
//   - RHS past a work cap   -> not decided (#3126)
//   - LHS != its value      -> arith_does_not_hold
//   - LHS == its value      -> Holds
func decideIs(args []core.Value) completion.TheoryGround {
	if len(args) != 2 {
		return arithFails("arith_bad_arity")
	}
	rhs, settled, ok := settle(evalArith(args[1]))
	if !ok {
		return settled
	}
	// `is` unifies arg0 with the embedding of the result's SORT (int(…) or decimal(…),
	// #331). The atom is ground, so "unify" is structural equality against the canonical
	// embedding: a decimal result lowers to decimal(…), so `5 is 2+3.0` fails (decimal(5,0)
	// != int(5)) and `5.0 is 2+3.0` holds.
	return arithHoldsIf(core.Equal(args[0], rhs.toTerm()))
}

// decideCompare decides one of the six arithmetic comparisons: evaluate both operands and accept
// iff `accept(cmp(a, b))`. A non-2 arity has no relation (arith_bad_arity). The operands are
// evaluated left to right and the first that gives no value settles the comparison, as a stop
// inside one expression does: a domainError makes it false (its code), a work cap leaves it not
// decided (#3126). Mirrors Rust's decide_compare.
func decideCompare(args []core.Value, accept func(int) bool) completion.TheoryGround {
	if len(args) != 2 {
		return arithFails("arith_bad_arity")
	}
	a, settled, ok := settle(evalArith(args[0]))
	if !ok {
		return settled
	}
	b, settled, ok := settle(evalArith(args[1]))
	if !ok {
		return settled
	}
	// Compare by VALUE across the int/decimal sorts (#331), so `2 =:= 2.0` holds.
	return arithHoldsIf(accept(a.cmpValue(b)))
}

// evalArith evaluates an arithmetic-expression value to an exact *big.Int, mirroring
// Rust's eval_arith. The grammar (over a ground value — there are no Vars in a
// ground atom, so the unbound-variable arm of Rust's eval is statically absent here):
//   - an int embedding Tuple(Atom("int"), Atom(payload)) -> its integer value;
//   - an operator compound Tuple(Atom(op), arg…) for a known op/arity -> combine;
//   - anything else (a bare/decimal atom, an unknown operator, the wrong arity for
//     an operator) -> a domainError, the language's answer that it has no value;
//   - an exceeded decimal scale alignment -> a stop (#3126), not decided.
//
// Never a panic on an input. There is no depth at which it stops (#3123): the walk keeps its place on an explicit heap stack,
// so a deep expression evaluates like a shallow one. Until #3123 a recursive walk stopped
// at 256 levels and the stop was read as a failure, so a capacity became a decided false
// that a negation or a closure read as knowledge. Operands are evaluated left to right and
// each compound is applied after its operands, the order the recursion used.
func evalArith(root core.Value) evaluation {
	work := []arithFrame{{op: arithEval, value: root}}
	var vals []num
	for len(work) > 0 {
		f := work[len(work)-1]
		work = work[:len(work)-1]
		switch f.op {
		case arithEval:
			v := f.value
			// A number leaf: the frozen ontos-data int embedding, then the decimal embedding (#331).
			if n, err := data.ReadInt(v); err == nil {
				vals = append(vals, numInt(n))
				continue
			}
			if d, ok := decFromTerm(v); ok {
				vals = append(vals, numDec(d))
				continue
			}
			tuple, ok := v.(core.Tuple)
			if !ok {
				// A bare or number-shaped atom is not an evaluable number.
				return noValue(domainNotANumber)
			}
			items := tuple.Items()
			if len(items) == 0 {
				return noValue(domainNotANumber)
			}
			op, ok := items[0].(core.Atom)
			if !ok {
				// Head child is not an operator atom.
				return noValue(domainNotANumber)
			}
			operands := items[1:]
			// The apply runs after every operand: it is pushed first (LIFO), and the operands in
			// reverse, so the leftmost is evaluated first.
			work = append(work, arithFrame{op: arithApply, operator: string(op.Bytes()), base: len(vals), arity: len(operands)})
			for i := len(operands) - 1; i >= 0; i-- {
				work = append(work, arithFrame{op: arithEval, value: operands[i]})
			}
		case arithApply:
			if len(vals)-f.base != f.arity {
				panic(fmt.Sprintf("arithmetic walk: an apply step found %d values above its base, want its arity %d", len(vals)-f.base, f.arity))
			}
			result := applyOperator(f.operator, vals[f.base:])
			if result.arm != evalValue {
				return result
			}
			vals = append(vals[:f.base], result.value)
		case arithFrameInvalid:
			// The zero value: a frame built without an op. Never read as a step.
			panic("arithmetic walk: a frame with no op")
		default:
			// A value no constant names: a frame nobody built.
			panic(fmt.Sprintf("arithmetic walk: frame op %d is not a step", f.op))
		}
	}
	// Every compound consumed its operands and pushed one value, so the root's is the only one.
	if len(vals) != 1 {
		panic(fmt.Sprintf("arithmetic walk: the root left %d values", len(vals)))
	}
	return valueOf(vals[0])
}

// arithFrameOp names one step of evalArith's walk. The walk's control lives HERE, never in the
// value stack or in the input (research 0030: no input value can be read as a control marker),
// and the zero value is deliberately invalid, so a frame built without an op is refused rather
// than read as one of the two steps.
type arithFrameOp uint8

const (
	// arithFrameInvalid is the zero value: never a step.
	arithFrameInvalid arithFrameOp = iota
	// arithEval evaluates value and pushes its number onto the value stack.
	arithEval
	// arithApply applies operator to the arity values from base up, which are its operands,
	// in order, and replaces them with the result.
	arithApply
)

// arithFrame is one step of evalArith's walk: an arithEval carries value; an arithApply carries
// operator, base and arity.
type arithFrame struct {
	op       arithFrameOp
	value    core.Value
	operator string
	base     int
	arity    int
}

// applyOperator applies an arithmetic operator to its already-evaluated operands,
// mirroring Rust's apply_operator EXACTLY: same operator/arity set, same exact-/
// truncating-division split, same floored mod, same domainError on an unknown
// operator or a zero divisor, and the same stop past the decimal work cap (#3126). The
// /-operator is EXACT division: a non-even quotient has no value (no fractional integer, never a
// float — Rust's div_exact).
func applyOperator(op string, vals []num) evaluation {
	switch op {
	case "+":
		if len(vals) == 2 {
			return numAdd(vals[0], vals[1])
		}
	case "-":
		switch len(vals) {
		case 2:
			return numSub(vals[0], vals[1])
		case 1:
			return valueOf(vals[0].negate()) // unary minus
		}
	case "*":
		if len(vals) == 2 {
			return numMul(vals[0], vals[1])
		}
	case "abs":
		if len(vals) == 1 {
			return valueOf(vals[0].abs())
		}
	case "min":
		// Order by value across sorts; return the chosen operand in its OWN sort (ties
		// keep the left operand).
		if len(vals) == 2 {
			if vals[0].cmpValue(vals[1]) > 0 {
				return valueOf(vals[1])
			}
			return valueOf(vals[0])
		}
	case "max":
		if len(vals) == 2 {
			if vals[0].cmpValue(vals[1]) < 0 {
				return valueOf(vals[1])
			}
			return valueOf(vals[0])
		}
	case "/":
		// Exact division in BOTH domains: integer (even quotient only) / decimal
		// (terminating-in-base-10 only). Fail loud otherwise — never a float (#331).
		if len(vals) == 2 {
			return numDiv(vals[0], vals[1])
		}
	case "//":
		// Truncating integer division (toward zero), same convention in both domains;
		// always an integer result. Fail loud on /0 (ADR 0022 Amendment).
		if len(vals) == 2 {
			return numFloorDiv(vals[0], vals[1])
		}
	case "mod":
		// ISO floored modulo (sign of the divisor), same convention in both domains;
		// result int for two ints, decimal when an operand is decimal. Fail loud on /0.
		if len(vals) == 2 {
			return numMod(vals[0], vals[1])
		}
	}
	// Unknown operator/arity.
	return noValue(domainUnknownOperator)
}

// numAdd: integer-closed when both are integers (byte-identical to the pre-#331 path),
// else promoted to the decimal domain.
func numAdd(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		return valueOf(numInt(new(big.Int).Add(a.i, b.i)))
	}
	d, err := a.toDecimal().add(b.toDecimal())
	return decimalStep(numDec(d), err)
}

func numSub(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		return valueOf(numInt(new(big.Int).Sub(a.i, b.i)))
	}
	d, err := a.toDecimal().sub(b.toDecimal())
	return decimalStep(numDec(d), err)
}

func numMul(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		return valueOf(numInt(new(big.Int).Mul(a.i, b.i)))
	}
	d, err := a.toDecimal().mul(b.toDecimal())
	return decimalStep(numDec(d), err)
}

// numDiv: exact integer division (even quotient) or exact terminating decimal division.
func numDiv(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		if b.i.Sign() == 0 {
			return noValue(domainDivisionByZero)
		}
		q, ok := divExact(a.i, b.i)
		if !ok {
			return noValue(domainInexactDivision)
		}
		return valueOf(numInt(q))
	}
	d, err := a.toDecimal().divTerminating(b.toDecimal())
	return decimalStep(numDec(d), err)
}

// numFloorDiv applies a // b — TRUNCATING integer division (toward zero), the same
// rounding convention in both domains (ADR 0022 Amendment). Integer: the truncated
// quotient (Quo, byte-identical to the pre-decimal path). Decimal (any operand a decimal,
// the integers promoted): the exact quotient of the scaled mantissas truncated toward zero
// (divTruncInt) — e.g. -7.5 // 2 = -3 (NOT floor -4). The result is always an INTEGER in
// both domains. domainDivisionByZero on a zero divisor.
func numFloorDiv(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		q, ok := divTrunc(a.i, b.i)
		if !ok {
			return noValue(domainDivisionByZero)
		}
		return valueOf(numInt(q))
	}
	q, err := a.toDecimal().divTruncInt(b.toDecimal())
	return decimalStep(numInt(q), err)
}

// numMod applies a mod b — ISO FLOORED modulo (sign of the divisor), the same sign
// convention in both domains (ADR 0022 Amendment). Integer: the floored remainder
// (modFloored, byte-identical to the pre-decimal path), result INTEGER. Decimal (any
// operand a decimal, the integers promoted): a − floor(a/b)·b (moduloFloored) — always
// exact (no division), result DECIMAL — e.g. 7.5 mod 0.25 = 0.0, -7.5 mod 2 = 0.5 (sign
// follows the divisor). domainDivisionByZero on a zero divisor.
func numMod(a, b num) evaluation {
	if !a.isDec && !b.isDec {
		r, ok := modFloored(a.i, b.i)
		if !ok {
			return noValue(domainDivisionByZero)
		}
		return valueOf(numInt(r))
	}
	d, err := a.toDecimal().moduloFloored(b.toDecimal())
	return decimalStep(numDec(d), err)
}

// divExact returns a/b iff b divides a evenly; nil/false on a zero divisor or a
// non-zero remainder. Mirrors Rust's BigInt::div_exact: there is no fractional
// integer, so an inexact division is a domain error (the goal fails), never a
// truncation and never a float.
func divExact(a, b *big.Int) (*big.Int, bool) {
	if b.Sign() == 0 {
		return nil, false
	}
	// Truncated division toward zero (Go's Quo/Rem), matching Rust's div_rem_trunc.
	q := new(big.Int)
	r := new(big.Int)
	q.QuoRem(a, b, r)
	if r.Sign() != 0 {
		return nil, false // inexact: operands do not divide evenly
	}
	return q, true
}

// divTrunc returns the truncating quotient a // b (toward zero); nil/false on /0.
// Mirrors Rust's // (div_rem_trunc quotient). Go's Quo truncates toward zero.
func divTrunc(a, b *big.Int) (*big.Int, bool) {
	if b.Sign() == 0 {
		return nil, false
	}
	return new(big.Int).Quo(a, b), true
}

// modFloored returns the ISO floored modulo `a mod b` (result takes the sign of the
// divisor b); nil/false on /0. Mirrors Rust's BigInt::modulo_floored.
//
// Go's big.Int.Mod is the EUCLIDEAN modulus (always non-negative), which differs
// from ISO floored mod when the divisor is negative. So compute the truncated
// remainder (Rem, sign of dividend) and correct it onto the divisor's side exactly
// as Rust does.
func modFloored(a, b *big.Int) (*big.Int, bool) {
	if b.Sign() == 0 {
		return nil, false
	}
	r := new(big.Int).Rem(a, b) // truncated remainder: sign of the dividend a
	// Floored mod differs from the truncated remainder exactly when r is non-zero
	// and its sign differs from the divisor's: then add the divisor.
	if r.Sign() != 0 && r.Sign() != b.Sign() {
		r.Add(r, b)
	}
	return r, true
}
