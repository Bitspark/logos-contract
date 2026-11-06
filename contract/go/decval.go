// bigDecimal — the Go binding of logos's exact-decimal numeric domain (#331), a
// judgment-for-judgment mirror of the Rust BigDecimal in contract/rs/src/decval.rs.
//
// A decimal is mantissa × 10^exponent, exact (no float — the §1.3 prize is structural
// value equality, which float breaks). Its ground form IS the FROZEN ontos-data §5.9
// `decimal` embedding Tuple(Atom("decimal"), int(mantissa), int(exponent)), canonical
// (a non-zero mantissa is not divisible by 10; zero is decimal(int 0, int 0)). All
// arithmetic reuses math/big — there is no second bignum.
//
// # The scale bound (#331 — total, DoS-resistant checker; byte-identical to Rust)
//
// The mantissa is UNBOUNDED (math/big, like the integer domain); the exponent is bounded
// to i128 — a decimal term whose exponent exceeds i128 is NOT a well-formed number
// (decFromTerm returns ok=false), matching Rust's i128 scale bound. Comparison decides by
// magnitude ORDER (digit-count + exponent) and only aligns within a shared decade (shift
// bounded by the digit counts). +/− align scales; the shift is capped at
// maxDecimalScaleShift (an adversarial vast exponent gap fails rather than materializing a
// giant integer). × and ÷ never align (they add/subtract exponents).
//
// # The value domain (#2679: one constructor, not one guard per producer)
//
// Every decimal has |exponent| <= maxDecimalExponent. Since #1385 that band IS the value
// domain on the wire, so a producer that minted a past-band value handed back something no
// core can read as a number. decFromParts is the ONE limit-checked constructor: every
// decimal-producing path (the arithmetic results and decFromString) returns through it.
// Mirrors Rust's BigDecimal::from_parts (research-docs/0016; seat:caa's ruling on #2679).
package contract

import (
	"math/big"
	"strings"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// decimalLabel is the functor label of the ontos/data `decimal` embedding.
const decimalLabel = "decimal"

// decimalError is why a decimal operation returned no value (#3161, #3126), Rust's DecimalError. Two
// kinds, and the difference is the point: the first three are the LANGUAGE's answer (the expression
// has no value in ADR 0022's domain, so the goal is false), and decAlignmentCap is the
// IMPLEMENTATION stopping before it knew (not decided). Nothing converts one into the other. The
// zero value, decOK, is no error.
type decimalError uint8

const (
	// decOK: the operation returned its value.
	decOK decimalError = iota
	// decDivisionByZero: a zero divisor for /, // or mod.
	decDivisionByZero
	// decNonTerminating: a / whose exact quotient does not terminate in base 10 (1.0 / 3).
	decNonTerminating
	// decOutsideDomain: the result lies outside the value domain |exponent| <= maxDecimalExponent.
	decOutsideDomain
	// decAlignmentCap: the exact alignment of two in-domain operands needs a shift past
	// maxDecimalScaleShift, a work cap. The result exists; it was not computed.
	decAlignmentCap
)

// maxDecimalScaleShift caps the +/− scale-alignment shift, mirroring Rust's
// MAX_DECIMAL_SCALE_SHIFT. Far above any realistic decimal, yet bounding the work so an
// adversarial ground term cannot force the trusted checker to build an enormous integer. A WORK
// CAP, not a failure (#3126): both operands are in the value domain and the result exists, so the
// stop is decAlignmentCap, which the evaluator reports as not decided, never as the goal failing.
// A DIFFERENT quantity from maxDecimalExponent (the VALUE bound): they share a number and are
// two names on purpose, so changing one never silently moves the other (research-docs/0016).
const maxDecimalScaleShift int64 = 65536

// maxDecimalExponent is the decimal value domain (#2679), mirroring Rust's
// MAX_DECIMAL_EXPONENT: every decimal logos produces or decodes has |exponent| <= it. Checked
// in ONE place, decFromParts, and at the wire decode (decFromTerm, #1385). INCLUSIVE: 1e65536
// is a value, 1e65537 is not.
const maxDecimalExponent int64 = 65536

// inDecimalDomain reports whether exponent lies in the decimal value domain.
func inDecimalDomain(exponent *big.Int) bool {
	return exponent.CmpAbs(big.NewInt(maxDecimalExponent)) <= 0
}

// i128Max is 2^127 − 1, the exponent scale bound (mirroring Rust's i128-bounded
// exponent). A decimal whose exponent magnitude exceeds this is not a well-formed number.
var i128Max = new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 127), big.NewInt(1))

// bigDecimal is an exact decimal mantissa × 10^exponent — the decimal sibling of the
// math/big integer domain. Canonical: a non-zero mantissa is not divisible by 10; zero is
// (0, 0). The mantissa is unbounded; the exponent is i128-bounded on decode (#331).
type bigDecimal struct {
	mantissa *big.Int
	exponent *big.Int
}

// decZero is the decimal zero, decimal(int 0, int 0).
func decZero() bigDecimal {
	return bigDecimal{mantissa: big.NewInt(0), exponent: big.NewInt(0)}
}

// decFromParts builds a canonical bigDecimal from a (mantissa, exponent) pair: zero
// collapses to (0,0); otherwise trailing base-10 zeros of the mantissa are carried into
// the exponent (the ontos canonical form, one spelling per value). Mirrors Rust's
// BigDecimal::from_parts.
//
// THE ONE LIMIT-CHECKED CONSTRUCTOR (#2679): ok=false when the CANONICAL exponent lies outside
// the value domain |exponent| <= maxDecimalExponent. Every decimal-producing path returns
// through here. The check runs AFTER canonicalization, because stripping trailing zeros raises
// the exponent and what must be in the domain is the value that actually results.
//
// Also ok=false when carrying a trailing zero would push the exponent past the i128 scale
// bound (#475): the canonicalization increment is CHECKED, not unbounded, so a value that
// cannot be represented as a well-formed i128-scaled decimal is rejected here (the goal
// fails) rather than producing a decimal(…, >i128) term that re-decodes as not-a-number —
// the live tri-core divergence at the exponent boundary (rs used to saturate; go/ts carried
// the increment on an unbounded big.Int/bigint). Now all three reject identically.
func decFromParts(mantissa, exponent *big.Int) (bigDecimal, bool) {
	d, ok := decCanonical(mantissa, exponent)
	if !ok || !inDecimalDomain(d.exponent) {
		return bigDecimal{}, false
	}
	return d, true
}

// decCanonical is the canonical form of mantissa × 10^exponent WITHOUT the domain check:
// ok=false only on the i128 canonicalization overflow (#475). Mirrors Rust's canonical.
func decCanonical(mantissa, exponent *big.Int) (bigDecimal, bool) {
	if mantissa.Sign() == 0 {
		return decZero(), true
	}
	m := new(big.Int).Set(mantissa)
	e := new(big.Int).Set(exponent)
	ten := big.NewInt(10)
	q := new(big.Int)
	r := new(big.Int)
	for {
		q.QuoRem(m, ten, r)
		if r.Sign() == 0 {
			m.Set(q)
			e.Add(e, big.NewInt(1))
			if e.CmpAbs(i128Max) > 0 {
				return bigDecimal{}, false // canonical exponent left the i128 band
			}
		} else {
			break
		}
	}
	return bigDecimal{mantissa: m, exponent: e}, true
}

// decFromBigInt promotes an exact integer to a decimal (n × 10^0). The int → decimal
// promotion the mixed-domain operators use.
//
// Infallible: the exponent starts at 0 and canonicalization carries at most digitCount(n)
// trailing zeros, so the result exponent is bounded by the operand's own digit count
// (input-proportional) — it cannot reach i128::MAX for any term that fits in memory. It
// canonicalizes WITHOUT the domain check (#2679): a promoted integer is an OPERAND, never a
// result, and an integer past 10^65536 must still compare and promote. Every decimal an
// operation RETURNS goes through decFromParts, including add's zero short-circuits.
func decFromBigInt(n *big.Int) bigDecimal {
	d, _ := decCanonical(n, big.NewInt(0))
	return d
}

// decFromString parses a decimal literal spelling [-+]?<digits>.<digits> (a `.` with at
// least one digit on each side), or ok=false for any other shape. Mirrors Rust's
// BigDecimal::from_decimal_str. ok=false, too, for a spelling whose value lies outside the
// domain (#2679, seat:caa's ruling (a)): it returns through decFromParts like every
// arithmetic result.
func decFromString(s string) (bigDecimal, bool) {
	negative := false
	rest := s
	if len(s) > 0 && (s[0] == '-' || s[0] == '+') {
		negative = s[0] == '-'
		rest = s[1:]
	}
	dot := strings.IndexByte(rest, '.')
	if dot < 0 {
		return bigDecimal{}, false
	}
	intPart := rest[:dot]
	fracPart := rest[dot+1:]
	if intPart == "" || fracPart == "" || !allDigits(intPart) || !allDigits(fracPart) {
		return bigDecimal{}, false
	}
	magnitude, ok := new(big.Int).SetString(intPart+fracPart, 10)
	if !ok {
		return bigDecimal{}, false
	}
	if negative {
		magnitude.Neg(magnitude)
	}
	// The exponent is −fracLen <= 0, and canonicalization only carries it up, so the i128 bound
	// cannot overflow here. The DOMAIN can: a fraction longer than maxDecimalExponent digits
	// (after its trailing zeros are stripped) is refused by decFromParts (#2679).
	exponent := big.NewInt(-int64(len(fracPart)))
	return decFromParts(magnitude, exponent)
}

func (d bigDecimal) isZero() bool     { return d.mantissa.Sign() == 0 }
func (d bigDecimal) isNegative() bool { return d.mantissa.Sign() < 0 }

func (d bigDecimal) negate() bigDecimal {
	return bigDecimal{mantissa: new(big.Int).Neg(d.mantissa), exponent: new(big.Int).Set(d.exponent)}
}

func (d bigDecimal) abs() bigDecimal {
	return bigDecimal{mantissa: new(big.Int).Abs(d.mantissa), exponent: new(big.Int).Set(d.exponent)}
}

// cmp is the total value order (consistent with equality): sign first, then by magnitude
// ORDER (alignment-free unless two same-sign values share a decade). Mirrors Rust's
// BigDecimal::cmp. Returns -1/0/+1.
func (d bigDecimal) cmp(o bigDecimal) int {
	dn, on := d.isNegative(), o.isNegative()
	switch {
	case !dn && on:
		return 1
	case dn && !on:
		return -1
	case !dn && !on:
		return cmpDecMagnitude(d, o)
	default: // both negative: reverse the magnitude order
		return cmpDecMagnitude(o, d)
	}
}

// cmpDecMagnitude compares two same-sign decimals by magnitude. Decides by order
// (digit-count + exponent); only aligns within a shared decade (shift bounded by the
// digit counts). Mirrors Rust's cmp_magnitude.
func cmpDecMagnitude(a, b bigDecimal) int {
	switch {
	case a.isZero() && b.isZero():
		return 0
	case a.isZero():
		return -1
	case b.isZero():
		return 1
	}
	orderA := new(big.Int).Add(big.NewInt(int64(digitCount(a.mantissa))), a.exponent)
	orderB := new(big.Int).Add(big.NewInt(int64(digitCount(b.mantissa))), b.exponent)
	if c := orderA.Cmp(orderB); c != 0 {
		return c
	}
	// Same decade ⇒ the exponent gap equals the digit-count difference (small): align to
	// the smaller exponent and compare magnitudes.
	eMin := bigIntMin(a.exponent, b.exponent)
	magA := new(big.Int).Mul(new(big.Int).Abs(a.mantissa), pow10(int(new(big.Int).Sub(a.exponent, eMin).Int64())))
	magB := new(big.Int).Mul(new(big.Int).Abs(b.mantissa), pow10(int(new(big.Int).Sub(b.exponent, eMin).Int64())))
	return magA.Cmp(magB)
}

// add returns self + other (exact), decAlignmentCap if the scale alignment exceeds
// maxDecimalScaleShift (not decided, #3126), or decOutsideDomain. Mirrors Rust's BigDecimal::add.
func (d bigDecimal) add(o bigDecimal) (bigDecimal, decimalError) {
	// A zero operand returns the other one, and that one may be a promoted integer outside the
	// domain (see decFromBigInt), so it is re-checked like every result (#2679).
	if d.isZero() {
		return inDomain(decFromParts(o.mantissa, o.exponent))
	}
	if o.isZero() {
		return inDomain(decFromParts(d.mantissa, d.exponent))
	}
	eMin := bigIntMin(d.exponent, o.exponent)
	shiftD := new(big.Int).Sub(d.exponent, eMin)
	shiftO := new(big.Int).Sub(o.exponent, eMin)
	maxShift := shiftD
	if shiftO.Cmp(shiftD) > 0 {
		maxShift = shiftO
	}
	if maxShift.Cmp(big.NewInt(maxDecimalScaleShift)) > 0 {
		return bigDecimal{}, decAlignmentCap
	}
	mD := new(big.Int).Mul(d.mantissa, pow10(int(shiftD.Int64())))
	mO := new(big.Int).Mul(o.mantissa, pow10(int(shiftO.Int64())))
	return inDomain(decFromParts(new(big.Int).Add(mD, mO), eMin))
}

// inDomain is decFromParts' refusal as the decimal error it is: a result outside the value domain.
func inDomain(d bigDecimal, ok bool) (bigDecimal, decimalError) {
	if !ok {
		return bigDecimal{}, decOutsideDomain
	}
	return d, decOK
}

// sub returns self − other (exact); see add for the scale bound.
func (d bigDecimal) sub(o bigDecimal) (bigDecimal, decimalError) {
	return d.add(o.negate())
}

// mul returns self * other (exact): multiply mantissas, add exponents (no alignment).
// ok=false when the product lies outside the value domain (#1022's cap, which go never got,
// now decFromParts' for all three cores, #2679), on the astronomical i128 exponent overflow, OR
// (#475) when canonicalizing the
// product mantissa carries a trailing zero past i128::MAX (e.g. decimal(2, i128::MAX) *
// decimal(5, 0) → mantissa 10, exponent i128::MAX + 1) — decFromParts rejects that
// boundary, in parity with Rust/TS. Each refusal is decOutsideDomain: the i128 overflow is past
// the domain by the argument Rust's mul records (research 0031 row 5), since for in-domain operands
// the canonical exponent stays within a digit count of e1 + e2.
func (d bigDecimal) mul(o bigDecimal) (bigDecimal, decimalError) {
	if d.isZero() || o.isZero() {
		return decZero(), decOK
	}
	exponent := new(big.Int).Add(d.exponent, o.exponent)
	if exponent.CmpAbs(i128Max) > 0 {
		return bigDecimal{}, decOutsideDomain
	}
	return inDomain(decFromParts(new(big.Int).Mul(d.mantissa, o.mantissa), exponent))
}

// divTerminating returns self / other iff the quotient TERMINATES in base 10 (the reduced
// denominator's only prime factors are 2 and 5); otherwise ok=false (the goal fails — no
// rounding, no float). ok=false on a zero divisor. Mirrors Rust's BigDecimal::div_terminating.
func (d bigDecimal) divTerminating(o bigDecimal) (bigDecimal, decimalError) {
	if o.isZero() {
		return bigDecimal{}, decDivisionByZero
	}
	if d.isZero() {
		return decZero(), decOK
	}
	k := factorCount(o.mantissa, 2)
	if q5 := factorCount(o.mantissa, 5); q5 > k {
		k = q5
	}
	scaledNum := new(big.Int).Mul(d.mantissa, pow10(k))
	quotient, ok := divExact(scaledNum, o.mantissa)
	if !ok {
		return bigDecimal{}, decNonTerminating
	}
	exponent := new(big.Int).Sub(new(big.Int).Sub(d.exponent, o.exponent), big.NewInt(int64(k)))
	if exponent.CmpAbs(i128Max) > 0 {
		return bigDecimal{}, decOutsideDomain
	}
	// #2679: / had no domain check, so 1e40000 / 1e-40000 minted decimal(1, 80000), which no
	// core decodes. It returns through the one constructor, which also rejects #475's boundary.
	return inDomain(decFromParts(quotient, exponent))
}

// alignedMantissas aligns d and o to their common (smaller) exponent and returns the two
// INTEGER mantissas at that scale plus the shared exponent, or decAlignmentCap if the alignment
// shift exceeds maxDecimalScaleShift (not decided, #3126 — the same DoS bound add/sub enforce).
// At the common scale eMin the values are Xs × 10^eMin and Ys × 10^eMin, so d/o = Xs/Ys
// EXACTLY — the cancelling scale factor lets // and mod reduce to integer division on
// (Xs, Ys) with no decimal division (no termination concern). Mirrors Rust's
// BigDecimal::aligned_mantissas; used by divTruncInt and moduloFloored.
func (d bigDecimal) alignedMantissas(o bigDecimal) (*big.Int, *big.Int, *big.Int, decimalError) {
	eMin := bigIntMin(d.exponent, o.exponent)
	shiftD := new(big.Int).Sub(d.exponent, eMin)
	shiftO := new(big.Int).Sub(o.exponent, eMin)
	maxShift := shiftD
	if shiftO.Cmp(shiftD) > 0 {
		maxShift = shiftO
	}
	if maxShift.Cmp(big.NewInt(maxDecimalScaleShift)) > 0 {
		return nil, nil, nil, decAlignmentCap
	}
	xs := new(big.Int).Mul(d.mantissa, pow10(int(shiftD.Int64())))
	ys := new(big.Int).Mul(o.mantissa, pow10(int(shiftO.Int64())))
	return xs, ys, eMin, decOK
}

// divTruncInt returns d // o — TRUNCATING integer division (toward zero), the decimal
// lift of the integer // (Quo). The result is an exact INTEGER (*big.Int), not a decimal:
// // answers "how many whole o's fit in d", e.g. 7.5 // 2 = 3, -7.5 // 2 = -3 (toward
// zero, NOT floor -4). ok=false on a zero divisor (mirroring the integer //) or an
// adversarial scale gap. Mirrors Rust's BigDecimal::div_trunc_int.
func (d bigDecimal) divTruncInt(o bigDecimal) (*big.Int, decimalError) {
	xs, ys, _, err := d.alignedMantissas(o)
	if err != decOK {
		return nil, err
	}
	if ys.Sign() == 0 {
		return nil, decDivisionByZero
	}
	return new(big.Int).Quo(xs, ys), decOK // Go's Quo truncates toward zero
}

// moduloFloored returns d mod o — ISO FLOORED modulo (the result takes the sign of the
// divisor), the decimal lift of the integer mod. The result is an exact DECIMAL:
// d mod o = d − floor(d/o)·o, always exact here (no division — pure mantissa arithmetic),
// e.g. 7.5 mod 0.25 = 0.0, -7.5 mod 2 = 0.5 (sign follows the positive divisor). ok=false
// on a zero divisor (mirroring the integer mod) or an adversarial scale gap. At the common
// scale eMin the floored remainder of the integer mantissas scaled back is the floored
// decimal remainder: (Xs mod Ys) × 10^eMin = d mod o. Mirrors Rust's BigDecimal::modulo_floored.
func (d bigDecimal) moduloFloored(o bigDecimal) (bigDecimal, decimalError) {
	xs, ys, eMin, err := d.alignedMantissas(o)
	if err != decOK {
		return bigDecimal{}, err
	}
	rem, ok := modFloored(xs, ys)
	if !ok {
		return bigDecimal{}, decDivisionByZero
	}
	return inDomain(decFromParts(rem, eMin))
}

// toDecimalTerm lowers to the ground `decimal` embedding via ontos-data EncodeDecimal —
// byte-identical to Rust's BigDecimal::to_decimal_term (the value is already canonical).
func (d bigDecimal) toDecimalTerm() core.Value {
	return data.EncodeDecimal(d.mantissa, d.exponent)
}

// decFromTerm recognizes and decodes the ontos/data `decimal` embedding, or ok=false for
// any term that is not a canonical decimal — including (the #331 scale bound) an exponent
// beyond i128. ontos-data's ReadDecimal is the canonical gate (it validates the structure
// and rejects a non-canonical mantissa); we then narrow the exponent to the i128 scale.
func decFromTerm(v core.Value) (bigDecimal, bool) {
	mantissa, exponent, err := data.ReadDecimal(v)
	if err != nil {
		return bigDecimal{}, false
	}
	// #1385: the value domain is WIRE VOCABULARY at this seam. An exponent past
	// +/-maxDecimalExponent is refused on decode rather than admitted as a print-only
	// value - every value narrowed away is one arithmetic already refuses to combine, and
	// admitting it was a live tri-core divergence (rs accepted i128::MIN; go/ts rejected
	// it, for the wrong reason). Decode-side only: decFromParts is untouched.
	if !inDecimalDomain(exponent) {
		return bigDecimal{}, false
	}
	return bigDecimal{mantissa: mantissa, exponent: exponent}, true
}

// --- small helpers ---

// digitCount is the number of base-10 digits of |n| (zero → 0).
func digitCount(n *big.Int) int {
	if n.Sign() == 0 {
		return 0
	}
	return len(new(big.Int).Abs(n).String())
}

// factorCount is how many times `base` divides |n| (bounded by digitCount(n)).
func factorCount(n *big.Int, base int64) int {
	if n.Sign() == 0 {
		return 0
	}
	b := big.NewInt(base)
	cur := new(big.Int).Abs(n)
	q := new(big.Int)
	r := new(big.Int)
	count := 0
	for {
		q.QuoRem(cur, b, r)
		if r.Sign() == 0 {
			cur.Set(q)
			count++
		} else {
			break
		}
	}
	return count
}

// pow10 is 10^exp as a big.Int (exp bounded by the caller — a scale / digit count).
func pow10(exp int) *big.Int {
	return new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(exp)), nil)
}

// bigIntMin returns whichever of a, b is the smaller value.
func bigIntMin(a, b *big.Int) *big.Int {
	if a.Cmp(b) <= 0 {
		return a
	}
	return b
}

// allDigits reports whether every byte of s is an ASCII digit (s assumed non-empty).
func allDigits(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return true
}
