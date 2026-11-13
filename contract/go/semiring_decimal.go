// The two decimal core semirings of v2 §8.3 (ADR 0031 D2), Tropical and Probability, over the
// contract's exact decimal (the frozen ontos-data decimal embedding). [PROPOSED] The Go binding of
// contract/rs/src/semiring_decimal.rs.
//
// Their carriers were ruled on #1821 (2026-11-11): exact only, no float (#331).
//   - An element is a CANONICAL non-negative decimal: decimal(int m, int e) with a non-zero m not
//     divisible by 10, zero only as decimal(0, 0), and e inside the decimal value band
//     (|e| <= 65536, #2679). An integer value is the decimal with e >= 0; an int embedding is NOT
//     an element, since two spellings of one value would break the axioms under value equality.
//   - Tropical adds +∞, the atom inf, as its zero.
//   - Both carriers declare the decimal's capacity bounds (ADR 0031 D1 as clarified on #1821): a
//     sum whose operands need an alignment shift past the decimal's cap (#3126), or a result whose
//     exponent leaves the band, is a capacity stop (SemiringCapacity), never an element and never
//     a rejection.

package contract

import (
	"math/big"

	core "github.com/bitspark/ontos/core/go"
)

// TropicalInfinity returns the bytes of the atom Tropical's +∞ is spelled with. A function, so no
// importer can rebind it.
func TropicalInfinity() []byte { return []byte("inf") }

// ringNonNegative is the canonical non-negative decimal v embeds, or ok=false.
func ringNonNegative(v core.Value) (bigDecimal, bool) {
	d, ok := decFromTerm(v)
	if !ok || d.isNegative() {
		return bigDecimal{}, false
	}
	return d, true
}

// ringDecimalAnswer is a decimal operation's result as a semiring answer: the element, or a
// capacity stop for every error (+ and × never divide, so the division errors cannot arise).
func ringDecimalAnswer(d bigDecimal, err decimalError) SemiringAnswer {
	if err != decOK {
		return SemiringCapacity()
	}
	return SemiringElement{Value: d.toDecimalTerm()}
}

func ringInfinity() core.Value { return core.NewAtom(TropicalInfinity()) }

// ringCost reads a Tropical element: a finite decimal (infinite=false) or +∞ (infinite=true).
func ringCost(v core.Value) (d bigDecimal, infinite bool, ok bool) {
	if core.Equal(v, ringInfinity()) {
		return bigDecimal{}, true, true
	}
	d, ok = ringNonNegative(v)
	return d, false, ok
}

// tropicalSemiring is the tropical semiring (ℚ≥0 ∪ {+∞}, min, +, +∞, 0).
type tropicalSemiring struct{}

// NewTropicalSemiring returns the tropical semiring (ℚ≥0 ∪ {+∞}, min, +, +∞, 0) over exact
// decimals (v2 §8.3 Tropical; ADR 0031 D2), a core semiring: shortest-path cost. It declares
// Idempotent, Bounded (min(0, a) = 0, so recursion through it converges), Monotone and
// Commutative; it does not support retraction. Identity logos-core/tropical-semiring@1.0.0.
func NewTropicalSemiring() Semiring { return tropicalSemiring{} }

func (tropicalSemiring) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("logos-core/tropical-semiring"), []byte("1.0.0"), [32]byte{})
}

func (tropicalSemiring) Laws() LawDeclaration {
	return LawDeclaration{Idempotent: true, Bounded: true, Monotone: true, Commutative: true}
}

func (tropicalSemiring) Zero() core.Value { return ringInfinity() }

func (tropicalSemiring) One() core.Value { return decZero().toDecimalTerm() }

func (tropicalSemiring) IsElement(v core.Value) bool {
	_, _, ok := ringCost(v)
	return ok
}

// Add is min(a, b); +∞ is its identity.
func (tropicalSemiring) Add(a, b core.Value) SemiringAnswer {
	x, xInf, okA := ringCost(a)
	y, yInf, okB := ringCost(b)
	switch {
	case !okA || !okB:
		return SemiringNotAnElement{}
	case xInf:
		return SemiringElement{Value: b}
	case yInf:
		return SemiringElement{Value: a}
	case y.cmp(x) < 0:
		return SemiringElement{Value: b}
	}
	return SemiringElement{Value: a}
}

// Mul is a + b; +∞ absorbs.
func (tropicalSemiring) Mul(a, b core.Value) SemiringAnswer {
	x, xInf, okA := ringCost(a)
	y, yInf, okB := ringCost(b)
	switch {
	case !okA || !okB:
		return SemiringNotAnElement{}
	case xInf || yInf:
		return SemiringElement{Value: ringInfinity()}
	}
	return ringDecimalAnswer(x.add(y))
}

// probabilitySemiring is the probability semiring (ℚ≥0, +, ×, 0, 1).
type probabilitySemiring struct{}

// NewProbabilitySemiring returns the probability semiring (ℚ≥0, +, ×, 0, 1) over exact decimals
// (v2 §8.3 Probability(Independence::Assumed), §14.4; ADR 0031 D2), a core semiring:
// sum-product, as ruled on #1821. Derivations that share base facts are counted twice and a
// value can exceed 1: the declared interpretation, not an error. It declares Monotone,
// Commutative and SupportsRetraction; it is neither idempotent nor bounded. Identity
// logos-core/probability-semiring@1.0.0.
func NewProbabilitySemiring() Semiring { return probabilitySemiring{} }

func (probabilitySemiring) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("logos-core/probability-semiring"), []byte("1.0.0"), [32]byte{})
}

func (probabilitySemiring) Laws() LawDeclaration {
	return LawDeclaration{Monotone: true, Commutative: true, SupportsRetraction: true}
}

func (probabilitySemiring) Zero() core.Value { return decZero().toDecimalTerm() }

func (probabilitySemiring) One() core.Value { return decFromBigInt(big.NewInt(1)).toDecimalTerm() }

func (probabilitySemiring) IsElement(v core.Value) bool {
	_, ok := ringNonNegative(v)
	return ok
}

func (probabilitySemiring) Add(a, b core.Value) SemiringAnswer {
	x, okA := ringNonNegative(a)
	y, okB := ringNonNegative(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return ringDecimalAnswer(x.add(y))
}

func (probabilitySemiring) Mul(a, b core.Value) SemiringAnswer {
	x, okA := ringNonNegative(a)
	y, okB := ringNonNegative(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return ringDecimalAnswer(x.mul(y))
}
