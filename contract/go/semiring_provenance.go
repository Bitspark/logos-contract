// The provenance core semiring ℕ[X] (v2 §8.3 Provenance; ADR 0031 D2): polynomials with natural
// coefficients over fact identities. [PROPOSED] The Go binding of
// contract/rs/src/semiring_provenance.rs.
//
// Its carrier was ruled on #1821 (2026-11-11): one canonical sorted encoding with integer
// coefficients. A polynomial is a Tuple of terms; a term is Tuple[int c, Tuple[x…]], its
// coefficient c >= 1 in the frozen ontos-data int embedding and its monomial the multiset of its
// variables, each any ground ontos value (a fact identity), in non-decreasing order of their
// ontos-codec bytes. The terms are in strictly increasing order of their monomials' codec bytes,
// so no monomial repeats. Zero is the empty Tuple; one is the single term 1·(). Coefficients are
// unbounded, so the operations never stop.

package contract

import (
	"bytes"
	"math/big"
	"sort"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ringTerm is one term of a polynomial: its monomial's variables and its coefficient.
type ringTerm struct {
	variables   []core.Value
	coefficient *big.Int
}

// ringTerms is a polynomial keyed by the codec bytes of each monomial.
type ringTerms map[string]ringTerm

// ringPolynomial is the canonical polynomial v encodes, or ok=false.
func ringPolynomial(v core.Value) (ringTerms, bool) {
	tuple, ok := v.(core.Tuple)
	if !ok {
		return nil, false
	}
	terms := ringTerms{}
	var last []byte
	for i, term := range tuple.Items() {
		pair, ok := term.(core.Tuple)
		if !ok || len(pair.Items()) != 2 {
			return nil, false
		}
		coefficient, err := data.ReadInt(pair.Items()[0])
		if err != nil || coefficient.Sign() <= 0 {
			return nil, false
		}
		monomial, ok := pair.Items()[1].(core.Tuple)
		if !ok {
			return nil, false
		}
		variables := monomial.Items()
		for j := 1; j < len(variables); j++ {
			if bytes.Compare(codec.Encode(variables[j-1]), codec.Encode(variables[j])) > 0 {
				return nil, false
			}
		}
		key := codec.Encode(monomial)
		if i > 0 && bytes.Compare(last, key) >= 0 {
			return nil, false
		}
		last = key
		terms[string(key)] = ringTerm{variables: append([]core.Value(nil), variables...), coefficient: coefficient}
	}
	return terms, true
}

// ringPolynomialValue is the canonical encoding of terms.
func ringPolynomialValue(terms ringTerms) core.Value {
	keys := make([]string, 0, len(terms))
	for k := range terms {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool { return bytes.Compare([]byte(keys[i]), []byte(keys[j])) < 0 })
	items := make([]core.Value, 0, len(keys))
	for _, k := range keys {
		t := terms[k]
		items = append(items, core.NewTuple(data.EncodeInt(t.coefficient), core.NewTuple(t.variables...)))
	}
	return core.NewTuple(items...)
}

// ringAccumulate adds coefficient · variables into terms.
func ringAccumulate(terms ringTerms, variables []core.Value, coefficient *big.Int) {
	key := string(codec.Encode(core.NewTuple(variables...)))
	if existing, ok := terms[key]; ok {
		terms[key] = ringTerm{variables: existing.variables, coefficient: new(big.Int).Add(existing.coefficient, coefficient)}
		return
	}
	terms[key] = ringTerm{variables: variables, coefficient: coefficient}
}

// provenanceSemiring is the provenance semiring ℕ[X].
type provenanceSemiring struct{}

// NewProvenanceSemiring returns the provenance semiring ℕ[X] (v2 §8.3 Provenance; ADR 0031 D2),
// a core semiring: an annotation records which facts, how many times and in which combinations,
// an answer was derived from. It declares Monotone, Commutative and SupportsRetraction; it is
// neither idempotent nor bounded. Identity logos-core/provenance-semiring@1.0.0.
func NewProvenanceSemiring() Semiring { return provenanceSemiring{} }

func (provenanceSemiring) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("logos-core/provenance-semiring"), []byte("1.0.0"), [32]byte{})
}

func (provenanceSemiring) Laws() LawDeclaration {
	return LawDeclaration{Monotone: true, Commutative: true, SupportsRetraction: true}
}

func (provenanceSemiring) Zero() core.Value { return ringPolynomialValue(ringTerms{}) }

func (provenanceSemiring) One() core.Value {
	terms := ringTerms{}
	ringAccumulate(terms, nil, big.NewInt(1))
	return ringPolynomialValue(terms)
}

func (provenanceSemiring) IsElement(v core.Value) bool {
	_, ok := ringPolynomial(v)
	return ok
}

func (provenanceSemiring) Add(a, b core.Value) SemiringAnswer {
	x, okA := ringPolynomial(a)
	y, okB := ringPolynomial(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	for _, t := range y {
		ringAccumulate(x, t.variables, t.coefficient)
	}
	return SemiringElement{Value: ringPolynomialValue(x)}
}

func (provenanceSemiring) Mul(a, b core.Value) SemiringAnswer {
	x, okA := ringPolynomial(a)
	y, okB := ringPolynomial(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	product := ringTerms{}
	for _, p := range x {
		for _, q := range y {
			variables := append(append([]core.Value(nil), p.variables...), q.variables...)
			sort.SliceStable(variables, func(i, j int) bool {
				return bytes.Compare(codec.Encode(variables[i]), codec.Encode(variables[j])) < 0
			})
			ringAccumulate(product, variables, new(big.Int).Mul(p.coefficient, q.coefficient))
		}
	}
	return SemiringElement{Value: ringPolynomialValue(product)}
}
