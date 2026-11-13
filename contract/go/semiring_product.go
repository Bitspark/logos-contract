// The product semiring (v2 §14.2; ADR 0031 D2): the binary product of two semirings, its first
// member then its second, with the rules ruled on #1821 (Q23 to Q28). [PROPOSED] The Go binding of
// contract/rs/src/semiring_product.rs; contract/ts/src/semiring_product.ts is the third.
//
//   - An element is a bare Tuple[a, b] of arity exactly 2, a an element of the first member and b
//     of the second. Zero and One are componentwise.
//   - Add and Mul answer SemiringNotAnElement for an operand that is not a product element, before
//     any member operation runs. Otherwise the first member's operation runs first: its
//     not-an-element or its stop is the product's answer, and the second member is not consulted.
//     Then the second member's operation runs, the same way. Two elements give Tuple[r0, r1].
//   - The laws are the AND of the members' laws, field by field. The product declares no law of its
//     own.
//   - The declared identity is logos-core/product-semiring@1.0.0, its configuration digest
//     SHA-256(ProductSemiringPrefix ‖ for each member in order: u64be(len id) ‖ id ‖
//     u64be(len version) ‖ version ‖ the member's COMPUTED identity digest), the per-member layout
//     CompoundIdentityOf folds. A member's computed identity (SemiringIdentity) carries its laws,
//     and the order is part of the digest, so the swapped product is another identity. The
//     product's own SemiringIdentity folds its laws as every semiring's does.

package contract

import (
	"crypto/sha256"

	core "github.com/bitspark/ontos/core/go"
)

// ProductSemiringPrefix returns the domain separator of a product semiring's configuration digest.
// A function, so no importer can rebind it.
func ProductSemiringPrefix() []byte { return []byte("logos-core/product-semiring/v1\n") }

// productSemiring is the binary product of two semirings, first then second.
type productSemiring struct {
	first  Semiring
	second Semiring
}

// NewProductSemiring returns the binary product of first and second (v2 §14.2): its elements are
// Tuple[a, b], its operations componentwise with the first member run first, and its laws the AND
// of the members' laws. Identity logos-core/product-semiring@1.0.0, its configuration digest
// committing to both members' computed identities in order; see the file comment.
func NewProductSemiring(first, second Semiring) Semiring {
	return productSemiring{first: first, second: second}
}

func (p productSemiring) DeclaredIdentity() ComponentIdentity {
	h := sha256.New()
	h.Write(ProductSemiringPrefix())
	writeIdentityMember(h, SemiringIdentity(p.first))
	writeIdentityMember(h, SemiringIdentity(p.second))
	var digest [32]byte
	copy(digest[:], h.Sum(nil))
	return NewComponentIdentity([]byte("logos-core/product-semiring"), []byte("1.0.0"), digest)
}

func (p productSemiring) Laws() LawDeclaration {
	l, r := p.first.Laws(), p.second.Laws()
	return LawDeclaration{
		Idempotent:         l.Idempotent && r.Idempotent,
		Bounded:            l.Bounded && r.Bounded,
		Monotone:           l.Monotone && r.Monotone,
		Commutative:        l.Commutative && r.Commutative,
		SupportsRetraction: l.SupportsRetraction && r.SupportsRetraction,
	}
}

func (p productSemiring) Zero() core.Value { return core.NewTuple(p.first.Zero(), p.second.Zero()) }

func (p productSemiring) One() core.Value { return core.NewTuple(p.first.One(), p.second.One()) }

func (p productSemiring) IsElement(v core.Value) bool {
	_, _, ok := p.pair(v)
	return ok
}

func (p productSemiring) Add(a, b core.Value) SemiringAnswer {
	return p.componentwise(a, b, Semiring.Add)
}

func (p productSemiring) Mul(a, b core.Value) SemiringAnswer {
	return p.componentwise(a, b, Semiring.Mul)
}

// pair is the two components of the product element v, or ok=false when v is not one: not a
// Tuple of arity 2, or a component outside its member's carrier.
func (p productSemiring) pair(v core.Value) (core.Value, core.Value, bool) {
	tuple, ok := v.(core.Tuple)
	if !ok || tuple.Len() != 2 {
		return nil, nil, false
	}
	first, second := tuple.At(0), tuple.At(1)
	if !p.first.IsElement(first) || !p.second.IsElement(second) {
		return nil, nil, false
	}
	return first, second, true
}

// componentwise is op over the product: SemiringNotAnElement for an operand that is not a product
// element, before any member runs; else the first member's answer on the first components, then
// the second member's on the second, the first that is not an element being the product's answer.
func (p productSemiring) componentwise(a, b core.Value, op func(Semiring, core.Value, core.Value) SemiringAnswer) SemiringAnswer {
	a0, a1, okA := p.pair(a)
	b0, b1, okB := p.pair(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	r0, other := productComponent(op(p.first, a0, b0))
	if other != nil {
		return other
	}
	r1, other := productComponent(op(p.second, a1, b1))
	if other != nil {
		return other
	}
	return SemiringElement{Value: core.NewTuple(r0, r1)}
}

// productComponent reads one member's answer: its element with a nil answer, or a nil element with
// the answer the product gives instead, the member's SemiringNotAnElement or its SemiringStopped.
func productComponent(answer SemiringAnswer) (core.Value, SemiringAnswer) {
	switch v := answer.(type) {
	case SemiringElement:
		return v.Value, nil
	case SemiringNotAnElement:
		return nil, v
	case SemiringStopped:
		return nil, v
	}
	panic("contract: an unknown SemiringAnswer")
}
