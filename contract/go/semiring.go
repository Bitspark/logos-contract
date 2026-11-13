// The Semiring SPI and its registration audit (ADR 0031 D1, G3; v2 §14.3). [PROPOSED]
// (ADR 0035 D7: a new extension seam enters at [PROPOSED]; its vector parity is not a tier.)
// The Go binding of contract/rs/src/semiring.rs; contract/ts/src/semiring.ts is the third.
//
// A semiring is the algebra an annotated evaluation combines values in: Add (⊕) joins
// alternative derivations, Mul (⊗) joins the premises of one derivation, Zero is the value
// of no derivation and One the value of an empty conjunction. ADR 0031 puts it on the path
// checkable theories already took: the checker may consult a semiring it did not link,
// because the verdict NAMES it by identity and what it names is pure.
//
// The obligations of an implementation:
//   - Pure, total over its carrier up to its declared capacity bounds, deterministic. Add and
//     Mul answer SemiringNotAnElement exactly when an operand is not an element (IsElement).
//     On elements they answer an element, the same one every time, or, for a result past a
//     bound the carrier declares, SemiringStopped with a capacity non-completion (ADR 0031 D1
//     as clarified on #1821): not decided, never "no such element".
//   - Laws declared, never inferred. Laws declares the five optional laws of v2 §14.3. The
//     semiring axioms are not declarable: ⊕ is associative and commutative with identity
//     Zero, ⊗ is associative with identity One, Zero annihilates, and ⊗ distributes over ⊕.
//     LawDeclaration.Commutative names ⊗; ⊕ is always commutative.
//   - Identity computed by the contract. SemiringIdentity folds the declared laws into the
//     declared (id, version, config digest), so changing a declared law changes the identity
//     a verdict names (ADR 0031 D1).
//
// What the audit can and cannot say: AuditSemiring evaluates every axiom and every declared
// law over a finite sample set, in one pinned order (SemiringAuditOrder), and reports the
// first counterexample. A finite sample can only refute a law, never prove one, so a passing
// audit is SemiringNoCounterexample: no counterexample in these samples, not "verified". A
// tuple on which an operation stopped is undecided, and a law no tuple decided is VACUOUS
// (SemiringVacuous), which is a state, never a pass.

package contract

import (
	"crypto/sha256"
	"encoding/binary"
	"math/big"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// SemiringIdentityPrefix returns the domain separator of a semiring's computed identity
// digest (SemiringIdentityOf). A function, so no importer can rebind it.
func SemiringIdentityPrefix() []byte { return []byte("logos-core/semiring-identity/v1\n") }

// SemiringAuditSampleLimit is the most caller samples AuditSemiring evaluates. The audit is
// cubic in the sample count, so a larger set is refused by name (SemiringSampleLimit).
const SemiringAuditSampleLimit = 16

// The bits of LawDeclaration.Bits, one per declarable law.
const (
	LawIdempotentBit         uint8 = 1
	LawBoundedBit            uint8 = 2
	LawMonotoneBit           uint8 = 4
	LawCommutativeBit        uint8 = 8
	LawSupportsRetractionBit uint8 = 16
)

// LawDeclaration is the five optional laws a semiring declares (v2 §14.3; ADR 0031 D1). Each
// is a CLAIM the audit tests on samples, never a fact it proves.
type LawDeclaration struct {
	// Idempotent: a ⊕ a = a.
	Idempotent bool
	// Bounded: One ⊕ a = One (absorptive), the law a fixpoint argument over recursion relies on.
	Bounded bool
	// Monotone: the natural order (a ≤ b iff a ⊕ c = b for some c) is antisymmetric.
	Monotone bool
	// Commutative: a ⊗ b = b ⊗ a (a commutative semiring; ⊕ is commutative by axiom).
	Commutative bool
	// SupportsRetraction: ⊕ is cancellative (a ⊕ b = a ⊕ c implies b = c).
	SupportsRetraction bool
}

// Bits is the declaration as one byte, the form SemiringIdentityOf hashes.
func (l LawDeclaration) Bits() uint8 {
	var bits uint8
	if l.Idempotent {
		bits |= LawIdempotentBit
	}
	if l.Bounded {
		bits |= LawBoundedBit
	}
	if l.Monotone {
		bits |= LawMonotoneBit
	}
	if l.Commutative {
		bits |= LawCommutativeBit
	}
	if l.SupportsRetraction {
		bits |= LawSupportsRetractionBit
	}
	return bits
}

// Obliges reports whether the audit tests law for a semiring with this declaration: every
// axiom always, a declarable law only when it is declared. An unknown law obliges nothing.
func (l LawDeclaration) Obliges(law SemiringLaw) bool {
	switch law {
	case LawCarrier, LawAddClosed, LawMulClosed, LawAddAssociative, LawAddCommutative,
		LawAddIdentity, LawMulAssociative, LawMulIdentity, LawAnnihilation, LawDistributive:
		return true
	case LawIdempotent:
		return l.Idempotent
	case LawBounded:
		return l.Bounded
	case LawMonotone:
		return l.Monotone
	case LawCommutative:
		return l.Commutative
	case LawSupportsRetraction:
		return l.SupportsRetraction
	}
	return false
}

// SemiringLaw is a law AuditSemiring tests, by its wire name (the spelling
// vectors/semiring.json pins): the ten axioms of a semiring over a carrier, then the five
// declarable laws of LawDeclaration.
type SemiringLaw string

// The laws, in audit order.
const (
	LawCarrier            SemiringLaw = "carrier"
	LawAddClosed          SemiringLaw = "add_closed"
	LawMulClosed          SemiringLaw = "mul_closed"
	LawAddAssociative     SemiringLaw = "add_associative"
	LawAddCommutative     SemiringLaw = "add_commutative"
	LawAddIdentity        SemiringLaw = "add_identity"
	LawMulAssociative     SemiringLaw = "mul_associative"
	LawMulIdentity        SemiringLaw = "mul_identity"
	LawAnnihilation       SemiringLaw = "annihilation"
	LawDistributive       SemiringLaw = "distributive"
	LawIdempotent         SemiringLaw = "idempotent"
	LawBounded            SemiringLaw = "bounded"
	LawMonotone           SemiringLaw = "monotone"
	LawCommutative        SemiringLaw = "commutative"
	LawSupportsRetraction SemiringLaw = "supports_retraction"
)

// SemiringAuditOrder returns the order AuditSemiring tests the laws in, as a fresh slice;
// its first counterexample is the one it reports.
func SemiringAuditOrder() []SemiringLaw {
	return []SemiringLaw{
		LawCarrier, LawAddClosed, LawMulClosed, LawAddAssociative, LawAddCommutative,
		LawAddIdentity, LawMulAssociative, LawMulIdentity, LawAnnihilation, LawDistributive,
		LawIdempotent, LawBounded, LawMonotone, LawCommutative, LawSupportsRetraction,
	}
}

// SemiringAnswer is what a semiring operation answered (ADR 0031 D1, as clarified on #1821):
// SemiringElement, SemiringNotAnElement or SemiringStopped.
//
// An operation is total over its carrier up to the carrier's declared capacity bounds: on
// elements it answers an element or, for a result past a bound the carrier declares,
// SemiringStopped with a capacity non-completion. A stop is "not decided", never "no such
// element", so a consumer reports it as a non-completion and never as a rejection.
type SemiringAnswer interface {
	isSemiringAnswer()
}

// SemiringElement is the result, an element of the carrier.
type SemiringElement struct {
	Value core.Value
}

// SemiringNotAnElement: an operand is not an element of the carrier.
type SemiringNotAnElement struct{}

// SemiringStopped: the operation stopped before establishing its result.
type SemiringStopped struct {
	Cause completion.NonCompletion
}

func (SemiringElement) isSemiringAnswer()      {}
func (SemiringNotAnElement) isSemiringAnswer() {}
func (SemiringStopped) isSemiringAnswer()      {}

// SemiringCapacity is the stop a carrier answers for a result past its declared capacity
// bound: a capacity non-completion of this one operation (literal scope).
func SemiringCapacity() SemiringAnswer {
	return SemiringStopped{Cause: completion.Capacity(completion.ScopeLiteral)}
}

// Semiring is a semiring the checker may consult (ADR 0031 D1). [PROPOSED]
//
// Elements are ontos values, so one interface carries every carrier. See the file comment
// for the obligations an implementation takes on.
type Semiring interface {
	// DeclaredIdentity is the (id, version, config digest) the implementation declares. The
	// identity a verdict names is SemiringIdentity, which folds Laws into it.
	DeclaredIdentity() ComponentIdentity
	// Laws is the optional laws this semiring claims (v2 §14.3).
	Laws() LawDeclaration
	// Zero is the identity of ⊕: the value of no derivation.
	Zero() core.Value
	// One is the identity of ⊗: the value of an empty conjunction.
	One() core.Value
	// IsElement reports whether v is an element of the carrier.
	IsElement(v core.Value) bool
	// Add is a ⊕ b; SemiringNotAnElement exactly when an operand is not an element.
	Add(a, b core.Value) SemiringAnswer
	// Mul is a ⊗ b; SemiringNotAnElement exactly when an operand is not an element.
	Mul(a, b core.Value) SemiringAnswer
}

// SemiringIdentityOf is the identity a semiring with this declared identity and these laws
// is named by: (id, version, SHA-256(prefix ‖ len(id) ‖ id ‖ len(version) ‖ version ‖
// config digest ‖ laws)), each length a big-endian uint64 and the laws LawDeclaration.Bits.
// The id and version are kept; the digest commits to the configuration AND the declared laws.
func SemiringIdentityOf(declared ComponentIdentity, laws LawDeclaration) ComponentIdentity {
	h := sha256.New()
	h.Write(SemiringIdentityPrefix())
	lenBuf := make([]byte, 8)
	binary.BigEndian.PutUint64(lenBuf, uint64(len(declared.Id)))
	h.Write(lenBuf)
	h.Write(declared.Id)
	binary.BigEndian.PutUint64(lenBuf, uint64(len(declared.Version)))
	h.Write(lenBuf)
	h.Write(declared.Version)
	h.Write(declared.ConfigDigest[:])
	h.Write([]byte{laws.Bits()})
	var digest [32]byte
	copy(digest[:], h.Sum(nil))
	return NewComponentIdentity(declared.Id, declared.Version, digest)
}

// SemiringIdentity is the identity s is named by: SemiringIdentityOf over its declared
// identity and its declared laws, each read once.
func SemiringIdentity(s Semiring) ComponentIdentity {
	return SemiringIdentityOf(s.DeclaredIdentity(), s.Laws())
}

// LawTally is how many tuples of the evaluated set decided a law, and how many were
// undecided because an operation the law names stopped. A law with no decided tuple is
// VACUOUS: the samples never exercised it, which is a state of the audit, never a pass.
type LawTally struct {
	// Law is the law.
	Law SemiringLaw
	// Decided counts the tuples on which every operation the law names answered, and the law
	// held.
	Decided int
	// Undecided counts the tuples on which an operation the law names stopped.
	Undecided int
}

// IsVacuous reports that no decided tuple exercised the law.
func (t LawTally) IsVacuous() bool { return t.Decided == 0 }

// SemiringAudit is the verdict of AuditSemiring: SemiringNoCounterexample, SemiringVacuous,
// SemiringCounterexample or SemiringSampleLimit.
type SemiringAudit interface {
	isSemiringAudit()
}

// SemiringNoCounterexample: no counterexample in the samples, and every law tested was
// decided on at least one tuple. NOT a proof: a finite sample can only refute a law.
type SemiringNoCounterexample struct {
	// Laws is every law evaluated, in audit order, with its tally.
	Laws []LawTally
}

// SemiringVacuous: no counterexample in the samples, but at least one law tested is vacuous
// (no tuple decided it, because every operation it needed stopped). Not a pass.
type SemiringVacuous struct {
	// Laws is every law evaluated, in audit order, with its tally; a vacuous law has
	// Decided == 0.
	Laws []LawTally
}

// SemiringCounterexample: the first law, in audit order, a decided tuple refutes, with the
// elements that refute it (one, two or three, in the order the law names them).
// Registration is rejected.
type SemiringCounterexample struct {
	// Law is the refuted law.
	Law SemiringLaw
	// Witness is the refuting elements.
	Witness []core.Value
}

// SemiringSampleLimit: more samples than SemiringAuditSampleLimit; nothing was evaluated.
type SemiringSampleLimit struct {
	// Given is the number of samples given.
	Given int
	// Limit is SemiringAuditSampleLimit.
	Limit int
}

func (SemiringNoCounterexample) isSemiringAudit() {}
func (SemiringVacuous) isSemiringAudit()          {}
func (SemiringCounterexample) isSemiringAudit()   {}
func (SemiringSampleLimit) isSemiringAudit()      {}

// AuditSemiring audits s over samples (v2 §14.3 audit_semiring; ADR 0031 G3).
//
// The evaluated set is [Zero, One, samples…] in that order. The laws are tested in
// SemiringAuditOrder, every axiom and each law Laws declares; within a law the elements are
// enumerated in set order, the first operand outermost. Each tuple is read in three values:
// the law holds, fails, or is undecided because an operation it names stopped (strong Kleene:
// a failing conjunct fails the tuple even beside a stop). An operation answering
// SemiringNotAnElement on elements fails the law it was evaluated for. The first failing tuple
// is the verdict; otherwise a law no tuple decided makes the verdict SemiringVacuous. The
// declared laws are read once.
func AuditSemiring(s Semiring, samples []core.Value) SemiringAudit {
	if len(samples) > SemiringAuditSampleLimit {
		return SemiringSampleLimit{Given: len(samples), Limit: SemiringAuditSampleLimit}
	}
	declared := s.Laws()
	zero := s.Zero()
	one := s.One()
	set := make([]core.Value, 0, len(samples)+2)
	set = append(set, zero, one)
	set = append(set, samples...)
	a := semiringAudit{s: s, set: set, zero: zero, one: one}
	laws := []LawTally{}
	vacuous := false
	for _, law := range SemiringAuditOrder() {
		if !declared.Obliges(law) {
			continue
		}
		tally := LawTally{Law: law}
		if witness, refuted := a.counterexample(law, &tally); refuted {
			return SemiringCounterexample{Law: law, Witness: witness}
		}
		vacuous = vacuous || tally.IsVacuous()
		laws = append(laws, tally)
	}
	if vacuous {
		return SemiringVacuous{Laws: laws}
	}
	return SemiringNoCounterexample{Laws: laws}
}

// ringTruth is a law's reading on one tuple: strong Kleene over the operations' answers.
type ringTruth uint8

const (
	ringHolds ringTruth = iota
	ringFails
	ringUndecided
)

func ringOf(holds bool) ringTruth {
	if holds {
		return ringHolds
	}
	return ringFails
}

// ringBoth is strong Kleene conjunction.
func ringBoth(l, r ringTruth) ringTruth {
	switch {
	case l == ringFails || r == ringFails:
		return ringFails
	case l == ringHolds && r == ringHolds:
		return ringHolds
	}
	return ringUndecided
}

// ringEither is strong Kleene disjunction.
func ringEither(l, r ringTruth) ringTruth {
	switch {
	case l == ringHolds || r == ringHolds:
		return ringHolds
	case l == ringFails && r == ringFails:
		return ringFails
	}
	return ringUndecided
}

// ringNot is strong Kleene negation.
func ringNot(t ringTruth) ringTruth {
	switch t {
	case ringHolds:
		return ringFails
	case ringFails:
		return ringHolds
	case ringUndecided:
		return ringUndecided
	}
	panic("contract: an unknown ringTruth")
}

// ringSame: both answers are the same element. A non-element on either side fails; otherwise
// a stop on either side is undecided.
func ringSame(l, r SemiringAnswer) ringTruth {
	le, lok := l.(SemiringElement)
	re, rok := r.(SemiringElement)
	if lok && rok {
		return ringOf(core.Equal(le.Value, re.Value))
	}
	_, lNot := l.(SemiringNotAnElement)
	_, rNot := r.(SemiringNotAnElement)
	if lNot || rNot {
		return ringFails
	}
	return ringUndecided
}

// ringGives: the answer is the element want.
func ringGives(r SemiringAnswer, want core.Value) ringTruth {
	switch v := r.(type) {
	case SemiringElement:
		return ringOf(core.Equal(v.Value, want))
	case SemiringNotAnElement:
		return ringFails
	case SemiringStopped:
		return ringUndecided
	}
	panic("contract: an unknown SemiringAnswer")
}

// ringThen applies op to an element; a non-element or a stop is carried unchanged.
func ringThen(r SemiringAnswer, op func(core.Value) SemiringAnswer) SemiringAnswer {
	if e, ok := r.(SemiringElement); ok {
		return op(e.Value)
	}
	return r
}

// count counts one tuple's reading, reporting true when it refutes the law.
func (t *LawTally) count(truth ringTruth) bool {
	switch truth {
	case ringHolds:
		t.Decided++
	case ringUndecided:
		t.Undecided++
	case ringFails:
		return true
	}
	return false
}

// semiringAudit is one audit run: the semiring and the evaluated set.
type semiringAudit struct {
	s    Semiring
	set  []core.Value
	zero core.Value
	one  core.Value
}

// sum is p ⊕ q over two answers.
func (a semiringAudit) sum(p, q SemiringAnswer) SemiringAnswer {
	return ringThen(p, func(pv core.Value) SemiringAnswer {
		return ringThen(q, func(qv core.Value) SemiringAnswer { return a.s.Add(pv, qv) })
	})
}

// below: x ≤ y in the natural order, witnessed inside the set (x ⊕ c = y for a sample c).
func (a semiringAudit) below(x, y core.Value) ringTruth {
	found := ringFails
	for _, c := range a.set {
		found = ringEither(found, ringGives(a.s.Add(x, c), y))
	}
	return found
}

// closed: an operation's answer is an element, and the same one when asked again.
func (a semiringAudit) closed(first, again SemiringAnswer) ringTruth {
	switch v := first.(type) {
	case SemiringElement:
		return ringBoth(ringOf(a.s.IsElement(v.Value)), ringGives(again, v.Value))
	case SemiringNotAnElement:
		return ringFails
	case SemiringStopped:
		return ringUndecided
	}
	panic("contract: an unknown SemiringAnswer")
}

func (a semiringAudit) each(t *LawTally, holds func(x core.Value) ringTruth) ([]core.Value, bool) {
	for _, x := range a.set {
		if t.count(holds(x)) {
			return []core.Value{x}, true
		}
	}
	return nil, false
}

func (a semiringAudit) pairs(t *LawTally, holds func(x, y core.Value) ringTruth) ([]core.Value, bool) {
	for _, x := range a.set {
		for _, y := range a.set {
			if t.count(holds(x, y)) {
				return []core.Value{x, y}, true
			}
		}
	}
	return nil, false
}

func (a semiringAudit) triples(t *LawTally, holds func(x, y, z core.Value) ringTruth) ([]core.Value, bool) {
	for _, x := range a.set {
		for _, y := range a.set {
			for _, z := range a.set {
				if t.count(holds(x, y, z)) {
					return []core.Value{x, y, z}, true
				}
			}
		}
	}
	return nil, false
}

// counterexample is the first tuple of the set on which law fails, with refuted=true, or
// refuted=false; t counts the decided and the undecided tuples.
func (a semiringAudit) counterexample(law SemiringLaw, t *LawTally) ([]core.Value, bool) {
	add, mul := a.s.Add, a.s.Mul
	switch law {
	case LawCarrier:
		return a.each(t, func(x core.Value) ringTruth { return ringOf(a.s.IsElement(x)) })
	case LawAddClosed:
		return a.pairs(t, func(x, y core.Value) ringTruth { return a.closed(add(x, y), add(x, y)) })
	case LawMulClosed:
		return a.pairs(t, func(x, y core.Value) ringTruth { return a.closed(mul(x, y), mul(x, y)) })
	case LawAddAssociative:
		return a.triples(t, func(x, y, z core.Value) ringTruth {
			return ringSame(
				ringThen(add(x, y), func(xy core.Value) SemiringAnswer { return add(xy, z) }),
				ringThen(add(y, z), func(yz core.Value) SemiringAnswer { return add(x, yz) }),
			)
		})
	case LawAddCommutative:
		return a.pairs(t, func(x, y core.Value) ringTruth { return ringSame(add(x, y), add(y, x)) })
	case LawAddIdentity:
		return a.each(t, func(x core.Value) ringTruth {
			return ringBoth(ringGives(add(a.zero, x), x), ringGives(add(x, a.zero), x))
		})
	case LawMulAssociative:
		return a.triples(t, func(x, y, z core.Value) ringTruth {
			return ringSame(
				ringThen(mul(x, y), func(xy core.Value) SemiringAnswer { return mul(xy, z) }),
				ringThen(mul(y, z), func(yz core.Value) SemiringAnswer { return mul(x, yz) }),
			)
		})
	case LawMulIdentity:
		return a.each(t, func(x core.Value) ringTruth {
			return ringBoth(ringGives(mul(a.one, x), x), ringGives(mul(x, a.one), x))
		})
	case LawAnnihilation:
		return a.each(t, func(x core.Value) ringTruth {
			return ringBoth(ringGives(mul(a.zero, x), a.zero), ringGives(mul(x, a.zero), a.zero))
		})
	case LawDistributive:
		return a.triples(t, func(x, y, z core.Value) ringTruth {
			left := ringSame(
				ringThen(add(y, z), func(yz core.Value) SemiringAnswer { return mul(x, yz) }),
				a.sum(mul(x, y), mul(x, z)),
			)
			right := ringSame(
				ringThen(add(x, y), func(xy core.Value) SemiringAnswer { return mul(xy, z) }),
				a.sum(mul(x, z), mul(y, z)),
			)
			return ringBoth(left, right)
		})
	case LawIdempotent:
		return a.each(t, func(x core.Value) ringTruth { return ringGives(add(x, x), x) })
	case LawBounded:
		return a.each(t, func(x core.Value) ringTruth { return ringGives(add(a.one, x), a.one) })
	case LawMonotone:
		return a.pairs(t, func(x, y core.Value) ringTruth {
			return ringEither(ringOf(core.Equal(x, y)), ringEither(ringNot(a.below(x, y)), ringNot(a.below(y, x))))
		})
	case LawCommutative:
		return a.pairs(t, func(x, y core.Value) ringTruth { return ringSame(mul(x, y), mul(y, x)) })
	case LawSupportsRetraction:
		return a.triples(t, func(x, y, z core.Value) ringTruth {
			return ringEither(ringOf(core.Equal(y, z)), ringNot(ringSame(add(x, y), add(x, z))))
		})
	}
	return nil, false
}

// countingSemiring is the counting semiring (ℕ, +, ×, 0, 1) (v2 §8.3 Counting; ADR 0031 D2).
type countingSemiring struct{}

// NewCountingSemiring returns the counting semiring (ℕ, +, ×, 0, 1), a core semiring.
//
// Its carrier is the non-negative integers in the frozen ontos-data int embedding,
// unbounded (math/big), so Add and Mul are exact and total on elements. It declares
// Monotone, Commutative and SupportsRetraction; it is neither idempotent nor bounded.
// Identity logos-core/counting-semiring@1.0.0, zero configuration.
func NewCountingSemiring() Semiring { return countingSemiring{} }

func (countingSemiring) DeclaredIdentity() ComponentIdentity {
	return NewComponentIdentity([]byte("logos-core/counting-semiring"), []byte("1.0.0"), [32]byte{})
}

func (countingSemiring) Laws() LawDeclaration {
	return LawDeclaration{Monotone: true, Commutative: true, SupportsRetraction: true}
}

func (countingSemiring) Zero() core.Value { return data.EncodeInt(big.NewInt(0)) }

func (countingSemiring) One() core.Value { return data.EncodeInt(big.NewInt(1)) }

func (countingSemiring) IsElement(v core.Value) bool {
	_, ok := ringNatural(v)
	return ok
}

func (countingSemiring) Add(a, b core.Value) SemiringAnswer {
	x, okA := ringNatural(a)
	y, okB := ringNatural(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return SemiringElement{Value: data.EncodeInt(new(big.Int).Add(x, y))}
}

func (countingSemiring) Mul(a, b core.Value) SemiringAnswer {
	x, okA := ringNatural(a)
	y, okB := ringNatural(b)
	if !okA || !okB {
		return SemiringNotAnElement{}
	}
	return SemiringElement{Value: data.EncodeInt(new(big.Int).Mul(x, y))}
}

// ringNatural is the non-negative integer v embeds, or ok=false when it is not one.
func ringNatural(v core.Value) (*big.Int, bool) {
	n, err := data.ReadInt(v)
	if err != nil || n.Sign() < 0 {
		return nil, false
	}
	return n, true
}
