// §5.2 Canonical wire encoding — AsValue + the digest helpers. [UNFROZEN v1]
//
// Go sibling of kernel/rs/src/seam/wire.rs. Every serializable negotiation type
// reads as a total, injective ontos Value via AsValue, exactly as the account codec
// reads a clause (ClauseValue). The codec then produces the frozen
// ontos-codec bytes, and a domain-separated SHA-256 yields the digest — mirroring
// ClauseId::canonical.
//
// ONTOS-NATIVE scalars. This seam never hand-rolls a scalar byte form. Integers and
// booleans go through the frozen ontos-data embeddings (data.EncodeInt /
// data.EncodeBool), so the rs/go/ts wire forms are identical *by construction* —
// there is no per-language scalar drift to keep in sync. This is the bug-fix vs the
// salvaged contract/go/negotiate version, which hand-rolled a fixed 8-byte big-endian
// int atom and a bare Atom("true"/"false") bool. The frozen ontos-data int is a
// sign-byte + big-endian MINIMAL-length magnitude; the frozen bool is
// Tuple[Atom("bool"), Atom(0x00|0x01)].
//
// FIRM sub-values (Subst/Derivation/Term/Literal) reuse the account's canonical
// quote/account readings; identifiers (Symbol/ComponentId/EngineId/version strings)
// stay bare Atom(bytes) — they are *names*, not human text, and bare-Atom is exactly
// the account's Symbol encoding (§0.3.6).
//
// The determinism rules (§0.3) are NON-NEGOTIABLE and realized here:
//
//  1. Fixed field order — a struct reads as Tuple[field₀, …] in declaration order.
//  2. Enums as tagged tuples — Tuple[Atom(tag), payload…] (Tagged); a fieldless
//     string-enum reads as the bare Atom(tag) (TagAtom).
//  3. Maps/sets sort before encoding — SortedMap/SortedSet sort by the codec bytes
//     of the key/member, reproducing Rust's BTreeMap/BTreeSet order.
//  4. Options — None → Tuple[Atom("none")]; Some(x) → Tuple[Atom("some"), x].
//  5. Integers — the frozen ontos-data int embedding (U64Atom/U32Atom).
//  6. Booleans — the frozen ontos-data bool embedding (BoolAtom).
//  7. Identifiers/digests — bare Atom(bytes) (BytesAtom / DigestAtom).
//  8. Reused FIRM sub-values read via the frozen account/quote readings.
package contract

import (
	"encoding/hex"
	"math/big"
	"sort"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// AsValue is a negotiation type that has a total, injective ontos-value reading
// (§0.3) — the Go analogue of the Rust AsValue trait.
type AsValue interface {
	// AsValue returns the canonical ontos value of the receiver (the encoder input).
	AsValue() core.Value
}

// ----------------------------- scalar readings ------------------------------

// BytesAtom reads a byte string as a bare Atom (§0.3.7) — the reading for an
// *identifier*: a Symbol, ComponentId, EngineId, or version string. Identifiers are
// names, not human text, so they are NOT the ontos-data utf8-text embedding; bare
// Atom(bytes) is exactly the account's Symbol encoding.
func BytesAtom(b []byte) core.Value { return core.NewAtom(b) }

// StrAtom reads a UTF-8/byte string as a bare Atom (the identifier reading). A Go
// string can hold arbitrary bytes; this never imposes UTF-8 validity.
func StrAtom(s string) core.Value { return core.NewAtom([]byte(s)) }

// U64Atom reads a uint64 as the frozen ontos-data int embedding (§0.3.5):
// Tuple[Atom("int"), Atom(sign ‖ minimal-magnitude)]. Going through data.EncodeInt
// is what makes the rs/go/ts integer wire form identical by construction — no
// hand-rolled big-endian atom to keep in sync per language.
func U64Atom(n uint64) core.Value {
	return data.EncodeInt(new(big.Int).SetUint64(n))
}

// U32Atom reads a uint32 via the same ontos-data int embedding (one integer reading
// for the whole seam, so arity bounds and 64-bit limits encode identically).
func U32Atom(n uint32) core.Value {
	return data.EncodeInt(big.NewInt(int64(n)))
}

// BoolAtom reads a bool as the frozen ontos-data bool embedding (§0.3.6):
// Tuple[Atom("bool"), Atom(0x00 | 0x01)]. Distinct from the int embedding by its
// label, so it never collides with an integer reading.
func BoolAtom(b bool) core.Value { return data.EncodeBool(b) }

// DigestAtom reads a 32-byte digest as its lowercase-hex Atom (§0.3.7, §1.3) — the
// on-the-wire form of every [32]byte digest in the seam. A digest is an opaque
// identifier, so it is a bare hex Atom, not a scalar embedding.
func DigestAtom(d Hash) core.Value {
	return core.NewAtom([]byte(hex.EncodeToString(d[:])))
}

// --------------------------- tagged-enum readings ---------------------------

// TagAtom reads a fieldless string-enum variant as the bare Atom(tag) (§0.3.2).
func TagAtom(tag string) core.Value { return core.NewAtom([]byte(tag)) }

// Tagged reads a tagged variant as Tuple[Atom(tag), payload…] (§0.3.2).
func Tagged(tag string, payload ...core.Value) core.Value {
	items := make([]core.Value, 0, len(payload)+1)
	items = append(items, TagAtom(tag))
	items = append(items, payload...)
	return core.NewTuple(items...)
}

// ------------------------------- composites ---------------------------------

// Record reads a fixed-order product as Tuple[fields…] (§0.3.1). The caller passes
// fields in the spec's declaration order.
func Record(fields ...core.Value) core.Value { return core.NewTuple(fields...) }

// List reads an ordered list (order is identity-bearing — NOT sorted) of AsValue
// items, e.g. the theories list or a fallback chain (§5.2).
func List[T AsValue](items []T) core.Value {
	out := make([]core.Value, len(items))
	for i, it := range items {
		out[i] = it.AsValue()
	}
	return core.NewTuple(out...)
}

// Seq reads an ordered (NON-sorted) slice of already-rendered Values as a Tuple in
// slice order — for order-bearing lists (premises, strata, edges) (§5.2).
func Seq(items []core.Value) core.Value { return core.NewTuple(items...) }

// Opt reads an Option<T AsValue> (§0.3.4): nil → Tuple[Atom("none")]; non-nil →
// Tuple[Atom("some"), x.AsValue()].
func Opt[T AsValue](o *T) core.Value {
	if o == nil {
		return Tagged("none")
	}
	return Tagged("some", (*o).AsValue())
}

// OptValue reads an Option whose Some payload is an already-rendered Value (present
// = false ⇒ none) (§0.3.4).
func OptValue(present bool, some core.Value) core.Value {
	if !present {
		return Tagged("none")
	}
	return Tagged("some", some)
}

// OptU64 reads an Option<uint64> — Opt specialized to the integer reading.
func OptU64(p *uint64) core.Value {
	if p == nil {
		return Tagged("none")
	}
	return Tagged("some", U64Atom(*p))
}

// OptU32 reads an Option<uint32> — Opt specialized to the integer reading.
func OptU32(p *uint32) core.Value {
	if p == nil {
		return Tagged("none")
	}
	return Tagged("some", U32Atom(*p))
}

// OptStr reads an Option<string> — Opt specialized to the byte-atom reading.
func OptStr(p *string) core.Value {
	if p == nil {
		return Tagged("none")
	}
	return Tagged("some", StrAtom(*p))
}

// SortedSet reads a set of already-rendered Values sorted by codec bytes (§0.3.3).
// Go/TS reproduce the order a Rust BTreeSet iterates in; the explicit sort is what
// makes Go's unordered maps/sets deterministic here.
func SortedSet(members []core.Value) core.Value {
	return core.NewTuple(sortByCodecBytes(members)...)
}

// SortedMap reads a map sorted by the codec bytes of its key (§0.3.3):
// Tuple[ Tuple[k₀,v₀], … ]. The entries arrive as (key, value) Value pairs.
func SortedMap(keys []core.Value, values []core.Value) core.Value {
	if len(keys) != len(values) {
		panic("seam: SortedMap: keys/values length mismatch")
	}
	idx := make([]int, len(keys))
	encoded := make([][]byte, len(keys))
	for i := range keys {
		idx[i] = i
		encoded[i] = codec.Encode(keys[i])
	}
	sort.SliceStable(idx, func(a, b int) bool {
		return wireBytesLess(encoded[idx[a]], encoded[idx[b]])
	})
	pairs := make([]core.Value, len(keys))
	for i, j := range idx {
		pairs[i] = core.NewTuple(keys[j], values[j])
	}
	return core.NewTuple(pairs...)
}

// sortByCodecBytes returns a copy of values sorted ascending by their ontos-codec
// bytes (§0.3.3 — the deterministic "sorted by key bytes" order a Rust
// BTreeMap/BTreeSet already gives; go reproduces it here).
func sortByCodecBytes(values []core.Value) []core.Value {
	out := make([]core.Value, len(values))
	copy(out, values)
	encoded := make([][]byte, len(out))
	for i, v := range out {
		encoded[i] = codec.Encode(v)
	}
	idx := make([]int, len(out))
	for i := range idx {
		idx[i] = i
	}
	sort.SliceStable(idx, func(a, b int) bool {
		return wireBytesLess(encoded[idx[a]], encoded[idx[b]])
	})
	sorted := make([]core.Value, len(out))
	for i, j := range idx {
		sorted[i] = out[j]
	}
	return sorted
}

// wireBytesLess reports lexicographic byte ordering (a < b), matching Rust's slice Ord
// (used to reproduce BTreeMap/BTreeSet key order).
func wireBytesLess(a, b []byte) bool {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	for i := 0; i < n; i++ {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return len(a) < len(b)
}

// ----------------------- reused FIRM sub-value readings ---------------------

// SymbolAsValue reads a predicate Symbol as a bare Atom(bytes) (the account reading).
func SymbolAsValue(sym Symbol) core.Value { return BytesAtom(sym.Bytes()) }

// SubstAsValue reads a Subst (map VarId→Term) as a Tuple of Tuple[Atom(var_id),
// quote(term)] sorted by var-id bytes — matching Rust's BTreeMap<VarId,Term> order
// (§5.2). Terms reuse the FROZEN quote reading; no second encoding.
func SubstAsValue(subst Subst) core.Value {
	// #2605: the shape is written once, in wire_sink.go, and read here as a value. Its sort is
	// SortedMap's: codec(key) order.
	return buildValue(func(w wireSink) { writeSubst(w, subst) })
}

// GroundLiteralAsValue reads a ground literal p(a…) as Tuple[Atom(p), quote(a)…] —
// the labeled-compound reading the account codec uses (goalAsTerm), threaded through
// the FROZEN quote. Reused by DerivationAsValue; never a second encoding.
func GroundLiteralAsValue(lit GroundLiteral) core.Value {
	// #2605: the shape is written once, in wire_sink.go, and read here as a value.
	return buildValue(func(w wireSink) { writeGroundLiteral(w, lit) })
}

func nodeMetaAsValue(meta NodeMeta) core.Value {
	if v, ok := meta.Value(); ok {
		return Tagged("some", v)
	}
	return Tagged("none")
}

func evidenceAsValue(evidence Evidence) core.Value {
	if v, ok := evidence.Value(); ok {
		return Tagged("some", v)
	}
	return Tagged("none")
}

func nodeAsValue(n Node) core.Value {
	switch node := n.(type) {
	case RuleNode:
		premises := make([]core.Value, len(node.Premises))
		for i, p := range node.Premises {
			premises[i] = premiseAsValue(p)
		}
		return Tagged("rule",
			GroundLiteralAsValue(node.Conc),
			StrAtom(node.Clause.String()),
			SubstAsValue(node.Subst),
			core.NewTuple(premises...),
			nodeMetaAsValue(node.Meta),
		)
	case BuiltinNode:
		return Tagged("builtin", GroundLiteralAsValue(node.Conc))
	case LeafNode:
		return Tagged("leaf", GroundLiteralAsValue(node.Conc), evidenceAsValue(node.Evidence))
	default:
		panic("seam: nodeAsValue: unknown Node implementation")
	}
}

// premiseAsValue reads a Premise as a value (ADR 0007). A positive premise reads as
// the BARE u64 atom node index — byte-identical to the pre-ADR-0007 wire (so a positive
// derivation's bytes are unchanged). A negated premise reads as a tagged tuple
// Tagged("neg", atom, Atom(cert)) (engines do not emit Neg yet; this path keeps the
// wire total over the additive Premise sum). Mirrors Rust's premise_as_value.
func premiseAsValue(p Premise) core.Value {
	switch premise := p.(type) {
	case PosPremise:
		return U64Atom(uint64(premise.Node))
	case NegPremise:
		return Tagged("neg", GroundLiteralAsValue(premise.Atom), U64Atom(uint64(premise.Cert.Index())))
	case CountPremise:
		// ADR 0023: Tagged("count", Tuple[Atom(pred),int(arity)], Tuple[Tuple[int(pos),value]…],
		// project, k, int(cert)). Mirrors Rust's premise_as_value Count arm.
		return Tagged("count",
			predicateRefAsValue(premise.Pred),
			countFilterAsValue(premise.Filter),
			projectSpecAsValue(premise.Project),
			premise.K,
			U64Atom(uint64(premise.Cert.Index())),
		)
	default:
		panic("seam: premiseAsValue: unknown Premise implementation")
	}
}

// predicateRefAsValue reads a PredicateRef as Tuple[Atom(pred), int(arity)] (#581).
func predicateRefAsValue(pred PredicateRef) core.Value {
	return core.NewTuple(SymbolAsValue(pred.Pred), U64Atom(uint64(pred.Arity)))
}

// countFilterAsValue reads a Count premise's ground filter as Tuple[ Tuple[int(pos), value] … ].
func countFilterAsValue(filter []GroundFilterEntry) core.Value {
	entries := make([]core.Value, len(filter))
	for i, e := range filter {
		entries[i] = core.NewTuple(U64Atom(uint64(e.Pos)), e.Value)
	}
	return core.NewTuple(entries...)
}

// projectSpecAsValue reads a ProjectSpec (ADR 0023 + #587): Atom("rows") for count, or
// Tagged(<fold>, int(attr)) for distinct/sum/min/max. Mirrors Rust's project_spec_as_value.
func projectSpecAsValue(p ProjectSpec) core.Value {
	switch p.Kind {
	case ProjectRows:
		return core.NewAtom([]byte("rows"))
	case ProjectDistinct:
		return Tagged("distinct", U64Atom(uint64(p.Attr)))
	case ProjectSum:
		return Tagged("sum", U64Atom(uint64(p.Attr)))
	case ProjectMin:
		return Tagged("min", U64Atom(uint64(p.Attr)))
	case ProjectMax:
		return Tagged("max", U64Atom(uint64(p.Attr)))
	default:
		panic("seam: projectSpecAsValue: unknown ProjectKind")
	}
}

// DerivationAsValue reads a Derivation as Tuple[ Tuple[node₀, …], int(root) ] — the
// nodes read via the FIRM account/quote readings of conclusions/substs (§5.2). The
// node ordering is the derivation's own (a DAG order is identity-bearing); it is NOT
// sorted.
func DerivationAsValue(d Derivation) core.Value {
	nodes := make([]core.Value, len(d.Nodes))
	for i, n := range d.Nodes {
		nodes[i] = nodeAsValue(n)
	}
	// closed_world is a TRAILING-OPTIONAL 3rd element (ADR 0007 / ADR 0023): appended ONLY
	// when non-empty, so an all-positive derivation encodes the EXACT same Tuple[nodes, root]
	// bytes as before — byte-compat for every existing positive derivation is preserved.
	fields := []core.Value{core.NewTuple(nodes...), U64Atom(uint64(d.Root))}
	if len(d.ClosedWorld) > 0 {
		certs := make([]core.Value, len(d.ClosedWorld))
		for i, c := range d.ClosedWorld {
			certs[i] = ClosedModelCertAsValue(c)
		}
		fields = append(fields, core.NewTuple(certs...))
	}
	return core.NewTuple(fields...)
}

// ClosedModelCertAsValue reads a ClosedModelCert (ADR 0007 / ADR 0023) as a value — the
// sealed finite-model certificate a Neg/Count premise discharges against, carried in
// DerivationAsValue's trailing closed_world slot so a certified candidate round-trips across
// the seam. The ClosureWitness is an empty v1 marker (no bytes); it is reconstructed by
// default on decode. Mirrors Rust's closed_model_cert_as_value.
func ClosedModelCertAsValue(cert ClosedModelCert) core.Value {
	// #2605: the shape is written once, in wire_sink.go, and read here as a value.
	return buildValue(func(w wireSink) { writeClosedModelCert(w, cert, cert.LimitsDecl) })
}

// CertEncodedBytes is a certificate's size in BYTES (#2524, seat:caa's ruling), the one
// definition a producer declares and the checker measures: the length of its canonical wire
// encoding (ClosedModelCertAsValue through the codec) with LimitsDecl.CertBytes set to 0. The
// encoding CONTAINS the declaration, so declaring your own encoded size would be circular;
// zeroing the field makes it well defined. Mirrors rs cert_encoded_bytes and ts certEncodedBytes,
// and a generated vector pins their agreement (vectors/cert_encoded_bytes.json).
func CertEncodedBytes(cert ClosedModelCert) uint64 {
	// #2605: measured through the length reading of the one wire shape, so no value tree and no
	// encoded buffer is built (the rs twin was 41% of a certified-set run's peak heap, #2602).
	decl := cert.LimitsDecl
	decl.CertBytes = 0
	return measureLen(func(w wireSink) { writeClosedModelCert(w, cert, decl) })
}

// ClauseAsValue reads a clause as its frozen account value (ClauseValue). Re-exported
// so a plan/analysis reading that embeds a clause reuses the one frozen reading.
func ClauseAsValue(c Clause) core.Value { return ClauseValue(c) }

// PredicateSetValue reads a slice of predicate Symbols as a Tuple of member symbols
// sorted by Symbol bytes (§3, §5.2). The members arrive as an explicit slice because
// Go's set has no stable iteration.
func PredicateSetValue(preds []Symbol) core.Value {
	members := make([]core.Value, len(preds))
	for i, p := range preds {
		members[i] = SymbolAsValue(p)
	}
	return SortedSet(members)
}

// ---------------------------- small value readers ---------------------------

// ----------------------------- Subst (the answer) ---------------------------

// ------------------------- GroundLiteral (a conclusion) ---------------------

// ------------------------------- Node + Derivation --------------------------

const DerivationWireV1Tag = "proof-interchange/derivation/v1"

// DerivationWirePayloadV1ToValue reads a derivation as the public v1 payload.
func DerivationWirePayloadV1ToValue(d Derivation) core.Value { return DerivationAsValue(d) }

// DerivationWireV1ToValue wraps a derivation payload with the proof-interchange v1 tag.
func DerivationWireV1ToValue(d Derivation) core.Value {
	return core.NewTuple(StrAtom(DerivationWireV1Tag), DerivationAsValue(d))
}

// EncodeDerivationWireV1 encodes the public proof-interchange v1 wrapper as ontos-codec bytes.
func EncodeDerivationWireV1(d Derivation) []byte { return codec.Encode(DerivationWireV1ToValue(d)) }
