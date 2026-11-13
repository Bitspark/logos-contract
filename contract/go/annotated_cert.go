// The annotated closed-model certificate (ADR 0031 D5; rulings Q14 and Q15 on #1821). [PROPOSED]
// The Go binding of contract/rs/src/annotated_cert.rs; contract/ts/src/annotated_cert.ts is the
// third.
//
// An AnnotatedClosedModelCert is a ClosedModelCert, unchanged, plus one semiring element per sealed
// row and the identity of the semiring those elements belong to. CheckAnnotatedClosedModel
// (check_annotated.go) checks it relative to that identity. ClosedModelCert, its wire, its digest
// and its check stay byte-identical: everything here is additive (ADR 0003).
//
// The wire, read by AnnotatedClosedModelCertAsValue and decoded, closed, by
// AnnotatedClosedModelCertFromValue:
//
//	Tuple[ Atom("annotated_closed_model_cert"),
//	       <ClosedModelCertAsValue(cert)>,
//	       Tuple[Atom(semiring id), Atom(semiring version), DigestAtom(config digest)],
//	       Tuple[ Tuple[Atom(pred), Tuple[element, ...]], ... ] ]
//
// The identity record is byte-equal to the kernel's ComponentBinding record (id, version,
// config_digest), the digest a lowercase-hex atom like every digest on the certificate wire.

package contract

import (
	core "github.com/bitspark/ontos/core/go"
)

// annotatedCertTag is the tag atom that opens an annotated certificate's wire.
const annotatedCertTag = "annotated_closed_model_cert"

// AnnotatedTable is the annotation of one sealed table (ADR 0031 D5): Elements[i] is the semiring
// element claimed for row i of the certificate's table for Pred, in the table's row order.
type AnnotatedTable struct {
	// Pred is the sealed table's predicate.
	Pred Symbol
	// Elements holds one semiring element per row of the table, in row order.
	Elements []core.Value
}

// AnnotatedClosedModelCert is a closed-model certificate whose sealed rows carry semiring elements
// (ADR 0031 D5; #1821 Q15). Annotations[i] annotates Cert.Extensions[i], in the certificate's table
// order, with one element per row.
//
// The elements of an extensional table are PREMISES: the wire binds them, and the check reads them,
// but nothing attests them (#1821 Q15 condition 1). The check recomputes every intensional row's
// element from them and names the extensional tables it relied on.
type AnnotatedClosedModelCert struct {
	// Cert is the closed-model certificate, unchanged.
	Cert ClosedModelCert
	// Semiring is the identity of the semiring the elements belong to (SemiringIdentity), the one
	// the verdict is relative to.
	Semiring ComponentIdentity
	// Annotations holds one table annotation per Cert.Extensions entry, in the same order.
	Annotations []AnnotatedTable
}

// AnnotatedClosedModelCertAsValue reads an annotated certificate as its wire value (see the file
// comment). The inner certificate is ClosedModelCertAsValue's reading, and its error is returned.
func AnnotatedClosedModelCertAsValue(a AnnotatedClosedModelCert) (core.Value, error) {
	cert, err := ClosedModelCertAsValue(a.Cert)
	if err != nil {
		return nil, err
	}
	identity := core.NewTuple(
		core.NewAtom(a.Semiring.Id),
		core.NewAtom(a.Semiring.Version),
		DigestAtom(a.Semiring.ConfigDigest),
	)
	tables := make([]core.Value, len(a.Annotations))
	for i, table := range a.Annotations {
		tables[i] = core.NewTuple(SymbolAsValue(table.Pred), core.NewTuple(table.Elements...))
	}
	return core.NewTuple(StrAtom(annotatedCertTag), cert, identity, core.NewTuple(tables...)), nil
}

// AnnotatedClosedModelCertFromValue decodes an annotated certificate, the inverse of
// AnnotatedClosedModelCertAsValue. It is CLOSED: it accepts exactly that shape and refuses
// everything else with a *DecodeError, the one decoder's error (a wrong tag, a wrong arity, a
// config digest that is not 32 bytes, a table that is not a pair, a predicate that is not an atom).
// The inner certificate is decoded by ClosedModelCertFromValue, with its refusals.
func AnnotatedClosedModelCertFromValue(v core.Value) (AnnotatedClosedModelCert, error) {
	const ctx = "annotated_closed_model_cert"
	its, err := decItemsN(v, ctx, []int{4})
	if err != nil {
		return AnnotatedClosedModelCert{}, err
	}
	tag, err := decAtomBytes(its[0], ctx)
	if err != nil {
		return AnnotatedClosedModelCert{}, err
	}
	if string(tag) != annotatedCertTag {
		return AnnotatedClosedModelCert{}, &DecodeError{Kind: DecodeUnknownTag, Ctx: ctx, Tag: string(tag)}
	}
	cert, err := ClosedModelCertFromValue(its[1])
	if err != nil {
		return AnnotatedClosedModelCert{}, err
	}
	identity, err := annotatedIdentityFromValue(its[2], ctx+".semiring")
	if err != nil {
		return AnnotatedClosedModelCert{}, err
	}
	tableValues, err := decItems(its[3], ctx+".annotations")
	if err != nil {
		return AnnotatedClosedModelCert{}, err
	}
	tables := make([]AnnotatedTable, 0, len(tableValues))
	for _, tv := range tableValues {
		table, err := annotatedTableFromValue(tv, ctx+".annotations.table")
		if err != nil {
			return AnnotatedClosedModelCert{}, err
		}
		tables = append(tables, table)
	}
	return AnnotatedClosedModelCert{Cert: cert, Semiring: identity, Annotations: tables}, nil
}

// annotatedIdentityFromValue decodes the identity record Tuple[Atom(id), Atom(version),
// DigestAtom(config digest)], the digest exactly 64 lowercase-hex characters (readHash).
func annotatedIdentityFromValue(v core.Value, ctx string) (ComponentIdentity, error) {
	its, err := decItemsN(v, ctx, []int{3})
	if err != nil {
		return ComponentIdentity{}, err
	}
	id, err := decAtomBytes(its[0], ctx+".id")
	if err != nil {
		return ComponentIdentity{}, err
	}
	version, err := decAtomBytes(its[1], ctx+".version")
	if err != nil {
		return ComponentIdentity{}, err
	}
	digest, err := readHash(its[2], ctx+".config_digest")
	if err != nil {
		return ComponentIdentity{}, err
	}
	return NewComponentIdentity(id, version, digest), nil
}

// annotatedTableFromValue decodes one table annotation Tuple[Atom(pred), Tuple[element, ...]].
func annotatedTableFromValue(v core.Value, ctx string) (AnnotatedTable, error) {
	its, err := decItemsN(v, ctx, []int{2})
	if err != nil {
		return AnnotatedTable{}, err
	}
	pred, err := symbolFromValue(its[0], ctx+".pred")
	if err != nil {
		return AnnotatedTable{}, err
	}
	elements, err := decItems(its[1], ctx+".elements")
	if err != nil {
		return AnnotatedTable{}, err
	}
	return AnnotatedTable{Pred: pred, Elements: append([]core.Value(nil), elements...)}, nil
}
