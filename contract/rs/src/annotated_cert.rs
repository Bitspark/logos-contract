//! ADR 0031 D5 (#1821 P9 I5a): the ANNOTATED closed-model certificate and its wire.
//! **[PROPOSED · additive]**
//!
//! An [`AnnotatedClosedModelCert`] is a [`ClosedModelCert`], unchanged, together with the identity
//! of the semiring its annotations are elements of and one element per row of every sealed table.
//! `annotations[i]` annotates `cert.extensions[i]`, in the certificate's table order, with one
//! element per row in row order. The check is
//! [`check_annotated_closed_model`](crate::check_annotated_closed_model); this module holds only
//! the data and its closed wire reading.
//!
//! The certificate, its wire and its digest stay byte-identical: the annotated reading wraps the
//! existing [`closed_model_cert_as_value`] and adds nothing inside it (ADR 0003, additive).

use crate::cert::ClosedModelCert;
use crate::derivation_wire::{
    atom_bytes, bytes_atom, closed_model_cert_as_value, closed_model_cert_from_value, digest_atom,
    items, items_n, read_hash, split_tag, symbol_as_value, tag_atom, DecodeError,
};
use crate::literal::Symbol;
use crate::spi::ComponentIdentity;
use ontos_core::Value;

/// The tag the annotated reading opens with.
const TAG: &str = "annotated_closed_model_cert";

/// One sealed table's annotations: the predicate it annotates and one semiring element per row of
/// that table, in the table's row order (ADR 0031 D5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnotatedTable {
    /// The predicate of the sealed table this annotates.
    pub pred: Symbol,
    /// One element per row of the table, in row order.
    pub elements: Vec<Value>,
}

/// A closed-model certificate annotated over a semiring (ADR 0031 D5; #1821 Q14, Q15).
///
/// The annotations are claims relative to `semiring`, the identity
/// [`semiring_identity`](crate::semiring_identity) computes. An extensional table's elements are
/// premises the certificate's digest binds: the check names them unattested and never attests
/// them (#1821 Q15 condition 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnotatedClosedModelCert {
    /// The boolean certificate, unchanged.
    pub cert: ClosedModelCert,
    /// The identity of the semiring the elements belong to.
    pub semiring: ComponentIdentity,
    /// One entry per table of `cert.extensions`, in the certificate's table order.
    pub annotations: Vec<AnnotatedTable>,
}

/// An [`AnnotatedClosedModelCert`] as a value:
/// `Tuple[Atom("annotated_closed_model_cert"), <the cert's closed_model_cert_as_value>,
/// Tuple[Atom(id), Atom(version), Atom(config_digest hex)], Tuple[Tuple[Atom(pred),
/// Tuple[element, ...]], ...]]`. The identity record is the kernel's component binding record:
/// the digest is the lowercase-hex atom every certificate digest uses ([`digest_atom`]). The
/// annotation tables keep their order.
pub fn annotated_closed_model_cert_as_value(annotated: &AnnotatedClosedModelCert) -> Value {
    let semiring = &annotated.semiring;
    let identity = Value::tuple([
        bytes_atom(semiring.id.clone()),
        bytes_atom(semiring.version.clone()),
        digest_atom(&semiring.config_digest),
    ]);
    let tables = annotated.annotations.iter().map(annotated_table_as_value);
    Value::tuple([
        tag_atom(TAG),
        closed_model_cert_as_value(&annotated.cert),
        identity,
        Value::tuple(tables),
    ])
}

fn annotated_table_as_value(table: &AnnotatedTable) -> Value {
    let elements = Value::tuple(table.elements.iter().cloned());
    Value::tuple([symbol_as_value(&table.pred), elements])
}

/// Read an [`AnnotatedClosedModelCert`] back from [`annotated_closed_model_cert_as_value`]'s
/// reading. CLOSED: it accepts exactly that shape and refuses everything else with the wire's
/// [`DecodeError`]: another tag, another arity, a digest that is not the hex of 32 bytes, an
/// annotation table that is not a pair, a predicate that is not an atom. The inner certificate is
/// read by
/// [`closed_model_cert_from_value`], with every refusal it makes.
pub fn annotated_closed_model_cert_from_value(
    v: &Value,
) -> Result<AnnotatedClosedModelCert, DecodeError> {
    let (tag, payload) = split_tag(v, TAG)?;
    if tag != TAG.as_bytes() {
        return Err(DecodeError::UnknownTag {
            ctx: TAG,
            tag: tag.to_vec(),
        });
    }
    let [cert, semiring, tables] = payload else {
        return Err(DecodeError::Arity {
            ctx: TAG,
            accepted: &[4],
            got: payload.len() + 1,
        });
    };
    let cert = closed_model_cert_from_value(cert)?;
    let semiring = identity_from_value(semiring)?;
    let mut annotations = Vec::new();
    for table in items(tables, "annotated_closed_model_cert.annotations")? {
        annotations.push(annotated_table_from_value(table)?);
    }
    Ok(AnnotatedClosedModelCert {
        cert,
        semiring,
        annotations,
    })
}

/// The identity record `Tuple[Atom(id), Atom(version), Atom(config_digest hex)]`. A digest that is
/// not 64 lowercase hex digits (32 bytes) is refused as every certificate digest is.
fn identity_from_value(v: &Value) -> Result<ComponentIdentity, DecodeError> {
    let its = items_n(v, "annotated_closed_model_cert.semiring", &[3])?;
    let id = atom_bytes(&its[0], "annotated_closed_model_cert.semiring.id")?;
    let version = atom_bytes(&its[1], "annotated_closed_model_cert.semiring.version")?;
    let digest_ctx = "annotated_closed_model_cert.semiring.config_digest";
    let digest = read_hash(&its[2], digest_ctx)?;
    Ok(ComponentIdentity::new(id, version, digest))
}

/// One annotation table `Tuple[Atom(pred), Tuple[element, ...]]`.
fn annotated_table_from_value(v: &Value) -> Result<AnnotatedTable, DecodeError> {
    let its = items_n(v, "annotated_closed_model_cert.table", &[2])?;
    let pred = atom_bytes(&its[0], "annotated_closed_model_cert.table.pred")?;
    let elements = items(&its[1], "annotated_closed_model_cert.table.elements")?;
    Ok(AnnotatedTable {
        pred: Symbol::new(pred),
        elements: elements.to_vec(),
    })
}
