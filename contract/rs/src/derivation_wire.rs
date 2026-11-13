//! §5.2 Canonical wire encoding — `AsValue` + the digest helpers. **[UNFROZEN v1]**
//!
//! Every serializable negotiation type reads as a total, injective ontos
//! [`Value`] via [`AsValue::as_value`], exactly as the account
//! codec reads a clause (`crate::clause_value`). The codec then produces the
//! frozen `ontos-codec` bytes, and a domain-separated SHA-256 yields the digest —
//! mirroring [`ClauseId::canonical`](crate::ClauseId).
//!
//! **Ontos-native scalars.** This seam is ONTOS-NATIVE: it never hand-rolls a scalar
//! byte form. Integers and booleans go through the frozen `ontos-data` embeddings
//! ([`ontos_data::encode_int`] / [`ontos_data::encode_bool`]), so the rs/go/ts wire
//! forms are identical *by construction* — there is no per-language scalar drift to
//! keep in sync. FIRM sub-values (`Subst`/`Derivation`/`Term`/`Literal`) reuse the
//! account's canonical `quote`/account readings; identifiers (`Symbol`/`ComponentId`/
//! `EngineId`/version strings) stay bare `Atom(bytes)` — they are *names*, not human
//! text, and bare-`Atom` is exactly the account's `Symbol` encoding (§0.3.6).
//!
//! The determinism rules (§0.3) are NON-NEGOTIABLE and are realized *here* so the
//! whole seam inherits them:
//!
//! 1. **Fixed field order** — a struct reads as `Tuple[field₀, …]` in the spec's
//!    declaration order (the `as_value` body lists fields in that order).
//! 2. **Enums as tagged tuples** — a variant reads as `Tuple[Atom(tag), payload…]`
//!    ([`tagged`]); a fieldless string-enum reads as the bare `Atom(tag)`
//!    ([`tag_atom`]).
//! 3. **Maps/sets sort before encoding** — [`sorted_map`]/[`sorted_set`] sort by the
//!    codec bytes of the key/member, reproducing `BTreeMap`/`BTreeSet` order.
//! 4. **Options** — `None` → `Tuple[Atom("none")]`, `Some(x)` → `Tuple[Atom("some"),
//!    x.as_value()]` ([`opt`]).
//! 5. **Integers** — the frozen `ontos-data` `int` embedding ([`u64_atom`]); never a
//!    bare hand-rolled big-endian atom, never decimal.
//! 6. **Booleans** — the frozen `ontos-data` `bool` embedding ([`bool_atom`]).
//! 7. **Identifiers/digests** — bare `Atom(bytes)` ([`bytes_atom`] / [`digest_atom`]).
//! 8. **Reused FIRM sub-values** (`Subst`, `Derivation`, …) read via the frozen
//!    account/`quote` readings — see [`subst_as_value`] / [`derivation_as_value`].

use crate::wire_sink::{self, LenSink, ValueSink};
use crate::{
    clause_value, reify, CertSizeDecl, Clause, ClauseId, ClosedModelCert, ClosureWitness,
    Derivation, Evidence, FiniteDomain, GroundLiteral, Node, NodeMeta, Premise, RelationTable,
    StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, VarId,
};
use ontos_core::Value;

/// A negotiation type that has a total, injective ontos-value reading (§0.3).
pub trait AsValue {
    /// The canonical ontos value of `self` (the encoder input).
    fn as_value(&self) -> Value;
}

// ----------------------------- scalar readings ------------------------------

/// A byte string as a bare `Atom` (§0.3.7) — the reading for an *identifier*: a
/// `Symbol`, `ComponentId`, `EngineId`, or version string. Identifiers are names,
/// not human text, so they are NOT the `ontos-data` `utf8-text` embedding; bare
/// `Atom(bytes)` is exactly the account's `Symbol` encoding.
pub fn bytes_atom(bytes: impl Into<Vec<u8>>) -> Value {
    Value::atom(bytes.into())
}

/// A `u64` as the frozen `ontos-data` `int` embedding (§0.3.5):
/// `Tuple[Atom("int"), Atom(sign ‖ magnitude)]`. Going through
/// [`ontos_data::encode_int`] is what makes the rs/go/ts integer wire form identical
/// by construction — no hand-rolled big-endian atom to keep in sync per language.
pub fn u64_atom(n: u64) -> Value {
    ontos_data::encode_int(i128::from(n))
}

/// A `u32` via the same `ontos-data` `int` embedding (one integer reading for the
/// whole seam, so arity bounds and 64-bit limits encode identically).
pub fn u32_atom(n: u32) -> Value {
    ontos_data::encode_int(i128::from(n))
}

/// A `bool` as the frozen `ontos-data` `bool` embedding (§0.3.6):
/// `Tuple[Atom("bool"), Atom(0x00 | 0x01)]`. Distinct from the `int` embedding by
/// its label, so it never collides with an integer reading.
pub fn bool_atom(b: bool) -> Value {
    ontos_data::encode_bool(b)
}

/// A 32-byte digest as its lowercase-hex `Atom` (§0.3.7, §1.3) — the on-the-wire
/// form of every `[u8;32]` digest in the seam. A digest is an opaque identifier,
/// so it is a bare hex `Atom`, not a scalar embedding.
pub fn digest_atom(d: &[u8; 32]) -> Value {
    Value::atom(to_hex(d).into_bytes())
}

pub(crate) fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

// --------------------------- tagged-enum readings ---------------------------

/// A fieldless string-enum variant: the bare `Atom(tag)` (§0.3.2).
pub fn tag_atom(tag: &str) -> Value {
    Value::atom(tag.as_bytes().to_vec())
}

/// A tagged variant `Tuple[Atom(tag), payload…]` (§0.3.2).
pub fn tagged(tag: &str, payload: impl IntoIterator<Item = Value>) -> Value {
    let mut items = Vec::new();
    items.push(tag_atom(tag));
    items.extend(payload);
    Value::tuple(items)
}

// ------------------------------- composites ---------------------------------

/// A fixed-order product: `Tuple[fields…]` (§0.3.1). The caller passes fields in
/// the spec's declaration order.
pub fn record(fields: impl IntoIterator<Item = Value>) -> Value {
    Value::tuple(fields)
}

/// An ordered list (order is identity-bearing — NOT sorted), e.g. the `theories`
/// list or a fallback chain (§5.2).
pub fn list<T: AsValue>(items: &[T]) -> Value {
    Value::tuple(items.iter().map(AsValue::as_value))
}

/// An `Option<T>` (§0.3.4): `None` → `Tuple[Atom("none")]`; `Some(x)` →
/// `Tuple[Atom("some"), x.as_value()]`.
pub fn opt<T: AsValue>(o: &Option<T>) -> Value {
    match o {
        None => tagged("none", []),
        Some(x) => tagged("some", [x.as_value()]),
    }
}

/// An `Option<u64>` — `opt` specialized to the integer reading.
pub fn opt_u64(o: &Option<u64>) -> Value {
    match o {
        None => tagged("none", []),
        Some(n) => tagged("some", [u64_atom(*n)]),
    }
}

/// An `Option<u32>` — `opt` specialized to the integer reading.
pub fn opt_u32(o: &Option<u32>) -> Value {
    match o {
        None => tagged("none", []),
        Some(n) => tagged("some", [u32_atom(*n)]),
    }
}

/// An `Option<String>` — `opt` specialized to the byte-atom reading.
pub fn opt_str(o: &Option<String>) -> Value {
    match o {
        None => tagged("none", []),
        Some(s) => tagged("some", [bytes_atom(s.as_bytes().to_vec())]),
    }
}

/// A set of values sorted by codec bytes (§0.3.3). Go/TS must reproduce this
/// order; rs callers that hold a `BTreeSet` already iterate in this order but go
/// through here for a single normative path.
pub fn sorted_set(members: impl IntoIterator<Item = Value>) -> Value {
    let mut items: Vec<Value> = members.into_iter().collect();
    items.sort_by_key(ontos_codec::encode);
    Value::tuple(items)
}

/// A map sorted by the codec bytes of its key (§0.3.3): `Tuple[ Tuple[k₀,v₀], … ]`.
pub fn sorted_map(entries: impl IntoIterator<Item = (Value, Value)>) -> Value {
    let mut pairs: Vec<(Value, Value)> = entries.into_iter().collect();
    pairs.sort_by_key(|(ka, _)| ontos_codec::encode(ka));
    Value::tuple(pairs.into_iter().map(|(k, v)| Value::tuple([k, v])))
}

// ----------------------- reused FIRM sub-value readings ---------------------

/// A predicate [`Symbol`] as a bare `Atom(bytes)` (the account reading).
pub fn symbol_as_value(sym: &Symbol) -> Value {
    bytes_atom(sym.bytes().to_vec())
}

/// A [`Subst`] (`BTreeMap<VarId, Term>`) as `Tuple` of `Tuple[Atom(var_id),
/// quote(term)]` sorted by var-id bytes — matching the `BTreeMap` order (§5.2,
/// `candidate`). Terms reuse the FROZEN [`quote`] reading; no second encoding.
pub fn subst_as_value(subst: &Subst) -> Value {
    // #2602: the shape is written once, in `wire_sink`, and read here as a value.
    ValueSink::build(|s| wire_sink::subst(s, subst))
}

/// A ground literal `p(a…)` as `Tuple[Atom(p), quote(a)…]` — the labeled-compound
/// reading the account codec uses (`goal_as_term`), threaded through the FROZEN
/// [`quote`]. Reused by [`derivation_as_value`]; never a second encoding.
pub fn ground_literal_as_value(lit: &GroundLiteral) -> Value {
    // #2602: the shape is written once, in `wire_sink`, and read here as a value.
    ValueSink::build(|s| wire_sink::ground_literal(s, lit))
}

fn node_meta_as_value(meta: &NodeMeta) -> Value {
    match meta.value() {
        None => tagged("none", []),
        Some(v) => tagged("some", [v.clone()]),
    }
}

fn evidence_as_value(evidence: &Evidence) -> Value {
    match evidence.value() {
        None => tagged("none", []),
        Some(v) => tagged("some", [v.clone()]),
    }
}

fn node_as_value(node: &Node) -> Value {
    match node {
        Node::Rule {
            conclusion,
            clause,
            subst,
            premises,
            meta,
        } => tagged(
            "rule",
            [
                ground_literal_as_value(conclusion),
                bytes_atom(clause.as_str().as_bytes().to_vec()),
                subst_as_value(subst),
                Value::tuple(premises.iter().map(premise_as_value)),
                node_meta_as_value(meta),
            ],
        ),
        Node::Builtin { conclusion } => tagged("builtin", [ground_literal_as_value(conclusion)]),
        Node::Leaf {
            conclusion,
            evidence,
        } => tagged(
            "leaf",
            [
                ground_literal_as_value(conclusion),
                evidence_as_value(evidence),
            ],
        ),
    }
}

/// A [`Premise`] as a value. A positive premise reads as the **bare** `u64_atom`
/// node index — byte-identical to the pre-ADR-0007 wire (so a positive derivation's
/// bytes are unchanged). A negated premise (ADR 0007) reads as a tagged tuple
/// `Tuple[Atom("neg"), atom, Atom(cert)]` (engines do not emit `Neg` yet; this path
/// keeps the wire total over the additive `Premise` sum).
fn premise_as_value(premise: &Premise) -> Value {
    match premise {
        Premise::Pos { node } => u64_atom(*node),
        Premise::Neg { atom, cert, .. } => tagged(
            "neg",
            [ground_literal_as_value(atom), u64_atom(cert.index())],
        ),
        // ADR 0023: a certifiable count premise reads as a tagged tuple carrying the
        // counted predicate, the (pos,value) filter, the projection, the claimed count
        // `k`, and the cert index. Engines do not emit `Count` yet (Phase 3); this path
        // keeps the wire total over the additive `Premise` sum.
        Premise::Count {
            pred,
            filter,
            project,
            k,
            cert,
        } => tagged(
            "count",
            [
                // ADR 0023 #581: the counted relation is arity-sensitive — carry
                // `Tuple[Atom(pred), int(arity)]` so the wire is not lossy on arity.
                Value::tuple([
                    Value::atom(pred.pred.bytes().to_vec()),
                    u64_atom(u64::from(pred.arity)),
                ]),
                Value::tuple(
                    filter
                        .iter()
                        .map(|(pos, v)| Value::tuple([u64_atom(*pos as u64), v.clone()])),
                ),
                project_spec_as_value(project),
                k.clone(),
                u64_atom(cert.index()),
            ],
        ),
    }
}

/// A [`ProjectSpec`] as a value (ADR 0023 + #587): `Rows` ⇒ `Atom("rows")`,
/// `Distinct { attr }` ⇒ `Tuple[Atom("distinct"), int(attr)]`, and the `min`/`max`/`sum`
/// folds ⇒ `Tuple[Atom("sum"|"min"|"max"), int(attr)]` — the same tags the account codec
/// uses, so the candidate digest commits to the fold kind.
fn project_spec_as_value(project: &crate::ProjectSpec) -> Value {
    use crate::ProjectSpec;
    match project {
        ProjectSpec::Rows => Value::atom(b"rows".to_vec()),
        ProjectSpec::Distinct { attr } => tagged("distinct", [u64_atom(*attr as u64)]),
        ProjectSpec::Sum { attr } => tagged("sum", [u64_atom(*attr as u64)]),
        ProjectSpec::Min { attr } => tagged("min", [u64_atom(*attr as u64)]),
        ProjectSpec::Max { attr } => tagged("max", [u64_atom(*attr as u64)]),
    }
}

/// A [`Derivation`] as `Tuple[ Tuple[node₀, …], Atom(root) (, Tuple[cert₀, …]) ]` — the
/// nodes read via the FIRM account/`quote` readings of conclusions/substs (§5.2,
/// `candidate`). The node ordering is the derivation's own (a DAG order is
/// identity-bearing); it is NOT sorted.
///
/// `closed_world` (the [`ClosedModelCert`]s a `Neg`/`Count` premise discharges against,
/// ADR 0007 / ADR 0023) is a **TRAILING-OPTIONAL** 3rd element: appended ONLY when
/// non-empty, so an all-positive derivation (no `Neg`/`Count` premise ⇒ empty
/// `closed_world`) encodes the EXACT same `Tuple[nodes, root]` bytes as before — byte
/// compatibility for every existing positive derivation is preserved.
pub fn derivation_as_value(deriv: &Derivation) -> Value {
    derivation_as_value_with(deriv, closed_world_as_value(deriv))
}

/// The `closed_world` element [`derivation_as_value`] appends: `Some(Tuple[cert₀, …])`, or `None`
/// when the derivation carries no certificate.
pub fn closed_world_as_value(deriv: &Derivation) -> Option<Value> {
    (!deriv.closed_world.is_empty())
        .then(|| Value::tuple(deriv.closed_world.iter().map(closed_model_cert_as_value)))
}

/// [`derivation_as_value`] with its trailing `closed_world` element GIVEN rather than built from
/// the certificates (#2604). The CLI's v3 stream passes its `cert_ref` tuple here, so a certified
/// answer's reference form is built in O(answer) without materializing one certificate. `None`
/// omits the element, exactly as an empty `closed_world` does. The layout lives here once:
/// [`derivation_as_value`] is this function over the real certificates. (It lived in the kernel
/// seam's copy of this reading until #2625 made the seam read through this one.)
pub fn derivation_as_value_with(deriv: &Derivation, closed_world: Option<Value>) -> Value {
    let mut fields = vec![
        Value::tuple(deriv.nodes.iter().map(node_as_value)),
        u64_atom(deriv.root),
    ];
    fields.extend(closed_world);
    Value::tuple(fields)
}

/// A [`ClosedModelCert`] (ADR 0007 / ADR 0023) as a value — the sealed finite-model
/// certificate a `Neg`/`Count` premise discharges against, carried in
/// [`derivation_as_value`]'s trailing `closed_world` slot so a certified candidate
/// round-trips across the seam. The [`ClosureWitness`](crate::ClosureWitness) is
/// an empty v1 marker (no engine-supplied bytes) and is reconstructed by default on decode.
pub fn closed_model_cert_as_value(cert: &ClosedModelCert) -> Value {
    closed_model_cert_with_decl_as_value(cert, &cert.limits_decl)
}

/// [`closed_model_cert_as_value`] with the size declaration supplied, so [`cert_encoded_bytes`]
/// can zero one field without cloning the certificate.
fn closed_model_cert_with_decl_as_value(cert: &ClosedModelCert, decl: &CertSizeDecl) -> Value {
    // #2602: the shape is written once, in `wire_sink`, and read here as a value.
    ValueSink::build(|s| wire_sink::closed_model_cert(s, cert, decl))
}

/// #2524 (`seat:caa`'s ruling): a certificate's size in BYTES, the one definition a producer
/// declares and the checker measures: the length of its canonical wire encoding
/// ([`closed_model_cert_as_value`] through the ontos codec) with `limits_decl.cert_bytes` set to 0.
///
/// The encoding CONTAINS the declaration, so "declare your own encoded size" would be circular;
/// zeroing the field makes it well defined, and it differs from the literal size by at most a
/// varint's width. go (`CertEncodedBytes`) and ts (`certEncodedBytes`) mirror it, and a generated
/// vector pins their agreement (`vectors/cert_encoded_bytes.json`).
pub fn cert_encoded_bytes(cert: &ClosedModelCert) -> u64 {
    let decl = CertSizeDecl {
        cert_bytes: 0,
        ..cert.limits_decl
    };
    // #2602: measured through the length reading of the one wire shape, so no value tree and no
    // encoded buffer is built (they were 41% of a certified-set run's peak heap). A debug build
    // re-derives every measured certificate the old way and asserts the two agree.
    let len = LenSink::measure(|s| wire_sink::closed_model_cert(s, cert, &decl));
    debug_assert_eq!(
        len,
        ontos_codec::encode(&closed_model_cert_with_decl_as_value(cert, &decl)).len() as u64,
        "the length reading disagrees with the encoding it measures"
    );
    len
}

/// #2524: a LOWER bound on [`cert_encoded_bytes`] of any certificate holding exactly `extensions`:
/// the encoded length of its extension tables, through the SAME path [`closed_model_cert_as_value`]
/// encodes them. That tuple is a literal sub-encoding of the whole certificate, so the bound is a
/// subset by construction, and a producer can read it before the certificate's support exists.
pub fn cert_tables_encoded_bytes(extensions: &[RelationTable]) -> u64 {
    let len = LenSink::measure(|s| wire_sink::relation_tables(s, extensions));
    debug_assert_eq!(
        len,
        ontos_codec::encode(&ValueSink::build(|s| wire_sink::relation_tables(
            s, extensions
        )))
        .len() as u64,
        "the length reading disagrees with the encoding it measures"
    );
    len
}

/// A clause as its frozen account value (`quote(clause-as-term)`). Re-exported so a
/// plan/analysis reading that embeds a clause reuses the one frozen reading.
pub fn clause_as_value(clause: &Clause) -> Value {
    clause_value(clause)
}

/// Why a [`Value`] is not in the image of the corresponding `*_as_value` reading, or why the trusted
/// bytes decoder could not read its caller's bytes at all.
///
/// Every variant but [`DecodeError::CodecFault`] is a malformed-wire refusal: the value does not
/// decode to a well-formed candidate/derivation/subst. `CodecFault` is the trusted decoder's own
/// arm (checker SPI v2, ADR 0036 D8 change 4, #2734 ruling C). The decoders return this instead of
/// panicking, so a byzantine or cross-language producer cannot crash the kernel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// A value was expected to be a `Tuple` (a record/list/tagged form) but was an
    /// `Atom`, or vice versa. `ctx` names the reading being decoded.
    Shape { ctx: &'static str },
    /// A `Tuple` had the wrong arity for its reading (e.g. a candidate is not a
    /// 3-tuple). `ctx` names the reading; `accepted` is EVERY arity the reading takes
    /// (#2630: a reading with trailing-optional slots accepts more than one, and a single
    /// number would understate it), `got` the arity seen. Rendered by
    /// [`arity_refusal`].
    Arity {
        ctx: &'static str,
        accepted: &'static [usize],
        got: usize,
    },
    /// A tagged-enum tag was not one of the reading's known variants. `ctx` names the
    /// reading; `tag` is the tag's exact bytes, rendered by [`render_tag`] (#2682).
    UnknownTag { ctx: &'static str, tag: Vec<u8> },
    /// A value was not in the image of `quote` (a term that is not a quoted term, or
    /// a non-ground argument). `ctx` names the reading.
    NotQuoted { ctx: &'static str },
    /// An integer field was not the canonical `ontos-data` `int` embedding, or it was
    /// out of range. `ctx` names the field.
    BadInt { ctx: &'static str },
    /// A byte-atom that had to be valid UTF-8 (a var-id or a provider string) was not.
    BadUtf8 { ctx: &'static str },
    /// A sorted-invariant certificate collection (scope predicates, domain values,
    /// extension rows) arrived on the wire out of canonical sorted+deduped order
    /// (issue #839). The in-memory types binary-search these collections, so
    /// admitting the bytes verbatim would silently defeat every membership decision
    /// downstream — and silently *repairing* them would mask the producer bug.
    /// Proof-carrying data is rejected, never fixed up. `ctx` names the collection.
    NotCanonical { ctx: &'static str },
    /// [`decode_derivation_wire_v1`]'s codec stopped on the caller's own bytes: the codec's error,
    /// unfolded (checker SPI v2, ADR 0036 D8 change 4; #2734 increment 3c, `seat:caa`'s ruling C).
    /// It is a FAULT, never a shape refusal: that decoder reads bytes its caller produced and
    /// trusts, so a codec that cannot read them (a capacity such as the decode depth, an atom
    /// length or an arity, or bytes that are not a value) is the caller's defect. Bytes from
    /// anyone else go through `decode_derivation_wire_v1_bounded`, whose `Stopped` arm carries the
    /// same error as an ordinary refusal. The rendering names the codec's portable `code`; its
    /// message stays in `error`, because the cores' codecs word it differently.
    CodecFault {
        ctx: &'static str,
        error: ontos_codec::DecodeError,
    },
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeError::Shape { ctx } => {
                write!(f, "decode {ctx}: expected a different value shape")
            }
            DecodeError::Arity { ctx, accepted, got } => {
                f.write_str(&arity_refusal(ctx, accepted, *got))
            }
            DecodeError::UnknownTag { ctx, tag } => {
                write!(f, "decode {ctx}: unknown tag {}", render_tag(tag))
            }
            DecodeError::NotQuoted { ctx } => {
                write!(f, "decode {ctx}: value is not a quoted ground term")
            }
            DecodeError::BadInt { ctx } => {
                write!(f, "decode {ctx}: not a canonical int embedding")
            }
            DecodeError::BadUtf8 { ctx } => write!(f, "decode {ctx}: not valid UTF-8"),
            DecodeError::NotCanonical { ctx } => {
                write!(f, "decode {ctx}: not in canonical sorted+deduped order")
            }
            DecodeError::CodecFault { ctx, error } => {
                write!(f, "decode {ctx}: codec fault: {}", error.code())
            }
        }
    }
}

impl std::error::Error for DecodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let DecodeError::CodecFault { error, .. } = self {
            Some(error)
        } else {
            None
        }
    }
}

/// The ONE rendering of an arity refusal (#2630, `seat:caa`'s ruling): a reading that takes a
/// single arity keeps the text it always had (`decode {ctx}: expected arity 3, got 2`); a reading
/// with trailing-optional slots names EVERY arity it takes (`decode closed_world.cert: 13
/// elements, expected 10, 11 or 12`), so the refusal never understates what would have been
/// accepted. The kernel seam's own `DecodeError` renders its arity refusals through this too.
pub fn arity_refusal(ctx: &str, accepted: &[usize], got: usize) -> String {
    match accepted {
        [one] => format!("decode {ctx}: expected arity {one}, got {got}"),
        [init @ .., last] => {
            let init: Vec<String> = init.iter().map(usize::to_string).collect();
            format!(
                "decode {ctx}: {got} elements, expected {} or {last}",
                init.join(", ")
            )
        }
        [] => format!("decode {ctx}: {got} elements, and no arity is accepted"),
    }
}

/// The ONE rendering of an unknown tag in a refusal text (#2682, `seat:caa`'s ruling B): a
/// double-quoted string in which each ASCII byte renders exactly as Rust's `{:?}` renders that
/// character (`\"`, `\\`, `\t`, `\r`, `\n`, `\0`, another control as `\u{hex}`, a printable byte
/// as itself), and each byte `>= 0x80` renders as `\x{hh}`. Nothing is UTF-8-decoded.
///
/// It is DEFINED here rather than inherited from `{:?}` because the text is pinned tri-core: Rust's
/// Debug decodes lossily and consults its own `is_printable` table (it escapes U+FEFF and U+200B,
/// prints `ü` and U+FFFD), so go and ts could only match it by copying that table. Byte-level
/// rendering is identical by construction in every core.
pub fn render_tag(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() + 2);
    out.push('"');
    for &b in bytes {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            b'\n' => out.push_str("\\n"),
            0 => out.push_str("\\0"),
            _ if b == b' ' || b.is_ascii_graphic() => out.push(char::from(b)),
            _ if b.is_ascii() => out.push_str(&format!("\\u{{{b:x}}}")),
            _ => out.push_str(&format!("\\x{{{b:02x}}}")),
        }
    }
    out.push('"');
    out
}

type Result<T> = std::result::Result<T, DecodeError>;

// ------------------------------- small helpers ------------------------------

/// Borrow `v`'s tuple items, or `Shape`.
pub(crate) fn items<'a>(v: &'a Value, ctx: &'static str) -> Result<&'a [Value]> {
    v.as_tuple()
        .map(|t| t.items())
        .ok_or(DecodeError::Shape { ctx })
}

/// Borrow `v`'s tuple items at one of the `accepted` arities.
pub(crate) fn items_n<'a>(
    v: &'a Value,
    ctx: &'static str,
    accepted: &'static [usize],
) -> Result<&'a [Value]> {
    let its = items(v, ctx)?;
    if !accepted.contains(&its.len()) {
        return Err(DecodeError::Arity {
            ctx,
            accepted,
            got: its.len(),
        });
    }
    Ok(its)
}

/// Borrow `v`'s atom bytes, or `Shape`.
pub(crate) fn atom_bytes<'a>(v: &'a Value, ctx: &'static str) -> Result<&'a [u8]> {
    v.as_atom()
        .map(|a| a.bytes())
        .ok_or(DecodeError::Shape { ctx })
}

/// Split a tagged value `Tuple[Atom(tag), payload…]` into its tag and payload — the
/// inverse of [`tagged`](super::wire::tagged). Requires at least the tag slot.
pub(crate) fn split_tag<'a>(v: &'a Value, ctx: &'static str) -> Result<(&'a [u8], &'a [Value])> {
    let its = items(v, ctx)?;
    let (head, rest) = its.split_first().ok_or(DecodeError::Arity {
        ctx,
        accepted: &[1],
        got: 0,
    })?;
    Ok((atom_bytes(head, ctx)?, rest))
}

/// The contract's bound on every index and count field: a root, a premise or certificate
/// index, a `limits_decl` field (#2682, `seat:caa`'s ruling A). `2^53 - 1`, so every core holds
/// every in-domain value exactly (ts's exact-integer range), and above it every core refuses
/// `BadInt` the same way. It is ONE number, not each platform's width: rs's `usize` (`2^64 - 1`
/// natively, `2^32 - 1` on wasm32), go's `int` and ts's number used to set four bounds.
pub const INDEX_MAX: u64 = (1 << 53) - 1;

/// Decode an index or count field into `0..=INDEX_MAX`, else `BadInt`.
fn read_index_u64(v: &Value, ctx: &'static str) -> Result<u64> {
    let n = ontos_data::read_int(v).map_err(|_| DecodeError::BadInt { ctx })?;
    match u64::try_from(n) {
        Ok(n) if n <= INDEX_MAX => Ok(n),
        _ => Err(DecodeError::BadInt { ctx }),
    }
}

/// Decode an index or count field: an INTEGER in the contract's domain (`<=` [`INDEX_MAX`]), never
/// narrowed to this build's `usize` (#2735). Whether it names an element is decided where it is
/// used, by [`index_offset`](crate::index_offset).
fn read_index(v: &Value, ctx: &'static str) -> Result<u64> {
    read_index_u64(v, ctx)
}

/// Decode an `int` field that the account types as `u32` (an arity, a position, an attribute, a
/// stratum level, a rank). A value past `u32::MAX` is refused as `BadInt`, never narrowed: a
/// truncation is a repaired input (#839), and it made the same bytes decode to different values
/// in rs/go (which truncated) and ts (which did not) (#2682).
fn read_u32(v: &Value, ctx: &'static str) -> Result<u32> {
    let n = ontos_data::read_int(v).map_err(|_| DecodeError::BadInt { ctx })?;
    u32::try_from(n).map_err(|_| DecodeError::BadInt { ctx })
}

/// Decode an `opt(_)` reading — `Tuple[Atom("none")]` or `Tuple[Atom("some"), x]` —
/// returning the inner payload value for `Some`. The inverse of
/// [`opt`](super::wire::opt) at the value layer.
fn read_opt<'a>(v: &'a Value, ctx: &'static str) -> Result<Option<&'a Value>> {
    let (tag, payload) = split_tag(v, ctx)?;
    match tag {
        b"none" => {
            if !payload.is_empty() {
                return Err(DecodeError::Arity {
                    ctx,
                    accepted: &[1],
                    got: payload.len() + 1,
                });
            }
            Ok(None)
        }
        b"some" => {
            if payload.len() != 1 {
                return Err(DecodeError::Arity {
                    ctx,
                    accepted: &[2],
                    got: payload.len() + 1,
                });
            }
            Ok(Some(&payload[0]))
        }
        other => Err(DecodeError::UnknownTag {
            ctx,
            tag: other.to_vec(),
        }),
    }
}

// ------------------------------ term / literal ------------------------------

/// Reconstruct a GROUND [`Value`] argument from its `quote`d wire form. The encoder
/// stores each ground-literal argument as `quote(Term::from_value(arg))`, so the
/// inverse is `reify` (→ `Term`) then `erase_ground` (→ `Value`). A non-ground or
/// non-quoted value is rejected.
///
/// #2731 (`seat:caa`'s ruling): the decoder imposes NO depth policy. Both readers recurse only
/// within [`TERM_RECURSION_BUDGET`](crate::TERM_RECURSION_BUDGET) and continue on a heap stack
/// past it (#2275 layer 3), so a deep term cannot overflow them; the fixed 256-value-level guard
/// that used to stand here (#253) refused, at about 128 TERM levels, derivations go and ts decode
/// and every core's `check` accepts. The one depth policy is `check`'s `max_term_depth`.
fn ground_arg_from_quoted(v: &Value, ctx: &'static str) -> Result<Value> {
    let term = reify(v).ok_or(DecodeError::NotQuoted { ctx })?;
    term.erase_ground().ok_or(DecodeError::NotQuoted { ctx })
}

/// The public strict inverse of [`ground_literal_as_value`] (#1914): decode ONE standalone
/// ground literal from its account representation `Tuple[Atom(pred), quote(arg)…]`.
///
/// This is the same decoder every derivation node conclusion goes through — one
/// interpretation, not a second one — exposed so a consumer that persists or exchanges a
/// bare fact can round-trip it without fabricating a derivation. It refuses a missing or
/// non-atom predicate (`Shape` / `Arity`), an argument outside the image of `quote`
/// (`NotQuoted`), and a quoted VARIABLE or any non-ground argument (`NotQuoted`). It refuses
/// no term for its depth (#2731): that is `check`'s `max_term_depth`. Ordinary data that merely LOOKS like a variable —
/// an atom whose bytes are `X` — is an atom under `quote` and round-trips unchanged.
///
/// ⚠ The account representation is not the raw Ontos compound `Tuple[Atom(pred), arg…]`:
/// the arguments are `quote`d, and that is what lets the inverse check groundness. Feeding
/// this function an unquoted compound is refused as `NotQuoted`, by design.
pub fn ground_literal_from_value_v1(v: &Value) -> Result<GroundLiteral> {
    ground_literal_from_value(v, "ground literal")
}

/// Reconstruct a [`GroundLiteral`] from `Tuple[Atom(pred), quote(arg)…]` — the
/// inverse of [`ground_literal_as_value`](super::wire::ground_literal_as_value).
fn ground_literal_from_value(v: &Value, ctx: &'static str) -> Result<GroundLiteral> {
    let its = items(v, ctx)?;
    let (pred, args) = its.split_first().ok_or(DecodeError::Arity {
        ctx,
        accepted: &[1],
        got: 0,
    })?;
    let pred = Symbol::new(atom_bytes(pred, ctx)?.to_vec());
    let mut decoded = Vec::with_capacity(args.len());
    for arg in args {
        decoded.push(ground_arg_from_quoted(arg, ctx)?);
    }
    Ok(GroundLiteral::new(pred, decoded))
}

// ---------------------------------- subst -----------------------------------

/// Reconstruct a [`Subst`] from `Tuple[ Tuple[Atom(var_id), quote(term)], … ]` — the
/// inverse of [`subst_as_value`](super::wire::subst_as_value).
///
/// The encoder emits entries strictly increasing in var-id codec bytes, and the decoder
/// requires exactly that order: a repeated or misordered var-id is refused as
/// `NotCanonical` (#2630), never re-sorted. A var-id is its exact bytes, so two ids that
/// differ only by a leading BOM are two variables (#2682). The term reuses the FROZEN
/// [`reify`] reader (the partial inverse of `quote`) — never a hand-rolled term decoder.
pub fn subst_from_value(v: &Value) -> Result<Subst> {
    const CTX: &str = "subst";
    let entries = items(v, CTX)?;
    let mut subst = Subst::new();
    let mut previous_key: Option<Vec<u8>> = None;
    for entry in entries {
        let pair = items_n(entry, "subst.entry", &[2])?;
        let name = std::str::from_utf8(atom_bytes(&pair[0], "subst.var")?)
            .map_err(|_| DecodeError::BadUtf8 { ctx: "subst.var" })?;
        // #2630 (`seat:caa`'s ruling): the encoder writes the entries strictly increasing in the
        // codec bytes of their key (`sorted_map`), so a repeated var-id or a misordered one is
        // refused by name, tri-core, where inserting it would keep one value silently.
        let key = ontos_codec::encode(&pair[0]);
        if previous_key
            .as_ref()
            .is_some_and(|previous| *previous >= key)
        {
            return Err(DecodeError::NotCanonical { ctx: "subst" });
        }
        previous_key = Some(key);
        let term = reify(&pair[1]).ok_or(DecodeError::NotQuoted { ctx: "subst.term" })?;
        subst.insert(VarId::new(name), term);
    }
    Ok(subst)
}

// -------------------------------- derivation --------------------------------

/// Reconstruct a [`NodeMeta`] from its `opt(value)` reading:
/// `None` → [`NodeMeta::none`]; `Some(v)` →
/// [`NodeMeta::new`] of the RAW inner value (it is opaque to the core).
fn node_meta_from_value(v: &Value) -> Result<NodeMeta> {
    Ok(match read_opt(v, "node.meta")? {
        None => NodeMeta::none(),
        Some(inner) => NodeMeta::new(inner.clone()),
    })
}

/// Reconstruct an [`Evidence`] from its `opt(value)` reading (`evidence_as_value`).
fn evidence_from_value(v: &Value) -> Result<Evidence> {
    Ok(match read_opt(v, "node.evidence")? {
        None => Evidence::none(),
        Some(inner) => Evidence::new(inner.clone()),
    })
}

/// Reconstruct one [`Node`] from its tagged reading — the inverse of
/// `node_as_value`. The three tags mirror the encoder exactly: `rule` carries
/// `[conclusion, clause, subst, premises, meta]`; `builtin` carries `[conclusion]`;
/// `leaf` carries `[conclusion, evidence]`.
fn node_from_value(v: &Value) -> Result<Node> {
    const CTX: &str = "node";
    let (tag, payload) = split_tag(v, CTX)?;
    match tag {
        b"rule" => {
            if payload.len() != 5 {
                return Err(DecodeError::Arity {
                    ctx: "node.rule",
                    accepted: &[6],
                    got: payload.len() + 1,
                });
            }
            let conclusion = ground_literal_from_value(&payload[0], "node.rule.conclusion")?;
            let clause = std::str::from_utf8(atom_bytes(&payload[1], "node.rule.clause")?)
                .map_err(|_| DecodeError::BadUtf8 {
                    ctx: "node.rule.clause",
                })?;
            let subst = subst_from_value(&payload[2])?;
            let premise_items = items(&payload[3], "node.rule.premises")?;
            let mut premises = Vec::with_capacity(premise_items.len());
            for p in premise_items {
                premises.push(premise_from_value(p)?);
            }
            let meta = node_meta_from_value(&payload[4])?;
            Ok(Node::Rule {
                conclusion,
                clause: crate::ClauseId::new(clause),
                subst,
                premises,
                meta,
            })
        }
        b"builtin" => {
            if payload.len() != 1 {
                return Err(DecodeError::Arity {
                    ctx: "node.builtin",
                    accepted: &[2],
                    got: payload.len() + 1,
                });
            }
            Ok(Node::Builtin {
                conclusion: ground_literal_from_value(&payload[0], "node.builtin.conclusion")?,
            })
        }
        b"leaf" => {
            if payload.len() != 2 {
                return Err(DecodeError::Arity {
                    ctx: "node.leaf",
                    accepted: &[3],
                    got: payload.len() + 1,
                });
            }
            Ok(Node::Leaf {
                conclusion: ground_literal_from_value(&payload[0], "node.leaf.conclusion")?,
                evidence: evidence_from_value(&payload[1])?,
            })
        }
        other => Err(DecodeError::UnknownTag {
            ctx: CTX,
            tag: other.to_vec(),
        }),
    }
}

/// Reconstruct one [`Premise`](crate::Premise) — the inverse of
/// `premise_as_value`. A bare `u64` atom is a positive premise (node index); a tagged
/// `Tuple[Atom("neg"|"count"), …]` is a `Neg` (ADR 0007) or `Count` (ADR 0023) premise.
/// (Before #613 this read only the bare-index form, so a `Count` premise a wasm-guest
/// candidate carried failed to decode — `BadInt { ctx: "node.rule.premise" }`.)
fn premise_from_value(p: &Value) -> Result<crate::Premise> {
    use crate::{CertId, NonMemberProof, PredicateRef, Premise};
    // A positive premise is a bare `int` node index (itself an ontos-data tagged value, so
    // it must be read with the int reader, NOT distinguished by `split_tag`); a `Neg`/`Count`
    // premise is a `Tuple[Atom("neg"|"count"), …]`, which `read_int` rejects.
    if let Ok(node) = read_index(p, "node.rule.premise") {
        return Ok(Premise::pos(node));
    }
    let (tag, payload) = split_tag(p, "node.rule.premise")?;
    match tag {
        b"neg" => {
            if payload.len() != 2 {
                return Err(DecodeError::Arity {
                    ctx: "node.rule.premise.neg",
                    accepted: &[3],
                    got: payload.len() + 1,
                });
            }
            Ok(Premise::Neg {
                atom: ground_literal_from_value(&payload[0], "node.rule.premise.neg.atom")?,
                cert: CertId(read_index(&payload[1], "node.rule.premise.neg.cert")?),
                // v1 has a single non-membership witness form; the encoder carries no
                // discriminant, so `DirectLookup` is the faithful reconstruction.
                nonmember: NonMemberProof::DirectLookup,
            })
        }
        b"count" => {
            if payload.len() != 5 {
                return Err(DecodeError::Arity {
                    ctx: "node.rule.premise.count",
                    accepted: &[6],
                    got: payload.len() + 1,
                });
            }
            // pred = Tuple[Atom(name), int(arity)] (#581: arity-sensitive).
            let pred_items = items_n(&payload[0], "node.rule.premise.count.pred", &[2])?;
            let name = atom_bytes(&pred_items[0], "node.rule.premise.count.pred.name")?;
            let arity = read_u32(&pred_items[1], "node.rule.premise.count.pred.arity")?;
            let pred = PredicateRef::new(Symbol::new(name.to_vec()), arity);
            // filter = Tuple[ Tuple[int(pos), value], … ].
            let filter_items = items(&payload[1], "node.rule.premise.count.filter")?;
            let mut filter: Vec<(u32, Value)> = Vec::with_capacity(filter_items.len());
            for entry in filter_items {
                let pair = items_n(entry, "node.rule.premise.count.filter.entry", &[2])?;
                let pos = read_u32(&pair[0], "node.rule.premise.count.filter.pos")?;
                filter.push((pos, pair[1].clone()));
            }
            Ok(Premise::Count {
                pred,
                filter,
                project: project_spec_from_value(&payload[2])?,
                // `k` is the canonical ontos/data `int` ground value, carried verbatim.
                k: payload[3].clone(),
                cert: CertId(read_index(&payload[4], "node.rule.premise.count.cert")?),
            })
        }
        other => Err(DecodeError::UnknownTag {
            ctx: "node.rule.premise",
            tag: other.to_vec(),
        }),
    }
}

/// Reconstruct a [`ProjectSpec`](crate::ProjectSpec) — the inverse of
/// `project_spec_as_value` (ADR 0023 + #587): `Atom("rows")` ⇒ `Rows`; a tagged
/// `Tuple[Atom("distinct"|"sum"|"min"|"max"), int(attr)]` ⇒ the corresponding fold.
fn project_spec_from_value(v: &Value) -> Result<crate::ProjectSpec> {
    use crate::ProjectSpec;
    // `Rows` is the bare Atom("rows"); the folds are Tuple[Atom(tag), int(attr)].
    if let Ok(bytes) = atom_bytes(v, "node.rule.premise.count.project") {
        return match bytes {
            b"rows" => Ok(ProjectSpec::Rows),
            other => Err(DecodeError::UnknownTag {
                ctx: "node.rule.premise.count.project",
                tag: other.to_vec(),
            }),
        };
    }
    let (tag, payload) = split_tag(v, "node.rule.premise.count.project")?;
    if payload.len() != 1 {
        return Err(DecodeError::Arity {
            ctx: "node.rule.premise.count.project",
            accepted: &[2],
            got: payload.len() + 1,
        });
    }
    let attr = read_u32(&payload[0], "node.rule.premise.count.project.attr")?;
    match tag {
        b"distinct" => Ok(ProjectSpec::Distinct { attr }),
        b"sum" => Ok(ProjectSpec::Sum { attr }),
        b"min" => Ok(ProjectSpec::Min { attr }),
        b"max" => Ok(ProjectSpec::Max { attr }),
        other => Err(DecodeError::UnknownTag {
            ctx: "node.rule.premise.count.project",
            tag: other.to_vec(),
        }),
    }
}

/// Reconstruct a [`Derivation`] from `Tuple[ Tuple[node₀, …], int(root) ]` — the
/// inverse of [`derivation_as_value`](super::wire::derivation_as_value).
///
/// Node order is IDENTITY-BEARING (a DAG order, premises reference earlier indices);
/// it is preserved exactly in iteration order and never sorted.
pub fn derivation_from_value(v: &Value) -> Result<Derivation> {
    const CTX: &str = "derivation";
    let its = items(v, CTX)?;
    // 2-tuple = all-positive derivation (empty closed_world); 3-tuple carries the
    // TRAILING-OPTIONAL closed_world (the ClosedModelCerts a Neg/Count premise cites).
    if its.len() != 2 && its.len() != 3 {
        return Err(DecodeError::Arity {
            ctx: CTX,
            accepted: &[2, 3],
            got: its.len(),
        });
    }
    let node_values = items(&its[0], "derivation.nodes")?;
    let mut nodes = Vec::with_capacity(node_values.len());
    for nv in node_values {
        nodes.push(node_from_value(nv)?);
    }
    let root = read_index(&its[1], "derivation.root")?;
    let closed_world = match its.get(2) {
        None => Vec::new(),
        Some(cw) => {
            let cert_values = items(cw, "derivation.closed_world")?;
            let mut certs = Vec::with_capacity(cert_values.len());
            for cv in cert_values {
                certs.push(closed_model_cert_from_value(cv)?);
            }
            certs
        }
    };
    Ok(Derivation::with_closed_world(nodes, root, closed_world))
}

/// Read a digest atom into a [`Hash`](crate::Hash) — the inverse of
/// [`digest_atom`](super::wire::digest_atom), which writes the 32 bytes as a 64-char
/// lowercase-hex `Atom`.
pub(crate) fn read_hash(v: &Value, ctx: &'static str) -> Result<[u8; 32]> {
    crate::parse_hash_hex(atom_bytes(v, ctx)?).ok_or(DecodeError::Shape { ctx })
}

/// Reconstruct a [`Symbol`] from a bare `Atom(bytes)`.
fn symbol_from_value(v: &Value, ctx: &'static str) -> Result<Symbol> {
    Ok(Symbol::new(atom_bytes(v, ctx)?.to_vec()))
}

/// Reconstruct a [`ClosedModelCert`] — the inverse of
/// [`closed_model_cert_as_value`](super::wire::closed_model_cert_as_value) (#613). The
/// [`ClosureWitness`] is an empty v1 marker, reconstructed by default.
pub fn closed_model_cert_from_value(v: &Value) -> Result<ClosedModelCert> {
    // TEN, ELEVEN or TWELVE: the 11th is D10's trailing-optional slice-seal pin, the 12th is
    // ADR 0030's trailing-optional partial sub-scope. Absent ⇒ `None` ⇒ the cert pins the
    // complete program / every table is exact — every pre-D10 / pre-0030 cert. Anything else
    // is refused by arity under the closed posture: a decoder that predates a field can never
    // read a partial table as complete, because it never reads the cert at all.
    let all = items(v, "closed_world.cert")?;
    let its: &[Value] = match all.len() {
        10..=12 => all,
        _ => {
            return Err(DecodeError::Arity {
                ctx: "closed_world.cert",
                accepted: &[10, 11, 12],
                got: all.len(),
            })
        }
    };
    // Slot 11 is a digest atom — or, ONLY when slot 12 is present, the `opt` none marker
    // `Tuple[Atom("none")]` standing in for an absent pin (trailing-optional elements are
    // positional). An eleven-element cert whose 11th is the marker is refused: it says
    // nothing a ten-element cert does not, and the canonical form is the shorter one.
    let decomposition_witness = match its.get(10) {
        None => None,
        Some(w) if its.len() == 12 && is_opt_none(w) => None,
        Some(w) => Some(read_hash(w, "closed_world.cert.decomposition_witness")?),
    };
    let partial_scope = match its.get(11) {
        Some(p) => Some(stratum_prefix_from_value(p)?),
        None => None,
    };
    let mut edb_snapshot_hashes = Vec::new();
    for h in items(&its[5], "closed_world.cert.edb_snapshot_hashes")? {
        edb_snapshot_hashes.push(read_hash(h, "closed_world.cert.edb_snapshot_hash")?);
    }
    let mut domains = Vec::new();
    for d in items(&its[6], "closed_world.cert.domains")? {
        domains.push(finite_domain_from_value(d)?);
    }
    let mut extensions = Vec::new();
    for t in items(&its[7], "closed_world.cert.extensions")? {
        extensions.push(relation_table_from_value(t)?);
    }
    let mut supports = Vec::new();
    for e in items(&its[8], "closed_world.cert.supports")? {
        supports.push(support_edge_from_value(e)?);
    }
    Ok(ClosedModelCert {
        scope: stratum_prefix_from_value(&its[0])?,
        program_hash: read_hash(&its[1], "closed_world.cert.program_hash")?,
        profile_hash: read_hash(&its[2], "closed_world.cert.profile_hash")?,
        ctx_hash: read_hash(&its[3], "closed_world.cert.ctx_hash")?,
        theory_config_hash: read_hash(&its[4], "closed_world.cert.theory_config_hash")?,
        edb_snapshot_hashes,
        domains,
        extensions,
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        limits_decl: cert_size_decl_from_value(&its[9])?,
        decomposition_witness,
        partial_scope,
    })
}

/// Is `v` the `opt` none marker `Tuple[Atom("none")]` (ADR 0030 D4's stand-in for an absent
/// slice-seal pin at the 11th cert slot when the 12th is present)? A malformed tuple is
/// simply *not* the marker; the caller's next read reports it.
fn is_opt_none(v: &Value) -> bool {
    matches!(
        split_tag(v, "closed_world.cert.decomposition_witness"),
        Ok((b"none", payload)) if payload.is_empty()
    )
}

/// Reconstruct a [`StratumPrefix`]. The wire encoding promises sorted + deduped
/// predicates; that promise is CHECKED, not assumed (issue #839) — the in-memory
/// type binary-searches this collection, so admitting unsorted bytes verbatim
/// would silently defeat membership, and sorting them here would silently repair
/// a producer bug. Proof-carrying data is rejected, never fixed up.
fn stratum_prefix_from_value(v: &Value) -> Result<StratumPrefix> {
    let its = items_n(v, "closed_world.cert.scope", &[2])?;
    let level = read_u32(&its[0], "closed_world.cert.scope.level")?;
    let mut predicates = Vec::new();
    for p in items(&its[1], "closed_world.cert.scope.predicates")? {
        predicates.push(symbol_from_value(p, "closed_world.cert.scope.predicate")?);
    }
    let scope = StratumPrefix { level, predicates };
    if !scope.is_canonical() {
        return Err(DecodeError::NotCanonical {
            ctx: "closed_world.cert.scope.predicates",
        });
    }
    Ok(scope)
}

/// Reconstruct a [`FiniteDomain`]. Values are carried verbatim and their canonical
/// sorted+deduped order is CHECKED, not assumed or repaired (issue #839; see
/// [`stratum_prefix_from_value`]).
fn finite_domain_from_value(v: &Value) -> Result<FiniteDomain> {
    let its = items_n(v, "closed_world.cert.domain", &[2])?;
    let type_tag = symbol_from_value(&its[0], "closed_world.cert.domain.type_tag")?;
    let values = items(&its[1], "closed_world.cert.domain.values")?.to_vec();
    let domain = FiniteDomain { type_tag, values };
    if !domain.is_canonical() {
        return Err(DecodeError::NotCanonical {
            ctx: "closed_world.cert.domain.values",
        });
    }
    Ok(domain)
}

/// Reconstruct a [`RelationTable`]. Row order is CHECKED against the canonical
/// sorted+deduped invariant, not assumed or repaired (issue #839; see
/// [`stratum_prefix_from_value`]).
fn relation_table_from_value(v: &Value) -> Result<RelationTable> {
    let its = items_n(v, "closed_world.cert.extension", &[3])?;
    let pred = symbol_from_value(&its[0], "closed_world.cert.extension.pred")?;
    let arity = read_u32(&its[1], "closed_world.cert.extension.arity")?;
    let mut rows = Vec::new();
    for r in items(&its[2], "closed_world.cert.extension.rows")? {
        rows.push(ground_literal_from_value(
            r,
            "closed_world.cert.extension.row",
        )?);
    }
    let table = RelationTable { pred, arity, rows };
    if !table.is_canonical() {
        return Err(DecodeError::NotCanonical {
            ctx: "closed_world.cert.extension.rows",
        });
    }
    Ok(table)
}

/// Reconstruct a [`SupportEdge`].
fn support_edge_from_value(v: &Value) -> Result<SupportEdge> {
    let its = items_n(v, "closed_world.cert.support", &[5])?;
    let fact = ground_literal_from_value(&its[0], "closed_world.cert.support.fact")?;
    let clause = ClauseId::new(
        std::str::from_utf8(atom_bytes(&its[1], "closed_world.cert.support.clause")?).map_err(
            |_| DecodeError::BadUtf8 {
                ctx: "closed_world.cert.support.clause",
            },
        )?,
    );
    let subst = subst_from_value(&its[2])?;
    let mut body_refs = Vec::new();
    for r in items(&its[3], "closed_world.cert.support.body_refs")? {
        body_refs.push(support_ref_from_value(r)?);
    }
    let rank = read_u32(&its[4], "closed_world.cert.support.rank")?;
    Ok(SupportEdge {
        fact,
        clause,
        subst,
        body_refs,
        rank,
    })
}

/// Reconstruct a [`SupportRef`] — the inverse of the 4-variant tagged reading.
fn support_ref_from_value(v: &Value) -> Result<SupportRef> {
    use crate::CertId;
    let (tag, payload) = split_tag(v, "closed_world.cert.support.ref")?;
    match tag {
        b"same_stratum" => {
            let p = expect_n(payload, &[3], "closed_world.cert.support.ref.same_stratum")?;
            Ok(SupportRef::SameStratum {
                fact: ground_literal_from_value(&p[0], "closed_world.cert.support.ref.fact")?,
                rank: read_u32(&p[1], "closed_world.cert.support.ref.rank")?,
            })
        }
        b"lower_stratum" => {
            let p = expect_n(payload, &[3], "closed_world.cert.support.ref.lower_stratum")?;
            Ok(SupportRef::LowerStratum {
                cert: CertId(read_index(&p[0], "closed_world.cert.support.ref.cert")?),
                atom: ground_literal_from_value(&p[1], "closed_world.cert.support.ref.atom")?,
            })
        }
        b"builtin" => {
            let p = expect_n(payload, &[2], "closed_world.cert.support.ref.builtin")?;
            Ok(SupportRef::Builtin {
                atom: ground_literal_from_value(&p[0], "closed_world.cert.support.ref.atom")?,
            })
        }
        b"neg_lower" => {
            let p = expect_n(payload, &[3], "closed_world.cert.support.ref.neg_lower")?;
            Ok(SupportRef::NegLower {
                cert: CertId(read_index(&p[0], "closed_world.cert.support.ref.cert")?),
                atom: ground_literal_from_value(&p[1], "closed_world.cert.support.ref.atom")?,
            })
        }
        b"count_lower" => {
            let p = expect_n(payload, &[2], "closed_world.cert.support.ref.count_lower")?;
            Ok(SupportRef::CountLower {
                cert: CertId(read_index(&p[0], "closed_world.cert.support.ref.cert")?),
            })
        }
        other => Err(DecodeError::UnknownTag {
            ctx: "closed_world.cert.support.ref",
            tag: other.to_vec(),
        }),
    }
}

/// Assert a tagged-payload arity, returning the payload slice.
fn expect_n<'a>(
    payload: &'a [Value],
    accepted: &'static [usize],
    ctx: &'static str,
) -> Result<&'a [Value]> {
    // `accepted` counts the tag, as the arity a reader sees on the wire does.
    if !accepted.contains(&(payload.len() + 1)) {
        return Err(DecodeError::Arity {
            ctx,
            accepted,
            got: payload.len() + 1,
        });
    }
    Ok(payload)
}

/// Reconstruct a [`CertSizeDecl`] from `Tuple[ 6 × int ]`.
fn cert_size_decl_from_value(v: &Value) -> Result<CertSizeDecl> {
    let its = items_n(v, "closed_world.cert.limits_decl", &[6])?;
    Ok(CertSizeDecl {
        cert_facts: read_index(&its[0], "closed_world.cert.limits_decl.cert_facts")?,
        domain_values: read_index(&its[1], "closed_world.cert.limits_decl.domain_values")?,
        support_edges: read_index(&its[2], "closed_world.cert.limits_decl.support_edges")?,
        rule_groundings: read_index(&its[3], "closed_world.cert.limits_decl.rule_groundings")?,
        join_steps: read_index(&its[4], "closed_world.cert.limits_decl.join_steps")?,
        cert_bytes: read_index_u64(&its[5], "closed_world.cert.limits_decl.cert_bytes")?,
    })
}

// --------------------------------- candidate --------------------------------

pub const DERIVATION_WIRE_V1_TAG: &str = "proof-interchange/derivation/v1";

/// Reads a derivation as the public v1 payload.
pub fn derivation_wire_payload_v1_to_value(deriv: &Derivation) -> Value {
    derivation_as_value(deriv)
}

/// Decodes the public v1 derivation payload.
pub fn derivation_wire_payload_v1_from_value(value: &Value) -> Result<Derivation> {
    derivation_from_value(value)
}

/// Wraps a derivation payload with the proof-interchange v1 tag.
pub fn derivation_wire_v1_to_value(deriv: &Derivation) -> Value {
    Value::tuple([
        Value::atom(DERIVATION_WIRE_V1_TAG.as_bytes()),
        derivation_as_value(deriv),
    ])
}

/// Unwraps a proof-interchange v1 tagged derivation payload.
pub fn derivation_wire_v1_from_value(value: &Value) -> Result<Derivation> {
    let items = items_n(value, "derivation wire v1", &[2])?;
    let tag = atom_bytes(&items[0], "derivation wire v1 tag")?;
    if tag != DERIVATION_WIRE_V1_TAG.as_bytes() {
        return Err(DecodeError::UnknownTag {
            ctx: "derivation wire v1",
            tag: tag.to_vec(),
        });
    }
    derivation_from_value(&items[1])
}

/// Encodes the public proof-interchange v1 wrapper as ontos-codec bytes.
pub fn encode_derivation_wire_v1(deriv: &Derivation) -> Vec<u8> {
    ontos_codec::encode(&derivation_wire_v1_to_value(deriv))
}

/// Decodes ontos-codec bytes as a public proof-interchange v1 derivation.
/// For bytes the caller trusts. Bytes it did not produce go through
/// [`decode_derivation_wire_v1_bounded`](crate::decode_derivation_wire_v1_bounded), which holds
/// every certificate to the caller's `CheckLimits` before decoding (#2561). A codec stop on the
/// caller's bytes is [`DecodeError::CodecFault`], a fault, never a shape refusal (checker SPI v2).
pub fn decode_derivation_wire_v1(bytes: &[u8]) -> Result<Derivation> {
    let value = ontos_codec::decode(bytes).map_err(|error| DecodeError::CodecFault {
        ctx: "derivation wire v1 bytes",
        error,
    })?;
    derivation_wire_v1_from_value(&value)
}

#[cfg(test)]
mod platform_domain_2682 {
    use super::*;

    /// The ASCII half of [`render_tag`] is Rust's `{:?}` exactly, byte for byte, so every row
    /// pinned before #2682 keeps its text. Checked over ALL 128 ASCII bytes, not a sample.
    #[test]
    fn render_tag_matches_debug_for_every_ascii_byte() {
        for b in 0u8..0x80 {
            let debug = format!("{:?}", char::from(b).to_string());
            assert_eq!(render_tag(&[b]), debug, "byte {b:#04x}");
        }
    }

    /// Each byte `>= 0x80` renders `\x{hh}`, with no UTF-8 decoding: a BOM is three bytes, not
    /// U+FEFF, and a lone 0xFF is not U+FFFD.
    #[test]
    fn render_tag_escapes_every_non_ascii_byte() {
        assert_eq!(
            render_tag(b"\xEF\xBB\xBFrule"),
            r#""\x{ef}\x{bb}\x{bf}rule""#
        );
        assert_eq!(render_tag(b"\xFF"), r#""\x{ff}""#);
        for b in 0x80u8..=0xff {
            assert_eq!(render_tag(&[b]), format!("\"\\x{{{b:02x}}}\""));
        }
    }
}

/// Checker SPI v2, ADR 0036 D8 change 4 (#3111; #2734 ruling C): the trusted decoder's codec stop is
/// its own FAULT arm, carrying the codec's error, and a decoded value of the wrong shape is still the
/// shape refusal. The go and ts twins pin the same text.
#[cfg(test)]
mod trusted_codec_fault_3111 {
    use super::*;

    #[test]
    fn a_codec_stop_on_trusted_bytes_is_a_codec_fault_not_a_shape_3111() {
        let err = decode_derivation_wire_v1(&[]).expect_err("empty bytes are not a value");
        let DecodeError::CodecFault { ctx, error } = &err else {
            panic!("expected the codec fault arm, got {err:?}");
        };
        assert_eq!(*ctx, "derivation wire v1 bytes");
        assert_eq!(error.code(), "unexpected_eof");
        assert_eq!(
            err.to_string(),
            "decode derivation wire v1 bytes: codec fault: unexpected_eof"
        );
        assert!(
            std::error::Error::source(&err).is_some(),
            "the codec error is the source"
        );
    }

    #[test]
    fn a_value_of_the_wrong_shape_is_still_a_shape_refusal_3111() {
        // CONTROL: the bytes ARE a value (an atom), so the codec did not stop; the wire reading
        // refuses it, and that is not the fault arm.
        let bytes = ontos_codec::encode(&Value::atom(*b"not-a-wire"));
        let err = decode_derivation_wire_v1(&bytes).expect_err("an atom is not a wire");
        assert!(
            !matches!(err, DecodeError::CodecFault { .. }),
            "a decoded value is never a codec fault: {err:?}"
        );
    }
}
