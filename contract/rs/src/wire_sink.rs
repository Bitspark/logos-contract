//! #2602 (`seat:caa`'s lever A): a closed-model certificate's canonical wire SHAPE, written ONCE
//! as a pre-order walk over a [`WireSink`], with more than one reading. [`ValueSink`] builds the
//! ontos [`Value`] that [`closed_model_cert_as_value`](crate::closed_model_cert_as_value) returns,
//! byte for byte. [`LenSink`] counts the bytes of that value's canonical encoding without building
//! anything. The walk emits each node before its children, in encoding order, so a sink that
//! streams the bytes themselves (#2604's hashing sink) is a third reading of the same shape.
//!
//! Why: [`cert_encoded_bytes`](crate::cert_encoded_bytes), the measure behind `max_cert_bytes`
//! (#2524), built the whole value tree and then its encoded buffer only to count the bytes. massif
//! put that transient at 41% of a certified-set run's peak heap (#2602). Measured through
//! [`LenSink`], the checker's budget check refuses an oversized certificate in bounded memory.
//!
//! What the length sink RESTATES, and why that is safe:
//! - the ontos codec's two framing rules, `Atom = 0x00 ‖ uvarint(len) ‖ bytes` and
//!   `Tuple = 0x01 ‖ uvarint(arity) ‖ children` (frozen in `ontos-codec`);
//! - the frozen `quote` reading's cases (`reify.rs`): an atom `b` becomes
//!   `Tuple[Atom([0x00]), Atom(b)]`, a variable `Tuple[Atom([0x02]), Atom(name)]`, and a tuple
//!   `Tuple[Atom([0x01]), Tuple[quote(child)…]]`.
//!
//! Both are frozen formats, and every rule is pinned against `ontos_codec::encode(..).len()` by the
//! tests below, including the uvarint width boundaries. In debug builds `cert_encoded_bytes` also
//! re-derives every measured certificate the old way and asserts the two agree.
//!
//! Recursion: the length functions recurse once per nesting level of the value they measure. That
//! is no deeper than `ontos_codec::encode`, which the old path ran over the QUOTED tree, twice as
//! deep.

use crate::{
    quote, CertSizeDecl, ClosedModelCert, FiniteDomain, GroundLiteral, RelationTable,
    StratumPrefix, Subst, SupportEdge, SupportRef, Symbol, Term,
};
use ontos_core::Value;
use std::cmp::Ordering;

/// One reading of the wire shape, fed in pre-order: every node before its children.
pub(crate) trait WireSink {
    /// Whether the walk must emit a sorted map's entries in codec order (§0.3.3).
    ///
    /// `false` is legal ONLY for a reading whose result does not depend on the order of those
    /// entries, which today means [`LenSink`]: a length is a sum. Any reading of the bytes or of
    /// the value, including #2604's hashing sink, MUST leave it `true`; a sink that skipped the
    /// sort would emit a different encoding, and the codec-order row (keys `Z` and `AB`) reds it.
    const ORDERED: bool = true;
    /// `Atom(bytes)`.
    fn atom(&mut self, bytes: &[u8]);
    /// An `Atom` of `len` bytes that only a reading of the bytes needs to see.
    fn atom_with(&mut self, len: usize, bytes: impl FnOnce() -> Vec<u8>);
    /// Opens `Tuple` of `arity` children; exactly `arity` nodes follow, then [`tuple_end`](Self::tuple_end).
    fn tuple_begin(&mut self, arity: usize);
    /// Closes the innermost open tuple.
    fn tuple_end(&mut self);
    /// An ontos value carried verbatim.
    fn value(&mut self, v: &Value);
    /// A ground value through the frozen `quote` reading.
    fn quoted_value(&mut self, v: &Value);
    /// A term through the frozen `quote` reading.
    fn quoted_term(&mut self, t: &Term);
    /// A `u64` as the `ontos-data` `int` embedding.
    fn int(&mut self, n: u64);
}

/// `Tuple` of `arity` children, the ones `children` emits.
fn tuple<S: WireSink>(s: &mut S, arity: usize, children: impl FnOnce(&mut S)) {
    s.tuple_begin(arity);
    children(s);
    s.tuple_end();
}

/// The value reading: exactly the tree `closed_model_cert_as_value` has always built.
pub(crate) struct ValueSink {
    /// The open tuples' children so far, innermost last; the bottom frame holds the result.
    frames: Vec<Vec<Value>>,
}

impl ValueSink {
    /// The value `emit` walks.
    pub(crate) fn build(emit: impl FnOnce(&mut ValueSink)) -> Value {
        let mut sink = ValueSink {
            frames: vec![Vec::with_capacity(1)],
        };
        emit(&mut sink);
        let mut root = sink.frames.pop().expect("the result frame");
        assert!(sink.frames.is_empty(), "every tuple is closed");
        assert_eq!(root.len(), 1, "a walk emits one value");
        root.pop().expect("one value")
    }

    fn push(&mut self, v: Value) {
        self.frames.last_mut().expect("an open frame").push(v);
    }
}

impl WireSink for ValueSink {
    fn atom(&mut self, bytes: &[u8]) {
        self.push(Value::atom(bytes.to_vec()));
    }
    fn atom_with(&mut self, _len: usize, bytes: impl FnOnce() -> Vec<u8>) {
        self.push(Value::atom(bytes()));
    }
    fn tuple_begin(&mut self, arity: usize) {
        self.frames.push(Vec::with_capacity(arity));
    }
    fn tuple_end(&mut self) {
        let items = self.frames.pop().expect("an open tuple");
        self.push(Value::tuple(items));
    }
    fn value(&mut self, v: &Value) {
        self.push(v.clone());
    }
    fn quoted_value(&mut self, v: &Value) {
        self.push(quote(&Term::from_value(v)));
    }
    fn quoted_term(&mut self, t: &Term) {
        self.push(quote(t));
    }
    fn int(&mut self, n: u64) {
        self.push(ontos_data::encode_int(i128::from(n)));
    }
}

/// The length reading: the canonical encoding's byte count, with no tree and no buffer.
#[derive(Default)]
pub(crate) struct LenSink {
    total: u64,
}

impl LenSink {
    /// The encoded length of the value `emit` walks.
    pub(crate) fn measure(emit: impl FnOnce(&mut LenSink)) -> u64 {
        let mut sink = LenSink::default();
        emit(&mut sink);
        sink.total
    }
}

/// `uvarint(n)`'s bytes, shortest-form LEB128, into a stack buffer: `(buffer, width)`.
fn uvarint_bytes(mut n: u64) -> ([u8; 10], usize) {
    let mut out = [0_u8; 10];
    let mut width = 0;
    loop {
        let byte = (n & 0x7f) as u8;
        n >>= 7;
        out[width] = if n == 0 { byte } else { byte | 0x80 };
        width += 1;
        if n == 0 {
            return (out, width);
        }
    }
}

/// The width of `n` as a shortest-form LEB128 uvarint.
fn uvarint_len(n: u64) -> u64 {
    let bits = u64::from(64 - n.leading_zeros());
    bits.div_ceil(7).max(1)
}

/// `Atom` of `n` bytes: tag, length, bytes.
fn atom_len(n: usize) -> u64 {
    1 + uvarint_len(n as u64) + n as u64
}

/// `Tuple` of `arity` children whose encodings sum to `children`: tag, arity, children.
fn tuple_len(arity: usize, children: u64) -> u64 {
    1 + uvarint_len(arity as u64) + children
}

/// A quote node's one-byte tag atom.
const QUOTE_TAG: u64 = 3;

/// The encoded length of `v`, without encoding it.
pub(crate) fn encoded_len(v: &Value) -> u64 {
    match v {
        Value::Atom(atom) => atom_len(atom.bytes().len()),
        Value::Tuple(tuple) => tuple_len(tuple.len(), tuple.items().iter().map(encoded_len).sum()),
    }
}

/// The encoded length of `quote(&Term::from_value(v))`, without building either.
fn quoted_len(v: &Value) -> u64 {
    let payload = match v {
        Value::Atom(atom) => atom_len(atom.bytes().len()),
        Value::Tuple(tuple) => tuple_len(tuple.len(), tuple.items().iter().map(quoted_len).sum()),
    };
    tuple_len(2, QUOTE_TAG + payload)
}

/// The encoded length of `quote(t)`, without building it.
fn quoted_term_len(t: &Term) -> u64 {
    let payload = match t {
        Term::Atom(bytes) => atom_len(bytes.len()),
        Term::Var(id) => atom_len(id.as_str().len()),
        Term::Tuple(children) => {
            tuple_len(children.len(), children.iter().map(quoted_term_len).sum())
        }
    };
    tuple_len(2, QUOTE_TAG + payload)
}

impl WireSink for LenSink {
    const ORDERED: bool = false;
    fn atom(&mut self, bytes: &[u8]) {
        self.total += atom_len(bytes.len());
    }
    fn atom_with(&mut self, len: usize, _bytes: impl FnOnce() -> Vec<u8>) {
        self.total += atom_len(len);
    }
    fn tuple_begin(&mut self, arity: usize) {
        self.total += 1 + uvarint_len(arity as u64);
    }
    fn tuple_end(&mut self) {}
    fn value(&mut self, v: &Value) {
        self.total += encoded_len(v);
    }
    fn quoted_value(&mut self, v: &Value) {
        self.total += quoted_len(v);
    }
    fn quoted_term(&mut self, t: &Term) {
        self.total += quoted_term_len(t);
    }
    fn int(&mut self, n: u64) {
        // The `int` embedding is ontos-data's to define; measuring its (three-node) value keeps
        // that definition in one place, at a constant transient per integer.
        self.total += encoded_len(&ontos_data::encode_int(i128::from(n)));
    }
}

/// The byte reading (#2604): the canonical encoding ITSELF, fed to `out` in encoding order, with
/// no tree and no buffer. With `out` feeding SHA-256 it is #2604's hashing sink; with `out`
/// extending a buffer it produces the bytes `ontos_codec::encode` would. It restates the codec's
/// two framing rules and the frozen `quote` shapes exactly as [`LenSink`] does, and its rows pin
/// every node kind against `ontos_codec::encode` of the [`ValueSink`] reading.
pub(crate) struct BytesSink<F: FnMut(&[u8])> {
    out: F,
}

impl<F: FnMut(&[u8])> BytesSink<F> {
    pub(crate) fn new(out: F) -> Self {
        BytesSink { out }
    }

    /// A node's header: its tag byte, then `uvarint(n)` (a length or an arity).
    fn header(&mut self, tag: u8, n: usize) {
        let (buf, width) = uvarint_bytes(n as u64);
        (self.out)(&[tag]);
        (self.out)(&buf[..width]);
    }

    fn stream_value(&mut self, v: &Value) {
        match v {
            Value::Atom(atom) => self.atom(atom.bytes()),
            Value::Tuple(tuple) => {
                self.tuple_begin(tuple.len());
                for child in tuple.items() {
                    self.stream_value(child);
                }
            }
        }
    }

    /// A `quote` node: `Tuple[Atom([tag]), payload]`.
    fn quote_node(&mut self, tag: u8, payload: impl FnOnce(&mut Self)) {
        self.tuple_begin(2);
        self.atom(&[tag]);
        payload(self);
    }

    fn stream_quoted_value(&mut self, v: &Value) {
        match v {
            Value::Atom(atom) => self.quote_node(0x00, |s| s.atom(atom.bytes())),
            Value::Tuple(tuple) => self.quote_node(0x01, |s| {
                s.tuple_begin(tuple.len());
                for child in tuple.items() {
                    s.stream_quoted_value(child);
                }
            }),
        }
    }

    fn stream_quoted_term(&mut self, t: &Term) {
        match t {
            Term::Atom(bytes) => self.quote_node(0x00, |s| s.atom(bytes)),
            Term::Var(id) => self.quote_node(0x02, |s| s.atom(id.as_str().as_bytes())),
            Term::Tuple(children) => self.quote_node(0x01, |s| {
                s.tuple_begin(children.len());
                for child in children {
                    s.stream_quoted_term(child);
                }
            }),
        }
    }
}

impl<F: FnMut(&[u8])> WireSink for BytesSink<F> {
    fn atom(&mut self, bytes: &[u8]) {
        self.header(0x00, bytes.len());
        (self.out)(bytes);
    }
    fn atom_with(&mut self, _len: usize, bytes: impl FnOnce() -> Vec<u8>) {
        let bytes = bytes();
        self.atom(&bytes);
    }
    fn tuple_begin(&mut self, arity: usize) {
        self.header(0x01, arity);
    }
    fn tuple_end(&mut self) {}
    fn value(&mut self, v: &Value) {
        self.stream_value(v);
    }
    fn quoted_value(&mut self, v: &Value) {
        self.stream_quoted_value(v);
    }
    fn quoted_term(&mut self, t: &Term) {
        self.stream_quoted_term(t);
    }
    fn int(&mut self, n: u64) {
        // As `LenSink`: the `int` embedding is ontos-data's to define.
        self.stream_value(&ontos_data::encode_int(i128::from(n)));
    }
}

/// A certificate's canonical encoding, the bytes `ontos_codec::encode(closed_model_cert_as_value
/// (cert))` produces, fed to `out` in order without building the value (#2604). A caller hashes
/// them as they arrive, or keeps them: the CLI's v3 stream does both in one pass, once per
/// certificate, so no answer materializes a certificate.
pub fn closed_model_cert_write(cert: &ClosedModelCert, out: impl FnMut(&[u8])) {
    closed_model_cert(&mut BytesSink::new(out), cert, &cert.limits_decl);
}

/// The codec order of two atoms (§0.3.3's sorted-map order), without encoding them: `0x00`,
/// then `uvarint(len)`, then the bytes. LEB128 is prefix-free, so comparing the length prefixes
/// first and the bytes second is the order of the whole encodings.
fn atom_codec_cmp(a: &[u8], b: &[u8]) -> Ordering {
    let ((la, wa), (lb, wb)) = (uvarint_bytes(a.len() as u64), uvarint_bytes(b.len() as u64));
    la[..wa].cmp(&lb[..wb]).then_with(|| a.cmp(b))
}

// ------------------------------ the shape, once ------------------------------

/// A predicate [`Symbol`] as a bare `Atom(bytes)`.
pub(crate) fn symbol<S: WireSink>(s: &mut S, sym: &Symbol) {
    s.atom(sym.bytes());
}

/// A 32-byte digest as its lowercase-hex `Atom`.
pub(crate) fn digest<S: WireSink>(s: &mut S, d: &[u8; 32]) {
    s.atom_with(64, || crate::derivation_wire::to_hex(d).into_bytes());
}

/// A ground literal `p(a…)` as `Tuple[Atom(p), quote(a)…]`.
pub(crate) fn ground_literal<S: WireSink>(s: &mut S, lit: &GroundLiteral) {
    tuple(s, 1 + lit.args.len(), |s| {
        symbol(s, &lit.pred);
        for arg in &lit.args {
            s.quoted_value(arg);
        }
    });
}

/// A [`Subst`] as `Tuple[Tuple[Atom(var), quote(term)], …]`, sorted by the key's codec bytes
/// (§0.3.3), which is NOT the map's own order: `Z` precedes `AB`.
pub(crate) fn subst<S: WireSink>(s: &mut S, subst: &Subst) {
    let entry = |s: &mut S, var: &crate::VarId, term: &Term| {
        tuple(s, 2, |s| {
            s.atom(var.as_str().as_bytes());
            s.quoted_term(term);
        });
    };
    tuple(s, subst.len(), |s| {
        if S::ORDERED {
            let mut entries: Vec<_> = subst.iter().collect();
            entries
                .sort_by(|a, b| atom_codec_cmp(a.0.as_str().as_bytes(), b.0.as_str().as_bytes()));
            for (var, term) in entries {
                entry(s, var, term);
            }
        } else {
            for (var, term) in subst {
                entry(s, var, term);
            }
        }
    });
}

/// A closed-model certificate with `decl` in its size-declaration slot.
///
/// ADR 0029 D10: `decomposition_witness` is an 11th TRAILING-OPTIONAL element, present only when
/// the cert is slice-sealed, so a cert that seals the complete program encodes to the same
/// TEN-element tuple it always did. ADR 0030 D4: `partial_scope` is the 12th; a partial cert with
/// no slice-seal pin carries the `opt` none marker `Tuple[Atom("none")]` at the 11th slot, never a
/// digest.
pub(crate) fn closed_model_cert<S: WireSink>(
    s: &mut S,
    cert: &ClosedModelCert,
    decl: &CertSizeDecl,
) {
    let trailing = match (cert.decomposition_witness, &cert.partial_scope) {
        (None, None) => 0,
        (Some(_), None) => 1,
        (_, Some(_)) => 2,
    };
    tuple(s, 10 + trailing, |s| {
        stratum_prefix(s, &cert.scope);
        digest(s, &cert.program_hash);
        digest(s, &cert.profile_hash);
        digest(s, &cert.ctx_hash);
        digest(s, &cert.theory_config_hash);
        tuple(s, cert.edb_snapshot_hashes.len(), |s| {
            for h in &cert.edb_snapshot_hashes {
                digest(s, h);
            }
        });
        tuple(s, cert.domains.len(), |s| {
            for d in &cert.domains {
                finite_domain(s, d);
            }
        });
        relation_tables(s, &cert.extensions);
        tuple(s, cert.supports.0.len(), |s| {
            for e in &cert.supports.0 {
                support_edge(s, e);
            }
        });
        cert_size_decl(s, decl);
        match (cert.decomposition_witness, &cert.partial_scope) {
            (None, None) => {}
            (Some(w), None) => digest(s, &w),
            (w, Some(p)) => {
                match w {
                    Some(w) => digest(s, &w),
                    None => tuple(s, 1, |s| s.atom(b"none")),
                }
                stratum_prefix(s, p);
            }
        }
    });
}

/// A [`StratumPrefix`] as `Tuple[ int(level), Tuple[Atom(pred), …] ]`.
fn stratum_prefix<S: WireSink>(s: &mut S, scope: &StratumPrefix) {
    tuple(s, 2, |s| {
        s.int(u64::from(scope.level));
        tuple(s, scope.predicates.len(), |s| {
            for p in &scope.predicates {
                symbol(s, p);
            }
        });
    });
}

/// A [`FiniteDomain`] as `Tuple[ Atom(type_tag), Tuple[value, …] ]`, the values verbatim.
fn finite_domain<S: WireSink>(s: &mut S, domain: &FiniteDomain) {
    tuple(s, 2, |s| {
        symbol(s, &domain.type_tag);
        tuple(s, domain.values.len(), |s| {
            for v in &domain.values {
                s.value(v);
            }
        });
    });
}

/// The certificate's extension tables as `Tuple[table, …]`.
pub(crate) fn relation_tables<S: WireSink>(s: &mut S, tables: &[RelationTable]) {
    tuple(s, tables.len(), |s| {
        for t in tables {
            relation_table(s, t);
        }
    });
}

/// A [`RelationTable`] as `Tuple[ Atom(pred), int(arity), Tuple[ground_literal, …] ]`.
fn relation_table<S: WireSink>(s: &mut S, table: &RelationTable) {
    tuple(s, 3, |s| {
        symbol(s, &table.pred);
        s.int(u64::from(table.arity));
        tuple(s, table.rows.len(), |s| {
            for row in &table.rows {
                ground_literal(s, row);
            }
        });
    });
}

/// A [`SupportEdge`] as `Tuple[ fact, Atom(clause_id), subst, Tuple[ref, …], int(rank) ]`.
fn support_edge<S: WireSink>(s: &mut S, edge: &SupportEdge) {
    tuple(s, 5, |s| {
        ground_literal(s, &edge.fact);
        s.atom(edge.clause.as_str().as_bytes());
        subst(s, &edge.subst);
        tuple(s, edge.body_refs.len(), |s| {
            for r in &edge.body_refs {
                support_ref(s, r);
            }
        });
        s.int(u64::from(edge.rank));
    });
}

/// A [`SupportRef`] as a tagged tuple `Tuple[Atom(tag), payload…]` (one tag per the 5 variants).
fn support_ref<S: WireSink>(s: &mut S, reference: &SupportRef) {
    match reference {
        SupportRef::SameStratum { fact, rank } => tuple(s, 3, |s| {
            s.atom(b"same_stratum");
            ground_literal(s, fact);
            s.int(u64::from(*rank));
        }),
        SupportRef::LowerStratum { cert, atom } => tuple(s, 3, |s| {
            s.atom(b"lower_stratum");
            s.int(cert.index());
            ground_literal(s, atom);
        }),
        SupportRef::Builtin { atom } => tuple(s, 2, |s| {
            s.atom(b"builtin");
            ground_literal(s, atom);
        }),
        SupportRef::NegLower { cert, atom } => tuple(s, 3, |s| {
            s.atom(b"neg_lower");
            s.int(cert.index());
            ground_literal(s, atom);
        }),
        // #2258 L3.3b: additive on the wire, a fifth tag.
        SupportRef::CountLower { cert } => tuple(s, 2, |s| {
            s.atom(b"count_lower");
            s.int(cert.index());
        }),
    }
}

/// A [`CertSizeDecl`] as `Tuple[ 6 × int ]` in field-declaration order.
fn cert_size_decl<S: WireSink>(s: &mut S, decl: &CertSizeDecl) {
    tuple(s, 6, |s| {
        s.int(decl.cert_facts);
        s.int(decl.domain_values);
        s.int(decl.support_edges);
        s.int(decl.rule_groundings);
        s.int(decl.join_steps);
        s.int(decl.cert_bytes);
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VarId;

    fn atom_of(n: usize) -> Value {
        Value::atom(vec![b'x'; n])
    }

    fn tuple_of(arity: usize) -> Value {
        Value::tuple((0..arity).map(|i| Value::atom(vec![(i % 251) as u8])))
    }

    fn len_of(v: &Value) -> u64 {
        ontos_codec::encode(v).len() as u64
    }

    fn assert_lengths(v: &Value, what: &str) {
        assert_eq!(encoded_len(v), len_of(v), "{what}: encoded_len");
        assert_eq!(
            LenSink::measure(|s| s.value(v)),
            len_of(v),
            "{what}: the value node"
        );
        let quoted = quote(&Term::from_value(v));
        assert_eq!(quoted_len(v), len_of(&quoted), "{what}: quoted_len");
        assert_eq!(
            LenSink::measure(|s| s.quoted_value(v)),
            len_of(&ValueSink::build(|s| s.quoted_value(v))),
            "{what}: the two sinks' quoted readings"
        );
    }

    /// `seat:caa`'s condition (2): the uvarint width boundaries, for atom lengths and tuple arities.
    #[test]
    fn the_length_sink_is_exact_at_every_uvarint_boundary_2602() {
        for n in [0, 1, 127, 128, 16383, 16384] {
            assert_lengths(&atom_of(n), &format!("atom of {n} bytes"));
            let bytes = vec![b'y'; n];
            assert_eq!(
                LenSink::measure(|s| s.atom(&bytes)),
                len_of(&ValueSink::build(|s| s.atom(&bytes))),
                "an atom node of {n} bytes"
            );
        }
        for arity in [0, 1, 127, 128] {
            assert_lengths(&tuple_of(arity), &format!("tuple of arity {arity}"));
            let emit = |s: &mut LenSink| {
                tuple(s, arity, |s| {
                    (0..arity).for_each(|i| s.atom(&[(i % 251) as u8]))
                })
            };
            assert_eq!(
                LenSink::measure(emit),
                len_of(&tuple_of(arity)),
                "a tuple node of arity {arity}"
            );
        }
        // The widths themselves, against the codec's own encoder.
        for n in [
            0_u64,
            127,
            128,
            16383,
            16384,
            2_097_151,
            2_097_152,
            u64::MAX,
        ] {
            let mut out = Vec::new();
            ontos_codec::encode_uvarint(n, &mut out);
            assert_eq!(uvarint_len(n), out.len() as u64, "uvarint width of {n}");
            let (buf, width) = uvarint_bytes(n);
            assert_eq!(&buf[..width], out.as_slice(), "uvarint bytes of {n}");
        }
    }

    /// `seat:caa`'s condition (1): every embedded value kind, nested, through both readings.
    #[test]
    fn the_length_sink_covers_every_value_kind_nested_2602() {
        let nested = Value::tuple([
            atom_of(0),
            atom_of(200),
            Value::tuple(Vec::<Value>::new()),
            Value::tuple([atom_of(3), Value::tuple([atom_of(128), tuple_of(130)])]),
            ontos_data::encode_int(-5),
            ontos_data::encode_int(i128::from(u64::MAX)),
        ]);
        assert_lengths(&nested, "a nested value of every kind");
        let term = Term::Tuple(vec![
            Term::Atom(b"a".to_vec()),
            Term::Var(VarId::new("X")),
            Term::Tuple(vec![
                Term::Var(VarId::new("a_longer_name")),
                Term::Atom(vec![7; 130]),
            ]),
        ]);
        assert_eq!(
            LenSink::measure(|s| s.quoted_term(&term)),
            len_of(&quote(&term)),
            "a term with variables"
        );
        for n in [0_u64, 1, 127, 128, 255, 256, 65_535, 65_536, u64::MAX] {
            assert_eq!(
                LenSink::measure(|s| s.int(n)),
                len_of(&ValueSink::build(|s| s.int(n))),
                "int {n}"
            );
        }
    }

    /// A byte reading into a caller's buffer.
    type ByteSink<'a> = BytesSink<&'a mut dyn FnMut(&[u8])>;

    /// The byte reading of whatever `emit` walks.
    fn bytes_of(emit: impl FnOnce(&mut ByteSink<'_>)) -> Vec<u8> {
        let mut out = Vec::new();
        let mut push = |b: &[u8]| out.extend_from_slice(b);
        let mut sink: ByteSink<'_> = BytesSink::new(&mut push);
        emit(&mut sink);
        out
    }

    /// #2604: the byte reading IS `ontos_codec::encode` of the value reading, on every node kind:
    /// atoms at the uvarint width boundaries, nested tuples, ints, a quoted value, a quoted term
    /// with variables, and a substitution whose codec order is not its map order.
    #[test]
    fn the_byte_reading_is_the_encoding_of_the_value_reading_2604() {
        let nested = Value::tuple([
            atom_of(0),
            atom_of(127),
            atom_of(128),
            Value::tuple(Vec::<Value>::new()),
            Value::tuple([atom_of(3), Value::tuple([atom_of(200), tuple_of(130)])]),
            ontos_data::encode_int(i128::from(u64::MAX)),
        ]);
        assert_eq!(
            bytes_of(|s| s.value(&nested)),
            ontos_codec::encode(&nested),
            "a nested value"
        );
        assert_eq!(
            bytes_of(|s| s.quoted_value(&nested)),
            ontos_codec::encode(&ValueSink::build(|s| s.quoted_value(&nested))),
            "a quoted value"
        );
        let term = Term::Tuple(vec![
            Term::Atom(b"a".to_vec()),
            Term::Var(VarId::new("X")),
            Term::Tuple(vec![
                Term::Var(VarId::new("a_longer_name")),
                Term::Atom(vec![7; 130]),
            ]),
        ]);
        assert_eq!(
            bytes_of(|s| s.quoted_term(&term)),
            ontos_codec::encode(&quote(&term)),
            "a term with variables"
        );
        for n in [0_u64, 1, 127, 128, 65_536, u64::MAX] {
            assert_eq!(
                bytes_of(|s| s.int(n)),
                ontos_codec::encode(&ValueSink::build(|s| s.int(n))),
                "int {n}"
            );
        }
        let mut sub = Subst::new();
        for (var, val) in [("AB", "1"), ("Z", "2")] {
            sub.insert(VarId::new(var), Term::Atom(val.as_bytes().to_vec()));
        }
        assert_eq!(
            bytes_of(|s| subst(s, &sub)),
            ontos_codec::encode(&ValueSink::build(|s| subst(s, &sub))),
            "a substitution in codec order (Z before AB)"
        );
    }

    /// A substitution in codec order, which is not the map's: `Z` sorts before `AB`, and the value
    /// reading must reproduce `sorted_map`'s order exactly.
    #[test]
    fn a_substitution_is_in_codec_order_not_map_order_2602() {
        let mut sub = Subst::new();
        for (var, val) in [("AB", "1"), ("Z", "2"), ("B", "3"), ("A_LONGER", "4")] {
            sub.insert(VarId::new(var), Term::Atom(val.as_bytes().to_vec()));
        }
        let old = crate::derivation_wire::sorted_map(
            sub.iter()
                .map(|(var, term)| (Value::atom(var.as_str().as_bytes().to_vec()), quote(term))),
        );
        let new = ValueSink::build(|s| subst(s, &sub));
        assert_eq!(new, old, "the substitution's value");
        assert_eq!(
            LenSink::measure(|s| subst(s, &sub)),
            len_of(&old),
            "its length"
        );
        assert_eq!(
            atom_codec_cmp(b"Z", b"AB"),
            Ordering::Less,
            "control: a shorter key precedes, whatever its bytes"
        );
    }
}
