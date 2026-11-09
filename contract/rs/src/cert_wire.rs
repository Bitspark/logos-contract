//! #2528 (`seat:caa`'s ruling (a)): the byte spans of the certificates inside an encoded frame,
//! read WITHOUT decoding it, so a host can refuse a certificate wire longer than its budget before
//! it materialises a single value. The checker's measure (#2524) bounds what a DECODED
//! certificate may declare and be; only this bounds what an adversary makes a host READ.
//!
//! The ontos codec stores no per-element length: a tuple is `0x01 || uvarint(arity) || items` and
//! an atom `0x00 || uvarint(len) || bytes`. So a span is found by walking tags and uvarints. Skipping
//! is iterative (a count of values still to skip, so a frame's nesting sets no recursion depth);
//! the walk recurses only along the host's own path steps. It allocates only its output, and
//! rejects a non-canonical or overflowing uvarint exactly as the codec's decoder does. go
//! (`CertWireSpans`, `CertWireSpansAt`) and ts (`certWireSpans`, `certWireSpansAt`) mirror it,
//! pinned by the generated `vectors/cert_wire_spans.json`.
//!
//! **Soundness** of refusing on a span: for a certificate the decoder accepts, the encoding is
//! canonical (the decoders refuse a non-canonical table, domain or scope), so its literal span is
//! its measure ([`cert_encoded_bytes`](crate::cert_encoded_bytes), the encoding with `cert_bytes`
//! zeroed) plus the declaration's own width above that of `0`, which is at most
//! [`cert_bytes_slack`]. So a span over `max_cert_bytes + slack` means a measure over
//! `max_cert_bytes`, which the checker refuses whatever the certificate declares.

use crate::check::{CheckLimitError, CheckLimits, ProofBudgetCount};
use crate::derivation_wire::{derivation_wire_v1_from_value, u64_atom, DecodeError, INDEX_MAX};
use crate::Derivation;

/// Why a requested walk could not proceed: invalid configuration or unreadable frame.
/// No variant is a verdict about a certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertWireError {
    /// A selector index is outside the portable index domain.
    InvalidPath,
    /// The frame ends inside a value.
    Truncated,
    /// A tag byte that is neither an atom (`0x00`) nor a tuple (`0x01`).
    UnknownTag,
    /// A uvarint that is not the shortest form, the codec's `non_canonical_uvarint`.
    NonCanonicalUvarint,
    /// A uvarint whose value is at least 2^64, the codec's `uvarint_overflow`.
    UvarintOverflow,
    /// The path crosses an atom where a tuple is required.
    NotATuple,
    /// Bytes follow the frame's one value, the codec's trailing-bytes refusal.
    TrailingBytes,
}

impl CertWireError {
    /// The stable name every core reports, pinned by the shared vector.
    pub fn name(self) -> &'static str {
        match self {
            CertWireError::InvalidPath => "invalid_path",
            CertWireError::Truncated => "truncated",
            CertWireError::UnknownTag => "unknown_tag",
            CertWireError::NonCanonicalUvarint => "non_canonical_uvarint",
            CertWireError::UvarintOverflow => "uvarint_overflow",
            CertWireError::NotATuple => "not_a_tuple",
            CertWireError::TrailingBytes => "trailing_bytes",
        }
    }
}

impl std::fmt::Display for CertWireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

impl std::error::Error for CertWireError {}

const TAG_ATOM: u8 = 0x00;
const TAG_TUPLE: u8 = 0x01;

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl Cursor<'_> {
    fn remaining(&self) -> u64 {
        (self.bytes.len() - self.pos) as u64
    }

    fn byte(&mut self) -> Result<u8, CertWireError> {
        let b = *self.bytes.get(self.pos).ok_or(CertWireError::Truncated)?;
        self.pos += 1;
        Ok(b)
    }

    /// One shortest-form LEB128 uvarint over the u64 domain, checked in the codec's order:
    /// overflow while reading, canonicality after.
    fn uvarint(&mut self) -> Result<u64, CertWireError> {
        let start = self.pos;
        let mut value: u64 = 0;
        let mut shift: u32 = 0;
        loop {
            let b = self.byte()?;
            if shift >= 64 || (shift == 63 && (b & 0x7f) > 1) {
                return Err(CertWireError::UvarintOverflow);
            }
            value |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        // Shortest form: the final byte carries payload, unless the value is a single 0x00.
        if self.pos - start > 1 && self.bytes[self.pos - 1] == 0 {
            return Err(CertWireError::NonCanonicalUvarint);
        }
        Ok(value)
    }

    /// A value's tag and its uvarint (an atom's length or a tuple's arity), bounded by the bytes
    /// left: every value takes at least two bytes, so an arity above half of them cannot be met.
    fn header(&mut self) -> Result<(u8, u64), CertWireError> {
        let tag = self.byte()?;
        if tag != TAG_ATOM && tag != TAG_TUPLE {
            return Err(CertWireError::UnknownTag);
        }
        let n = self.uvarint()?;
        let bound = if tag == TAG_ATOM {
            self.remaining()
        } else {
            self.remaining() / 2
        };
        if n > bound {
            return Err(CertWireError::Truncated);
        }
        Ok((tag, n))
    }

    /// Skip one whole value without materialising it.
    fn skip(&mut self) -> Result<(), CertWireError> {
        self.skip_values(1)
    }

    /// Skip `pending` whole values without materialising them.
    fn skip_values(&mut self, mut pending: u64) -> Result<(), CertWireError> {
        while pending > 0 {
            pending -= 1;
            let (tag, n) = self.header()?;
            if tag == TAG_ATOM {
                self.pos += n as usize;
            } else {
                pending += n;
            }
        }
        Ok(())
    }
}

/// The byte span of every element of the tuple reached by following `path` from the frame's root
/// value, each step an index into the tuple at that point. A step at or past a tuple's arity means
/// the slot is ABSENT (an optional trailing element, an option's `none`): there are no
/// certificates, and the result is empty.
/// Every index must be in 0..=INDEX_MAX; malformed configuration is refused before reading the frame.
///
/// The WHOLE frame is walked, not only the path (`seat:caa`'s fail-closed condition): every sibling
/// after the target and the rest of an absent slot's tuple are skipped too, and bytes after the one
/// value are refused. So a frame this returns `Ok` for is one the codec could read in full, and a
/// host that refuses every `Err` never hands the decoder a frame its bound has not covered.
///
/// The index-only case of [`cert_wire_spans_at`], which it runs.
pub fn cert_wire_spans(frame: &[u8], path: &[u64]) -> Result<Vec<usize>, CertWireError> {
    let steps: Vec<PathStep> = path.iter().map(|&i| PathStep::Index(i)).collect();
    Ok(cert_wire_spans_at(frame, &steps)?
        .into_iter()
        .map(|c| c.span)
        .collect())
}

/// One step of a certificate path (#2561, `seat:caa`'s ruling): an index into the tuple at that
/// point, or every element of it. `Each` may appear any number of times, at any depth, so a frame
/// that carries certificates inside a list (the event door's output batch) needs no new walker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PathStep {
    /// The element at this index. One at or past the tuple's arity is an ABSENT slot (an optional
    /// trailing element, an option's `none`), with no certificates.
    Index(u64),
    /// Every element, each followed by the rest of the path.
    Each,
}

impl PathStep {
    /// An index step's coordinate, and None for every other kind of step. Go's Index
    /// reports the same distinction with a boolean. The enum is non-exhaustive, so a crate outside
    /// this one cannot match it without a wildcard; it asks here instead, and a kind added later
    /// is placed by this match (#2892, research 0025 A22).
    pub fn index(&self) -> Option<u64> {
        match self {
            PathStep::Index(i) => Some(*i),
            PathStep::Each => None,
        }
    }
}

/// One certificate [`cert_wire_spans_at`] found: its byte span, where it starts, and the concrete
/// path to it, every `Each` resolved to the element's index and the certificate's own index last, so
/// a refusal names which element carried it. `start` (#2584) lets a host read the certificate's own
/// bytes, `frame[start..start + span]`, to share a stack whose bytes an earlier frame carried.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CertSpan {
    /// The concrete path from the frame's root to the certificate.
    pub path: Vec<usize>,
    /// The certificate's byte span on the wire.
    pub span: usize,
    /// The offset in the frame at which the certificate's encoding starts.
    pub start: usize,
}

/// The byte span of every certificate the `steps` reach, with its concrete path: each path the
/// steps expand to (every `Each` over every element) leads to a tuple, and each element of that
/// tuple is a certificate. A path through an absent slot reaches none.
///
/// Fail closed exactly as [`cert_wire_spans`]: the WHOLE frame is walked and bytes after the one
/// value are refused. The walk recurses only along the steps, so its depth is the path's length,
/// which the host chooses, never the frame's nesting; skipping stays iterative.
pub fn cert_wire_spans_at(
    frame: &[u8],
    steps: &[PathStep],
) -> Result<Vec<CertSpan>, CertWireError> {
    if steps
        .iter()
        .any(|step| matches!(step, PathStep::Index(index) if *index > INDEX_MAX))
    {
        return Err(CertWireError::InvalidPath);
    }
    let mut c = Cursor {
        bytes: frame,
        pos: 0,
    };
    let mut out = Vec::new();
    let mut path = Vec::with_capacity(steps.len() + 1);
    c.spans_at(steps, &mut path, &mut out)?;
    if c.pos != frame.len() {
        return Err(CertWireError::TrailingBytes);
    }
    Ok(out)
}

/// The fail-closed walk alone (#2561): the whole frame read without decoding it, and refused by
/// the same names as [`cert_wire_spans`]. For a frame that carries no certificates, so a host
/// never hands the decoder bytes no walk has covered.
pub fn cert_wire_walk(frame: &[u8]) -> Result<(), CertWireError> {
    let mut c = Cursor {
        bytes: frame,
        pos: 0,
    };
    c.skip()?;
    if c.pos != frame.len() {
        return Err(CertWireError::TrailingBytes);
    }
    Ok(())
}

impl Cursor<'_> {
    /// Walk one whole value, following `steps` from it; `path` is the concrete path to it.
    fn spans_at(
        &mut self,
        steps: &[PathStep],
        path: &mut Vec<usize>,
        out: &mut Vec<CertSpan>,
    ) -> Result<(), CertWireError> {
        let (tag, arity) = self.header()?;
        if tag != TAG_TUPLE {
            return Err(CertWireError::NotATuple);
        }
        let Some((step, rest)) = steps.split_first() else {
            // The certificates' tuple: each element is one.
            for i in 0..arity {
                let start = self.pos;
                self.skip()?;
                path.push(i as usize);
                out.push(CertSpan {
                    path: path.clone(),
                    span: self.pos - start,
                    start,
                });
                path.pop();
            }
            return Ok(());
        };
        match *step {
            PathStep::Index(n) if n >= arity => self.skip_values(arity),
            PathStep::Index(n) => {
                self.skip_values(n)?;
                path.push(n as usize);
                self.spans_at(rest, path, out)?;
                path.pop();
                self.skip_values(arity - n - 1)
            }
            PathStep::Each => {
                for i in 0..arity {
                    path.push(i as usize);
                    self.spans_at(rest, path, out)?;
                    path.pop();
                }
                Ok(())
            }
        }
    }
}

/// The bytes of the atom that tags a frame, `Tuple[Atom(tag), ..]`, read without decoding; `None`
/// when the root is not a tuple led by an atom. A host checks it before choosing a path, so an
/// `incomplete` trailer is never walked as a completeness one.
pub fn cert_wire_tag(frame: &[u8]) -> Result<Option<&[u8]>, CertWireError> {
    let mut c = Cursor {
        bytes: frame,
        pos: 0,
    };
    let (tag, arity) = c.header()?;
    if tag != TAG_TUPLE || arity == 0 {
        return Ok(None);
    }
    let (tag, len) = c.header()?;
    if tag != TAG_ATOM {
        return Ok(None);
    }
    Ok(Some(&frame[c.pos..c.pos + len as usize]))
}

/// The most a certificate's literal span can exceed its measure: the widest encoding of the
/// declared `cert_bytes` (an `int` atom) minus the encoding of the `0` the measure writes there.
pub fn cert_bytes_slack() -> u64 {
    let width = |n: u64| ontos_codec::encode(&u64_atom(n)).len() as u64;
    width(u64::MAX) - width(0)
}

/// Whether a certificate whose wire span is `span` measures over `max_cert_bytes` for certain,
/// so a host may refuse it undecoded (see the module's soundness note).
pub fn cert_span_over_budget(span: usize, max_cert_bytes: ProofBudgetCount) -> bool {
    encoded_span_exceeds(span, max_cert_bytes.get())
}

fn encoded_span_exceeds(span: usize, max_cert_bytes: u64) -> bool {
    (span as u64).saturating_sub(max_cert_bytes) > cert_bytes_slack()
}

/// The path to a v1 derivation wire's certificates: the tagged payload, then the derivation's
/// trailing `closed_world` slot (absent for an all-positive derivation).
pub const DERIVATION_WIRE_V1_CERT_PATH: [u64; 2] = [1, 2];

/// Why [`decode_derivation_wire_v1_bounded`] refused its bytes. A type of its own, because
/// [`DecodeError`] is exhaustive and contract v1 is additive-only (#2561). It is
/// `#[non_exhaustive]` from its first release (`seat:caa`), so the next decode-time bound adds a
/// variant additively.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BoundedWireError {
    /// The caller supplied a proof policy outside the portable index domain.
    InvalidLimits(CheckLimitError),
    /// The walk could not read the bytes, so nothing was decoded (fail closed).
    Unreadable(CertWireError),
    /// Certificate `cert` spans `span` bytes, over `max_cert_bytes` plus the declaration's slack,
    /// so nothing was decoded.
    OverBudget {
        /// The certificate's index in `closed_world`.
        cert: usize,
        /// Its byte span on the wire.
        span: usize,
        /// The budget it was held to.
        max_cert_bytes: usize,
    },
    /// The bytes walked within budget, and the codec STOPPED before they were a value: its own
    /// error, unfolded (#2734 3c, `seat:caa`'s ruling C). A capacity stop (the codec's decode depth,
    /// an atom length or an arity) is not evidence the bytes are invalid, so a consumer classifies
    /// it apart from malformed bytes (the kernel's `classify_decode_stop` reads this error).
    Stopped(ontos_codec::DecodeError),
    /// The bytes decoded to a value, and the value is not a derivation wire.
    Decode(DecodeError),
}

impl std::fmt::Display for BoundedWireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundedWireError::InvalidLimits(e) => write!(f, "invalid_check_limits: {e}"),
            BoundedWireError::Unreadable(e) => write!(f, "cert_wire_unreadable: {}", e.name()),
            BoundedWireError::OverBudget {
                cert,
                span,
                max_cert_bytes,
            } => write!(
                f,
                "cert_wire_over_budget: certificate {cert} spans {span} bytes, over max_cert_bytes \
                 {max_cert_bytes} + slack {}",
                cert_bytes_slack()
            ),
            BoundedWireError::Stopped(e) => write!(f, "decode_stopped: {}: {e}", e.code()),
            BoundedWireError::Decode(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for BoundedWireError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidLimits(error) => Some(error),
            Self::Unreadable(error) => Some(error),
            Self::Stopped(error) => Some(error),
            Self::Decode(error) => Some(error),
            Self::OverBudget { .. } => None,
        }
    }
}

/// #2561 (`seat:caa`'s ruling): [`decode_derivation_wire_v1`](crate::decode_derivation_wire_v1)
/// held to the caller's [`CheckLimits`] BEFORE decoding, for a consumer decoding a derivation from
/// bytes it did not produce. The bytes are walked whole ([`cert_wire_spans`], fail closed) and every
/// `closed_world` certificate's span is held to `max_cert_bytes` plus the slack, the rule the hosts
/// apply to the guest's frames (#2528). It takes the whole `CheckLimits` so a future decode bound
/// joins by construction.
pub fn decode_derivation_wire_v1_bounded(
    bytes: &[u8],
    limits: &CheckLimits,
) -> Result<Derivation, BoundedWireError> {
    limits.validate().map_err(BoundedWireError::InvalidLimits)?;
    let max_cert_bytes = limits.max_cert_bytes;
    let spans = cert_wire_spans(bytes, &DERIVATION_WIRE_V1_CERT_PATH)
        .map_err(BoundedWireError::Unreadable)?;
    if let Some((cert, &span)) = spans
        .iter()
        .enumerate()
        .find(|(_, &span)| encoded_span_exceeds(span, max_cert_bytes as u64))
    {
        return Err(BoundedWireError::OverBudget {
            cert,
            span,
            max_cert_bytes,
        });
    }
    // The codec's own stop, never folded into the value's shape (#2734 3c): the trusted
    // `decode_derivation_wire_v1` still folds it, which ADR 0036's v2 list records as a fault.
    let value = ontos_codec::decode(bytes).map_err(BoundedWireError::Stopped)?;
    derivation_wire_v1_from_value(&value).map_err(BoundedWireError::Decode)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ontos_core::Value;

    fn enc(v: &Value) -> Vec<u8> {
        ontos_codec::encode(v)
    }

    #[test]
    fn spans_are_the_encoded_lengths_of_the_elements() {
        let a = Value::atom(b"a".to_vec());
        let t = Value::tuple([
            Value::atom(b"xyz".to_vec()),
            Value::tuple(Vec::<Value>::new()),
        ]);
        let target = Value::tuple([a.clone(), t.clone()]);
        let frame = enc(&Value::tuple([a.clone(), target]));
        assert_eq!(
            cert_wire_spans(&frame, &[1]),
            Ok(vec![enc(&a).len(), enc(&t).len()])
        );
        // A step past the arity is an absent slot: no certificates.
        assert_eq!(cert_wire_spans(&frame, &[2]), Ok(vec![]));
        // An atom on the path is refused.
        assert_eq!(
            cert_wire_spans(&frame, &[0, 0]),
            Err(CertWireError::NotATuple)
        );
    }

    #[test]
    fn the_walk_refuses_what_the_codec_refuses() {
        let frame = enc(&Value::tuple([Value::atom(b"a".to_vec())]));
        // Truncated anywhere.
        for cut in 0..frame.len() {
            assert_eq!(
                cert_wire_spans(&frame[..cut], &[]),
                Err(CertWireError::Truncated)
            );
        }
        // A padded arity uvarint (0x81 0x00 for 1) is the codec's non_canonical_uvarint.
        let mut padded = vec![TAG_TUPLE, 0x81, 0x00];
        padded.extend_from_slice(&frame[2..]);
        assert!(
            ontos_codec::decode(&padded).is_err(),
            "CONTROL: the codec refuses it"
        );
        assert_eq!(
            cert_wire_spans(&padded, &[]),
            Err(CertWireError::NonCanonicalUvarint)
        );
        assert_eq!(
            cert_wire_spans(&[0x02, 0x00], &[]),
            Err(CertWireError::UnknownTag)
        );
        // Fail closed: the whole frame is walked, so trailing bytes and a truncated LATER sibling
        // are refused, and an atom declaring far more bytes than remain is refused before any read.
        let mut trailing = frame.clone();
        trailing.push(0x00);
        assert_eq!(
            cert_wire_spans(&trailing, &[]),
            Err(CertWireError::TrailingBytes)
        );
        let huge = [
            TAG_TUPLE, 0x02, TAG_TUPLE, 0x00, TAG_ATOM, 0xff, 0xff, 0xff, 0xff, 0x0f, b'x',
        ];
        assert_eq!(cert_wire_spans(&huge, &[0]), Err(CertWireError::Truncated));
        let eleven = [
            TAG_TUPLE, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
        ];
        assert_eq!(
            cert_wire_spans(&eleven, &[]),
            Err(CertWireError::UvarintOverflow)
        );
    }

    #[test]
    fn each_expands_every_element_and_names_the_concrete_path() {
        let cert = |s: &str| Value::atom(s.as_bytes().to_vec());
        // Tuple[tag, Tuple[Tuple[certs], Tuple[], Tuple[certs, certs]]]: two levels of lists.
        let inner0 = Value::tuple([Value::tuple([cert("a"), cert("bcd")])]);
        let inner1 = Value::tuple(Vec::<Value>::new());
        let inner2 = Value::tuple([
            Value::tuple(Vec::<Value>::new()),
            Value::tuple([cert("efgh")]),
        ]);
        let frame = enc(&Value::tuple([
            cert("tag"),
            Value::tuple([inner0, inner1, inner2]),
        ]));
        let got = cert_wire_spans_at(
            &frame,
            &[PathStep::Index(1), PathStep::Each, PathStep::Each],
        )
        .expect("the walk");
        // Each start addresses the certificate's own bytes (#2584).
        let own: Vec<&[u8]> = got
            .iter()
            .map(|c| &frame[c.start..c.start + c.span])
            .collect();
        assert_eq!(
            own,
            vec![
                &enc(&cert("a"))[..],
                &enc(&cert("bcd"))[..],
                &enc(&cert("efgh"))[..]
            ]
        );
        let paths: Vec<(Vec<usize>, usize)> = got.into_iter().map(|c| (c.path, c.span)).collect();
        assert_eq!(
            paths,
            vec![
                (vec![1, 0, 0, 0], enc(&cert("a")).len()),
                (vec![1, 0, 0, 1], enc(&cert("bcd")).len()),
                (vec![1, 2, 1, 0], enc(&cert("efgh")).len()),
            ]
        );
        // An index past an element's arity is that element's absent slot, not the whole frame's.
        let got = cert_wire_spans_at(
            &frame,
            &[PathStep::Index(1), PathStep::Each, PathStep::Index(1)],
        )
        .expect("the walk");
        let paths: Vec<Vec<usize>> = got.into_iter().map(|c| c.path).collect();
        assert_eq!(paths, vec![vec![1, 2, 1, 0]]);
        // Each over an atom is refused, and the whole frame is still walked: trailing bytes refuse.
        assert_eq!(
            cert_wire_spans_at(&frame, &[PathStep::Each]),
            Err(CertWireError::NotATuple)
        );
        let mut trailing = frame.clone();
        trailing.push(0x00);
        assert_eq!(
            cert_wire_spans_at(
                &trailing,
                &[PathStep::Index(1), PathStep::Each, PathStep::Each]
            ),
            Err(CertWireError::TrailingBytes)
        );
        // The walk alone reads any value, an atom root included, and refuses what the codec does.
        assert_eq!(cert_wire_walk(&frame), Ok(()));
        assert_eq!(cert_wire_walk(&enc(&cert("x"))), Ok(()));
        assert_eq!(cert_wire_walk(&trailing), Err(CertWireError::TrailingBytes));
        assert_eq!(
            cert_wire_walk(&frame[..frame.len() - 1]),
            Err(CertWireError::Truncated)
        );
    }

    #[test]
    fn the_tag_is_read_without_decoding() {
        let frame = enc(&Value::tuple([
            Value::atom(b"completeness_certificate".to_vec()),
            Value::tuple(Vec::<Value>::new()),
        ]));
        assert_eq!(
            cert_wire_tag(&frame),
            Ok(Some(&b"completeness_certificate"[..]))
        );
        assert_eq!(cert_wire_tag(&enc(&Value::atom(b"x".to_vec()))), Ok(None));
    }

    #[test]
    fn the_slack_is_the_declarations_widest_growth() {
        let slack = cert_bytes_slack();
        assert!(slack > 0 && slack <= 10, "slack {slack}");
        // Every declaration's growth over 0 is within it, and u64::MAX reaches it.
        for n in [0, 1, 255, 256, 1 << 20, 1 << 40, u64::MAX] {
            let growth = enc(&u64_atom(n)).len() - enc(&u64_atom(0)).len();
            assert!(growth as u64 <= slack, "{n}: {growth}");
        }
        let budget = ProofBudgetCount::from(100u32);
        assert!(cert_span_over_budget(100 + slack as usize + 1, budget));
        assert!(!cert_span_over_budget(100 + slack as usize, budget));
    }

    #[test]
    fn only_an_index_step_projects_an_index() {
        assert_eq!(PathStep::Index(0).index(), Some(0));
        assert_eq!(PathStep::Index(7).index(), Some(7));
        assert_eq!(PathStep::Each.index(), None);
    }
}
