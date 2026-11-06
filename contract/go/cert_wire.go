package contract

// #2528 (seat:caa's ruling (a)): the byte spans of the certificates inside an encoded frame, read
// WITHOUT decoding it, so a host can refuse a certificate wire longer than its budget before it
// materialises a single value. The checker's measure (#2524) bounds what a DECODED certificate may
// declare and be; only this bounds what an adversary makes a host READ.
//
// The ontos codec stores no per-element length: a tuple is 0x01 || uvarint(arity) || items and an
// atom 0x00 || uvarint(len) || bytes, so a span is found by walking tags and uvarints. Skipping is
// iterative (a count of values still to skip, so a frame's nesting sets no recursion depth); the
// walk recurses only along the host's own path steps. It allocates only its output, and rejects a
// non-canonical or overflowing uvarint exactly as the codec's decoder does. Mirrors rs cert_wire
// and ts cert_wire, pinned by the generated vectors/cert_wire_spans.json.
//
// Soundness of refusing on a span holds for a CANONICALLY encoded certificate: its literal span is
// its measure (CertEncodedBytes, the encoding with CertBytes zeroed) plus the declaration's own
// width above that of 0, which is at most CertBytesSlack. So a span over MaxCertBytes + slack means
// a measure over MaxCertBytes, which the checker refuses whatever the certificate declares. A
// non-canonical (padded) certificate may be refused although a normalising decoder would shrink
// it; that is still right, since the bound is on the bytes a host reads.

import (
	"errors"
	"fmt"
	"math"

	codec "github.com/bitspark/ontos/codec/go"
)

// CertWireError is why a frame could not be walked. It refuses the frame; it is never a verdict
// about a certificate. Name is the stable name every core reports, pinned by the shared vector.
type CertWireError struct{ Name string }

func (e *CertWireError) Error() string { return "cert wire: " + e.Name }

var (
	errWireTruncated    = &CertWireError{"truncated"}
	errWireUnknownTag   = &CertWireError{"unknown_tag"}
	errWireNonCanonical = &CertWireError{"non_canonical_uvarint"}
	errWireOverflow     = &CertWireError{"uvarint_overflow"}
	errWireNotATuple    = &CertWireError{"not_a_tuple"}
	errWireTrailing     = &CertWireError{"trailing_bytes"}
)

const (
	wireTagAtom  byte = 0x00
	wireTagTuple byte = 0x01
)

type wireCursor struct {
	bytes []byte
	pos   int
}

func (c *wireCursor) remaining() uint64 { return uint64(len(c.bytes) - c.pos) }

func (c *wireCursor) byte1() (byte, error) {
	if c.pos >= len(c.bytes) {
		return 0, errWireTruncated
	}
	b := c.bytes[c.pos]
	c.pos++
	return b, nil
}

// uvarint reads one shortest-form LEB128 uvarint over the u64 domain, checked in the codec's
// order: overflow while reading, canonicality after.
func (c *wireCursor) uvarint() (uint64, error) {
	start := c.pos
	var value uint64
	var shift uint
	for {
		b, err := c.byte1()
		if err != nil {
			return 0, err
		}
		if shift >= 64 || (shift == 63 && b&0x7f > 1) {
			return 0, errWireOverflow
		}
		value |= uint64(b&0x7f) << shift
		if b&0x80 == 0 {
			break
		}
		shift += 7
	}
	// Shortest form: the final byte carries payload, unless the value is a single 0x00.
	if c.pos-start > 1 && c.bytes[c.pos-1] == 0 {
		return 0, errWireNonCanonical
	}
	return value, nil
}

// header reads a value's tag and its uvarint, bounded by the bytes left: every value takes at
// least two bytes, so an arity above half of them cannot be met.
func (c *wireCursor) header() (byte, uint64, error) {
	tag, err := c.byte1()
	if err != nil {
		return 0, 0, err
	}
	if tag != wireTagAtom && tag != wireTagTuple {
		return 0, 0, errWireUnknownTag
	}
	n, err := c.uvarint()
	if err != nil {
		return 0, 0, err
	}
	bound := c.remaining()
	if tag == wireTagTuple {
		bound /= 2
	}
	if n > bound {
		return 0, 0, errWireTruncated
	}
	return tag, n, nil
}

// skip skips one whole value without materialising it.
func (c *wireCursor) skip() error { return c.skipValues(1) }

// skipValues skips pending whole values without materialising them.
func (c *wireCursor) skipValues(pending uint64) error {
	for pending > 0 {
		pending--
		tag, n, err := c.header()
		if err != nil {
			return err
		}
		if tag == wireTagAtom {
			c.pos += int(n)
		} else {
			pending += n
		}
	}
	return nil
}

// CertWireSpans returns the byte span of every element of the tuple reached by following path
// from the frame's root value, each step an index into the tuple at that point. A step at or past
// a tuple's arity means the slot is ABSENT (an optional trailing element, an option's none): there
// are no certificates, and the result is empty.
//
// The WHOLE frame is walked, not only the path (seat:caa's fail-closed condition): every sibling
// after the target and the rest of an absent slot's tuple are skipped too, and bytes after the one
// value are refused. So a frame this accepts is one the codec could read in full, and a host that
// refuses every error never hands the decoder a frame its bound has not covered.
//
// The index-only case of CertWireSpansAt, which it runs.
func CertWireSpans(frame []byte, path []int) ([]int, error) {
	steps := make([]PathStep, len(path))
	for i, step := range path {
		steps[i] = PathIndex(step)
	}
	certs, err := CertWireSpansAt(frame, steps)
	if err != nil {
		return nil, err
	}
	spans := make([]int, len(certs))
	for i, c := range certs {
		spans[i] = c.Span
	}
	return spans, nil
}

// PathStep is one step of a certificate path (#2561, seat:caa's ruling): an index into the tuple
// at that point (PathIndex), or every element of it (PathEach). PathEach may appear any number of
// times, at any depth, so a frame that carries certificates inside a list (the event door's output
// batch) needs no new walker. Its kinds are open to growth.
type PathStep struct {
	each  bool
	index int
}

// PathIndex is the step to the element at index. One at or past the tuple's arity is an ABSENT
// slot (an optional trailing element, an option's none), with no certificates.
func PathIndex(index int) PathStep { return PathStep{index: index} }

// PathEach is the step to every element, each followed by the rest of the path.
func PathEach() PathStep { return PathStep{each: true} }

// IsEach reports whether the step is PathEach.
func (s PathStep) IsEach() bool { return s.each }

// Index is a PathIndex step's index (0 for PathEach).
func (s PathStep) Index() int { return s.index }

// CertSpan is one certificate CertWireSpansAt found: its byte span, where it starts, and the
// concrete path to it, every PathEach resolved to the element's index and the certificate's own
// index last, so a refusal names which element carried it. Start (#2584) lets a host read the
// certificate's own bytes, frame[Start:Start+Span], to share a stack whose bytes an earlier frame
// carried.
type CertSpan struct {
	// Path is the concrete path from the frame's root to the certificate.
	Path []int
	// Span is the certificate's byte span on the wire.
	Span int
	// Start is the offset in the frame at which the certificate's encoding starts.
	Start int
}

// CertWireSpansAt returns the byte span of every certificate the steps reach, with its concrete
// path: each path the steps expand to (every PathEach over every element) leads to a tuple, and
// each element of that tuple is a certificate. A path through an absent slot reaches none.
//
// Fail closed exactly as CertWireSpans: the WHOLE frame is walked and bytes after the one value
// are refused. The walk recurses only along the steps, so its depth is the path's length, which the
// host chooses, never the frame's nesting; skipping stays iterative.
func CertWireSpansAt(frame []byte, steps []PathStep) ([]CertSpan, error) {
	c := &wireCursor{bytes: frame}
	out := []CertSpan{}
	path := make([]int, 0, len(steps)+1)
	if err := c.spansAt(steps, path, &out); err != nil {
		return nil, err
	}
	if c.pos != len(c.bytes) {
		return nil, errWireTrailing
	}
	return out, nil
}

// CertWireWalk is the fail-closed walk alone (#2561): the whole frame read without decoding it,
// refused by the same names as CertWireSpans. For a frame that carries no certificates, so a host
// never hands the decoder bytes no walk has covered.
func CertWireWalk(frame []byte) error {
	c := &wireCursor{bytes: frame}
	if err := c.skip(); err != nil {
		return err
	}
	if c.pos != len(c.bytes) {
		return errWireTrailing
	}
	return nil
}

// spansAt walks one whole value, following steps from it; path is the concrete path to it.
func (c *wireCursor) spansAt(steps []PathStep, path []int, out *[]CertSpan) error {
	tag, arity, err := c.header()
	if err != nil {
		return err
	}
	if tag != wireTagTuple {
		return errWireNotATuple
	}
	if len(steps) == 0 {
		// The certificates' tuple: each element is one.
		for i := uint64(0); i < arity; i++ {
			start := c.pos
			if err := c.skip(); err != nil {
				return err
			}
			certPath := append(append(make([]int, 0, len(path)+1), path...), int(i))
			*out = append(*out, CertSpan{Path: certPath, Span: c.pos - start, Start: start})
		}
		return nil
	}
	step, rest := steps[0], steps[1:]
	if step.each {
		for i := uint64(0); i < arity; i++ {
			if err := c.spansAt(rest, append(path, int(i)), out); err != nil {
				return err
			}
		}
		return nil
	}
	if uint64(step.index) >= arity {
		return c.skipValues(arity)
	}
	if err := c.skipValues(uint64(step.index)); err != nil {
		return err
	}
	if err := c.spansAt(rest, append(path, step.index), out); err != nil {
		return err
	}
	return c.skipValues(arity - uint64(step.index) - 1)
}

// CertWireTag returns the bytes of the atom that tags a frame, Tuple[Atom(tag), ..], read without
// decoding; nil when the root is not a tuple led by an atom. A host checks it before choosing a
// path, so an incomplete trailer is never walked as a completeness one.
func CertWireTag(frame []byte) ([]byte, error) {
	c := &wireCursor{bytes: frame}
	tag, arity, err := c.header()
	if err != nil {
		return nil, err
	}
	if tag != wireTagTuple || arity == 0 {
		return nil, nil
	}
	tag, n, err := c.header()
	if err != nil {
		return nil, err
	}
	if tag != wireTagAtom {
		return nil, nil
	}
	return frame[c.pos : c.pos+int(n)], nil
}

// CertBytesSlack is the most a certificate's literal span can exceed its measure: the widest
// encoding of the declared CertBytes (an int atom) minus the encoding of the 0 the measure writes.
func CertBytesSlack() uint64 {
	width := func(n uint64) uint64 { return uint64(len(codec.Encode(U64Atom(n)))) }
	return width(math.MaxUint64) - width(0)
}

// CertSpanOverBudget reports whether a certificate whose wire span is span measures over
// maxCertBytes for certain, so a host may refuse it undecoded.
func CertSpanOverBudget(span, maxCertBytes int) bool {
	return uint64(span) > uint64(maxCertBytes)+CertBytesSlack()
}

// CertWireOverBudget names the refusal a host reports for a certificate wire whose span exceeds
// its budget, with the offending certificate's index and span.
func CertWireOverBudget(index, span, maxCertBytes int) error {
	return fmt.Errorf("cert_wire_over_budget: certificate %d spans %d bytes, over max_cert_bytes %d + slack %d",
		index, span, maxCertBytes, CertBytesSlack())
}

// DerivationWireV1CertPath is the path to a v1 derivation wire's certificates: the tagged payload,
// then the derivation's trailing closed_world slot (absent for an all-positive derivation).
var DerivationWireV1CertPath = []int{1, 2}

// The kinds of BoundedWireError. The set is OPEN (seat:caa, #2561): a future decode-time bound adds a
// kind, so a consumer must treat an unknown kind as a refusal, never as success.
const (
	// BoundedWireUnreadable: the walk could not read the bytes, so nothing was decoded (fail closed).
	BoundedWireUnreadable = "cert_wire_unreadable"
	// BoundedWireOverBudget: a certificate spans over MaxCertBytes plus the slack; nothing decoded.
	BoundedWireOverBudget = "cert_wire_over_budget"
	// BoundedWireStopped: the bytes walked within budget, and the codec STOPPED before they were a
	// value (#2734 3c, seat:caa's ruling C). Err is the codec's own *codec.DecodeError, unfolded: a
	// capacity stop (its decode depth, an atom length or an arity) is not evidence the bytes are
	// invalid, so a consumer classifies it apart from malformed bytes (the kernel's
	// outcome.ClassifyDecodeStop reads it).
	BoundedWireStopped = "decode_stopped"
	// BoundedWireDecode: the bytes decoded to a value, and the value is not a derivation wire.
	BoundedWireDecode = "decode"
)

// BoundedWireError is why DecodeDerivationWireV1Bounded refused its bytes. Kind is one of the
// BoundedWire* kinds, an open set. Cert, Span and MaxCertBytes are set for BoundedWireOverBudget;
// Err carries the walk's *CertWireError or the decoder's error.
type BoundedWireError struct {
	Kind         string
	Cert         int
	Span         int
	MaxCertBytes int
	Err          error
}

func (e *BoundedWireError) Error() string {
	switch e.Kind {
	case BoundedWireOverBudget:
		return fmt.Sprintf("%s: certificate %d spans %d bytes, over max_cert_bytes %d + slack %d",
			e.Kind, e.Cert, e.Span, e.MaxCertBytes, CertBytesSlack())
	case BoundedWireUnreadable:
		var we *CertWireError
		if errors.As(e.Err, &we) {
			return e.Kind + ": " + we.Name
		}
	}
	return e.Kind + ": " + e.Err.Error()
}

func (e *BoundedWireError) Unwrap() error { return e.Err }

// DecodeDerivationWireV1Bounded is DecodeDerivationWireV1 held to the caller's CheckLimits BEFORE
// decoding (#2561, seat:caa's ruling), for a consumer decoding a derivation from bytes it did not
// produce. The bytes are walked whole (CertWireSpans, fail closed) and every closed_world
// certificate's span is held to MaxCertBytes plus the slack, the rule the hosts apply to the
// guest's frames (#2528). It takes the whole CheckLimits so a future decode bound joins by
// construction. Mirrors rs decode_derivation_wire_v1_bounded and ts decodeDerivationWireV1Bounded.
func DecodeDerivationWireV1Bounded(bytes []byte, limits CheckLimits) (Derivation, error) {
	spans, err := CertWireSpans(bytes, DerivationWireV1CertPath)
	if err != nil {
		return Derivation{}, &BoundedWireError{Kind: BoundedWireUnreadable, Err: err}
	}
	for i, span := range spans {
		if CertSpanOverBudget(span, limits.MaxCertBytes) {
			return Derivation{}, &BoundedWireError{Kind: BoundedWireOverBudget, Cert: i, Span: span, MaxCertBytes: limits.MaxCertBytes}
		}
	}
	// The codec's own stop, never folded into the value's shape (#2734 3c): the trusted
	// DecodeDerivationWireV1 still folds it, which ADR 0036's v2 list records as a fault.
	v, err := codec.Decode(bytes)
	if err != nil {
		return Derivation{}, &BoundedWireError{Kind: BoundedWireStopped, Err: err}
	}
	d, err := DerivationWireV1FromValue(v)
	if err != nil {
		return Derivation{}, &BoundedWireError{Kind: BoundedWireDecode, Err: err}
	}
	return d, nil
}
