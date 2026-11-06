package contract

// The ONE derivation/certificate decoder (#2630, seat:caa's ruling): the inverse of
// DerivationAsValue and ClosedModelCertAsValue, and the only one — the kernel seam reads every
// derivation, subst and certificate it decodes through these functions.
//
// It is a line-for-line port of rs's contract decoder (contract/rs/src/derivation_wire.rs):
// the same readers, the same helpers, the same CHECK ORDER, and the same path at every
// refusal. A refusal is a *DecodeError whose Error() renders the one tri-core text,
// `decode <path>: <defect>`, byte-identical to rs's Display; vectors/derivation_wire.json's
// `refusal` rows pin it in all three cores.

import (
	"fmt"
	"math"
	"strings"
	"unicode/utf8"

	codec "github.com/bitspark/ontos/codec/go"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// DecodeErrorKind is a refusal class of the one decoder. Each has exactly one rendering.
type DecodeErrorKind int

const (
	// DecodeShape: a value was a Tuple where an Atom was expected, or the reverse.
	DecodeShape DecodeErrorKind = iota
	// DecodeArity: a Tuple had an arity its reading does not take.
	DecodeArity
	// DecodeUnknownTag: a tag was none of the reading's variants.
	DecodeUnknownTag
	// DecodeNotQuoted: a value is not in the image of quote, or is not ground.
	DecodeNotQuoted
	// DecodeBadInt: an integer field is not the canonical ontos-data int embedding, or is out
	// of range.
	DecodeBadInt
	// DecodeBadUtf8: a byte atom that must be UTF-8 is not.
	DecodeBadUtf8
	// DecodeNotCanonical: a collection arrived out of canonical sorted+deduped order (#839,
	// #2630's subst entries).
	DecodeNotCanonical
)

// There is no depth class here, in any core (#2731, `seat:caa`'s ruling). The decoder imposes no
// depth POLICY: check's max_term_depth (default 256, identical tri-core) is the one depth refusal,
// so a derivation within it decodes everywhere (derivation_wire.json's ground_arg_256/257 rows).
// rs refused a quoted term past 256 VALUE levels here until #2731; its readers no longer recurse.
// A core's CAPACITY is separate and declared: go's host bounds a reply by its own measured limit
// and refuses past it as reply_decode_limit (#2366, #2456).

// DecodeError is a refusal by the one derivation/certificate decoder: its class, the PATH to
// the offending element, and what the class carries.
type DecodeError struct {
	Kind DecodeErrorKind
	// Ctx is the path to the offending element, e.g. closed_world.cert.domain.values.
	Ctx string
	// Accepted is EVERY arity the reading takes (DecodeArity).
	Accepted []int
	// Got is the arity seen (DecodeArity).
	Got int
	// Tag is the tag's exact bytes (DecodeUnknownTag); a Go string holds any bytes. Rendered by
	// RenderTag.
	Tag string
}

// Error renders the one tri-core text, byte-identical to rs's DecodeError Display.
func (e *DecodeError) Error() string {
	switch e.Kind {
	case DecodeShape:
		return "decode " + e.Ctx + ": expected a different value shape"
	case DecodeArity:
		return ArityRefusal(e.Ctx, e.Accepted, e.Got)
	case DecodeUnknownTag:
		return "decode " + e.Ctx + ": unknown tag " + RenderTag([]byte(e.Tag))
	case DecodeNotQuoted:
		return "decode " + e.Ctx + ": value is not a quoted ground term"
	case DecodeBadInt:
		return "decode " + e.Ctx + ": not a canonical int embedding"
	case DecodeBadUtf8:
		return "decode " + e.Ctx + ": not valid UTF-8"
	case DecodeNotCanonical:
		return "decode " + e.Ctx + ": not in canonical sorted+deduped order"
	default:
		return "decode " + e.Ctx + ": unknown refusal"
	}
}

// ArityRefusal is the ONE rendering of an arity refusal, rs's arity_refusal: a reading that
// takes one arity keeps `decode <ctx>: expected arity N, got M`; a reading with trailing-optional
// slots names every arity it takes, `decode <ctx>: M elements, expected 10, 11 or 12`.
func ArityRefusal(ctx string, accepted []int, got int) string {
	switch len(accepted) {
	case 0:
		return fmt.Sprintf("decode %s: %d elements, and no arity is accepted", ctx, got)
	case 1:
		return fmt.Sprintf("decode %s: expected arity %d, got %d", ctx, accepted[0], got)
	default:
		init := make([]string, len(accepted)-1)
		for i, n := range accepted[:len(accepted)-1] {
			init[i] = fmt.Sprint(n)
		}
		return fmt.Sprintf("decode %s: %d elements, expected %s or %d", ctx, got, strings.Join(init, ", "), accepted[len(accepted)-1])
	}
}

// RenderTag is the ONE rendering of an unknown tag in a refusal text (#2682, seat:caa's ruling B):
// a double-quoted string in which each ASCII byte renders exactly as rs's `{:?}` renders that
// character (\" \\ \t \r \n \0, another control as \u{hex}, a printable byte as itself), and each
// byte >= 0x80 renders as \x{hh}. Nothing is UTF-8-decoded, so it is identical in rs, go and ts
// by construction; rs's `{:?}` decoded lossily and consulted Rust's own is_printable table.
func RenderTag(p []byte) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, c := range p {
		switch {
		case c == '"':
			b.WriteString(`\"`)
		case c == '\\':
			b.WriteString(`\\`)
		case c == '\t':
			b.WriteString(`\t`)
		case c == '\r':
			b.WriteString(`\r`)
		case c == '\n':
			b.WriteString(`\n`)
		case c == 0:
			b.WriteString(`\0`)
		case c >= 0x20 && c <= 0x7e:
			b.WriteByte(c)
		case c < 0x80:
			fmt.Fprintf(&b, `\u{%x}`, c)
		default:
			fmt.Fprintf(&b, `\x{%02x}`, c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

// UnknownTagError is a refusal that NAMES a wire tag (#2771): it carries the tag's exact BYTES, and
// its only formatter is RenderTag, so a refusal site passes bytes and has no way to quote a tag
// itself. Prefix and What are the site's per-core wording (seat:caa's ruling on #2771: only the
// rendering is interface, so a reader matches it by CONTAINS, never by the whole text).
type UnknownTagError struct {
	// Prefix is where the refusal came from, e.g. "seam decode: <ctx>".
	Prefix string
	// What names what the tag should have been, e.g. "unknown resolution arm".
	What string
	// Tag is the refused tag's exact bytes.
	Tag []byte
}

// Error renders `<prefix>: <what> <RenderTag(tag)>`.
func (e *UnknownTagError) Error() string {
	return e.Prefix + ": " + e.What + " " + RenderTag(e.Tag)
}

// NewUnknownTagError is the refusal naming tag, copied so the caller's buffer cannot change it.
func NewUnknownTagError(prefix, what string, tag []byte) error {
	return &UnknownTagError{Prefix: prefix, What: what, Tag: append([]byte(nil), tag...)}
}

// ------------------------------- small helpers ------------------------------

func decItems(v core.Value, ctx string) ([]core.Value, error) {
	t, ok := v.(core.Tuple)
	if !ok {
		return nil, &DecodeError{Kind: DecodeShape, Ctx: ctx}
	}
	return t.Items(), nil
}

func decItemsN(v core.Value, ctx string, accepted []int) ([]core.Value, error) {
	its, err := decItems(v, ctx)
	if err != nil {
		return nil, err
	}
	if !containsInt(accepted, len(its)) {
		return nil, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: accepted, Got: len(its)}
	}
	return its, nil
}

func containsInt(set []int, n int) bool {
	for _, m := range set {
		if m == n {
			return true
		}
	}
	return false
}

func decAtomBytes(v core.Value, ctx string) ([]byte, error) {
	a, ok := v.(core.Atom)
	if !ok {
		return nil, &DecodeError{Kind: DecodeShape, Ctx: ctx}
	}
	return a.Bytes(), nil
}

func decSplitTag(v core.Value, ctx string) ([]byte, []core.Value, error) {
	its, err := decItems(v, ctx)
	if err != nil {
		return nil, nil, err
	}
	if len(its) == 0 {
		return nil, nil, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: []int{1}, Got: 0}
	}
	tag, err := decAtomBytes(its[0], ctx)
	if err != nil {
		return nil, nil, err
	}
	return tag, its[1:], nil
}

// IndexMax is the contract's bound on every index and count field: a root, a premise or
// certificate index, a limits_decl field (#2682, seat:caa's ruling A). 2^53 - 1, so every core
// holds every in-domain value exactly, and above it every core refuses BadInt the same way. It is
// ONE number: rs's usize, go's int and ts's number used to set four different bounds.
const IndexMax uint64 = 1<<53 - 1

// decReadIndex reads an index or count field into 0..=IndexMax, else BadInt. The value is a
// PROTOCOL integer, held as uint64 whatever this build's int width (#2735): it becomes a host
// offset only through IndexOffset, after a range check against the collection it indexes, so an
// index past the collection reaches check (root_out_of_range, cert_out_of_range) on every platform.
func decReadIndex(v core.Value, ctx string) (uint64, error) {
	n, err := data.ReadInt(v)
	if err != nil || n.Sign() < 0 || !n.IsUint64() || n.Uint64() > IndexMax {
		return 0, &DecodeError{Kind: DecodeBadInt, Ctx: ctx}
	}
	return n.Uint64(), nil
}

// decReadU32 reads an int field the account types as uint32 (an arity, a position, an attribute,
// a stratum level, a rank). A value past MaxUint32 is refused as BadInt, never narrowed: a
// truncation is a repaired input (#839), and uint32() made the same bytes decode to different
// values in go/rs (which truncated) and ts (which did not) (#2682).
func decReadU32(v core.Value, ctx string) (uint32, error) {
	n, err := data.ReadInt(v)
	if err != nil || n.Sign() < 0 || !n.IsUint64() || n.Uint64() > math.MaxUint32 {
		return 0, &DecodeError{Kind: DecodeBadInt, Ctx: ctx}
	}
	return uint32(n.Uint64()), nil
}

func decReadOpt(v core.Value, ctx string) (core.Value, bool, error) {
	tag, payload, err := decSplitTag(v, ctx)
	if err != nil {
		return nil, false, err
	}
	switch string(tag) {
	case "none":
		if len(payload) != 0 {
			return nil, false, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: []int{1}, Got: len(payload) + 1}
		}
		return nil, false, nil
	case "some":
		if len(payload) != 1 {
			return nil, false, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: []int{2}, Got: len(payload) + 1}
		}
		return payload[0], true, nil
	default:
		return nil, false, &DecodeError{Kind: DecodeUnknownTag, Ctx: ctx, Tag: string(tag)}
	}
}

func decGroundArgFromQuoted(v core.Value, ctx string) (core.Value, error) {
	term, ok := Reify(v)
	if !ok {
		return nil, &DecodeError{Kind: DecodeNotQuoted, Ctx: ctx}
	}
	ground, ok := term.EraseGround()
	if !ok {
		return nil, &DecodeError{Kind: DecodeNotQuoted, Ctx: ctx}
	}
	return ground, nil
}

// decExpectN asserts a tagged payload's arity; accepted counts the tag, as the arity a reader
// sees on the wire does.
func decExpectN(payload []core.Value, accepted []int, ctx string) ([]core.Value, error) {
	if !containsInt(accepted, len(payload)+1) {
		return nil, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: accepted, Got: len(payload) + 1}
	}
	return payload, nil
}

// ------------------------------ term / literal ------------------------------

// GroundLiteralFromValueV1 is the public strict inverse of GroundLiteralAsValue (#1914): decode
// ONE standalone ground literal from its account representation Tuple[Atom(pred), quote(arg)…].
// It refuses a missing or non-atom predicate, an argument outside the image of quote, and a
// quoted variable or any non-ground argument. An unquoted compound is refused, by design: the
// quoting is what lets the inverse check groundness. There is no decode depth bound here, unlike
// rs's (#2658's retracted ruling 3): go builds deep terms safely.
func GroundLiteralFromValueV1(v core.Value) (GroundLiteral, error) {
	return groundLiteralFromValue(v, "ground literal")
}

func groundLiteralFromValue(v core.Value, ctx string) (GroundLiteral, error) {
	its, err := decItems(v, ctx)
	if err != nil {
		return GroundLiteral{}, err
	}
	if len(its) == 0 {
		return GroundLiteral{}, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: []int{1}, Got: 0}
	}
	pred, err := decAtomBytes(its[0], ctx)
	if err != nil {
		return GroundLiteral{}, err
	}
	args := make([]core.Value, 0, len(its)-1)
	for _, arg := range its[1:] {
		g, err := decGroundArgFromQuoted(arg, ctx)
		if err != nil {
			return GroundLiteral{}, err
		}
		args = append(args, g)
	}
	return GroundLiteral{Pred: NewSymbol(pred), Args: args}, nil
}

// ---------------------------------- subst -----------------------------------

// SubstFromValue reconstructs a Subst from Tuple[ Tuple[Atom(var_id), quote(term)], … ]. The
// entries must arrive strictly increasing in the codec bytes of their key, as the encoder writes
// them (#2630): a repeated or misordered var-id is refused by name. Terms go through Reify, the
// frozen inverse of quote, and may contain holes.
func SubstFromValue(v core.Value) (Subst, error) {
	entries, err := decItems(v, "subst")
	if err != nil {
		return nil, err
	}
	out := make(Subst, len(entries))
	var previousKey []byte
	for i, entry := range entries {
		pair, err := decItemsN(entry, "subst.entry", []int{2})
		if err != nil {
			return nil, err
		}
		name, err := decAtomBytes(pair[0], "subst.var")
		if err != nil {
			return nil, err
		}
		// ParseVarId's test is the one every VarId construction makes (validVarName, #3115).
		id, err := ParseVarId(string(name))
		if err != nil {
			return nil, &DecodeError{Kind: DecodeBadUtf8, Ctx: "subst.var"}
		}
		key := codec.Encode(pair[0])
		if i > 0 && string(previousKey) >= string(key) {
			return nil, &DecodeError{Kind: DecodeNotCanonical, Ctx: "subst"}
		}
		previousKey = key
		term, ok := Reify(pair[1])
		if !ok {
			return nil, &DecodeError{Kind: DecodeNotQuoted, Ctx: "subst.term"}
		}
		out[id] = term
	}
	return out, nil
}

// -------------------------------- derivation --------------------------------

func nodeMetaFromValue(v core.Value) (NodeMeta, error) {
	inner, present, err := decReadOpt(v, "node.meta")
	if err != nil {
		return NodeMeta{}, err
	}
	if !present {
		return NoMeta(), nil
	}
	return NewNodeMeta(inner), nil
}

func evidenceFromValue(v core.Value) (Evidence, error) {
	inner, present, err := decReadOpt(v, "node.evidence")
	if err != nil {
		return Evidence{}, err
	}
	if !present {
		return NoEvidence(), nil
	}
	return NewEvidence(inner), nil
}

func nodeFromValue(v core.Value) (Node, error) {
	tag, payload, err := decSplitTag(v, "node")
	if err != nil {
		return nil, err
	}
	switch string(tag) {
	case "rule":
		if len(payload) != 5 {
			return nil, &DecodeError{Kind: DecodeArity, Ctx: "node.rule", Accepted: []int{6}, Got: len(payload) + 1}
		}
		conc, err := groundLiteralFromValue(payload[0], "node.rule.conclusion")
		if err != nil {
			return nil, err
		}
		clause, err := decAtomBytes(payload[1], "node.rule.clause")
		if err != nil {
			return nil, err
		}
		if !utf8.Valid(clause) {
			return nil, &DecodeError{Kind: DecodeBadUtf8, Ctx: "node.rule.clause"}
		}
		subst, err := SubstFromValue(payload[2])
		if err != nil {
			return nil, err
		}
		premiseItems, err := decItems(payload[3], "node.rule.premises")
		if err != nil {
			return nil, err
		}
		premises := make([]Premise, 0, len(premiseItems))
		for _, p := range premiseItems {
			premise, err := premiseFromValue(p)
			if err != nil {
				return nil, err
			}
			premises = append(premises, premise)
		}
		meta, err := nodeMetaFromValue(payload[4])
		if err != nil {
			return nil, err
		}
		return RuleNode{
			Conc:     conc,
			Clause:   NewClauseId(string(clause)),
			Subst:    subst,
			Premises: premises,
			Meta:     meta,
		}, nil
	case "builtin":
		if len(payload) != 1 {
			return nil, &DecodeError{Kind: DecodeArity, Ctx: "node.builtin", Accepted: []int{2}, Got: len(payload) + 1}
		}
		conc, err := groundLiteralFromValue(payload[0], "node.builtin.conclusion")
		if err != nil {
			return nil, err
		}
		return BuiltinNode{Conc: conc}, nil
	case "leaf":
		if len(payload) != 2 {
			return nil, &DecodeError{Kind: DecodeArity, Ctx: "node.leaf", Accepted: []int{3}, Got: len(payload) + 1}
		}
		conc, err := groundLiteralFromValue(payload[0], "node.leaf.conclusion")
		if err != nil {
			return nil, err
		}
		evidence, err := evidenceFromValue(payload[1])
		if err != nil {
			return nil, err
		}
		return LeafNode{Conc: conc, Evidence: evidence}, nil
	default:
		return nil, &DecodeError{Kind: DecodeUnknownTag, Ctx: "node", Tag: string(tag)}
	}
}

// premiseFromValue: a bare int is a positive premise (node index), read FIRST as rs does; a
// Tuple[Atom("neg"|"count"), …] is a Neg (ADR 0007) or Count (ADR 0023) premise.
func premiseFromValue(p core.Value) (Premise, error) {
	if node, err := decReadIndex(p, "node.rule.premise"); err == nil {
		return PosNode(node), nil
	}
	tag, payload, err := decSplitTag(p, "node.rule.premise")
	if err != nil {
		return nil, err
	}
	switch string(tag) {
	case "neg":
		if len(payload) != 2 {
			return nil, &DecodeError{Kind: DecodeArity, Ctx: "node.rule.premise.neg", Accepted: []int{3}, Got: len(payload) + 1}
		}
		atom, err := groundLiteralFromValue(payload[0], "node.rule.premise.neg.atom")
		if err != nil {
			return nil, err
		}
		cert, err := decReadIndex(payload[1], "node.rule.premise.neg.cert")
		if err != nil {
			return nil, err
		}
		return NegPremise{Atom: atom, Cert: NewCertId(cert), Nonmember: DirectLookup}, nil
	case "count":
		if len(payload) != 5 {
			return nil, &DecodeError{Kind: DecodeArity, Ctx: "node.rule.premise.count", Accepted: []int{6}, Got: len(payload) + 1}
		}
		predItems, err := decItemsN(payload[0], "node.rule.premise.count.pred", []int{2})
		if err != nil {
			return nil, err
		}
		name, err := decAtomBytes(predItems[0], "node.rule.premise.count.pred.name")
		if err != nil {
			return nil, err
		}
		arity, err := decReadU32(predItems[1], "node.rule.premise.count.pred.arity")
		if err != nil {
			return nil, err
		}
		pred := NewPredicateRef(NewSymbol(name), arity)
		filterItems, err := decItems(payload[1], "node.rule.premise.count.filter")
		if err != nil {
			return nil, err
		}
		filter := make([]GroundFilterEntry, 0, len(filterItems))
		for _, entry := range filterItems {
			pair, err := decItemsN(entry, "node.rule.premise.count.filter.entry", []int{2})
			if err != nil {
				return nil, err
			}
			pos, err := decReadU32(pair[0], "node.rule.premise.count.filter.pos")
			if err != nil {
				return nil, err
			}
			filter = append(filter, GroundFilterEntry{Pos: pos, Value: pair[1]})
		}
		project, err := projectSpecFromValue(payload[2])
		if err != nil {
			return nil, err
		}
		cert, err := decReadIndex(payload[4], "node.rule.premise.count.cert")
		if err != nil {
			return nil, err
		}
		return CountPremise{Pred: pred, Filter: filter, Project: project, K: payload[3], Cert: NewCertId(cert)}, nil
	default:
		return nil, &DecodeError{Kind: DecodeUnknownTag, Ctx: "node.rule.premise", Tag: string(tag)}
	}
}

// projectSpecFromValue: Atom("rows") is Rows; Tuple[Atom("distinct"|"sum"|"min"|"max"), int(attr)]
// is the corresponding fold (ADR 0023 + #587).
func projectSpecFromValue(v core.Value) (ProjectSpec, error) {
	const ctx = "node.rule.premise.count.project"
	if bytes, err := decAtomBytes(v, ctx); err == nil {
		if string(bytes) == "rows" {
			return Rows(), nil
		}
		return ProjectSpec{}, &DecodeError{Kind: DecodeUnknownTag, Ctx: ctx, Tag: string(bytes)}
	}
	tag, payload, err := decSplitTag(v, ctx)
	if err != nil {
		return ProjectSpec{}, err
	}
	if len(payload) != 1 {
		return ProjectSpec{}, &DecodeError{Kind: DecodeArity, Ctx: ctx, Accepted: []int{2}, Got: len(payload) + 1}
	}
	attr, err := decReadU32(payload[0], "node.rule.premise.count.project.attr")
	if err != nil {
		return ProjectSpec{}, err
	}
	switch string(tag) {
	case "distinct":
		return ProjectSpec{Kind: ProjectDistinct, Attr: attr}, nil
	case "sum":
		return ProjectSpec{Kind: ProjectSum, Attr: attr}, nil
	case "min":
		return ProjectSpec{Kind: ProjectMin, Attr: attr}, nil
	case "max":
		return ProjectSpec{Kind: ProjectMax, Attr: attr}, nil
	default:
		return ProjectSpec{}, &DecodeError{Kind: DecodeUnknownTag, Ctx: ctx, Tag: string(tag)}
	}
}

// DerivationFromValue reconstructs a Derivation from Tuple[ Tuple[node…], int(root) (, Tuple[cert…]) ].
// Node order is identity-bearing and preserved. The root is NOT checked against the node count
// here (#2630, seat:caa's ruling): Derivation's root is a public field the type can hold out of
// range, and check refuses it by its FIRM root_out_of_range, so the decoder passes it through.
func DerivationFromValue(v core.Value) (Derivation, error) {
	its, err := decItems(v, "derivation")
	if err != nil {
		return Derivation{}, err
	}
	if len(its) != 2 && len(its) != 3 {
		return Derivation{}, &DecodeError{Kind: DecodeArity, Ctx: "derivation", Accepted: []int{2, 3}, Got: len(its)}
	}
	nodeValues, err := decItems(its[0], "derivation.nodes")
	if err != nil {
		return Derivation{}, err
	}
	nodes := make([]Node, 0, len(nodeValues))
	for _, nv := range nodeValues {
		n, err := nodeFromValue(nv)
		if err != nil {
			return Derivation{}, err
		}
		nodes = append(nodes, n)
	}
	root, err := decReadIndex(its[1], "derivation.root")
	if err != nil {
		return Derivation{}, err
	}
	var closedWorld []ClosedModelCert
	if len(its) == 3 {
		certValues, err := decItems(its[2], "derivation.closed_world")
		if err != nil {
			return Derivation{}, err
		}
		closedWorld = make([]ClosedModelCert, 0, len(certValues))
		for _, cv := range certValues {
			c, err := ClosedModelCertFromValue(cv)
			if err != nil {
				return Derivation{}, err
			}
			closedWorld = append(closedWorld, c)
		}
	}
	return NewDerivationWithClosedWorld(nodes, root, closedWorld), nil
}

// readHash reads a digest atom (64 lowercase-hex chars) into a Hash, the inverse of DigestAtom.
func readHash(v core.Value, ctx string) (Hash, error) {
	var h Hash
	hex, err := decAtomBytes(v, ctx)
	if err != nil {
		return h, err
	}
	if len(hex) != 64 {
		return h, &DecodeError{Kind: DecodeShape, Ctx: ctx}
	}
	for i := 0; i < 32; i++ {
		hi, ok1 := hexNibble(hex[2*i])
		lo, ok2 := hexNibble(hex[2*i+1])
		if !ok1 || !ok2 {
			return h, &DecodeError{Kind: DecodeShape, Ctx: ctx}
		}
		h[i] = hi<<4 | lo
	}
	return h, nil
}

// hexNibble maps one lowercase-hex digit 0-9a-f to its nibble.
func hexNibble(c byte) (byte, bool) {
	switch {
	case c >= '0' && c <= '9':
		return c - '0', true
	case c >= 'a' && c <= 'f':
		return c - 'a' + 10, true
	default:
		return 0, false
	}
}

func symbolFromValue(v core.Value, ctx string) (Symbol, error) {
	b, err := decAtomBytes(v, ctx)
	if err != nil {
		return Symbol{}, err
	}
	return NewSymbol(b), nil
}

// ClosedModelCertFromValue reconstructs a ClosedModelCert: the ONE certificate decoder (#2630).
// TEN, ELEVEN or TWELVE elements: the 11th is ADR 0029 D10's slice-seal pin, the 12th ADR 0030's
// partial sub-scope; anything else is refused by arity under the closed posture. The slots are
// read in rs's order, so a certificate with two defects is refused for the same one in every core.
func ClosedModelCertFromValue(v core.Value) (ClosedModelCert, error) {
	its, err := decItems(v, "closed_world.cert")
	if err != nil {
		return ClosedModelCert{}, err
	}
	if len(its) < 10 || len(its) > 12 {
		return ClosedModelCert{}, &DecodeError{Kind: DecodeArity, Ctx: "closed_world.cert", Accepted: []int{10, 11, 12}, Got: len(its)}
	}
	var witness *Hash
	if len(its) >= 11 && !(len(its) == 12 && isOptNone(its[10])) {
		w, err := readHash(its[10], "closed_world.cert.decomposition_witness")
		if err != nil {
			return ClosedModelCert{}, err
		}
		witness = &w
	}
	var partialScope *StratumPrefix
	if len(its) == 12 {
		p, err := stratumPrefixFromValue(its[11])
		if err != nil {
			return ClosedModelCert{}, err
		}
		partialScope = &p
	}
	edbValues, err := decItems(its[5], "closed_world.cert.edb_snapshot_hashes")
	if err != nil {
		return ClosedModelCert{}, err
	}
	edbHashes := make([]Hash, 0, len(edbValues))
	for _, hv := range edbValues {
		h, err := readHash(hv, "closed_world.cert.edb_snapshot_hash")
		if err != nil {
			return ClosedModelCert{}, err
		}
		edbHashes = append(edbHashes, h)
	}
	domainValues, err := decItems(its[6], "closed_world.cert.domains")
	if err != nil {
		return ClosedModelCert{}, err
	}
	domains := make([]FiniteDomain, 0, len(domainValues))
	for _, dv := range domainValues {
		d, err := finiteDomainFromValue(dv)
		if err != nil {
			return ClosedModelCert{}, err
		}
		domains = append(domains, d)
	}
	extensionValues, err := decItems(its[7], "closed_world.cert.extensions")
	if err != nil {
		return ClosedModelCert{}, err
	}
	extensions := make([]RelationTable, 0, len(extensionValues))
	for _, ev := range extensionValues {
		e, err := relationTableFromValue(ev)
		if err != nil {
			return ClosedModelCert{}, err
		}
		extensions = append(extensions, e)
	}
	supportValues, err := decItems(its[8], "closed_world.cert.supports")
	if err != nil {
		return ClosedModelCert{}, err
	}
	edges := make([]SupportEdge, 0, len(supportValues))
	for _, sv := range supportValues {
		s, err := supportEdgeFromValue(sv)
		if err != nil {
			return ClosedModelCert{}, err
		}
		edges = append(edges, s)
	}
	scope, err := stratumPrefixFromValue(its[0])
	if err != nil {
		return ClosedModelCert{}, err
	}
	programHash, err := readHash(its[1], "closed_world.cert.program_hash")
	if err != nil {
		return ClosedModelCert{}, err
	}
	profileHash, err := readHash(its[2], "closed_world.cert.profile_hash")
	if err != nil {
		return ClosedModelCert{}, err
	}
	ctxHash, err := readHash(its[3], "closed_world.cert.ctx_hash")
	if err != nil {
		return ClosedModelCert{}, err
	}
	theoryHash, err := readHash(its[4], "closed_world.cert.theory_config_hash")
	if err != nil {
		return ClosedModelCert{}, err
	}
	limitsDecl, err := certSizeDeclFromValue(its[9])
	if err != nil {
		return ClosedModelCert{}, err
	}
	return ClosedModelCert{
		Scope:                scope,
		ProgramHash:          programHash,
		ProfileHash:          profileHash,
		CtxHash:              ctxHash,
		TheoryConfigHash:     theoryHash,
		EdbSnapshotHashes:    edbHashes,
		Domains:              domains,
		Extensions:           extensions,
		Supports:             SupportWitness{Edges: edges},
		Closure:              ClosureWitness{},
		LimitsDecl:           limitsDecl,
		DecompositionWitness: witness,
		PartialScope:         partialScope,
	}, nil
}

// isOptNone reports whether v is the opt none marker Tuple[Atom("none")], ADR 0030 D4's stand-in
// for an absent slice-seal pin at the 11th slot when the 12th is present. A malformed tuple is
// simply NOT the marker; the next read reports it.
func isOptNone(v core.Value) bool {
	tag, payload, err := decSplitTag(v, "closed_world.cert.decomposition_witness")
	return err == nil && string(tag) == "none" && len(payload) == 0
}

// stratumPrefixFromValue: the wire promises sorted+deduped predicates, and that promise is
// CHECKED, never assumed or repaired (#839).
func stratumPrefixFromValue(v core.Value) (StratumPrefix, error) {
	its, err := decItemsN(v, "closed_world.cert.scope", []int{2})
	if err != nil {
		return StratumPrefix{}, err
	}
	level, err := decReadU32(its[0], "closed_world.cert.scope.level")
	if err != nil {
		return StratumPrefix{}, err
	}
	predValues, err := decItems(its[1], "closed_world.cert.scope.predicates")
	if err != nil {
		return StratumPrefix{}, err
	}
	preds := make([]Symbol, 0, len(predValues))
	for _, pv := range predValues {
		p, err := symbolFromValue(pv, "closed_world.cert.scope.predicate")
		if err != nil {
			return StratumPrefix{}, err
		}
		preds = append(preds, p)
	}
	scope := StratumPrefix{Level: level, Predicates: preds}
	if !scope.IsCanonical() {
		return StratumPrefix{}, &DecodeError{Kind: DecodeNotCanonical, Ctx: "closed_world.cert.scope.predicates"}
	}
	return scope, nil
}

func finiteDomainFromValue(v core.Value) (FiniteDomain, error) {
	its, err := decItemsN(v, "closed_world.cert.domain", []int{2})
	if err != nil {
		return FiniteDomain{}, err
	}
	typeTag, err := symbolFromValue(its[0], "closed_world.cert.domain.type_tag")
	if err != nil {
		return FiniteDomain{}, err
	}
	values, err := decItems(its[1], "closed_world.cert.domain.values")
	if err != nil {
		return FiniteDomain{}, err
	}
	domain := FiniteDomain{TypeTag: typeTag, Values: append([]core.Value(nil), values...)}
	if !domain.IsCanonical() {
		return FiniteDomain{}, &DecodeError{Kind: DecodeNotCanonical, Ctx: "closed_world.cert.domain.values"}
	}
	return domain, nil
}

func relationTableFromValue(v core.Value) (RelationTable, error) {
	its, err := decItemsN(v, "closed_world.cert.extension", []int{3})
	if err != nil {
		return RelationTable{}, err
	}
	pred, err := symbolFromValue(its[0], "closed_world.cert.extension.pred")
	if err != nil {
		return RelationTable{}, err
	}
	arity, err := decReadU32(its[1], "closed_world.cert.extension.arity")
	if err != nil {
		return RelationTable{}, err
	}
	rowValues, err := decItems(its[2], "closed_world.cert.extension.rows")
	if err != nil {
		return RelationTable{}, err
	}
	rows := make([]GroundLiteral, 0, len(rowValues))
	for _, rv := range rowValues {
		r, err := groundLiteralFromValue(rv, "closed_world.cert.extension.row")
		if err != nil {
			return RelationTable{}, err
		}
		rows = append(rows, r)
	}
	table := RelationTable{Pred: pred, Arity: arity, Rows: rows}
	if !table.IsCanonical() {
		return RelationTable{}, &DecodeError{Kind: DecodeNotCanonical, Ctx: "closed_world.cert.extension.rows"}
	}
	return table, nil
}

func supportEdgeFromValue(v core.Value) (SupportEdge, error) {
	its, err := decItemsN(v, "closed_world.cert.support", []int{5})
	if err != nil {
		return SupportEdge{}, err
	}
	fact, err := groundLiteralFromValue(its[0], "closed_world.cert.support.fact")
	if err != nil {
		return SupportEdge{}, err
	}
	clause, err := decAtomBytes(its[1], "closed_world.cert.support.clause")
	if err != nil {
		return SupportEdge{}, err
	}
	if !utf8.Valid(clause) {
		return SupportEdge{}, &DecodeError{Kind: DecodeBadUtf8, Ctx: "closed_world.cert.support.clause"}
	}
	subst, err := SubstFromValue(its[2])
	if err != nil {
		return SupportEdge{}, err
	}
	refValues, err := decItems(its[3], "closed_world.cert.support.body_refs")
	if err != nil {
		return SupportEdge{}, err
	}
	refs := make([]SupportRef, 0, len(refValues))
	for _, rv := range refValues {
		r, err := supportRefFromValue(rv)
		if err != nil {
			return SupportEdge{}, err
		}
		refs = append(refs, r)
	}
	rank, err := decReadU32(its[4], "closed_world.cert.support.rank")
	if err != nil {
		return SupportEdge{}, err
	}
	return SupportEdge{Fact: fact, Clause: NewClauseId(string(clause)), Subst: subst, BodyRefs: refs, Rank: rank}, nil
}

func supportRefFromValue(v core.Value) (SupportRef, error) {
	tag, payload, err := decSplitTag(v, "closed_world.cert.support.ref")
	if err != nil {
		return nil, err
	}
	switch string(tag) {
	case "same_stratum":
		p, err := decExpectN(payload, []int{3}, "closed_world.cert.support.ref.same_stratum")
		if err != nil {
			return nil, err
		}
		fact, err := groundLiteralFromValue(p[0], "closed_world.cert.support.ref.fact")
		if err != nil {
			return nil, err
		}
		rank, err := decReadU32(p[1], "closed_world.cert.support.ref.rank")
		if err != nil {
			return nil, err
		}
		return SameStratumRef{Fact: fact, Rank: rank}, nil
	case "lower_stratum":
		p, err := decExpectN(payload, []int{3}, "closed_world.cert.support.ref.lower_stratum")
		if err != nil {
			return nil, err
		}
		cert, err := decReadIndex(p[0], "closed_world.cert.support.ref.cert")
		if err != nil {
			return nil, err
		}
		atom, err := groundLiteralFromValue(p[1], "closed_world.cert.support.ref.atom")
		if err != nil {
			return nil, err
		}
		return LowerStratumRef{Cert: NewCertId(cert), Atom: atom}, nil
	case "builtin":
		p, err := decExpectN(payload, []int{2}, "closed_world.cert.support.ref.builtin")
		if err != nil {
			return nil, err
		}
		atom, err := groundLiteralFromValue(p[0], "closed_world.cert.support.ref.atom")
		if err != nil {
			return nil, err
		}
		return BuiltinRef{Atom: atom}, nil
	case "neg_lower":
		p, err := decExpectN(payload, []int{3}, "closed_world.cert.support.ref.neg_lower")
		if err != nil {
			return nil, err
		}
		cert, err := decReadIndex(p[0], "closed_world.cert.support.ref.cert")
		if err != nil {
			return nil, err
		}
		atom, err := groundLiteralFromValue(p[1], "closed_world.cert.support.ref.atom")
		if err != nil {
			return nil, err
		}
		return NegLowerRef{Cert: NewCertId(cert), Atom: atom}, nil
	case "count_lower":
		p, err := decExpectN(payload, []int{2}, "closed_world.cert.support.ref.count_lower")
		if err != nil {
			return nil, err
		}
		cert, err := decReadIndex(p[0], "closed_world.cert.support.ref.cert")
		if err != nil {
			return nil, err
		}
		return CountLowerRef{Cert: NewCertId(cert)}, nil
	default:
		return nil, &DecodeError{Kind: DecodeUnknownTag, Ctx: "closed_world.cert.support.ref", Tag: string(tag)}
	}
}

func certSizeDeclFromValue(v core.Value) (CertSizeDecl, error) {
	its, err := decItemsN(v, "closed_world.cert.limits_decl", []int{6})
	if err != nil {
		return CertSizeDecl{}, err
	}
	fields := [5]uint64{}
	for i, ctx := range [5]string{
		"closed_world.cert.limits_decl.cert_facts",
		"closed_world.cert.limits_decl.domain_values",
		"closed_world.cert.limits_decl.support_edges",
		"closed_world.cert.limits_decl.rule_groundings",
		"closed_world.cert.limits_decl.join_steps",
	} {
		n, err := decReadIndex(its[i], ctx)
		if err != nil {
			return CertSizeDecl{}, err
		}
		fields[i] = n
	}
	// cert_bytes is a uint64 in the account, so it is read whole: no platform narrowing.
	certBytes, err := decReadIndex(its[5], "closed_world.cert.limits_decl.cert_bytes")
	if err != nil {
		return CertSizeDecl{}, err
	}
	return CertSizeDecl{
		CertFacts:      fields[0],
		DomainValues:   fields[1],
		SupportEdges:   fields[2],
		RuleGroundings: fields[3],
		JoinSteps:      fields[4],
		CertBytes:      certBytes,
	}, nil
}

// ------------------------------- the v1 wrapper -----------------------------

// DerivationWirePayloadV1FromValue decodes the public v1 derivation payload.
func DerivationWirePayloadV1FromValue(v core.Value) (Derivation, error) {
	return DerivationFromValue(v)
}

// DerivationWireV1FromValue unwraps a proof-interchange v1 tagged derivation payload.
func DerivationWireV1FromValue(v core.Value) (Derivation, error) {
	its, err := decItemsN(v, "derivation wire v1", []int{2})
	if err != nil {
		return Derivation{}, err
	}
	tag, err := decAtomBytes(its[0], "derivation wire v1 tag")
	if err != nil {
		return Derivation{}, err
	}
	if string(tag) != DerivationWireV1Tag {
		return Derivation{}, &DecodeError{Kind: DecodeUnknownTag, Ctx: "derivation wire v1", Tag: string(tag)}
	}
	return DerivationFromValue(its[1])
}

// DecodeDerivationWireV1 decodes ontos-codec bytes as a public proof-interchange v1 derivation.
// For bytes the caller trusts; bytes it did not produce go through DecodeDerivationWireV1Bounded.
func DecodeDerivationWireV1(bytes []byte) (Derivation, error) {
	v, err := codec.Decode(bytes)
	if err != nil {
		return Derivation{}, &DecodeError{Kind: DecodeShape, Ctx: "derivation wire v1 bytes"}
	}
	return DerivationWireV1FromValue(v)
}
