// Shelf-B prelude loader — the hash-pinned Horn-clause standard library. [STABLE v1]
// Go sibling of contract/rs/src/prelude.rs (and the TS contract/ts/src/prelude.ts).
//
// ADR 0016 sorts every predefined predicate onto one of three shelves by the question
// "what must be trusted to admit its result?". Shelf B is the answer "nothing new": a
// relation derivable as ordinary Rule | Builtin | Leaf derivations over the Shelf-A
// primitives lives here as CURATED DATA, not a crate — an array of clauses with a
// pinned program_digest, re-checked everywhere by the existing check as plain Rule
// nodes. Zero new trusted code: this file adds no checker logic and no account node
// kind; it only LOADS clauses the engine and checker already understand.
//
// The trust anchor is DIGEST RE-DERIVATION, not the JSON parser. LoadPrelude
// deserializes a manifest, then RECOMPUTES the program_digest over the deserialized
// clauses using the frozen account codec (ClauseBytes -> ProgramDigest) and REJECTS
// any mismatch. A bundle whose pinned digest does not equal the digest of its own
// clauses is refused, so a corrupted or tampered manifest can never load. The frozen
// ontos-codec + syntactic VarId make the digest BYTE-IDENTICAL across {rs,go,ts}, so
// this Go loader recomputes the same hex and refuses the same mismatched bundles as
// the Rust loader (replayed against the shared vectors/prelude.json).
//
// Manifest shape (prelude/<name>@<version>.json):
//
//	{
//	  "name": "sample",
//	  "version": "1.0.0",
//	  "program_digest": "<64-hex sha-256>",
//	  "clauses": [
//	    { "id": "<ClauseId>", "clause": { "head": <goal>, "body": [<body-lit>, ...] } }
//	  ]
//	}
//
// where a term is {"atom":"<hex>"} | {"atom_str":"<utf8>"} | {"tuple":[term…]} |
// {"var":"<id>"}, a goal is {"pred":"<utf8>", "args":[term…]}, and a body literal is a
// positive goal or a negated {"neg":<goal>} (ADR 0007) — exactly the notation of
// vectors/account.json. id is optional; when present it must equal the recomputed
// CanonicalClauseId of the clause.
package contract

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sort"
	"unicode/utf8"
)

// PreludeBundle is a loaded, DIGEST-VERIFIED Shelf-B prelude bundle. Its clauses are
// ordinary account Rule nodes; merge them into a program (Program / MergeInto) and the
// existing check verifies them with no new trusted code. Go sibling of Rust's
// PreludeBundle.
type PreludeBundle struct {
	// Name is the bundle name (e.g. "lists"), the name of prelude/<name>@<version>.json.
	Name string
	// Version is the bundle version (e.g. "1.0.0") — Shelf B is byte-frozen per (name@version).
	Version string
	// ProgramDigest is the pinned, recomputed-and-verified canonical program digest
	// (64-char lowercase hex).
	ProgramDigest string
	// Clauses are the bundle's clauses, in manifest order, each with its (verified)
	// canonical id.
	Clauses []PreludeClause
}

// PreludeClause pairs a clause with its verified canonical id (manifest order).
type PreludeClause struct {
	ID     ClauseId
	Clause Clause
}

// Program returns the bundle as a standalone MapProgram — the prelude clauses keyed by
// id, ready to hand to an engine or check. (MapProgram is order-independent; the DIGEST
// is what commits to the exact clause set.)
func (b *PreludeBundle) Program() *MapProgram {
	program := NewMapProgram()
	for _, pc := range b.Clauses {
		program.Insert(pc.ID, pc.Clause)
	}
	return program
}

// MergeInto is the ADR-0016 PROGRAM-PREPEND: return a new MapProgram containing this
// bundle's clauses PLUS every clause in extra (keyed by id), so a consumer program is
// checked together with the standard library. A consumer clause sharing a prelude id
// (the canonical hash collides ⇒ the clauses are identical) is a harmless overwrite.
// The engine and checker see one clause set; the prelude relations resolve as ordinary
// Rule nodes. (Go's Program interface exposes only Clause(id) lookup, so the caller
// passes the consumer clauses explicitly — mirroring Rust's MergeInto over a Program's
// for_each_clause.)
func (b *PreludeBundle) MergeInto(extra []PreludeClause) *MapProgram {
	merged := b.Program()
	for _, pc := range extra {
		merged.Insert(pc.ID, pc.Clause)
	}
	return merged
}

// PreludeErrorKind is the cross-core error variant tag — byte-identical to the Rust
// PreludeError variant strings and the {"err": "<variant>"} field of vectors/prelude.json.
type PreludeErrorKind string

const (
	// PreludeMalformed: the manifest is not valid JSON, or a required field is missing/mistyped.
	PreludeMalformed PreludeErrorKind = "malformed"
	// PreludeBadClause: a clause could not be deserialized from the account-codec term form.
	PreludeBadClause PreludeErrorKind = "bad_clause"
	// PreludeClauseIDMismatch: a per-clause id was present but did not equal the recomputed canonical id.
	PreludeClauseIDMismatch PreludeErrorKind = "clause_id_mismatch"
	// PreludeDuplicateClauseID: two clauses share the same canonical id.
	PreludeDuplicateClauseID PreludeErrorKind = "duplicate_clause_id"
	// PreludeDigestMismatch: the recomputed program_digest did not match the pinned one — the tamper check.
	PreludeDigestMismatch PreludeErrorKind = "digest_mismatch"
	// PreludeEmpty: the bundle declared no clauses (rejected — its digest is degenerate).
	PreludeEmpty PreludeErrorKind = "empty"
)

// PreludeError is a refusal to trust. Every variant means a bundle that does not load
// is never silently accepted. Go sibling of Rust's PreludeError enum.
type PreludeError struct {
	// Kind is the cross-core variant tag (the vector pins this).
	Kind PreludeErrorKind
	// Index is the offending clause index (for BadClause / ClauseIDMismatch); -1 otherwise.
	Index int
	// Detail is a diagnostic message (not normative; only Kind is pinned cross-core).
	Detail string
	// Declared / Recomputed carry the two hex strings for ClauseIDMismatch / DigestMismatch.
	Declared   string
	Recomputed string
}

func (e *PreludeError) Error() string {
	switch e.Kind {
	case PreludeMalformed:
		return "malformed prelude manifest: " + e.Detail
	case PreludeBadClause:
		return fmt.Sprintf("clause[%d] is malformed: %s", e.Index, e.Detail)
	case PreludeClauseIDMismatch:
		return fmt.Sprintf("clause[%d] id mismatch: declared %s, recomputed %s", e.Index, e.Declared, e.Recomputed)
	case PreludeDuplicateClauseID:
		return "duplicate clause id " + e.Declared
	case PreludeDigestMismatch:
		return fmt.Sprintf("program_digest mismatch: declared %s, recomputed %s", e.Declared, e.Recomputed)
	case PreludeEmpty:
		return "prelude bundle has no clauses"
	default:
		return "prelude error: " + string(e.Kind)
	}
}

func malformed(detail string) *PreludeError {
	return &PreludeError{Kind: PreludeMalformed, Index: -1, Detail: detail}
}

// unrepairedJSONText names what encoding/json would silently repair in `data`: a byte sequence
// that is not UTF-8, or a `\u` escape naming a UTF-16 surrogate that is not half of a high+low
// pair. It returns "" when there is neither. It judges only escapes inside string literals and
// leaves every other malformation to json.Unmarshal, which reports it.
func unrepairedJSONText(data []byte) string {
	if !utf8.Valid(data) {
		return "the document is not valid UTF-8"
	}
	inString := false
	for i := 0; i < len(data); i++ {
		c := data[i]
		switch {
		case !inString:
			inString = c == '"'
		case c == '"':
			inString = false
		case c == '\\':
			if i+1 >= len(data) || data[i+1] != 'u' {
				i++ // a one-character escape, or a truncated one json.Unmarshal reports
				continue
			}
			unit, ok := hexUnit(data, i+2)
			if !ok {
				return "" // a malformed \u escape: json.Unmarshal reports it
			}
			i += 5 // now on the escape's last hex digit
			if unit >= 0xDC00 && unit <= 0xDFFF {
				return fmt.Sprintf(`a lone UTF-16 surrogate escape \u%04x`, unit)
			}
			if unit >= 0xD800 && unit <= 0xDBFF {
				// A high surrogate is well-formed only when a low one's escape follows at once.
				if i+6 < len(data) && data[i+1] == '\\' && data[i+2] == 'u' {
					if low, ok := hexUnit(data, i+3); ok && low >= 0xDC00 && low <= 0xDFFF {
						i += 6
						continue
					}
				}
				return fmt.Sprintf(`a lone UTF-16 surrogate escape \u%04x`, unit)
			}
		}
	}
	return ""
}

// hexUnit reads the four hex digits of a `\u` escape that start at data[at].
func hexUnit(data []byte, at int) (uint16, bool) {
	if at+4 > len(data) {
		return 0, false
	}
	var unit uint16
	for _, c := range data[at : at+4] {
		var digit byte
		switch {
		case c >= '0' && c <= '9':
			digit = c - '0'
		case c >= 'a' && c <= 'f':
			digit = c - 'a' + 10
		case c >= 'A' && c <= 'F':
			digit = c - 'A' + 10
		default:
			return 0, false
		}
		unit = unit<<4 | uint16(digit)
	}
	return unit, true
}

func badClause(index int, detail string) *PreludeError {
	return &PreludeError{Kind: PreludeBadClause, Index: index, Detail: detail}
}

// LoadPrelude loads a Shelf-B prelude manifest, VERIFYING its pinned program_digest
// against the digest recomputed over the deserialized clauses.
//
// On success the returned PreludeBundle is guaranteed: non-empty; free of duplicate
// canonical clause ids; every present per-clause id equals the recomputed
// CanonicalClauseId; and ProgramDigest equals ProgramDigestOfClauses over the bundle's
// clauses (the tamper anchor).
//
// The JSON parser is NOT the trust boundary, but the digest is recomputed over the DECODED
// clauses, so it cannot see a parse that silently decodes the wrong ones (#2233).
// encoding/json does exactly that for a lone UTF-16 surrogate escape or a byte that is not
// UTF-8: it substitutes U+FFFD, so two distinct authored names load as one. Rust's loader
// rejects both, and a parse may only ever REJECT a bundle, so they are refused before decoding.
// Mirrors Rust's load_prelude.
func LoadPrelude(data []byte) (*PreludeBundle, error) {
	if detail := unrepairedJSONText(data); detail != "" {
		return nil, malformed(detail)
	}
	var root map[string]json.RawMessage
	if err := json.Unmarshal(data, &root); err != nil {
		return nil, malformed(err.Error())
	}

	name, err := stringField(root, "name")
	if err != nil {
		return nil, err
	}
	version, err := stringField(root, "version")
	if err != nil {
		return nil, err
	}
	declaredDigest, err := stringField(root, "program_digest")
	if err != nil {
		return nil, err
	}

	clausesRaw, ok := root["clauses"]
	if !ok {
		return nil, malformed("missing field `clauses`")
	}
	var clausesJSON []json.RawMessage
	if err := json.Unmarshal(clausesRaw, &clausesJSON); err != nil {
		return nil, malformed("field `clauses` is not an array")
	}
	if len(clausesJSON) == 0 {
		return nil, &PreludeError{Kind: PreludeEmpty, Index: -1}
	}

	clauses := make([]PreludeClause, 0, len(clausesJSON))
	seen := make(map[string]struct{}, len(clausesJSON))
	for index, entry := range clausesJSON {
		clause, declaredID, hasID, err := parseClauseEntry(index, entry)
		if err != nil {
			return nil, err
		}
		// #2247: a reserved predicate reads exactly like a tagged literal, so it would share that
		// literal's id and the bundle's digest. Refused here, BEFORE the digest check, since a
		// digest match is exactly what such a clause would pass.
		if pred, ok := ReservedPredicateOf(clause); ok {
			return nil, badClause(index, fmt.Sprintf("reserved predicate symbol 0x%x (an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)", pred))
		}
		id := CanonicalClauseId(clause)
		// If the manifest pins a per-clause id, it must equal the recomputed canonical id.
		if hasID && declaredID != id.String() {
			return nil, &PreludeError{
				Kind:       PreludeClauseIDMismatch,
				Index:      index,
				Declared:   declaredID,
				Recomputed: id.String(),
			}
		}
		if _, dup := seen[id.String()]; dup {
			return nil, &PreludeError{Kind: PreludeDuplicateClauseID, Index: -1, Declared: id.String()}
		}
		seen[id.String()] = struct{}{}
		clauses = append(clauses, PreludeClause{ID: id, Clause: clause})
	}

	// Recompute the canonical program digest over the deserialized clauses (the tamper
	// anchor) and refuse a mismatch. The SAME digest definition the checker uses (ADR
	// 0007 §3.1) hashes the bundle — one digest definition, no drift.
	recomputed := programDigestHexOf(clauses)
	if recomputed != declaredDigest {
		return nil, &PreludeError{
			Kind:       PreludeDigestMismatch,
			Index:      -1,
			Declared:   declaredDigest,
			Recomputed: recomputed,
		}
	}

	return &PreludeBundle{
		Name:          name,
		Version:       version,
		ProgramDigest: recomputed,
		Clauses:       clauses,
	}, nil
}

func stringField(obj map[string]json.RawMessage, key string) (string, error) {
	raw, ok := obj[key]
	if !ok {
		return "", malformed("missing field `" + key + "`")
	}
	var s string
	if err := json.Unmarshal(raw, &s); err != nil {
		return "", malformed("field `" + key + "` is not a string")
	}
	return s, nil
}

// parseClauseEntry parses one { "id"?, "clause": { head, body } } wrapper (or a bare
// { "head", "body" } object) into a Clause, returning the clause, the declared id (if
// present), and whether an id was declared.
func parseClauseEntry(index int, entry json.RawMessage) (Clause, string, bool, error) {
	var wrapper struct {
		ID     *json.RawMessage `json:"id"`
		Clause *json.RawMessage `json:"clause"`
	}
	if err := json.Unmarshal(entry, &wrapper); err != nil {
		return Clause{}, "", false, badClause(index, "clause entry is not an object")
	}

	// The clause object is either the nested `clause` field or the bare entry itself.
	clauseRaw := entry
	if wrapper.Clause != nil {
		clauseRaw = *wrapper.Clause
	}

	clause, err := parseClause(index, clauseRaw)
	if err != nil {
		return Clause{}, "", false, err
	}

	declaredID := ""
	hasID := false
	if wrapper.ID != nil {
		if err := json.Unmarshal(*wrapper.ID, &declaredID); err != nil {
			return Clause{}, "", false, badClause(index, "`id` is not a string")
		}
		hasID = true
	}
	return clause, declaredID, hasID, nil
}

// parseClause parses a { "head": <goal>, "body": [<body-lit>…] } into a Clause.
func parseClause(index int, raw json.RawMessage) (Clause, error) {
	var obj struct {
		Head *json.RawMessage   `json:"head"`
		Body *[]json.RawMessage `json:"body"`
	}
	if err := json.Unmarshal(raw, &obj); err != nil {
		return Clause{}, badClause(index, "clause is not an object")
	}
	if obj.Head == nil {
		return Clause{}, badClause(index, "missing `head`")
	}
	head, err := parseGoal(index, *obj.Head)
	if err != nil {
		return Clause{}, err
	}
	body := make([]BodyLit, 0)
	if obj.Body != nil {
		for _, litRaw := range *obj.Body {
			lit, err := parseBodyLit(index, litRaw)
			if err != nil {
				return Clause{}, err
			}
			body = append(body, lit)
		}
	}
	return Clause{Head: head, Body: body}, nil
}

// parseGoal parses a { "pred": "<utf8>", "args": [term…] } goal.
func parseGoal(index int, raw json.RawMessage) (Goal, error) {
	var obj struct {
		Pred *string            `json:"pred"`
		Args *[]json.RawMessage `json:"args"`
	}
	if err := json.Unmarshal(raw, &obj); err != nil {
		return Goal{}, badClause(index, "goal is not an object")
	}
	if obj.Pred == nil {
		return Goal{}, badClause(index, "goal missing string `pred`")
	}
	args := make([]Term, 0)
	if obj.Args != nil {
		for _, argRaw := range *obj.Args {
			arg, err := parseTerm(index, argRaw)
			if err != nil {
				return Goal{}, err
			}
			args = append(args, arg)
		}
	}
	return Goal{Pred: SymbolFromString(*obj.Pred), Args: args}, nil
}

// parseBodyLit parses a positive goal or a negated { "neg": <goal> } body literal (ADR 0007).
func parseBodyLit(index int, raw json.RawMessage) (BodyLit, error) {
	var probe map[string]json.RawMessage
	if err := json.Unmarshal(raw, &probe); err != nil {
		return BodyLit{}, badClause(index, "body literal is not an object")
	}
	if neg, ok := probe["neg"]; ok {
		g, err := parseGoal(index, neg)
		if err != nil {
			return BodyLit{}, err
		}
		return NegLit(g), nil
	}
	g, err := parseGoal(index, raw)
	if err != nil {
		return BodyLit{}, err
	}
	return PosLit(g), nil
}

// parseTerm parses a term: {"atom":"<hex>"} | {"atom_str":"<utf8>"} | {"tuple":[term…]}
// | {"var":"<id>"} — the vectors/account.json notation.
func parseTerm(index int, raw json.RawMessage) (Term, error) {
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		return nil, badClause(index, "term is not an object: "+string(raw))
	}
	if hexRaw, ok := obj["atom"]; ok {
		var s string
		if err := json.Unmarshal(hexRaw, &s); err != nil {
			return nil, badClause(index, "`atom` is not a string")
		}
		bytes, err := hex.DecodeString(s)
		if err != nil {
			return nil, badClause(index, "`atom` is not valid hex: "+err.Error())
		}
		return Atom(bytes), nil
	}
	if strRaw, ok := obj["atom_str"]; ok {
		var s string
		if err := json.Unmarshal(strRaw, &s); err != nil {
			return nil, badClause(index, "`atom_str` is not a string")
		}
		return Atom([]byte(s)), nil
	}
	if varRaw, ok := obj["var"]; ok {
		var s string
		if err := json.Unmarshal(varRaw, &s); err != nil {
			return nil, badClause(index, "`var` is not a string")
		}
		// The loader has already refused non-UTF-8 text and lone-surrogate escapes (#2233), so
		// this cannot refuse; it is ParseVarId all the same, the one VarId test (#3115).
		id, err := ParseVarId(s)
		if err != nil {
			return nil, badClause(index, err.Error())
		}
		return VarFromID(id), nil
	}
	if tupleRaw, ok := obj["tuple"]; ok {
		var children []json.RawMessage
		if err := json.Unmarshal(tupleRaw, &children); err != nil {
			return nil, badClause(index, "`tuple` is not an array")
		}
		out := make([]Term, 0, len(children))
		for _, c := range children {
			child, err := parseTerm(index, c)
			if err != nil {
				return nil, err
			}
			out = append(out, child)
		}
		return Tuple(out...), nil
	}
	return nil, badClause(index, "unrecognized term shape: "+string(raw))
}

// programDigestHexOf is the lowercase-hex canonical program digest of a slice of loaded
// prelude clauses — the value a manifest pins. (The digest depends only on the clause
// SET via ClauseBytes; the per-clause ids are not hashed.)
func programDigestHexOf(clauses []PreludeClause) string {
	cs := make([]Clause, len(clauses))
	for i, pc := range clauses {
		cs[i] = pc.Clause
	}
	digest := ProgramDigest(cs)
	return hex.EncodeToString(digest[:])
}

// BundleDigest is the canonical program_digest (lowercase hex) of a set of clauses —
// the value a manifest pins. Exposed so a prelude GENERATOR can author the
// program_digest field from the same computation the loader verifies against (one
// digest definition, no drift). Mirrors Rust's bundle_digest.
func BundleDigest(clauses []Clause) string {
	digest := ProgramDigest(clauses)
	return hex.EncodeToString(digest[:])
}

// sortByteSlices sorts a slice of byte slices lexicographically (the same total order
// Rust's Vec<Vec<u8>>::sort uses), so the program digest is independent of clause
// enumeration order.
func sortByteSlices(s [][]byte) {
	sort.Slice(s, func(i, j int) bool { return lessBytes(s[i], s[j]) })
}

// lessBytes reports lexicographic byte ordering (a < b), matching Rust's slice Ord.
func lessBytes(a, b []byte) bool {
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
