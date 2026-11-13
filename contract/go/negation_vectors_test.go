// Go replay of the cross-core ADR-0007 certifiable-stratified-negation vector
// vectors/negation.json (issues #424, #422). Each of the 20 hand-authored cases is
// run through Check / CheckWithCertContext under the negation_v1 profile and asserted
// against the pinned oracle outcome. The SAME file drives the differential CLI harness
// (conformance/) and the Rust replay — one oracle pins both cores.
//
// The negation_v1 profile (from the vector's note): lt theory (lt(a,b) Holds iff a<b
// bytewise); EDB leaves = the top-level `extensional` set, attesting an EDB-of-record
// snapshot from the top-level `edb` map (§3.6); Context = unit. The bound context is
// DERIVED (recomputed program_hash + fixed non-zero profile/ctx/theory pins); each cert
// is auto-bound to it unless it sets an explicit pin (the mismatch cases). A case with
// plain_check:true calls the plain Check() (unbound zero context).
package contract

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ----- the on-disk vector shape (mirrors the conformance CLI's negation decoders) -----

type negVectorFile struct {
	Extensional []string                 `json:"extensional"`
	Edb         map[string][]negJSONLit  `json:"edb"`
	Program     map[string]negJSONClause `json:"program"`
	Cases       []negCase                `json:"cases"`
}

type negCase struct {
	Name        string         `json:"name"`
	Claim       negJSONLit     `json:"claim"`
	PlainCheck  bool           `json:"plain_check"`
	CertContext *negJSONPins   `json:"cert_context"`
	Limits      *negJSONLimits `json:"limits"`
	Derivation  struct {
		Nodes       []negJSONNode `json:"nodes"`
		Root        int           `json:"root"`
		ClosedWorld []negJSONCert `json:"closed_world"`
	} `json:"derivation"`
	Outcome json.RawMessage `json:"outcome"`
	// Report, where the row states one, is check()'s exact report (#4206): counters_version and
	// the 17 counters by their snake_case names, hand-computed from the rules in report.rs.
	Report map[string]any `json:"report"`
}

type negJSONPins struct {
	ProgramHash      *string `json:"program_hash"`
	ProfileHash      *string `json:"profile_hash"`
	CtxHash          *string `json:"ctx_hash"`
	TheoryConfigHash *string `json:"theory_config_hash"`
	// ADR 0029 D10: the decomposition the run is bound to; absent = an ordinary whole-program run.
	DecompositionWitness *string `json:"decomposition_witness"`
}

type negJSONLimits struct {
	MaxNodes          *int `json:"max_nodes"`
	MaxDepth          *int `json:"max_depth"`
	MaxTermDepth      *int `json:"max_term_depth"`
	MaxCertBytes      *int `json:"max_cert_bytes"`
	MaxCertFacts      *int `json:"max_cert_facts"`
	MaxDomainValues   *int `json:"max_domain_values"`
	MaxSupportEdges   *int `json:"max_support_edges"`
	MaxRuleGroundings *int `json:"max_rule_groundings"`
	MaxJoinSteps      *int `json:"max_join_steps"`
}

type negJSONTerm struct {
	Atom    *string       `json:"atom"`
	AtomStr *string       `json:"atom_str"`
	Tuple   []negJSONTerm `json:"tuple"`
	Var     *string       `json:"var"`
}

func (j negJSONTerm) build(t *testing.T) Term {
	switch {
	case j.Atom != nil:
		b, err := hex.DecodeString(*j.Atom)
		if err != nil {
			t.Fatalf("bad hex %q: %v", *j.Atom, err)
		}
		return Atom(b)
	case j.AtomStr != nil:
		return Atom([]byte(*j.AtomStr))
	case j.Var != nil:
		return Var(*j.Var)
	case j.Tuple != nil:
		children := make([]Term, len(j.Tuple))
		for i, c := range j.Tuple {
			children[i] = c.build(t)
		}
		return Tuple(children...)
	default:
		t.Fatalf("term must be atom/atom_str/tuple/var: %+v", j)
		return nil
	}
}

type negJSONLit struct {
	Pred string        `json:"pred"`
	Args []negJSONTerm `json:"args"`
}

func (j negJSONLit) buildGoal(t *testing.T) Goal {
	args := make([]Term, len(j.Args))
	for i, a := range j.Args {
		args[i] = a.build(t)
	}
	return Goal{Pred: SymbolFromString(j.Pred), Args: args}
}

func (j negJSONLit) buildGround(t *testing.T) GroundLiteral {
	gl, ok := j.buildGoal(t).AsGround()
	if !ok {
		t.Fatalf("literal must be ground: %+v", j)
	}
	return gl
}

type negJSONBodyLit struct {
	Pred     string           `json:"pred"`
	Args     []negJSONTerm    `json:"args"`
	Neg      *negJSONLit      `json:"neg"`
	CountLit *negJSONCountLit `json:"count_lit"`
}

func (j negJSONBodyLit) build(t *testing.T) BodyLit {
	if j.Neg != nil {
		return NegLit(j.Neg.buildGoal(t))
	}
	// ADR 0023 count body literal — the aggregation vectors' `count_lit` form, admitted here
	// for ADR 0030 G2's count-over-partial case (the first count premise in negation.json).
	if j.CountLit != nil {
		filter := make([]CountFilterEntry, len(j.CountLit.Filter))
		for i, e := range j.CountLit.Filter {
			var term Term
			switch {
			case e.Var != nil:
				term = Var(*e.Var)
			case e.AtomStr != nil:
				term = Atom([]byte(*e.AtomStr))
			default:
				t.Fatalf("count_lit filter entry must bind a var/atom_str: %+v", e)
			}
			filter[i] = CountFilterEntry{Pos: e.Pos, Term: term}
		}
		return CountLitBody(CountLit{
			Pred:    NewPredicateRef(SymbolFromString(j.CountLit.Pred.Name), j.CountLit.Pred.Arity),
			Filter:  filter,
			Project: negProjectFromJSON(t, j.CountLit.Project),
			Count:   j.CountLit.Count.build(t),
		})
	}
	return PosLit(negJSONLit{Pred: j.Pred, Args: j.Args}.buildGoal(t))
}

// The count-premise authoring forms, mirrored from aggregation_vectors_test.go (ADR 0023).
type negJSONPredRef struct {
	Name  string `json:"name"`
	Arity uint32 `json:"arity"`
}

// a filter entry binds a position to either a var/atom (clause body) or a ground value (premise).
type negJSONFilterEntry struct {
	Pos     uint32       `json:"pos"`
	Var     *string      `json:"var"`
	AtomStr *string      `json:"atom_str"`
	Value   *negJSONTerm `json:"value"`
}

type negJSONCountLit struct {
	Pred    negJSONPredRef       `json:"pred"`
	Filter  []negJSONFilterEntry `json:"filter"`
	Project json.RawMessage      `json:"project"`
	Count   negJSONTerm          `json:"count"`
}

type negJSONCountPremise struct {
	Pred    negJSONPredRef       `json:"pred"`
	Filter  []negJSONFilterEntry `json:"filter"`
	Project json.RawMessage      `json:"project"`
	K       int64                `json:"k"`
	Cert    int                  `json:"cert"`
}

// project is "rows" (a JSON string) or {"distinct"|"sum"|"min"|"max": <attr>} (#587).
func negProjectFromJSON(t *testing.T, raw json.RawMessage) ProjectSpec {
	var s string
	if err := json.Unmarshal(raw, &s); err == nil {
		if s == "rows" {
			return Rows()
		}
		t.Fatalf("unknown project string %q", s)
	}
	var d struct {
		Distinct *uint32 `json:"distinct"`
		Sum      *uint32 `json:"sum"`
		Min      *uint32 `json:"min"`
		Max      *uint32 `json:"max"`
	}
	if err := json.Unmarshal(raw, &d); err != nil {
		t.Fatalf("project must be 'rows' or {distinct|sum|min|max:<attr>}: %s", string(raw))
	}
	switch {
	case d.Distinct != nil:
		return Distinct(*d.Distinct)
	case d.Sum != nil:
		return Sum(*d.Sum)
	case d.Min != nil:
		return Min(*d.Min)
	case d.Max != nil:
		return Max(*d.Max)
	}
	t.Fatalf("project must be 'rows' or {distinct|sum|min|max:<attr>}: %s", string(raw))
	return ProjectSpec{}
}

// the canonical ontos-data int value for a count premise's k.
func negIntV(n int64) core.Value { return data.EncodeInt(big.NewInt(n)) }

type negJSONClause struct {
	Head negJSONLit       `json:"head"`
	Body []negJSONBodyLit `json:"body"`
}

type negJSONPremise struct {
	pos    int
	isNeg  bool
	negVal struct {
		Atom      negJSONLit `json:"atom"`
		Cert      int        `json:"cert"`
		Nonmember string     `json:"nonmember"`
	}
	isCount bool
	count   negJSONCountPremise
}

func (p *negJSONPremise) UnmarshalJSON(raw []byte) error {
	var n int
	if err := json.Unmarshal(raw, &n); err == nil {
		p.pos = n
		return nil
	}
	var wrap struct {
		Neg *struct {
			Atom      negJSONLit `json:"atom"`
			Cert      int        `json:"cert"`
			Nonmember string     `json:"nonmember"`
		} `json:"neg"`
		Count *negJSONCountPremise `json:"count"`
	}
	if err := json.Unmarshal(raw, &wrap); err != nil {
		return err
	}
	// ADR 0023 count premise (`{count: {pred, filter, project, k, cert}}`), admitted here for
	// ADR 0030 G2's count-over-partial case.
	if wrap.Count != nil {
		p.isCount = true
		p.count = *wrap.Count
		return nil
	}
	if wrap.Neg == nil {
		return fmt.Errorf("premise must be an int, {neg:...} or {count:...}: %s", string(raw))
	}
	p.isNeg = true
	p.negVal = *wrap.Neg
	return nil
}

func (p negJSONPremise) build(t *testing.T) Premise {
	if p.isCount {
		filter := make([]GroundFilterEntry, len(p.count.Filter))
		for i, e := range p.count.Filter {
			if e.Value == nil {
				t.Fatalf("count premise filter entry must carry a ground value: %+v", e)
			}
			gv, ok := e.Value.build(t).EraseGround()
			if !ok {
				t.Fatalf("count premise filter value must be ground: %+v", e)
			}
			filter[i] = GroundFilterEntry{Pos: e.Pos, Value: gv}
		}
		return CountPremise{
			Pred:    NewPredicateRef(SymbolFromString(p.count.Pred.Name), p.count.Pred.Arity),
			Filter:  filter,
			Project: negProjectFromJSON(t, p.count.Project),
			K:       negIntV(p.count.K),
			Cert:    NewCertId(uint64(p.count.Cert)),
		}
	}
	if !p.isNeg {
		return PosNode(uint64(p.pos))
	}
	return NegPremise{
		Atom:      p.negVal.Atom.buildGround(t),
		Cert:      NewCertId(uint64(p.negVal.Cert)),
		Nonmember: DirectLookup,
	}
}

type negJSONNode struct {
	Kind       string                 `json:"kind"`
	Conclusion negJSONLit             `json:"conclusion"`
	Clause     string                 `json:"clause"`
	Subst      map[string]negJSONTerm `json:"subst"`
	Premises   []negJSONPremise       `json:"premises"`
}

func (j negJSONNode) build(t *testing.T) Node {
	conc := j.Conclusion.buildGround(t)
	switch j.Kind {
	case "rule":
		subst := make(Subst, len(j.Subst))
		for name, term := range j.Subst {
			subst[NewVarId(name)] = term.build(t)
		}
		premises := make([]Premise, len(j.Premises))
		for i, p := range j.Premises {
			premises[i] = p.build(t)
		}
		return RuleNode{Conc: conc, Clause: NewClauseId(j.Clause), Subst: subst, Premises: premises, Meta: NoMeta()}
	case "builtin":
		return BuiltinNode{Conc: conc}
	case "leaf":
		return LeafNode{Conc: conc, Evidence: NoEvidence()}
	default:
		t.Fatalf("unknown node kind %q", j.Kind)
		return nil
	}
}

type negJSONSupportRef struct {
	SameStratum *struct {
		Fact negJSONLit `json:"fact"`
		Rank uint32     `json:"rank"`
	} `json:"same_stratum"`
	LowerStratum *struct {
		Cert int        `json:"cert"`
		Atom negJSONLit `json:"atom"`
	} `json:"lower_stratum"`
	Builtin *struct {
		Atom negJSONLit `json:"atom"`
	} `json:"builtin"`
	NegLower *struct {
		Cert int        `json:"cert"`
		Atom negJSONLit `json:"atom"`
	} `json:"neg_lower"`
}

func (j negJSONSupportRef) build(t *testing.T) SupportRef {
	switch {
	case j.SameStratum != nil:
		return SameStratumRef{Fact: j.SameStratum.Fact.buildGround(t), Rank: j.SameStratum.Rank}
	case j.LowerStratum != nil:
		return LowerStratumRef{Cert: NewCertId(uint64(j.LowerStratum.Cert)), Atom: j.LowerStratum.Atom.buildGround(t)}
	case j.Builtin != nil:
		return BuiltinRef{Atom: j.Builtin.Atom.buildGround(t)}
	case j.NegLower != nil:
		return NegLowerRef{Cert: NewCertId(uint64(j.NegLower.Cert)), Atom: j.NegLower.Atom.buildGround(t)}
	default:
		t.Fatalf("support ref must be same_stratum/lower_stratum/builtin/neg_lower")
		return nil
	}
}

type negJSONCert struct {
	ProgramHash      *string `json:"program_hash"`
	ProfileHash      *string `json:"profile_hash"`
	CtxHash          *string `json:"ctx_hash"`
	TheoryConfigHash *string `json:"theory_config_hash"`
	// ADR 0029 D10: the slice seal. Absent = every pre-D10 cert (pins the COMPLETE program).
	DecompositionWitness *string  `json:"decomposition_witness"`
	EdbSnapshotHashes    []string `json:"edb_snapshot_hashes"`
	Scope                struct {
		Level      uint32   `json:"level"`
		Predicates []string `json:"predicates"`
	} `json:"scope"`
	// ADR 0030 D1: the partial sub-scope. Absent = every table exact (every pre-0030 cert).
	PartialScope *struct {
		Level      uint32   `json:"level"`
		Predicates []string `json:"predicates"`
	} `json:"partial_scope"`
	Domains []struct {
		TypeTag string        `json:"type_tag"`
		Values  []negJSONTerm `json:"values"`
	} `json:"domains"`
	Extensions []struct {
		Pred  string       `json:"pred"`
		Arity uint32       `json:"arity"`
		Rows  []negJSONLit `json:"rows"`
	} `json:"extensions"`
	Supports []struct {
		Fact     negJSONLit             `json:"fact"`
		Clause   string                 `json:"clause"`
		Subst    map[string]negJSONTerm `json:"subst"`
		BodyRefs []negJSONSupportRef    `json:"body_refs"`
		Rank     uint32                 `json:"rank"`
	} `json:"supports"`
	LimitsDecl struct {
		CertFacts      int    `json:"cert_facts"`
		DomainValues   int    `json:"domain_values"`
		SupportEdges   int    `json:"support_edges"`
		RuleGroundings int    `json:"rule_groundings"`
		JoinSteps      int    `json:"join_steps"`
		CertBytes      uint64 `json:"cert_bytes"`
	} `json:"limits_decl"`
}

func negHashFromHex(t *testing.T, s string) Hash {
	var h Hash
	b, err := hex.DecodeString(s)
	if err != nil {
		t.Fatalf("bad hash hex %q: %v", s, err)
	}
	for i := 0; i < len(b) && i < 32; i++ {
		h[i] = b[i]
	}
	return h
}

func (j negJSONCert) build(t *testing.T, derived CertContext) ClosedModelCert {
	preds := make([]Symbol, len(j.Scope.Predicates))
	for i, p := range j.Scope.Predicates {
		preds[i] = SymbolFromString(p)
	}
	domains := make([]FiniteDomain, len(j.Domains))
	for i, d := range j.Domains {
		vals := make([]core.Value, len(d.Values))
		for k, v := range d.Values {
			gv, ok := v.build(t).EraseGround()
			if !ok {
				t.Fatalf("domain value must be ground")
			}
			vals[k] = gv
		}
		// Verbatim, NOT NewFiniteDomain: the loader must carry the vector's collection
		// order as authored, or a non-canonical case (issue #839) is silently repaired
		// before it can reach the gate it exists to pin.
		domains[i] = FiniteDomain{TypeTag: SymbolFromString(d.TypeTag), Values: vals}
	}
	extensions := make([]RelationTable, len(j.Extensions))
	for i, e := range j.Extensions {
		rows := make([]GroundLiteral, len(e.Rows))
		for k, r := range e.Rows {
			rows[k] = r.buildGround(t)
		}
		// Verbatim, NOT NewRelationTable (see the domains note above).
		extensions[i] = RelationTable{Pred: SymbolFromString(e.Pred), Arity: e.Arity, Rows: rows}
	}
	edges := make([]SupportEdge, len(j.Supports))
	for i, s := range j.Supports {
		subst := make(Subst, len(s.Subst))
		for name, term := range s.Subst {
			subst[NewVarId(name)] = term.build(t)
		}
		refs := make([]SupportRef, len(s.BodyRefs))
		for k, r := range s.BodyRefs {
			refs[k] = r.build(t)
		}
		edges[i] = SupportEdge{Fact: s.Fact.buildGround(t), Clause: NewClauseId(s.Clause), Subst: subst, BodyRefs: refs, Rank: s.Rank}
	}
	var edbHashes []Hash
	for _, h := range j.EdbSnapshotHashes {
		edbHashes = append(edbHashes, negHashFromHex(t, h))
	}
	pin := func(p *string, fallback Hash) Hash {
		if p == nil {
			return fallback
		}
		return negHashFromHex(t, *p)
	}
	var witness *Hash
	if j.DecompositionWitness != nil {
		w := negHashFromHex(t, *j.DecompositionWitness)
		witness = &w
	}
	var partial *StratumPrefix
	if j.PartialScope != nil {
		ps := make([]Symbol, len(j.PartialScope.Predicates))
		for i, p := range j.PartialScope.Predicates {
			ps[i] = SymbolFromString(p)
		}
		// Verbatim, NOT NewStratumPrefix — the loader carries the vector's order as authored.
		partial = &StratumPrefix{Level: j.PartialScope.Level, Predicates: ps}
	}
	return ClosedModelCert{
		// Verbatim, NOT NewStratumPrefix (see the domains note above).
		Scope:             StratumPrefix{Level: j.Scope.Level, Predicates: preds},
		ProgramHash:       pin(j.ProgramHash, derived.ProgramHash),
		ProfileHash:       pin(j.ProfileHash, derived.ProfileHash),
		CtxHash:           pin(j.CtxHash, derived.CtxHash),
		TheoryConfigHash:  pin(j.TheoryConfigHash, derived.TheoryConfigHash),
		EdbSnapshotHashes: edbHashes,
		Domains:           domains,
		Extensions:        extensions,
		Supports:          SupportWitness{Edges: edges},
		Closure:           ClosureWitness{},
		// D10: a POINTER, read from the vector when present. Silence here would be the Go hazard
		// this whole file exists for — a nil that compiles and exercises nothing.
		DecompositionWitness: witness,
		PartialScope:         partial, // ADR 0030 D1, read from the vector when present
		LimitsDecl: CertSizeDecl{
			CertFacts:      uint64(j.LimitsDecl.CertFacts),
			DomainValues:   uint64(j.LimitsDecl.DomainValues),
			SupportEdges:   uint64(j.LimitsDecl.SupportEdges),
			RuleGroundings: uint64(j.LimitsDecl.RuleGroundings),
			JoinSteps:      uint64(j.LimitsDecl.JoinSteps),
			CertBytes:      j.LimitsDecl.CertBytes,
		},
	}
}

// ----- the negation_v1 profile (mirrors the CLI / Rust) -----

// test-double: consumer(the negation vector EDB with snapshots)
type negVectorLeaves struct {
	extensional *PredicateSet
	edb         map[string][]GroundLiteral
}

func (n negVectorLeaves) Extensional() *PredicateSet { return n.extensional }

func (negVectorLeaves) Verify(_ GroundLiteral, _ Evidence, _ unitCtx) LeafOutcome {
	return LeafAdmit{}
}

func (n negVectorLeaves) EdbSnapshot(pred Symbol, _ unitCtx) (Hash, bool) {
	if rows, ok := n.edb[string(pred.Bytes())]; ok {
		return EdbTableHash(pred, rows), true
	}
	if n.extensional.Contains(pred) {
		return EdbTableHash(pred, nil), true
	}
	return Hash{}, false
}

func negVectorPin(b byte) Hash {
	var h Hash
	for i := range h {
		h[i] = b
	}
	return h
}

func loadNegVectors(t *testing.T) negVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "negation.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/negation.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf negVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

// expectedOutcome decodes a case's pinned outcome: "accept" or {"reject":"<code>"}.
func expectedOutcome(t *testing.T, raw json.RawMessage) string {
	var s string
	if err := json.Unmarshal(raw, &s); err == nil {
		return s // "accept"
	}
	var rej struct {
		Reject string `json:"reject"`
	}
	if err := json.Unmarshal(raw, &rej); err != nil {
		t.Fatalf("bad outcome %s: %v", string(raw), err)
	}
	return "reject:" + rej.Reject
}

// TestNegationVectors replays every vectors/negation.json case through the trusted
// Check and asserts the pinned oracle outcome (issues #424, #422).
func TestNegationVectors(t *testing.T) {
	vf := loadNegVectors(t)

	program := NewMapProgram()
	for id, clause := range vf.Program {
		body := make([]BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build(t)
		}
		program.Insert(NewClauseId(id), NewClauseLits(clause.Head.buildGoal(t), body...))
	}

	extensional := NewPredicateSet()
	for _, p := range vf.Extensional {
		extensional.Insert(SymbolFromString(p))
	}
	edb := make(map[string][]GroundLiteral, len(vf.Edb))
	for pred, rows := range vf.Edb {
		grounds := make([]GroundLiteral, len(rows))
		for i, r := range rows {
			grounds[i] = r.buildGround(t)
		}
		edb[pred] = grounds
	}

	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))

	if len(vf.Cases) == 0 {
		t.Fatal("no negation cases loaded")
	}
	// #4206: the report pin is vacuous if no row states a report.
	reports := 0
	for _, c := range vf.Cases {
		if c.Report != nil {
			reports++
		}
	}
	if reports == 0 {
		t.Fatal("no negation case states a report (#4206): the report pin would be vacuous")
	}
	for _, c := range vf.Cases {
		t.Run(c.Name, func(t *testing.T) {
			nodes := make([]Node, len(c.Derivation.Nodes))
			for i, nj := range c.Derivation.Nodes {
				nodes[i] = nj.build(t)
			}
			closedWorld := make([]ClosedModelCert, len(c.Derivation.ClosedWorld))
			for i, cj := range c.Derivation.ClosedWorld {
				closedWorld[i] = cj.build(t, derived)
			}
			// #2605 (seat:caa's condition 3): the length reading equals the encoding it measures.
			for _, cert := range closedWorld {
				assertLengthReading2605(t, c.Name, cert)
			}
			deriv := NewDerivationWithClosedWorld(nodes, uint64(c.Derivation.Root), closedWorld)

			limits := DefaultLimits()
			if c.Limits != nil {
				setLimitIf(&limits.MaxNodes, c.Limits.MaxNodes)
				setLimitIf(&limits.MaxDepth, c.Limits.MaxDepth)
				setLimitIf(&limits.MaxTermDepth, c.Limits.MaxTermDepth)
				setLimitIf(&limits.MaxCertBytes, c.Limits.MaxCertBytes)
				setLimitIf(&limits.MaxCertFacts, c.Limits.MaxCertFacts)
				setLimitIf(&limits.MaxDomainValues, c.Limits.MaxDomainValues)
				setLimitIf(&limits.MaxSupportEdges, c.Limits.MaxSupportEdges)
				setLimitIf(&limits.MaxRuleGroundings, c.Limits.MaxRuleGroundings)
				setLimitIf(&limits.MaxJoinSteps, c.Limits.MaxJoinSteps)
			}
			profile := &CheckProfile[unitCtx]{
				Theory: ltTheory{},
				Leaves: negVectorLeaves{extensional: extensional, edb: edb},
				Admit:  AlwaysAdmit[unitCtx]{},
				Limits: limits,
			}

			cx := derived
			if c.CertContext != nil {
				if c.CertContext.ProgramHash != nil {
					cx.ProgramHash = negHashFromHex(t, *c.CertContext.ProgramHash)
				}
				if c.CertContext.ProfileHash != nil {
					cx.ProfileHash = negHashFromHex(t, *c.CertContext.ProfileHash)
				}
				if c.CertContext.CtxHash != nil {
					cx.CtxHash = negHashFromHex(t, *c.CertContext.CtxHash)
				}
				if c.CertContext.TheoryConfigHash != nil {
					cx.TheoryConfigHash = negHashFromHex(t, *c.CertContext.TheoryConfigHash)
				}
				if c.CertContext.DecompositionWitness != nil {
					cx = cx.WithDecomposition(negHashFromHex(t, *c.CertContext.DecompositionWitness))
				}
			}

			var got Outcome
			if c.PlainCheck {
				got = Check[unitCtx](program, c.Claim.buildGround(t), deriv, unitCtx{}, profile)
			} else {
				got = CheckWithCertContext[unitCtx](program, c.Claim.buildGround(t), deriv, unitCtx{}, profile, cx)
			}

			gotStr := negOutcomeString(got)
			want := expectedOutcome(t, c.Outcome)
			if gotStr != want {
				t.Fatalf("case %q: got %q, want %q (detail: %s)", c.Name, gotStr, want, got.Verdict.Detail())
			}
			if c.Report != nil {
				assertVectorReport(t, c.Name, got.Report, c.Report)
			}

			// #2569: the memoized check gives the same verdict on its miss and on its hit, and the
			// hit verifies nothing: the world is verified in full once, or never (a precheck refused).
			if !c.PlainCheck {
				memo := NewWorldMemo[unitCtx](program, profile, unitCtx{}, cx)
				for pass := 0; pass < 2; pass++ {
					m := CheckWithWorldMemo(memo, c.Claim.buildGround(t), deriv)
					if s := negOutcomeString(m); s != gotStr {
						t.Fatalf("case %q: memo pass %d gave %q, the plain check %q", c.Name, pass, s, gotStr)
					}
				}
				if v := memo.CertificatesVerified(); v != 0 && v != len(closedWorld) {
					t.Fatalf("case %q: memo verified %d certificates over two passes, want 0 or %d", c.Name, v, len(closedWorld))
				}
			}
		})
	}
}

// assertVectorReport asserts a row's stated report (#4206) against check()'s: counters_version and
// every one of the 17 counters by its snake_case name. A counter the row states as an integer is
// pinned exactly; one it states as "counted" (its value depends on the checker's order of work) must
// be counted, and its value is not pinned. A row states all of them, so a counter the row omits, or
// a name no counter has, fails too.
func assertVectorReport(t *testing.T, name string, got CheckReport, want map[string]any) {
	t.Helper()
	counters := []struct {
		name  string
		count ReportCount
	}{
		{"nodes_walked", got.NodesWalked},
		{"rule_nodes", got.RuleNodes},
		{"builtin_nodes", got.BuiltinNodes},
		{"leaf_nodes", got.LeafNodes},
		{"premises_pos", got.PremisesPos},
		{"premises_neg", got.PremisesNeg},
		{"theory_decisions", got.TheoryDecisions},
		{"leaf_verifications", got.LeafVerifications},
		{"admissibility_checks", got.AdmissibilityChecks},
		{"certs_verified", got.CertsVerified},
		{"certs_memo_hits", got.CertsMemoHits},
		{"cert_tables_read", got.CertTablesRead},
		{"cert_rows_read", got.CertRowsRead},
		{"join_steps_used", got.JoinStepsUsed},
		{"groundings_enumerated", got.GroundingsEnumerated},
		{"max_depth_reached", got.MaxDepthReached},
		{"max_term_depth_reached", got.MaxTermDepthReached},
	}
	if v, ok := want["counters_version"].(float64); !ok || int(v) != int(got.CountersVersion) {
		t.Errorf("case %q: report.counters_version = %d, the row states %v", name, got.CountersVersion, want["counters_version"])
	}
	for _, c := range counters {
		w, ok := want[c.name]
		if !ok {
			t.Errorf("case %q: the row's report does not state %s", name, c.name)
			continue
		}
		n, counted := c.count.Get()
		if s, isText := w.(string); isText {
			if s != "counted" || !counted {
				t.Errorf("case %q: report.%s = %v, the row states %q", name, c.name, c.count, s)
			}
			continue
		}
		if f, isNum := w.(float64); !isNum || !counted || n != int(f) {
			t.Errorf("case %q: report.%s = %v, the row states %v", name, c.name, c.count, w)
		}
	}
	if len(want) != len(counters)+1 {
		t.Errorf("case %q: the row's report states %d keys, want counters_version and the %d counters", name, len(want), len(counters))
	}
}

func negOutcomeString(o Outcome) string {
	if o.IsAccept() {
		return "accept"
	}
	return "reject:" + o.Verdict.Code().Code()
}

func setLimitIf(dst *int, src *int) {
	if src != nil {
		*dst = *src
	}
}
