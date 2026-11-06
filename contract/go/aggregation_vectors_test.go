// Go replay of the cross-core ADR-0023 certifiable-aggregation vector
// vectors/aggregation.json (Phase 5, #585, epic #579). Each hand-authored case is run
// through CheckWithCertContext under the aggregation_v1 profile and asserted against the
// pinned rs oracle outcome. The SAME file drives the rs and ts replays — one oracle (rs,
// per the #464 lesson) pins all three cores byte-identically.
//
// The aggregation_v1 profile (from the vector's note): NO theory (aggNoTheory owns
// nothing); EDB leaves = the top-level `extensional` set attesting an EDB-of-record
// snapshot from the top-level `edb` map (§3.6); Context = unit. The bound context is
// DERIVED (recomputed program_hash + fixed non-zero pins); each cert auto-binds to it.
// Certs are named in a top-level `certs` map and selected per case by `cert` (a key, or
// null ⇒ no cert supplied).
//
// THE CORE GUARANTEE pinned tri-core is `tamper_wrong_k_over_valid_cert`: a derivation
// claiming a wrong k over an otherwise VALID cert MUST be rejected count_mismatch.
package contract

import (
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/Bitspark/logos-contract/contract/go/internal/r3domain"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// ----- the on-disk vector shape -----

type aggVectorFile struct {
	Extensional []string                 `json:"extensional"`
	Edb         map[string][]aggJSONLit  `json:"edb"`
	Program     map[string]aggJSONClause `json:"program"`
	Certs       map[string]aggJSONCert   `json:"certs"`
	Cases       []aggCase                `json:"cases"`
}

type aggCase struct {
	Name  string     `json:"name"`
	Claim aggJSONLit `json:"claim"`
	Cert  *string    `json:"cert"`
	// Certs (#2258 L3.3b) names the closed world as an ORDERED list of keys into certs
	// (index = position), instead of the single Cert.
	Certs      []string `json:"certs"`
	Derivation struct {
		Nodes []aggJSONNode `json:"nodes"`
		Root  uint64        `json:"root"`
	} `json:"derivation"`
	// An optional per-case limits override (issue #253): every key is a checker budget by the name
	// CheckLimits.Budgets gives it, read by one reader (#3376's class), and an absent key keeps its
	// default.
	Limits  map[string]int  `json:"limits"`
	Outcome json.RawMessage `json:"outcome"`
}

type aggJSONTerm struct {
	AtomStr *string       `json:"atom_str"`
	Tuple   []aggJSONTerm `json:"tuple"`
	Var     *string       `json:"var"`
	Int     *int64        `json:"int"`
	// Decimal (#2813) is the canonical ontos decimal embedding (#331, the term.json notation), for
	// the frozen decimal-column rows and the non-int k row.
	Decimal *string `json:"decimal"`
}

func (j aggJSONTerm) build(t *testing.T) Term {
	switch {
	case j.AtomStr != nil:
		return Atom([]byte(*j.AtomStr))
	case j.Var != nil:
		return Var(*j.Var)
	case j.Int != nil:
		return FromValue(aggIntV(*j.Int))
	case j.Decimal != nil:
		d, ok := decFromString(*j.Decimal)
		if !ok {
			t.Fatalf("decimal %q is not a decimal literal", *j.Decimal)
		}
		return FromValue(d.toDecimalTerm())
	case j.Tuple != nil:
		children := make([]Term, len(j.Tuple))
		for i, c := range j.Tuple {
			children[i] = c.build(t)
		}
		return Tuple(children...)
	default:
		t.Fatalf("term must be atom_str/var/int/decimal/tuple: %+v", j)
		return nil
	}
}

func (j aggJSONTerm) buildValue(t *testing.T) core.Value {
	gv, ok := j.build(t).EraseGround()
	if !ok {
		t.Fatalf("value must be ground: %+v", j)
	}
	return gv
}

type aggJSONLit struct {
	Pred string        `json:"pred"`
	Args []aggJSONTerm `json:"args"`
}

func (j aggJSONLit) buildGoal(t *testing.T) Goal {
	args := make([]Term, len(j.Args))
	for i, a := range j.Args {
		args[i] = a.build(t)
	}
	return Goal{Pred: SymbolFromString(j.Pred), Args: args}
}

func (j aggJSONLit) buildGround(t *testing.T) GroundLiteral {
	gl, ok := j.buildGoal(t).AsGround()
	if !ok {
		t.Fatalf("literal must be ground: %+v", j)
	}
	return gl
}

type aggJSONPredRef struct {
	Name  string `json:"name"`
	Arity uint32 `json:"arity"`
}

// project is "rows" (a JSON string) or {"distinct"|"sum"|"min"|"max": <attr>} (#587).
func aggProjectFromJSON(t *testing.T, raw json.RawMessage) ProjectSpec {
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

// a clause body literal: a positive goal, or a count_lit count body literal.
type aggJSONBodyLit struct {
	Pred     string           `json:"pred"`
	Args     []aggJSONTerm    `json:"args"`
	CountLit *aggJSONCountLit `json:"count_lit"`
}

type aggJSONCountLit struct {
	Pred    aggJSONPredRef       `json:"pred"`
	Filter  []aggJSONFilterEntry `json:"filter"`
	Project json.RawMessage      `json:"project"`
	Count   aggJSONTerm          `json:"count"`
}

// a filter entry binds a position to either a var (clause body) or a ground value (premise).
type aggJSONFilterEntry struct {
	Pos     uint32       `json:"pos"`
	Var     *string      `json:"var"`
	AtomStr *string      `json:"atom_str"`
	Value   *aggJSONTerm `json:"value"`
}

func (j aggJSONBodyLit) build(t *testing.T) BodyLit {
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
			Project: aggProjectFromJSON(t, j.CountLit.Project),
			Count:   j.CountLit.Count.build(t),
		})
	}
	return PosLit(aggJSONLit{Pred: j.Pred, Args: j.Args}.buildGoal(t))
}

type aggJSONClause struct {
	Head aggJSONLit       `json:"head"`
	Body []aggJSONBodyLit `json:"body"`
}

// a derivation premise: a bare positive node index, or a {count:..} count premise.
type aggJSONPremise struct {
	pos     uint64
	isCount bool
	count   aggJSONCountPremise
}

type aggJSONCountPremise struct {
	Pred    aggJSONPredRef       `json:"pred"`
	Filter  []aggJSONFilterEntry `json:"filter"`
	Project json.RawMessage      `json:"project"`
	// K is a bare int (the canonical int embedding) or, #2813, any value in the term notation (a
	// non-int claim). Raw, so a missing or ill-shaped k fails the replay instead of decoding to 0.
	K    json.RawMessage `json:"k"`
	Cert uint64          `json:"cert"`
}

// aggPremiseK decodes a count premise's k: a bare JSON int, or a term object.
func aggPremiseK(t *testing.T, raw json.RawMessage) core.Value {
	// json.Unmarshal accepts null into an int64 as a no-op, so absence and null are refused first.
	if len(raw) == 0 || string(raw) == "null" {
		t.Fatalf("count k is missing or null")
	}
	var n int64
	if err := json.Unmarshal(raw, &n); err == nil {
		return aggIntV(n)
	}
	var term aggJSONTerm
	if raw[0] != '{' || json.Unmarshal(raw, &term) != nil {
		t.Fatalf("count k must be an int or a term object, got %q", string(raw))
	}
	return term.buildValue(t)
}

func (p *aggJSONPremise) UnmarshalJSON(dataB []byte) error {
	var n int
	if err := json.Unmarshal(dataB, &n); err == nil {
		p.pos = uint64(n)
		return nil
	}
	var wrap struct {
		Count *aggJSONCountPremise `json:"count"`
	}
	if err := json.Unmarshal(dataB, &wrap); err != nil {
		return err
	}
	p.isCount = true
	p.count = *wrap.Count
	return nil
}

func (p aggJSONPremise) build(t *testing.T) Premise {
	if !p.isCount {
		return PosNode(p.pos)
	}
	filter := make([]GroundFilterEntry, len(p.count.Filter))
	for i, e := range p.count.Filter {
		if e.Value == nil {
			t.Fatalf("count premise filter entry must carry a ground value: %+v", e)
		}
		filter[i] = GroundFilterEntry{Pos: e.Pos, Value: e.Value.buildValue(t)}
	}
	return CountPremise{
		Pred:    NewPredicateRef(SymbolFromString(p.count.Pred.Name), p.count.Pred.Arity),
		Filter:  filter,
		Project: aggProjectFromJSON(t, p.count.Project),
		K:       aggPremiseK(t, p.count.K),
		Cert:    NewCertId(p.count.Cert),
	}
}

type aggJSONNode struct {
	Kind       string                 `json:"kind"`
	Conclusion aggJSONLit             `json:"conclusion"`
	Clause     string                 `json:"clause"`
	Subst      map[string]aggJSONTerm `json:"subst"`
	Premises   []aggJSONPremise       `json:"premises"`
}

func (j aggJSONNode) build(t *testing.T) Node {
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

type aggJSONCert struct {
	Scope struct {
		Level      uint32   `json:"level"`
		Predicates []string `json:"predicates"`
	} `json:"scope"`
	Domains []struct {
		TypeTag string        `json:"type_tag"`
		Values  []aggJSONTerm `json:"values"`
	} `json:"domains"`
	Extensions []struct {
		Pred  string       `json:"pred"`
		Arity uint32       `json:"arity"`
		Rows  []aggJSONLit `json:"rows"`
	} `json:"extensions"`
	// #2258 L3.3b: a stacked cert carries support edges and may seal PARTIAL.
	Supports     []aggJSONSupportEdge `json:"supports"`
	PartialScope *struct {
		Level      uint32   `json:"level"`
		Predicates []string `json:"predicates"`
	} `json:"partial_scope"`
	LimitsDecl struct {
		CertFacts      uint64 `json:"cert_facts"`
		DomainValues   uint64 `json:"domain_values"`
		SupportEdges   uint64 `json:"support_edges"`
		RuleGroundings uint64 `json:"rule_groundings"`
		JoinSteps      uint64 `json:"join_steps"`
		CertBytes      uint64 `json:"cert_bytes"`
	} `json:"limits_decl"`
}

func (j aggJSONCert) build(t *testing.T, derived CertContext) ClosedModelCert {
	preds := make([]Symbol, len(j.Scope.Predicates))
	for i, p := range j.Scope.Predicates {
		preds[i] = SymbolFromString(p)
	}
	domains := make([]FiniteDomain, len(j.Domains))
	for i, d := range j.Domains {
		vals := make([]core.Value, len(d.Values))
		for k, vv := range d.Values {
			vals[k] = vv.buildValue(t)
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
	for i, e := range j.Supports {
		edges[i] = e.build(t)
	}
	var partial *StratumPrefix
	if j.PartialScope != nil {
		pp := make([]Symbol, len(j.PartialScope.Predicates))
		for i, q := range j.PartialScope.Predicates {
			pp[i] = SymbolFromString(q)
		}
		partial = &StratumPrefix{Level: j.PartialScope.Level, Predicates: pp}
	}
	return ClosedModelCert{
		// Verbatim, NOT NewStratumPrefix (see the domains note above).
		Scope:            StratumPrefix{Level: j.Scope.Level, Predicates: preds},
		ProgramHash:      derived.ProgramHash,
		ProfileHash:      derived.ProfileHash,
		CtxHash:          derived.CtxHash,
		TheoryConfigHash: derived.TheoryConfigHash,
		Domains:          domains,
		Extensions:       extensions,
		Supports:         SupportWitness{Edges: edges},
		Closure:          ClosureWitness{},
		PartialScope:     partial,
		LimitsDecl: CertSizeDecl{
			CertFacts:      j.LimitsDecl.CertFacts,
			DomainValues:   j.LimitsDecl.DomainValues,
			SupportEdges:   j.LimitsDecl.SupportEdges,
			RuleGroundings: j.LimitsDecl.RuleGroundings,
			JoinSteps:      j.LimitsDecl.JoinSteps,
			CertBytes:      j.LimitsDecl.CertBytes,
		},
	}
}

// aggJSONSupportEdge is a support edge (#2258 L3.3b): {fact, clause, subst, body_refs, rank}.
type aggJSONSupportEdge struct {
	Fact     aggJSONLit             `json:"fact"`
	Clause   string                 `json:"clause"`
	Subst    map[string]aggJSONTerm `json:"subst"`
	BodyRefs []aggJSONSupportRef    `json:"body_refs"`
	Rank     uint32                 `json:"rank"`
}

// aggJSONSupportRef is one of same_stratum / lower_stratum / builtin / neg_lower / count_lower.
type aggJSONSupportRef struct {
	SameStratum *struct {
		Fact aggJSONLit `json:"fact"`
		Rank uint32     `json:"rank"`
	} `json:"same_stratum"`
	LowerStratum *struct {
		Cert uint64     `json:"cert"`
		Atom aggJSONLit `json:"atom"`
	} `json:"lower_stratum"`
	Builtin *struct {
		Atom aggJSONLit `json:"atom"`
	} `json:"builtin"`
	NegLower *struct {
		Cert uint64     `json:"cert"`
		Atom aggJSONLit `json:"atom"`
	} `json:"neg_lower"`
	CountLower *struct {
		Cert uint64 `json:"cert"`
	} `json:"count_lower"`
}

func (j aggJSONSupportRef) build(t *testing.T) SupportRef {
	switch {
	case j.SameStratum != nil:
		return SameStratumRef{Fact: j.SameStratum.Fact.buildGround(t), Rank: j.SameStratum.Rank}
	case j.LowerStratum != nil:
		return LowerStratumRef{Cert: NewCertId(j.LowerStratum.Cert), Atom: j.LowerStratum.Atom.buildGround(t)}
	case j.Builtin != nil:
		return BuiltinRef{Atom: j.Builtin.Atom.buildGround(t)}
	case j.NegLower != nil:
		return NegLowerRef{Cert: NewCertId(j.NegLower.Cert), Atom: j.NegLower.Atom.buildGround(t)}
	case j.CountLower != nil:
		return CountLowerRef{Cert: NewCertId(j.CountLower.Cert)}
	default:
		t.Fatalf("unknown support ref")
		return nil
	}
}

func (j aggJSONSupportEdge) build(t *testing.T) SupportEdge {
	subst := make(Subst, len(j.Subst))
	for name, term := range j.Subst {
		subst[NewVarId(name)] = term.build(t)
	}
	refs := make([]SupportRef, len(j.BodyRefs))
	for i, r := range j.BodyRefs {
		refs[i] = r.build(t)
	}
	return SupportEdge{Fact: j.Fact.buildGround(t), Clause: NewClauseId(j.Clause), Subst: subst, BodyRefs: refs, Rank: j.Rank}
}

// ----- helpers -----

func aggIntV(n int64) core.Value { return data.EncodeInt(big.NewInt(n)) }

func aggVecPin(b byte) Hash {
	var h Hash
	for i := range h {
		h[i] = b
	}
	return h
}

func loadAggVectors(t *testing.T) aggVectorFile {
	t.Helper()
	dir, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}
	var path string
	for d := dir; ; {
		candidate := filepath.Join(d, "vectors", "aggregation.json")
		if _, err := os.Stat(candidate); err == nil {
			path = candidate
			break
		}
		parent := filepath.Dir(d)
		if parent == d {
			t.Fatalf("could not locate vectors/aggregation.json above %s", dir)
		}
		d = parent
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var vf aggVectorFile
	if err := json.Unmarshal(raw, &vf); err != nil {
		t.Fatalf("unmarshal %s: %v", path, err)
	}
	return vf
}

func aggExpectedOutcome(t *testing.T, raw json.RawMessage) string {
	var s string
	if err := json.Unmarshal(raw, &s); err == nil {
		return s
	}
	var rej struct {
		Reject string `json:"reject"`
	}
	if err := json.Unmarshal(raw, &rej); err != nil {
		t.Fatalf("bad outcome %s: %v", string(raw), err)
	}
	return "reject:" + rej.Reject
}

// TestAggregationVectors replays every vectors/aggregation.json case through the trusted
// CheckWithCertContext and asserts the pinned rs oracle outcome (#585, epic #579).
func TestAggregationVectors(t *testing.T) {
	vf := loadAggVectors(t)

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

	derived := NewCertContext(ProgramDigestOf(program), aggVecPin(1), aggVecPin(2), aggVecPin(3))

	if len(vf.Cases) == 0 {
		t.Fatal("no aggregation cases loaded")
	}
	// #2569 control: at least one case must reach the memo's verification, or the
	// miss-then-hit assertion below would hold of a memo that never filled.
	memoizedWorlds := 0
	names := make([]string, 0, len(vf.Cases))
	for _, c := range vf.Cases {
		names = append(names, c.Name)
	}
	domain := r3domain.Domain(t, "aggregation.json", names)
	raised := r3domain.Raised(t)
	for _, c := range vf.Cases {
		t.Run(c.Name, func(t *testing.T) {
			nodes := make([]Node, len(c.Derivation.Nodes))
			for i, nj := range c.Derivation.Nodes {
				nodes[i] = nj.build(t)
			}
			var closedWorld []ClosedModelCert
			if len(c.Certs) > 0 {
				for _, key := range c.Certs {
					cj, ok := vf.Certs[key]
					if !ok {
						t.Fatalf("case %q names unknown cert %q", c.Name, key)
					}
					closedWorld = append(closedWorld, cj.build(t, derived))
				}
			} else if c.Cert != nil {
				cj, ok := vf.Certs[*c.Cert]
				if !ok {
					t.Fatalf("case %q names unknown cert %q", c.Name, *c.Cert)
				}
				closedWorld = []ClosedModelCert{cj.build(t, derived)}
			}
			// #2605 (seat:caa's condition 3): the length reading equals the encoding it measures.
			for _, cert := range closedWorld {
				assertLengthReading2605(t, c.Name, cert)
			}
			deriv := NewDerivationWithClosedWorld(nodes, c.Derivation.Root, closedWorld)

			limits := DefaultLimits()
			for key, value := range c.Limits {
				found := false
				for _, budget := range limits.Budgets() {
					if budget.Name == key {
						*budget.Value = value
						found = true
					}
				}
				if !found {
					t.Fatalf("case %q: unknown budget %q", c.Name, key)
				}
			}
			profile := &CheckProfile[unitCtx]{
				Theory: aggNoTheory{},
				Leaves: negVectorLeaves{extensional: extensional, edb: edb},
				Admit:  AlwaysAdmit[unitCtx]{},
				Limits: limits,
			}

			got := CheckWithCertContext[unitCtx](program, c.Claim.buildGround(t), deriv, unitCtx{}, profile, derived)

			gotStr := negOutcomeString(got)
			want := aggExpectedOutcome(t, c.Outcome)
			if gotStr != want {
				t.Fatalf("case %q: got %q, want %q (detail: %s)", c.Name, gotStr, want, got.Detail())
			}

			// R3 (#2733, the checker's arm): an accepted case stays accepted under each raised
			// budget, alone and together, to the declared table's value.
			if domain[c.Name] {
				for _, rb := range limits.EachBudgetRaised(raised) {
					raisedProfile := *profile
					raisedProfile.Limits = rb.Limits
					again := CheckWithCertContext[unitCtx](program, c.Claim.buildGround(t), deriv, unitCtx{}, &raisedProfile, derived)
					if s := negOutcomeString(again); s != gotStr {
						t.Fatalf("case %q: raising %s changed the verdict to %q", c.Name, rb.Name, s)
					}
				}
			}

			// #2569: the memoized check gives the same verdict on its miss and on its hit, and the
			// hit verifies nothing.
			memo := NewWorldMemo[unitCtx](program, profile, unitCtx{}, derived)
			for pass := 0; pass < 2; pass++ {
				m := CheckWithWorldMemo(memo, c.Claim.buildGround(t), deriv)
				if s := negOutcomeString(m); s != gotStr {
					t.Fatalf("case %q: memo pass %d gave %q, the plain check %q", c.Name, pass, s, gotStr)
				}
			}
			switch v := memo.CertificatesVerified(); v {
			case 0:
			case len(closedWorld):
				memoizedWorlds++
			default:
				t.Fatalf("case %q: memo verified %d certificates over two passes, want 0 or %d", c.Name, v, len(closedWorld))
			}
		})
	}
	if memoizedWorlds == 0 {
		t.Fatal("no aggregation case reached the memo's verification: the miss-then-hit check is vacuous")
	}
}
