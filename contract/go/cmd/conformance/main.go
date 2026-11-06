// Command conformance is the Go conformance CLI — a dev/CI artifact, NOT part of the
// contract package's imported API. It implements the `conformance v1` protocol
// (ADR 0006): `conformance <family>` reads the family's vector JSON on stdin and
// writes one NDJSON line per case to stdout, in input order, baking in the demo_v1
// profile and ignoring any expected outcome/id in the input. The language-agnostic
// harness (conformance/harness.mjs) drives this and the rs/ts CLIs as black boxes and
// asserts each line against the hand-authored oracle.
//
//	check   : in  {program, cases:[{name, claim, derivation, limits?}]}
//	          out {"name":…,"outcome":"accept"|{"reject":"<code>"}}
//	account : in  {clauses:[{name, head, body}]}
//	          out {"name":…,"id":"<hex>"}
//
// The theory-decision families (arithmetic, list, term, text, compound) share one shape:
//
//	<theory> : in  {identity, owns, decisions:[{name, pred, args}]}
//	           out one {"name":…,"outcome":"holds"|{"fails":"<code>"}} line per decision,
//	                then {"name":"__identity__","outcome":"<config_digest_hex>"} pinning the
//	                theory's identity config digest (zero for the single theories, the
//	                ordered-membership digest for compound).
package main

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"

	contract "github.com/Bitspark/logos-contract/contract/go"
	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// =================== demo_v1 profile (baked in) ===================
// Mirrors contract/go/vectors_test.go; identical behaviour, no *testing.T.

type unitCtx = struct{}

type ltTheory struct{}

func (ltTheory) Owns(pred contract.Symbol) bool { return pred.Equal(contract.SymbolFromString("lt")) }

// Completion: #3142, every lt decision completes (a byte comparison).
func (ltTheory) Completion(contract.Symbol) contract.DecisionCompletion {
	return contract.DecisionStopsAreTyped{}
}

func (ltTheory) Decide(atom contract.GroundLiteral) contract.TheoryOutcome {
	if len(atom.Args) != 2 {
		return contract.TheoryFails{Code: "lt_arity"}
	}
	a, aok := atom.Args[0].(core.Atom)
	b, bok := atom.Args[1].(core.Atom)
	if aok && bok && bytesLess(a.Bytes(), b.Bytes()) {
		return contract.TheoryHolds{}
	}
	return contract.TheoryFails{Code: "not_less_than"}
}

func bytesLess(a, b []byte) bool {
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

type edgeLeaves struct {
	extensional *contract.PredicateSet
}

func newEdgeLeaves() edgeLeaves { return edgeLeaves{extensional: contract.PredicateSetOf("edge")} }

func (e edgeLeaves) Extensional() *contract.PredicateSet { return e.extensional }

func (edgeLeaves) Verify(_ contract.GroundLiteral, _ contract.Evidence, _ unitCtx) contract.LeafOutcome {
	return contract.LeafAdmit{}
}

func demoProfile(limits contract.CheckLimits) *contract.CheckProfile[unitCtx] {
	return &contract.CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: newEdgeLeaves(),
		Admit:  contract.AlwaysAdmit[unitCtx]{},
		Limits: limits,
	}
}

// ===================== authoring notation -> contract types ====================
// Panics on malformed input (this is a CLI fed hand-authored vectors, not a library).

type jsonTerm struct {
	Atom    *string    `json:"atom"`
	AtomStr *string    `json:"atom_str"`
	Tuple   []jsonTerm `json:"tuple"`
	Var     *string    `json:"var"`
	Nest    *jsonNest  `json:"nest"`
}

// jsonNest is #2731's {nest: {functor, times, leaf}}: functor(functor(...leaf...)), Times levels
// around Leaf, expanded by a loop, so a term past any JSON parser's nesting limit is authored flat.
type jsonNest struct {
	Functor string   `json:"functor"`
	Times   int      `json:"times"`
	Leaf    jsonTerm `json:"leaf"`
}

func (j jsonTerm) build() contract.Term {
	switch {
	case j.Atom != nil:
		b, err := hex.DecodeString(*j.Atom)
		if err != nil {
			panic(fmt.Sprintf("bad hex %q: %v", *j.Atom, err))
		}
		return contract.Atom(b)
	case j.AtomStr != nil:
		return contract.Atom([]byte(*j.AtomStr))
	case j.Var != nil:
		return contract.Var(*j.Var)
	case j.Tuple != nil:
		children := make([]contract.Term, len(j.Tuple))
		for i, c := range j.Tuple {
			children[i] = c.build()
		}
		return contract.Tuple(children...)
	case j.Nest != nil:
		t := j.Nest.Leaf.build()
		for i := 0; i < j.Nest.Times; i++ {
			t = contract.Tuple(contract.Atom([]byte(j.Nest.Functor)), t)
		}
		return t
	default:
		panic(fmt.Sprintf("term must be atom/atom_str/tuple/var/nest: %+v", j))
	}
}

type jsonGoal struct {
	Pred string     `json:"pred"`
	Args []jsonTerm `json:"args"`
}

func (j jsonGoal) buildGoal() contract.Goal {
	args := make([]contract.Term, len(j.Args))
	for i, a := range j.Args {
		args[i] = a.build()
	}
	return contract.Goal{Pred: contract.SymbolFromString(j.Pred), Args: args}
}

func (j jsonGoal) buildGround() contract.GroundLiteral {
	gl, ok := j.buildGoal().AsGround()
	if !ok {
		panic(fmt.Sprintf("conclusion/claim must be ground: %+v", j))
	}
	return gl
}

type jsonNode struct {
	Kind       string              `json:"kind"`
	Conclusion jsonGoal            `json:"conclusion"`
	Clause     string              `json:"clause"`
	Subst      map[string]jsonTerm `json:"subst"`
	Premises   []jsonPremise       `json:"premises"`
}

// jsonPremise decodes one Rule premise: a bare int is a positive premise (so existing
// all-positive check.json bodies decode unchanged), and {neg:{atom,cert,nonmember}} is
// a negated premise discharged against a closed-model certificate (ADR 0007).
type jsonPremise struct {
	pos     uint64
	isNeg   bool
	negVal  jsonNegPremise
	isCount bool
	count   jsonCountPremise
}

type jsonNegPremise struct {
	Atom      jsonGoal `json:"atom"`
	Cert      uint64   `json:"cert"`
	Nonmember string   `json:"nonmember"`
}

// The ADR 0023 count forms — the aggregation vectors' authoring notation, admitted in the
// negation family for ADR 0030 G2's count-over-partial case (negation.json's first count).
type jsonPredRef struct {
	Name  string `json:"name"`
	Arity uint32 `json:"arity"`
}

// a filter entry binds a position to either a var/atom (clause body) or a ground value (premise).
type jsonFilterEntry struct {
	Pos     uint32    `json:"pos"`
	Var     *string   `json:"var"`
	AtomStr *string   `json:"atom_str"`
	Value   *jsonTerm `json:"value"`
}

type jsonCountLit struct {
	Pred    jsonPredRef       `json:"pred"`
	Filter  []jsonFilterEntry `json:"filter"`
	Project json.RawMessage   `json:"project"`
	Count   jsonTerm          `json:"count"`
}

type jsonCountPremise struct {
	Pred    jsonPredRef       `json:"pred"`
	Filter  []jsonFilterEntry `json:"filter"`
	Project json.RawMessage   `json:"project"`
	K       int64             `json:"k"`
	Cert    uint64            `json:"cert"`
}

// projectFromJSON: "rows" (a JSON string) or {"distinct"|"sum"|"min"|"max": <attr>} (#587).
func projectFromJSON(raw json.RawMessage) contract.ProjectSpec {
	var s string
	if err := json.Unmarshal(raw, &s); err == nil {
		if s == "rows" {
			return contract.Rows()
		}
		panic(fmt.Sprintf("unknown project string %q", s))
	}
	var d struct {
		Distinct *uint32 `json:"distinct"`
		Sum      *uint32 `json:"sum"`
		Min      *uint32 `json:"min"`
		Max      *uint32 `json:"max"`
	}
	if err := json.Unmarshal(raw, &d); err != nil {
		panic(fmt.Sprintf("project must be 'rows' or {distinct|sum|min|max:<attr>}: %s", string(raw)))
	}
	switch {
	case d.Distinct != nil:
		return contract.Distinct(*d.Distinct)
	case d.Sum != nil:
		return contract.Sum(*d.Sum)
	case d.Min != nil:
		return contract.Min(*d.Min)
	case d.Max != nil:
		return contract.Max(*d.Max)
	}
	panic(fmt.Sprintf("project must be 'rows' or {distinct|sum|min|max:<attr>}: %s", string(raw)))
}

func (p *jsonPremise) UnmarshalJSON(raw []byte) error {
	// A bare integer is a positive premise.
	var n int
	if err := json.Unmarshal(raw, &n); err == nil {
		p.pos = uint64(n)
		p.isNeg = false
		return nil
	}
	var wrap struct {
		Neg   *jsonNegPremise   `json:"neg"`
		Count *jsonCountPremise `json:"count"`
	}
	if err := json.Unmarshal(raw, &wrap); err != nil {
		return err
	}
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

func (p jsonPremise) build() contract.Premise {
	if p.isCount {
		filter := make([]contract.GroundFilterEntry, len(p.count.Filter))
		for i, e := range p.count.Filter {
			if e.Value == nil {
				panic(fmt.Sprintf("count premise filter entry must carry a ground value: %+v", e))
			}
			gv, ok := e.Value.build().EraseGround()
			if !ok {
				panic(fmt.Sprintf("count premise filter value must be ground: %+v", e))
			}
			filter[i] = contract.GroundFilterEntry{Pos: e.Pos, Value: gv}
		}
		return contract.CountPremise{
			Pred:    contract.NewPredicateRef(contract.SymbolFromString(p.count.Pred.Name), p.count.Pred.Arity),
			Filter:  filter,
			Project: projectFromJSON(p.count.Project),
			K:       data.EncodeInt(big.NewInt(p.count.K)),
			Cert:    contract.NewCertId(p.count.Cert),
		}
	}
	if !p.isNeg {
		return contract.PosNode(p.pos)
	}
	nonmember := contract.DirectLookup
	if p.negVal.Nonmember != "" && p.negVal.Nonmember != "direct_lookup" {
		panic("unknown nonmember proof " + p.negVal.Nonmember)
	}
	return contract.NegPremise{
		Atom:      p.negVal.Atom.buildGround(),
		Cert:      contract.NewCertId(p.negVal.Cert),
		Nonmember: nonmember,
	}
}

func (j jsonNode) build() contract.Node {
	conclusion := j.Conclusion.buildGround()
	switch j.Kind {
	case "rule":
		subst := make(contract.Subst, len(j.Subst))
		for name, term := range j.Subst {
			subst[contract.NewVarId(name)] = term.build()
		}
		premises := make([]contract.Premise, len(j.Premises))
		for i, p := range j.Premises {
			premises[i] = p.build()
		}
		return contract.RuleNode{
			Conc:     conclusion,
			Clause:   contract.NewClauseId(j.Clause),
			Subst:    subst,
			Premises: premises,
			Meta:     contract.NoMeta(),
		}
	case "builtin":
		return contract.BuiltinNode{Conc: conclusion}
	case "leaf":
		return contract.LeafNode{Conc: conclusion, Evidence: contract.NoEvidence()}
	default:
		panic("unknown node kind " + j.Kind)
	}
}

type jsonClause struct {
	Head jsonGoal      `json:"head"`
	Body []jsonBodyLit `json:"body"`
}

// jsonBodyLit decodes one body literal: a bare goal {pred, args} is positive (so
// existing all-positive check.json/account.json bodies decode byte-identically), and
// {neg: <goal>} is a negated body literal (ADR 0007). Mirrors Rust's
// body_lit_from_json.
type jsonBodyLit struct {
	Pred     string        `json:"pred"`
	Args     []jsonTerm    `json:"args"`
	Neg      *jsonGoal     `json:"neg"`
	CountLit *jsonCountLit `json:"count_lit"`
}

func (j jsonBodyLit) build() contract.BodyLit {
	if j.Neg != nil {
		return contract.NegLit(j.Neg.buildGoal())
	}
	// ADR 0023 count body literal (`count_lit`), admitted in the negation family for ADR 0030 G2.
	if j.CountLit != nil {
		filter := make([]contract.CountFilterEntry, len(j.CountLit.Filter))
		for i, e := range j.CountLit.Filter {
			switch {
			case e.Var != nil:
				filter[i] = contract.CountFilterEntry{Pos: e.Pos, Term: jsonTerm{Var: e.Var}.build()}
			case e.AtomStr != nil:
				filter[i] = contract.CountFilterEntry{Pos: e.Pos, Term: jsonTerm{AtomStr: e.AtomStr}.build()}
			default:
				panic(fmt.Sprintf("count_lit filter entry must bind a var/atom_str: %+v", e))
			}
		}
		return contract.CountLitBody(contract.CountLit{
			Pred:    contract.NewPredicateRef(contract.SymbolFromString(j.CountLit.Pred.Name), j.CountLit.Pred.Arity),
			Filter:  filter,
			Project: projectFromJSON(j.CountLit.Project),
			Count:   j.CountLit.Count.build(),
		})
	}
	return contract.PosLit(jsonGoal{Pred: j.Pred, Args: j.Args}.buildGoal())
}

// ================================ output =====================================

type checkResult struct {
	Name    string `json:"name"`
	Outcome any    `json:"outcome"`
}

type accountResult struct {
	Name string `json:"name"`
	ID   string `json:"id"`
}

func emit(v any) {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	fmt.Println(string(b))
}

// ================================ families ===================================

func runCheck(data []byte) {
	var doc struct {
		Program map[string]jsonClause `json:"program"`
		Cases   []struct {
			Name       string      `json:"name"`
			Claim      jsonGoal    `json:"claim"`
			Limits     *jsonLimits `json:"limits"`
			Derivation struct {
				Nodes []jsonNode `json:"nodes"`
				Root  uint64     `json:"root"`
			} `json:"derivation"`
		} `json:"cases"`
	}
	if err := json.Unmarshal(data, &doc); err != nil {
		panic(err)
	}

	program := contract.NewMapProgram()
	for id, clause := range doc.Program {
		body := make([]contract.BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build()
		}
		program.Insert(contract.NewClauseId(id), contract.NewClauseLits(clause.Head.buildGoal(), body...))
	}

	for _, c := range doc.Cases {
		nodes := make([]contract.Node, len(c.Derivation.Nodes))
		for i, nj := range c.Derivation.Nodes {
			nodes[i] = nj.build()
		}
		deriv := contract.NewDerivation(nodes, c.Derivation.Root)
		limits := c.Limits.apply(contract.DefaultLimits())
		got := contract.Check[unitCtx](program, c.Claim.buildGround(), deriv, unitCtx{}, demoProfile(limits))
		var outcome any
		if got.IsAccept() {
			outcome = "accept"
		} else {
			outcome = map[string]string{"reject": got.Code().Code()}
		}
		emit(checkResult{Name: c.Name, Outcome: outcome})
	}
}

func runAccount(data []byte) {
	var doc struct {
		Clauses []struct {
			Name string        `json:"name"`
			Head jsonGoal      `json:"head"`
			Body []jsonBodyLit `json:"body"`
		} `json:"clauses"`
	}
	if err := json.Unmarshal(data, &doc); err != nil {
		panic(err)
	}
	for _, c := range doc.Clauses {
		// Body literals may be bare goals (Pos) or {neg: <goal>} (Neg); existing
		// all-positive account vectors decode byte-identically.
		body := make([]contract.BodyLit, len(c.Body))
		for i, b := range c.Body {
			body[i] = b.build()
		}
		id := contract.CanonicalClauseId(contract.NewClauseLits(c.Head.buildGoal(), body...))
		emit(accountResult{Name: c.Name, ID: id.String()})
	}
}

// ===================== negation family (ADR 0007) ============================
// Like check, but each derivation carries closed_world certificates, premises may be
// {neg:{...}}, body literals may be {neg:<goal>}. The bound context is DERIVED
// (recomputed program_hash + fixed non-zero pins). A cert with no explicit pins in the
// vector is auto-bound to the derived context (the honest case); a cert that sets a pin
// keeps it (the mismatch cases). A case with "plain_check":true calls the plain
// Check() (zero/unbound context). Mirrors the Rust CLI's run_negation byte-for-byte.

// The fixed non-zero profile/ctx/theory pins the negation_v1 profile binds (the
// program_hash is recomputed from the live program). Byte-identical to Rust's
// NEG_PROFILE_PIN / NEG_CTX_PIN / NEG_THEORY_PIN.
func negPin(b byte) contract.Hash {
	var h contract.Hash
	for i := range h {
		h[i] = b
	}
	return h
}

// negLeaves declares the vector's extensional set and attests an EDB-of-record snapshot
// from the vector's edb map (ADR 0007 §3.6). It implements both LeafVerifier and the
// optional EdbSnapshotProvider.
type negLeaves struct {
	extensional *contract.PredicateSet
	edb         map[string][]contract.GroundLiteral
}

func (n negLeaves) Extensional() *contract.PredicateSet { return n.extensional }

func (negLeaves) Verify(_ contract.GroundLiteral, _ contract.Evidence, _ unitCtx) contract.LeafOutcome {
	return contract.LeafAdmit{}
}

func (n negLeaves) EdbSnapshot(pred contract.Symbol, _ unitCtx) (contract.Hash, bool) {
	if rows, ok := n.edb[string(pred.Bytes())]; ok {
		return contract.EdbTableHash(pred, rows), true
	}
	if n.extensional.Contains(pred) {
		return contract.EdbTableHash(pred, nil), true
	}
	return contract.Hash{}, false
}

// negationTheory is the negation_v1 profile's theory: lt for the builtin support refs, and since
// #3126 the standard arithmetic theory beside it, so vectors/theory_not_decided.json can state a
// literal the theory does not decide. No negation-family vector names an arithmetic predicate as a
// relation, so the verdicts of negation.json and exact_claims.json do not move.
func negationTheory() contract.CompoundTheory {
	return contract.NewCompoundTheory(ltTheory{}, contract.NewArithmeticTheory())
}

func negationProfile(limits contract.CheckLimits, extensional *contract.PredicateSet, edb map[string][]contract.GroundLiteral) *contract.CheckProfile[unitCtx] {
	return &contract.CheckProfile[unitCtx]{
		Theory: negationTheory(),
		Leaves: negLeaves{extensional: extensional, edb: edb},
		Admit:  contract.AlwaysAdmit[unitCtx]{},
		Limits: limits,
	}
}

// hashFromHex reads a 32-byte hash from up-to-64 lowercase-hex chars, padding the rest
// with zero (so a vector can write a short value for pins it does not care about).
func hashFromHex(s string) contract.Hash {
	var h contract.Hash
	b, err := hex.DecodeString(s)
	if err != nil {
		panic(fmt.Sprintf("bad hash hex %q: %v", s, err))
	}
	for i := 0; i < len(b) && i < 32; i++ {
		h[i] = b[i]
	}
	return h
}

type jsonSupportRef struct {
	SameStratum *struct {
		Fact jsonGoal `json:"fact"`
		Rank uint32   `json:"rank"`
	} `json:"same_stratum"`
	LowerStratum *struct {
		Cert uint64   `json:"cert"`
		Atom jsonGoal `json:"atom"`
	} `json:"lower_stratum"`
	Builtin *struct {
		Atom jsonGoal `json:"atom"`
	} `json:"builtin"`
	NegLower *struct {
		Cert uint64   `json:"cert"`
		Atom jsonGoal `json:"atom"`
	} `json:"neg_lower"`
	CountLower *struct {
		Cert uint64 `json:"cert"`
	} `json:"count_lower"`
}

func (j jsonSupportRef) build() contract.SupportRef {
	switch {
	case j.SameStratum != nil:
		return contract.SameStratumRef{Fact: j.SameStratum.Fact.buildGround(), Rank: j.SameStratum.Rank}
	case j.LowerStratum != nil:
		return contract.LowerStratumRef{Cert: contract.NewCertId(j.LowerStratum.Cert), Atom: j.LowerStratum.Atom.buildGround()}
	case j.Builtin != nil:
		return contract.BuiltinRef{Atom: j.Builtin.Atom.buildGround()}
	case j.NegLower != nil:
		return contract.NegLowerRef{Cert: contract.NewCertId(j.NegLower.Cert), Atom: j.NegLower.Atom.buildGround()}
	case j.CountLower != nil:
		return contract.CountLowerRef{Cert: contract.NewCertId(j.CountLower.Cert)}
	default:
		panic("support ref must be same_stratum/lower_stratum/builtin/neg_lower/count_lower")
	}
}

type jsonCert struct {
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
		TypeTag string     `json:"type_tag"`
		Values  []jsonTerm `json:"values"`
	} `json:"domains"`
	Extensions []struct {
		Pred  string     `json:"pred"`
		Arity uint32     `json:"arity"`
		Rows  []jsonGoal `json:"rows"`
	} `json:"extensions"`
	Supports []struct {
		Fact     jsonGoal            `json:"fact"`
		Clause   string              `json:"clause"`
		Subst    map[string]jsonTerm `json:"subst"`
		BodyRefs []jsonSupportRef    `json:"body_refs"`
		Rank     uint32              `json:"rank"`
	} `json:"supports"`
	LimitsDecl struct {
		CertFacts      uint64 `json:"cert_facts"`
		DomainValues   uint64 `json:"domain_values"`
		SupportEdges   uint64 `json:"support_edges"`
		RuleGroundings uint64 `json:"rule_groundings"`
		JoinSteps      uint64 `json:"join_steps"`
		CertBytes      uint64 `json:"cert_bytes"`
	} `json:"limits_decl"`
}

func (j jsonCert) build(derived contract.CertContext) contract.ClosedModelCert {
	preds := make([]contract.Symbol, len(j.Scope.Predicates))
	for i, p := range j.Scope.Predicates {
		preds[i] = contract.SymbolFromString(p)
	}
	domains := make([]contract.FiniteDomain, len(j.Domains))
	for i, d := range j.Domains {
		vals := make([]core.Value, len(d.Values))
		for k, v := range d.Values {
			gv, ok := v.build().EraseGround()
			if !ok {
				panic("domain value must be ground")
			}
			vals[k] = gv
		}
		// Verbatim, NOT NewFiniteDomain: the harness must carry the vector's collection
		// order as authored, or a non-canonical case (issue #839) is silently repaired
		// before it can reach the gate it exists to pin.
		domains[i] = contract.FiniteDomain{TypeTag: contract.SymbolFromString(d.TypeTag), Values: vals}
	}
	extensions := make([]contract.RelationTable, len(j.Extensions))
	for i, e := range j.Extensions {
		rows := make([]contract.GroundLiteral, len(e.Rows))
		for k, r := range e.Rows {
			rows[k] = r.buildGround()
		}
		// Verbatim, NOT NewRelationTable (see the domains note above).
		extensions[i] = contract.RelationTable{Pred: contract.SymbolFromString(e.Pred), Arity: e.Arity, Rows: rows}
	}
	edges := make([]contract.SupportEdge, len(j.Supports))
	for i, s := range j.Supports {
		subst := make(contract.Subst, len(s.Subst))
		for name, term := range s.Subst {
			subst[contract.NewVarId(name)] = term.build()
		}
		refs := make([]contract.SupportRef, len(s.BodyRefs))
		for k, r := range s.BodyRefs {
			refs[k] = r.build()
		}
		edges[i] = contract.SupportEdge{
			Fact:     s.Fact.buildGround(),
			Clause:   contract.NewClauseId(s.Clause),
			Subst:    subst,
			BodyRefs: refs,
			Rank:     s.Rank,
		}
	}
	var edbHashes []contract.Hash
	for _, h := range j.EdbSnapshotHashes {
		edbHashes = append(edbHashes, hashFromHex(h))
	}
	// Auto-bind to the derived context unless the vector pins it explicitly.
	pin := func(p *string, fallback contract.Hash) contract.Hash {
		if p == nil {
			return fallback
		}
		return hashFromHex(*p)
	}
	var witness *contract.Hash
	if j.DecompositionWitness != nil {
		w := hashFromHex(*j.DecompositionWitness)
		witness = &w
	}
	var partial *contract.StratumPrefix
	if j.PartialScope != nil {
		ps := make([]contract.Symbol, len(j.PartialScope.Predicates))
		for i, p := range j.PartialScope.Predicates {
			ps[i] = contract.SymbolFromString(p)
		}
		// Verbatim, NOT NewStratumPrefix — the loader carries the vector's order as authored.
		partial = &contract.StratumPrefix{Level: j.PartialScope.Level, Predicates: ps}
	}
	return contract.ClosedModelCert{
		// Verbatim, NOT NewStratumPrefix (see the domains note above).
		Scope:                contract.StratumPrefix{Level: j.Scope.Level, Predicates: preds},
		ProgramHash:          pin(j.ProgramHash, derived.ProgramHash),
		ProfileHash:          pin(j.ProfileHash, derived.ProfileHash),
		CtxHash:              pin(j.CtxHash, derived.CtxHash),
		TheoryConfigHash:     pin(j.TheoryConfigHash, derived.TheoryConfigHash),
		EdbSnapshotHashes:    edbHashes,
		Domains:              domains,
		Extensions:           extensions,
		Supports:             contract.SupportWitness{Edges: edges},
		Closure:              contract.ClosureWitness{},
		DecompositionWitness: witness, // D10, read from the vector when present
		PartialScope:         partial, // ADR 0030 D1, read from the vector when present
		LimitsDecl: contract.CertSizeDecl{
			CertFacts:      j.LimitsDecl.CertFacts,
			DomainValues:   j.LimitsDecl.DomainValues,
			SupportEdges:   j.LimitsDecl.SupportEdges,
			RuleGroundings: j.LimitsDecl.RuleGroundings,
			JoinSteps:      j.LimitsDecl.JoinSteps,
			CertBytes:      j.LimitsDecl.CertBytes,
		},
	}
}

func runNegation(data []byte) {
	var doc struct {
		Extensional []string              `json:"extensional"`
		Edb         map[string][]jsonGoal `json:"edb"`
		Program     map[string]jsonClause `json:"program"`
		Cases       []struct {
			Name        string   `json:"name"`
			Claim       jsonGoal `json:"claim"`
			PlainCheck  bool     `json:"plain_check"`
			CertContext *struct {
				ProgramHash      *string `json:"program_hash"`
				ProfileHash      *string `json:"profile_hash"`
				CtxHash          *string `json:"ctx_hash"`
				TheoryConfigHash *string `json:"theory_config_hash"`
				// ADR 0029 D10: absent = an ordinary whole-program run.
				DecompositionWitness *string `json:"decomposition_witness"`
			} `json:"cert_context"`
			Limits     *jsonLimits `json:"limits"`
			Derivation struct {
				Nodes       []jsonNode `json:"nodes"`
				Root        uint64     `json:"root"`
				ClosedWorld []jsonCert `json:"closed_world"`
			} `json:"derivation"`
		} `json:"cases"`
	}
	if err := json.Unmarshal(data, &doc); err != nil {
		panic(err)
	}

	program := contract.NewMapProgram()
	for id, clause := range doc.Program {
		body := make([]contract.BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build()
		}
		program.Insert(contract.NewClauseId(id), contract.NewClauseLits(clause.Head.buildGoal(), body...))
	}

	extensional := contract.NewPredicateSet()
	for _, p := range doc.Extensional {
		extensional.Insert(contract.SymbolFromString(p))
	}
	edb := make(map[string][]contract.GroundLiteral, len(doc.Edb))
	for pred, rows := range doc.Edb {
		grounds := make([]contract.GroundLiteral, len(rows))
		for i, r := range rows {
			grounds[i] = r.buildGround()
		}
		edb[pred] = grounds
	}

	derived := contract.NewCertContext(
		contract.ProgramDigestOf(program),
		negPin(1),
		negPin(2),
		negPin(3),
	)

	for _, c := range doc.Cases {
		nodes := make([]contract.Node, len(c.Derivation.Nodes))
		for i, nj := range c.Derivation.Nodes {
			nodes[i] = nj.build()
		}
		closedWorld := make([]contract.ClosedModelCert, len(c.Derivation.ClosedWorld))
		for i, cj := range c.Derivation.ClosedWorld {
			closedWorld[i] = cj.build(derived)
		}
		deriv := contract.NewDerivationWithClosedWorld(nodes, c.Derivation.Root, closedWorld)

		limits := c.Limits.apply(contract.DefaultLimits())
		profile := negationProfile(limits, extensional, edb)

		// Per-case context override (rare — the mismatch-on-context cases) starts from
		// the derived context.
		cx := derived
		if c.CertContext != nil {
			if c.CertContext.ProgramHash != nil {
				cx.ProgramHash = hashFromHex(*c.CertContext.ProgramHash)
			}
			if c.CertContext.ProfileHash != nil {
				cx.ProfileHash = hashFromHex(*c.CertContext.ProfileHash)
			}
			if c.CertContext.CtxHash != nil {
				cx.CtxHash = hashFromHex(*c.CertContext.CtxHash)
			}
			if c.CertContext.TheoryConfigHash != nil {
				cx.TheoryConfigHash = hashFromHex(*c.CertContext.TheoryConfigHash)
			}
			if c.CertContext.DecompositionWitness != nil {
				cx = cx.WithDecomposition(hashFromHex(*c.CertContext.DecompositionWitness))
			}
		}

		var got contract.Outcome
		if c.PlainCheck {
			got = contract.Check[unitCtx](program, c.Claim.buildGround(), deriv, unitCtx{}, profile)
		} else {
			got = contract.CheckWithCertContext[unitCtx](program, c.Claim.buildGround(), deriv, unitCtx{}, profile, cx)
		}
		var outcome any
		if got.IsAccept() {
			outcome = "accept"
		} else {
			outcome = map[string]string{"reject": got.Code().Code()}
		}
		emit(checkResult{Name: c.Name, Outcome: outcome})
	}
}

// jsonLimits is a case's `limits` object, read ONE way by every family (#3376): each of the nine
// checker budgets is optional, and an absent key keeps the default. Two readers of this one object
// disagreed until #3376 (the check family set an absent max_nodes or max_depth to 0), which is
// research 0022's class, one decision computed twice.
type jsonLimits struct {
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

// apply overlays the budgets a case sets on base; a nil object (no `limits`) is base unchanged.
func (l *jsonLimits) apply(base contract.CheckLimits) contract.CheckLimits {
	if l == nil {
		return base
	}
	setIf(&base.MaxNodes, l.MaxNodes)
	setIf(&base.MaxDepth, l.MaxDepth)
	setIf(&base.MaxTermDepth, l.MaxTermDepth)
	setIf(&base.MaxCertBytes, l.MaxCertBytes)
	setIf(&base.MaxCertFacts, l.MaxCertFacts)
	setIf(&base.MaxDomainValues, l.MaxDomainValues)
	setIf(&base.MaxSupportEdges, l.MaxSupportEdges)
	setIf(&base.MaxRuleGroundings, l.MaxRuleGroundings)
	setIf(&base.MaxJoinSteps, l.MaxJoinSteps)
	return base
}

// setIf overwrites *dst with *src when src is non-nil (a vector limit override).
func setIf(dst *int, src *int) {
	if src != nil {
		*dst = *src
	}
}

// ===================== theory-decision families (ADR 0006 / #95, #154) ==============
// arithmetic / list / term / text / compound — each drives a contract Theory's Decide
// over the shared vectors/<family>.json `decisions` array, emitting one {name,outcome}
// line per ground decision plus a trailing __identity__ line pinning the theory's config
// digest. The arg builder mirrors the unit replays' buildArg (arithmetic_vectors_test.go)
// byte-for-byte so the black-box CLI agrees with the in-process oracle.

// buildTheoryArg decodes one structural arg object into the ontos Value the atom carries,
// matching the encoding in vectors/{arithmetic,list,term,text,compound}.json (and the
// Rust/TS builders) EXACTLY:
//
//	{"int": N}                 -> the ontos-data int embedding of N
//	{"bigint": "<digits>"}     -> the int embedding of a value beyond JSON int range
//	{"decimal": "<d.dddd>"}    -> the ontos-data decimal embedding of that decimal literal
//	{"text": "<s>"}            -> the ontos-data utf8-text embedding
//	{"atom": "<utf8>"}         -> a bare Atom of those UTF-8 bytes
//	{"op": "<op>", "args": []} -> an operator compound Tuple(Atom(op), arg..)
//	{"list": [..]}             -> the ontos-data list embedding of the encoded children
//	{"tuple": [..]}            -> a raw Tuple of the encoded children
func buildTheoryArg(raw json.RawMessage) core.Value {
	var obj map[string]json.RawMessage
	if err := json.Unmarshal(raw, &obj); err != nil {
		panic(fmt.Sprintf("arg is not an object: %s: %v", raw, err))
	}
	has := func(key string) bool { _, ok := obj[key]; return ok }
	switch {
	case has("int"):
		var n int64
		if err := json.Unmarshal(obj["int"], &n); err != nil {
			panic(fmt.Sprintf("bad int arg %s: %v", obj["int"], err))
		}
		return data.EncodeInt(big.NewInt(n))
	case has("bigint"):
		var s string
		if err := json.Unmarshal(obj["bigint"], &s); err != nil {
			panic(fmt.Sprintf("bad bigint arg: %v", err))
		}
		n, ok := new(big.Int).SetString(s, 10)
		if !ok {
			panic(fmt.Sprintf("bigint %q is not a base-10 integer", s))
		}
		return data.EncodeInt(n)
	case has("decimal"):
		var s string
		if err := json.Unmarshal(obj["decimal"], &s); err != nil {
			panic(fmt.Sprintf("bad decimal arg: %v", err))
		}
		m, e, ok := decimalParts(s)
		if !ok {
			panic(fmt.Sprintf("decimal %q is not a decimal literal", s))
		}
		// EncodeDecimal canonicalizes (trailing-zero carry) — byte-identical to the unit
		// replay's decFromString -> toDecimalTerm.
		return data.EncodeDecimal(m, e)
	case has("text"):
		var s string
		if err := json.Unmarshal(obj["text"], &s); err != nil {
			panic(fmt.Sprintf("bad text arg: %v", err))
		}
		// ontos v0.8.0 made EncodeText fallible (it rejects non-UTF-8). A JSON string is
		// always valid UTF-8, so this cannot fire on a vector; it is refused loudly if it does.
		v, err := data.EncodeText(s)
		if err != nil {
			panic(fmt.Sprintf("text arg %q does not encode: %v", s, err))
		}
		return v
	case has("atom"):
		var s string
		if err := json.Unmarshal(obj["atom"], &s); err != nil {
			panic(fmt.Sprintf("bad atom arg: %v", err))
		}
		return core.NewAtom([]byte(s))
	case has("op"):
		var op string
		if err := json.Unmarshal(obj["op"], &op); err != nil {
			panic(fmt.Sprintf("bad op arg: %v", err))
		}
		var args []json.RawMessage
		if err := json.Unmarshal(obj["args"], &args); err != nil {
			panic(fmt.Sprintf("bad op args: %v", err))
		}
		items := make([]core.Value, 0, len(args)+1)
		items = append(items, core.NewAtom([]byte(op)))
		for _, a := range args {
			items = append(items, buildTheoryArg(a))
		}
		return core.NewTuple(items...)
	case has("list"):
		var children []json.RawMessage
		if err := json.Unmarshal(obj["list"], &children); err != nil {
			panic(fmt.Sprintf("bad list arg: %v", err))
		}
		elems := make([]core.Value, 0, len(children))
		for _, c := range children {
			elems = append(elems, buildTheoryArg(c))
		}
		return data.EncodeList(elems)
	case has("tuple"):
		var children []json.RawMessage
		if err := json.Unmarshal(obj["tuple"], &children); err != nil {
			panic(fmt.Sprintf("bad tuple arg: %v", err))
		}
		items := make([]core.Value, 0, len(children))
		for _, c := range children {
			items = append(items, buildTheoryArg(c))
		}
		return core.NewTuple(items...)
	default:
		panic(fmt.Sprintf("unrecognized arg shape: %s", raw))
	}
}

// decimalParts parses a decimal literal spelling [-+]?<digits>.<digits> into (mantissa,
// exponent) such that the value is mantissa × 10^exponent — the pre-canonical form
// data.EncodeDecimal then normalizes. Mirrors Rust's BigDecimal::from_decimal_str and the
// Go unit replay's decFromString (sans the explicit trailing-zero carry, which EncodeDecimal
// performs).
func decimalParts(s string) (mantissa, exponent *big.Int, ok bool) {
	negative := false
	rest := s
	if len(s) > 0 && (s[0] == '-' || s[0] == '+') {
		negative = s[0] == '-'
		rest = s[1:]
	}
	dot := strings.IndexByte(rest, '.')
	if dot < 0 {
		return nil, nil, false
	}
	intPart := rest[:dot]
	fracPart := rest[dot+1:]
	if intPart == "" || fracPart == "" || !allDigits(intPart) || !allDigits(fracPart) {
		return nil, nil, false
	}
	m, good := new(big.Int).SetString(intPart+fracPart, 10)
	if !good {
		return nil, nil, false
	}
	if negative {
		m.Neg(m)
	}
	return m, big.NewInt(-int64(len(fracPart))), true
}

func allDigits(s string) bool {
	for i := 0; i < len(s); i++ {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return len(s) > 0
}

// theoryByName builds the contract Theory the family names. compound composes [arithmetic,
// text] in that order (mirroring buildCompound in compound_vectors_test.go).
func theoryByName(name string) contract.Theory {
	switch name {
	case "arithmetic":
		return contract.NewArithmeticTheory()
	case "list":
		return contract.NewListTheory()
	case "term":
		return contract.NewTermTheory()
	case "text":
		return contract.NewTextTheory()
	case "compound":
		return contract.NewCompoundTheory(contract.NewArithmeticTheory(), contract.NewTextTheory())
	default:
		panic("unknown theory family " + name)
	}
}

func runTheory(name string, raw []byte) {
	theory := theoryByName(name)
	var doc struct {
		Decisions []struct {
			Name string            `json:"name"`
			Pred string            `json:"pred"`
			Args []json.RawMessage `json:"args"`
		} `json:"decisions"`
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		panic(err)
	}
	for _, d := range doc.Decisions {
		args := make([]core.Value, 0, len(d.Args))
		for _, a := range d.Args {
			args = append(args, buildTheoryArg(a))
		}
		atom := contract.GroundLiteral{Pred: contract.SymbolFromString(d.Pred), Args: args}
		// #3126: the ground verdict, which can say "not decided" ({"not_completed": <kind>}).
		outcome := completion.MatchTheory[completion.NoCallerLimit, any](contract.DecideGround(theory, atom), theoryOutcomeJSON{name: name, caseName: d.Name, pred: d.Pred})
		emit(checkResult{Name: d.Name, Outcome: outcome})
	}
	// Pin the theory's identity config digest as a synthetic case so the harness asserts
	// the composed/ordered identity (the compound digest commits to membership AND order),
	// uniformly across every theory family. Every standard theory implements the optional
	// Identified seam.
	id := theory.(contract.Identified).Identity()
	emit(checkResult{Name: "__identity__", Outcome: hex.EncodeToString(id.ConfigDigest[:])})
}

// theoryOutcomeJSON renders a theory's ground verdict as the decision vectors spell it.
type theoryOutcomeJSON struct{ name, caseName, pred string }

func (theoryOutcomeJSON) Holds() any {
	return "holds"
}

func (theoryOutcomeJSON) Fails(code string) any {
	return map[string]string{"fails": code}
}

func (o theoryOutcomeJSON) LimitExceeded(completion.NoCallerLimit) any {
	panic(fmt.Sprintf("%s %q: a caller's limit for the owned predicate %q", o.name, o.caseName, o.pred))
}

func (o theoryOutcomeJSON) NotCompleted(cause completion.NonCompletion) any {
	// The decision vectors only carry owned predicates, so a routed atom is never disowned; if it
	// is, the vector or the owns set is wrong.
	if cause.Kind() == completion.KindInconsistentTheory {
		panic(fmt.Sprintf("%s %q: the theory disowned the owned predicate %q", o.name, o.caseName, o.pred))
	}
	return map[string]string{"not_completed": cause.Kind().Tag()}
}

func main() {
	const usage = "usage: conformance <check|account|negation|arithmetic|list|term|text|compound>"
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, usage)
		os.Exit(2)
	}
	input, err := io.ReadAll(os.Stdin)
	if err != nil {
		panic(err)
	}
	switch os.Args[1] {
	case "check":
		runCheck(input)
	case "account":
		runAccount(input)
	case "negation":
		runNegation(input)
	case "arithmetic", "list", "term", "text", "compound":
		runTheory(os.Args[1], input)
	default:
		fmt.Fprintf(os.Stderr, "%s (got %q)\n", usage, os.Args[1])
		os.Exit(2)
	}
}
