// #2226 step 0 (seat:caa, issuecomment-5812490508): can a certificate SEAL a table row spelled
// list(a) while the leaves admit .(a,[])? If so, the now-EXACT negation lookup (#2227) finds the
// body literal absent and certifies a false negation under the default reading. The same
// witnesses are pinned in contract/rs and contract/ts; see the rs file for the two routes.
package contract

import (
	"testing"

	core "github.com/bitspark/ontos/core/go"
)

// srLeaves admits exactly the EDB-of-record and attests its snapshot per extensional predicate.
// test-double: consumer(a fixed EDB: admits exactly its rows and attests them)
type srLeaves struct {
	extensional *PredicateSet
	edb         []GroundLiteral
}

func (l srLeaves) Extensional() *PredicateSet { return l.extensional }
func (l srLeaves) Verify(lit GroundLiteral, _ Evidence, _ struct{}) LeafOutcome {
	for _, r := range l.edb {
		if r.Equal(lit) {
			return LeafAdmit{}
		}
	}
	return LeafReject{Code: "not_admitted"}
}
func (l srLeaves) EdbSnapshot(p Symbol, _ struct{}) (Hash, bool) {
	if !l.extensional.Contains(p) {
		return Hash{}, false
	}
	var rows []GroundLiteral
	for _, r := range l.edb {
		if r.Pred.Equal(p) {
			rows = append(rows, r)
		}
	}
	return EdbTableHash(p, rows), true
}

func srLit(pred string, v core.Value) GroundLiteral { return NewGroundLiteral(pred, v) }

// srNegation checks `r :- \+ seen(.(a,[]))` (plus `extra`) with a Neg premise seen(.(a,[])),
// EXACTLY the body literal, against a cert over `tables`.
func srNegation(extra map[string]Clause, extensional []string, edb []GroundLiteral, level uint32,
	tables []RelationTable, edbHashes []Hash, edges []SupportEdge) Outcome {
	prog := NewMapProgram().With(NewClauseId("r_rule"),
		NewClauseLits(NewGoal("r"), NegLit(NewGoal("seen", FromValue(pmConsA)))))
	for id, c := range extra {
		prog = prog.With(NewClauseId(id), c)
	}
	pin := Hash{1}
	var preds []Symbol
	facts := 0
	for _, t := range tables {
		preds = append(preds, t.Pred)
		facts += len(t.Rows)
	}
	cert := ClosedModelCert{
		Scope:       NewStratumPrefix(level, preds),
		ProgramHash: ProgramDigestOf(prog),
		ProfileHash: pin, CtxHash: pin, TheoryConfigHash: pin,
		EdbSnapshotHashes: edbHashes,
		Domains:           []FiniteDomain{NewFiniteDomain(SymbolFromString("v"), []core.Value{pmConsA, pmListA})},
		Extensions:        tables,
		Supports:          SupportWitness{Edges: edges},
		LimitsDecl: CertSizeDecl{CertFacts: uint64(facts), DomainValues: 2, SupportEdges: uint64(len(edges)),
			RuleGroundings: 1_000, JoinSteps: 10_000},
	}
	cert.LimitsDecl.CertBytes = CertEncodedBytes(cert) // #2524: an honest cert declares its measured bytes
	claim := NewGroundLiteral("r")
	nodes := []Node{RuleNode{
		Conc: claim, Clause: NewClauseId("r_rule"), Subst: Subst{},
		Premises: []Premise{NegPremise{Atom: srLit("seen", pmConsA), Cert: NewCertId(0), Nonmember: DirectLookup}},
		Meta:     NoMeta(),
	}}
	profile := &CheckProfile[struct{}]{
		Theory: NewCompoundTheory(),
		Leaves: srLeaves{PredicateSetOf(extensional...), edb},
		Admit:  AlwaysAdmit[struct{}]{},
		Limits: DefaultLimits(),
	}
	return CheckWithCertContext(prog, claim, NewDerivationWithClosedWorld(nodes, 0, []ClosedModelCert{cert}),
		struct{}{}, profile, NewCertContext(ProgramDigestOf(prog), pin, pin, pin))
}

// srRouteE: `seen` is extensional and the leaves attest seen(.(a,[])); the cert seals `sealed`.
func srRouteE(sealed core.Value) Outcome {
	row := srLit("seen", sealed)
	seen := SymbolFromString("seen")
	return srNegation(nil, []string{"seen"}, []GroundLiteral{srLit("seen", pmConsA)}, 0,
		[]RelationTable{NewRelationTable(seen, 1, []GroundLiteral{row})},
		[]Hash{EdbTableHash(seen, []GroundLiteral{row})}, nil)
}

func TestSealedRowSpelling2226Extensional(t *testing.T) {
	if got := pmVerdict(srRouteE(pmConsA)); got != "neg_atom_present" {
		t.Fatalf("control: %s, want neg_atom_present", got)
	}
	if got := pmVerdict(srRouteE(pmListA)); got != "cert_edb_mismatch" {
		t.Fatalf("E1 (extensional row respelled): %s, want cert_edb_mismatch", got)
	}
}

// srRouteI: `seen(X) :- src(X)` over extensional src(.(a,[])); the cert seals seen(row),
// supported with X = supportX and a body ref src(supportX).
func srRouteI(row, supportX core.Value) Outcome {
	x := Var("X")
	seenClause := NewClauseLits(NewGoal("seen", x), PosLit(NewGoal("src", x)))
	srcRow := srLit("src", pmConsA)
	src, seen := SymbolFromString("src"), SymbolFromString("seen")
	edge := SupportEdge{
		Fact:     srLit("seen", row),
		Clause:   NewClauseId("seen_rule"),
		Subst:    Subst{NewVarId("X"): FromValue(supportX)},
		BodyRefs: []SupportRef{LowerStratumRef{Cert: NewCertId(0), Atom: srLit("src", supportX)}},
		Rank:     1,
	}
	return srNegation(map[string]Clause{"seen_rule": seenClause}, []string{"src"}, []GroundLiteral{srcRow}, 1,
		[]RelationTable{
			NewRelationTable(src, 1, []GroundLiteral{srcRow}),
			NewRelationTable(seen, 1, []GroundLiteral{srLit("seen", row)}),
		},
		[]Hash{EdbTableHash(src, []GroundLiteral{srcRow})}, []SupportEdge{edge})
}

func TestSealedRowSpelling2226Intensional(t *testing.T) {
	if got := pmVerdict(srRouteI(pmConsA, pmConsA)); got != "neg_atom_present" {
		t.Fatalf("control: %s, want neg_atom_present", got)
	}
	if got := pmVerdict(srRouteI(pmListA, pmListA)); got != "cert_unsupported" {
		t.Fatalf("I1 (support X = list(a)): %s, want cert_unsupported", got)
	}
	if got := pmVerdict(srRouteI(pmListA, pmConsA)); got != "cert_unsupported" {
		t.Fatalf("I2 (support X = .(a,[])): %s, want cert_unsupported", got)
	}
}
