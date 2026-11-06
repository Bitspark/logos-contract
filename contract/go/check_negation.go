// ADR 0007 closed-model certificates — the total, NON-SEARCHING \+ verifier.
//
// SOUNDNESS, stratum by stratum (#3022 step 3; research 0028's advice §2, row A4). Let L be the
// already-verified interpretation of the strictly lower strata: the lower certificates a sealed
// clause reads, each Valid before it is cited (#2258 (a)), and the pinned Theory's decisions. Let
// T_s^L be the immediate-consequence operator of this certificate's scope, with every negation and
// count evaluated against L. Two obligations make the sealed finite table E_s EXACTLY lfp(T_s^L):
//
//   - SUPPORT gives E_s ⊆ lfp(T_s^L) ("no junk"): every fact in E_s has a support edge, a cited
//     clause grounded so its head equals the fact, whose body literals each hold in E_s or L, and
//     whose same-stratum positive dependencies have a STRICTLY SMALLER rank than the fact. The
//     strict rank rejects the `p :- p` upper-bound trap: `{p}` is closed, but p's only edge would
//     need a same-stratum dependency `p` ranked below itself. By induction on rank.
//
//   - CLOSURE gives T_s^L(E_s) ⊆ E_s ("no missing heads"), hence lfp(T_s^L) ⊆ E_s: for every
//     clause of the scope, taken from the trusted program, every grounding whose body is true
//     against E_s and L has its head in E_s. The checker meets those groundings by a COMPLETE
//     relational join over the sealed tables (#1829), never by enumerating the domains: under the
//     safety gate every clause variable occurs in a positive sealed, non-builtin literal, so a
//     satisfied grounding binds each variable from a row that exists, and the structural matcher
//     meets it. A satisfied grounding whose head leaves the supplied domains is refused
//     (cert_out_of_domain), and an undecidable or inconsistent literal (a Theory's NotMine after
//     owns()) refuses by name, never reads as false, so the closure cannot under-fire.
//
// Support and closure give E_s = lfp(T_s^L), so `a ∉ E_s` proves `a` absent from the stratum's
// least model: absence is sound, not an upper bound. Neither obligation needs the program to be
// constructor-acyclic: a finiteness guarantee is an admission promise that evaluation ends, and
// closure is the evidence that this table is complete.
//
// Every loop below ranges over a SUPPLIED finite table, pre-bounded by a CheckLimits cert budget
// validated BEFORE any scan. No fixpoint, no Herbrand enumeration, no engine call.
// Go sibling of the cert path in contract/rs/src/check/cert.rs.
package contract

import (
	"fmt"
	"sort"

	"github.com/Bitspark/logos-contract/contract/go/completion"
	core "github.com/bitspark/ontos/core/go"
	data "github.com/bitspark/ontos/data/go"
)

// sortedVarIds returns the variable set as a slice sorted by VarId name (byte order) —
// a deterministic order matching Rust's Vec<VarId>::sort. The closure self-enumeration
// is order-independent (the odometer enumerates the full product regardless), but a
// stable order keeps behaviour reproducible across runs and cores.
func sortedVarIds(set map[VarId]struct{}) []VarId {
	vars := make([]VarId, 0, len(set))
	for v := range set {
		vars = append(vars, v)
	}
	sort.Slice(vars, func(i, j int) bool { return vars[i].String() < vars[j].String() })
	return vars
}

// certStatus is the memoized verification status of one cited ClosedModelCert. Computed
// once, up front, into a slice parallel to Derivation.ClosedWorld; a Neg premise reuses
// the cached result rather than re-verifying.
type certStatus struct {
	valid  bool
	code   RejectionCode
	detail string
}

func validCert() certStatus { return certStatus{valid: true} }

func invalidCert(code RejectionCode, detail string) certStatus {
	return certStatus{valid: false, code: code, detail: detail}
}

// certErr is an internal (code, detail) pair the per-gate helpers return.
type certErr struct {
	code   RejectionCode
	detail string
}

// verifyCert verifies one certificate fully, ONCE, in the normative order
// budget → context → scope-closure → domain → support → closure → EDB (ADR 0007 §3),
// with a canonical-form precheck (1b, issue #839) between budget and context — not a
// new semantic gate, but the representation invariant every later gate's
// binary-search lookups assume. The budget gate is first (before any scan); context
// is *recomputed*, not merely compared; the scope-closure + domain gates establish
// the well-formed invariants that make the support and closure checks sound;
// the EDB gate binds extensional tables to the live snapshot.
//
// world is the derivation's ClosedWorld and status/verified the statuses computed so far, in
// verificationOrder: every certificate at a lower level is final, so a predicate this cert reads
// from one is read only once that cert is known Valid (#2258 (a)).
func verifyCert[C any](cert ClosedModelCert, place certPlace, world []ClosedModelCert, status []certStatus, verified []bool, program Program, profile *CheckProfile[C], ctx C, certContext CertContext, limits CheckLimits) certStatus {
	theory := profile.Theory
	// 1. BUDGET GATE — first, before any scan.
	if e := checkCertBudget(cert, limits); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 1b. CANONICAL FORM (issue #839) — every binary-searched collection the cert
	//     carries (scope predicates, domain values, extension rows) must actually BE
	//     sorted + deduped by its canonical key. The exported fields make a
	//     non-canonical literal representable (the constructors sort; wire decode and
	//     struct literals do not have to), and a defeated binary search does not fail
	//     loudly — it fabricates arbitrary per-lookup verdicts. Reject
	//     deterministically here, bounded by the budget just validated, before any
	//     gate consults a lookup.
	if e := checkCertCanonicalForm(cert); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 1c. PARTIAL SUB-SCOPE (ADR 0030 D1) — before any table is consulted: PartialScope is the
	//     one field a malicious producer would most like the checker to trust, so its three
	//     invariants are verified up front. A cert with no PartialScope passes untouched.
	if e := checkCertPartialScope(cert, program, profile.Leaves.Extensional()); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 2. CONTEXT (§3.1) — RECOMPUTE program_hash from the live program, require the
	//    cert's pin to equal it, AND require all four cert pins to equal the
	//    caller-derived context.
	if e := checkCertContext(cert, program, certContext); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 2a. PARTITION GATE (admissible fragment) — a stratum prefix holds only
	//     intensional/extensional predicates, NEVER theory-owned builtins (§4.4: the
	//     builtin partition is decided LIVE by the Theory, not sealed in a table). A
	//     sealed theory-owned pred would let \+ b(a) be discharged against a FABRICATED
	//     table instead of the theory — reject before any model gate.
	for _, pred := range cert.Scope.Predicates {
		if theory.Owns(pred) {
			return invalidCert(CertScopeIncomplete, fmt.Sprintf(
				"sealed scope predicate %q is theory-owned (builtins are a separate partition, decided live — not sealable)",
				pred.String()))
		}
	}
	// 2b. STACKED READS (#2258 (a)) — every predicate a sealed clause reads without this cert
	//     sealing it resolves to the UNIQUE certificate at a strictly lower level that seals it
	//     EXACTLY and is Valid; an invalid one invalidates this cert with its own code.
	view, e := resolveLowerSeals(cert, place.own, world, status, verified, program, theory)
	if e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 3. SCOPE DOWNWARD-CLOSURE (§3.2) — the sealed prefix must be self-contained.
	if e := checkScopeDownwardClosed(view, program, theory); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 4. DOMAIN COVERAGE (§3.4) — every value reachable through the cert must lie in
	//    ∪domains, so the closure self-enumeration's universe is a superset of the
	//    active domain.
	if e := checkCertDomainCoverage(cert); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 5. SUPPORT (§3.5) — E ⊆ least model (no junk; rank-consistent strict descent).
	if e := checkCertSupport(view, place, program, theory, profile.Leaves.Extensional()); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 6. CLOSURE (§3.3) — least model ⊆ E, driven by the TRUSTED enumerated defining
	//    clauses of the sealed scope.
	if e := checkCertClosure(view, program, theory, limits); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 7. EDB BINDING (§3.6) — every sealed extensional predicate's table must equal the
	//    live EDB snapshot the bound LeafVerifier attests.
	if e := checkCertEdb(cert, profile.Leaves, ctx); e != nil {
		return invalidCert(e.code, e.detail)
	}
	// 8. exact.
	return validCert()
}

// checkCertCanonicalForm (1b, issue #839). The cert's three binary-searched
// collections must be sorted + deduped by their canonical keys, or every membership
// decision downstream is unsound — silently: an unsorted FiniteDomain reports
// present values absent per lookup luck, surfacing as an arbitrary
// cert_out_of_domain with every correct value in the list. Reject deterministically
// instead, with the code that collection's defeated search would have fabricated and
// a detail that names the canonicalizing constructor.
// checkCertPartialScope — 1c. PARTIAL SUB-SCOPE (ADR 0030 D1). A cert with no PartialScope
// passes untouched (every pre-0030 cert, every exact seal). Otherwise the three invariants,
// each cert_partial_scope_invalid, verified BEFORE any table is consulted because a
// certificate is untrusted input: (1) p ⊆ Scope, canonical, at the prefix's own level;
// (2) upward-closed within the sealed prefix — a sealed clause whose head is COMPLETE may not
// read (positively, or under a count) a predicate marked partial, or its closure proof would
// be closed over E and vacuous for the rows the lower bound is missing; (3) an extensional
// table is never partial (snapshot-bound, complete by definition). Mirrors rs.
func checkCertPartialScope(cert ClosedModelCert, program Program, extensional *PredicateSet) *certErr {
	p := cert.PartialScope
	if p == nil {
		return nil
	}
	invalid := func(detail string) *certErr { return &certErr{CertPartialScopeInvalid, detail} }
	for i := 1; i < len(p.Predicates); i++ {
		if !(string(p.Predicates[i-1].Bytes()) < string(p.Predicates[i].Bytes())) {
			return invalid("partial_scope predicates are not sorted+deduped by symbol byte order - build it via NewStratumPrefix, not a struct literal (issue #839)")
		}
	}
	if len(p.Predicates) == 0 {
		return invalid("partial_scope is present but names no predicate - encode an exact seal as an ABSENT partial_scope")
	}
	if p.Level != cert.Scope.Level {
		return invalid(fmt.Sprintf("partial_scope level %d is not the sealed prefix's level %d", p.Level, cert.Scope.Level))
	}
	for _, pred := range p.Predicates {
		if !cert.Scope.Seals(pred) {
			return invalid(fmt.Sprintf("partial_scope names predicate %q that the sealed scope does not seal", pred.String()))
		}
		if extensional.Contains(pred) {
			return invalid(fmt.Sprintf("partial_scope marks extensional predicate %q as partial - an EDB table is snapshot-bound and complete by definition", pred.String()))
		}
	}
	var err *certErr
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		if err != nil || !cert.Scope.Seals(clause.Head.Pred) || cert.IsPartial(clause.Head.Pred) {
			return
		}
		for _, bl := range clause.Body {
			// An intra-scope negation is already refused by the scope gate; a positive or
			// counting read of a lower bound is what makes a "complete" closure vacuous.
			if bl.IsNeg() {
				continue
			}
			if cert.IsPartial(bl.Pred()) {
				err = invalid(fmt.Sprintf("partial_scope is not upward-closed: complete sealed predicate %q is defined by a clause that reads partial predicate %q", clause.Head.Pred.String(), bl.Pred().String()))
				return
			}
		}
	})
	return err
}

func checkCertCanonicalForm(cert ClosedModelCert) *certErr {
	if !cert.Scope.IsCanonical() {
		return &certErr{CertScopeIncomplete,
			"sealed scope predicates are not sorted+deduped by symbol byte order - build the prefix via NewStratumPrefix, not a struct literal (issue #839)"}
	}
	for _, d := range cert.Domains {
		if !d.IsCanonical() {
			return &certErr{CertOutOfDomain, fmt.Sprintf(
				"finite domain %q values are not sorted+deduped by canonical codec bytes, so binary-search membership is defeated - build the domain via NewFiniteDomain, not a struct literal (issue #839)",
				d.TypeTag.String())}
		}
	}
	for _, t := range cert.Extensions {
		if !t.IsCanonical() {
			return &certErr{CertUnsupported, fmt.Sprintf(
				"sealed table %q rows are not sorted+deduped by canonical codec bytes, so binary-search membership is defeated - build the table via NewRelationTable, not a struct literal (issue #839)",
				t.Pred.String())}
		}
	}
	return nil
}

// checkCertContext (§3.1). Recompute program_hash from the live program and require
// the cert's pin to equal it; then require the cert's four pins to equal the
// caller-derived certContext.
// programDigestOverScope is the canonical program digest over the SLICE a slice-sealed cert
// covers (ADR 0029 D10): the defining clauses of the cert's sealed scope, and nothing else.
//
// Identical construction to ProgramDigestOf over a SUBSET of the clauses, so the two digests are
// directly comparable. A predicate that is a dependency-edge target but not a stratum member (an
// EDB predicate) contributes no clause, exactly as it contributes none to the component.
func programDigestOverScope(program Program, cert ClosedModelCert) Hash {
	var clauses []Clause
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		if cert.Scope.Seals(clause.Head.Pred) {
			clauses = append(clauses, clause)
		}
	})
	return ProgramDigest(clauses)
}

func checkCertContext(cert ClosedModelCert, program Program, certContext CertContext) *certErr {
	// ADR 0029 D10 — WHICH CLAUSE SET DOES ProgramHash PIN? See the rs twin in
	// contract/rs/src/check/cert.rs for the full argument; the four cases are identical.
	//
	// The downward-closure gate is deliberately NOT relaxed: checkScopeDownwardClosed walks
	// every clause of the COMPLETE program whatever this decides. That is what makes a slice
	// seal sound — only the PIN's coverage narrows.
	var recomputed Hash
	switch {
	case cert.DecompositionWitness == nil:
		recomputed = ProgramDigestOf(program)
	case certContext.DecompositionWitness == nil:
		return &certErr{CertContextMismatch, "certificate is sealed over a decomposition slice, but the bound check context declares no decomposition — a slice-sealed cert cannot discharge a negation in a whole-program run (ADR 0029 D10)"}
	case *cert.DecompositionWitness != *certContext.DecompositionWitness:
		return &certErr{CertContextMismatch, "certificate is sealed over a decomposition slice, but the bound check context names a DIFFERENT decomposition — a slice seal is valid only under the decomposition that authorized it (ADR 0029 D10)"}
	default:
		recomputed = programDigestOverScope(program, cert)
	}
	if cert.ProgramHash != recomputed {
		return &certErr{CertContextMismatch, "certificate program_hash does not match the recomputed live program"}
	}
	// The other three pins are properties of the RUN and must match in every case: a component
	// gets neither its own profile nor its own `not`.
	if cert.ProfileHash != certContext.ProfileHash ||
		cert.CtxHash != certContext.CtxHash ||
		cert.TheoryConfigHash != certContext.TheoryConfigHash {
		return &certErr{CertContextMismatch, "certificate pins do not match the bound check context"}
	}
	// ProgramHash is the one pin whose coverage D10 narrows, so it is compared separately.
	// A slice seal MUST NOT equal the caller's whole-program pin — requiring it would make D10
	// unsatisfiable, since the two cover different clause sets by construction. The seal is
	// already tied to the run by the witness pins agreeing and by the slice recompute above.
	if cert.DecompositionWitness == nil && cert.ProgramHash != certContext.ProgramHash {
		return &certErr{CertContextMismatch, "certificate pins do not match the bound check context"}
	}
	return nil
}

// checkCertBudget — validate the declared sizes against the CheckLimits cert budgets,
// AND the cert's ACTUAL sizes against the declaration (a lying decl is caught). All
// strict > comparisons; the budget gate must pass before any scan.
func checkCertBudget(cert ClosedModelCert, limits CheckLimits) *certErr {
	decl := cert.LimitsDecl
	// (a) declared ≤ budget. Both halves are the CALLER's verify budget (#2335), and each
	// family has its own code so the kernel's check-limit table can name one kind per code:
	// the four SIZE fields are cert_size_exceeded, the two CLOSURE fields cert_budget_exceeded.
	// A declared size is a protocol integer (uint64, #2735); a budget is the checker's int. A
	// negative budget admits nothing.
	exceeds := func(got uint64, max int) bool { return max < 0 || got > uint64(max) }
	overSize := func(name string, got uint64, max int) *certErr {
		return &certErr{CertSizeExceeded, fmt.Sprintf("declared %s %d exceeds budget %d", name, got, max)}
	}
	over := func(name string, got uint64, max int) *certErr {
		return &certErr{CertBudgetExceeded, fmt.Sprintf("declared %s %d exceeds budget %d", name, got, max)}
	}
	// Order matches Rust so the FIRST trip is identical.
	if exceeds(decl.CertBytes, limits.MaxCertBytes) {
		return overSize("cert_bytes", decl.CertBytes, limits.MaxCertBytes)
	}
	if exceeds(decl.CertFacts, limits.MaxCertFacts) {
		return overSize("cert_facts", decl.CertFacts, limits.MaxCertFacts)
	}
	if exceeds(decl.DomainValues, limits.MaxDomainValues) {
		return overSize("domain_values", decl.DomainValues, limits.MaxDomainValues)
	}
	if exceeds(decl.SupportEdges, limits.MaxSupportEdges) {
		return overSize("support_edges", decl.SupportEdges, limits.MaxSupportEdges)
	}
	if exceeds(decl.RuleGroundings, limits.MaxRuleGroundings) {
		return over("rule_groundings", decl.RuleGroundings, limits.MaxRuleGroundings)
	}
	if exceeds(decl.JoinSteps, limits.MaxJoinSteps) {
		return over("join_steps", decl.JoinSteps, limits.MaxJoinSteps)
	}
	// (b) actual ≤ declared (no under-declaration to slip past the budget).
	actualFacts := 0
	for _, t := range cert.Extensions {
		actualFacts += len(t.Rows)
	}
	actualDomainValues := 0
	for _, d := range cert.Domains {
		actualDomainValues += len(d.Values)
	}
	actualSupportEdges := len(cert.Supports.Edges)
	// A cert whose actual size exceeds its OWN declaration lied: the producer's fault,
	// cert_decl_mismatch (#2335), never the caller's budget.
	liar := func(name string, actual int, declared uint64) *certErr {
		return &certErr{CertDeclMismatch, fmt.Sprintf("actual %s %d exceeds declared %d", name, actual, declared)}
	}
	if uint64(actualFacts) > decl.CertFacts {
		return liar("cert_facts", actualFacts, decl.CertFacts)
	}
	if uint64(actualDomainValues) > decl.DomainValues {
		return liar("domain_values", actualDomainValues, decl.DomainValues)
	}
	if uint64(actualSupportEdges) > decl.SupportEdges {
		return liar("support_edges", actualSupportEdges, decl.SupportEdges)
	}
	// #2524: the BYTES, measured on the canonical encoding, so MaxCertBytes bounds what the
	// certificate IS, not only what it declares (declared <= budget is checked above).
	if actualBytes := CertEncodedBytes(cert); actualBytes > decl.CertBytes {
		return liar("cert_bytes", int(actualBytes), decl.CertBytes)
	}
	return nil
}

// checkScopeDownwardClosed (§3.2). The sealed prefix must be self-contained: for EVERY
// clause (from the TRUSTED whole-program enumeration) whose head is sealed by the
// scope, every body literal's predicate must be sealed-by-scope OR theory-owned — else
// cert_scope_incomplete. Also enforces the constructor-acyclic gate (#2759), the
// intra-prefix negation ban, and the safety / range-restriction gate.
func checkScopeDownwardClosed(view certView, program Program, theory Theory) *certErr {
	cert := view.cert
	// #3067 (research 0028 row A15): every gate below is the contract tier's ONE classification,
	// ClassifySealedClause, which the seal plan calls too. check builds the clause's context from
	// this certificate and the lower certificates it resolved (step 2b), and the scope's dependency
	// graph from the bound program, and renders the first gate a clause fails as
	// cert_scope_incomplete. It never trusts the producer's classification. Mirrors rs.
	ctx := view.sealContext()
	graph := NewScopeGraph()
	program.ForEachClause(func(_ ClauseId, clause Clause) { graph.Add(clause, cert.Scope.Seals) })
	var err *certErr
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		if err != nil || !cert.Scope.Seals(clause.Head.Pred) {
			return
		}
		if outside, ok := ClassifySealedClause(clause, ctx, graph, theory.Owns, theory.Owns); ok {
			err = &certErr{CertScopeIncomplete, scopeIncompleteDetail(clause, outside)}
		}
	})
	return err
}

// scopeIncompleteDetail is cert_scope_incomplete's detail for the first gate a sealed clause fails,
// worded as check has always worded each gate. Every OutsideKind has a case; the fragment.json
// replay's census fails if one is added without a vector row that reaches it.
func scopeIncompleteDetail(clause Clause, o Outside) string {
	switch o.Kind {
	case OutsideCountNotLower:
		why := "which no unique, exact, Valid strictly lower certificate seals"
		if o.SameScope {
			why = "which this same certificate seals (a count must read a strictly lower certificate, never the table under construction)"
		}
		return fmt.Sprintf("scope-defining clause body contains a count over predicate %q, %s", o.Pred.String(), why)
	case OutsideCountOpenCompound:
		return fmt.Sprintf(
			"scope-defining clause count over predicate %q contains an open compound (a tuple with a variable) term (not function-free)", o.Pred.String())
	case OutsideConstructorCycle:
		return fmt.Sprintf(
			"scope-defining clause head %q constructs an open compound (a tuple with a variable) on a dependency cycle through %q (outside the constructor-acyclic fragment)",
			clause.Head.Pred.String(), o.Through.String())
	case OutsideUnserved:
		return fmt.Sprintf(
			"scope-defining clause body references predicate %q that is neither sealed nor theory-owned, nor sealed by a strictly lower certificate",
			o.Pred.String())
	case OutsideIntraScopeNegation:
		return fmt.Sprintf(
			"scope-defining clause negates predicate %q sealed by this same prefix (intra-scope negation)", o.Pred.String())
	case OutsideUnboundCountFilter:
		return fmt.Sprintf(
			"scope-defining clause count over predicate %q has filter variable %q not bound by any positive sealed-relation body literal (range-restriction)",
			o.Pred.String(), o.Var.String())
	case OutsideUnboundVariable:
		return fmt.Sprintf(
			"scope-defining clause has unsafe variable %q: not bound by any positive sealed-relation body literal (range-restriction)",
			o.Var.String())
	}
	panic(fmt.Sprintf("scopeIncompleteDetail: an Outside kind with no wording: %d", o.Kind))
}

// collectVarsGoal collects the VarIds appearing in a goal's argument terms.
func collectVarsGoal(goal Goal, out map[VarId]struct{}) {
	for _, t := range goal.Args {
		collectVarsTerm(t, out)
	}
}

func collectVarsTerm(term Term, out map[VarId]struct{}) {
	switch t := term.(type) {
	case VarTerm:
		out[t.ID()] = struct{}{}
	case TupleTerm:
		for _, c := range t.Children() {
			collectVarsTerm(c, out)
		}
	case AtomTerm:
		// No variable.
	default:
		// Only program clauses reach here: the safety gate and the closure planner (#3074:
		// internal, so an unknown kind panics by name).
		panic(fmt.Sprintf("contract: collectVarsTerm: unknown Term %T", term))
	}
}

// checkCertDomainCoverage (§3.4). Every value the cert can introduce — every argument
// of every extension row, every support-ref atom/fact argument, and every value in
// every edge.Subst image — MUST lie in ∪domains, else cert_out_of_domain.
func checkCertDomainCoverage(cert ClosedModelCert) *certErr {
	oob := func(what string) *certErr {
		return &certErr{CertOutOfDomain, what + " carries a value outside the certificate's finite domains"}
	}
	checkVal := func(v core.Value) bool {
		_, ok := cert.DomainContaining(v)
		return ok
	}
	checkGround := func(g GroundLiteral) bool {
		for _, v := range g.Args {
			if !checkVal(v) {
				return false
			}
		}
		return true
	}
	// (a) every extension row's args.
	for _, table := range cert.Extensions {
		for _, fact := range table.Rows {
			if !checkGround(fact) {
				return oob("a sealed extension row")
			}
		}
	}
	// (b) every support edge: subst image values + each body ref's atom/fact args.
	for _, edge := range cert.Supports.Edges {
		for _, term := range edge.Subst {
			v, ok := term.EraseGround()
			if !ok {
				return &certErr{CertUnsupported, "support edge subst image is not ground"}
			}
			if !checkVal(v) {
				return oob("a support edge subst image")
			}
		}
		if !checkGround(edge.Fact) {
			return oob("a support edge fact")
		}
		for _, bodyRef := range edge.BodyRefs {
			atom, ok := supportRefAtom(bodyRef)
			if !ok {
				continue // #2258 L3.3b: a count ref carries no atom; its values are the Subst's.
			}
			if !checkGround(atom) {
				return oob("a support ref atom")
			}
		}
	}
	return nil
}

// checkCertEdb (§3.6). For every sealed predicate the bound LeafVerifier declares
// extensional, the cert's sealed table must equal the live EDB snapshot:
// EdbTableHash(p, cert.Table(p).Rows) == EdbSnapshot(p, ctx). A missing snapshot (the
// fail-closed default) means the cert cannot bind p to the live EDB → cert_edb_mismatch.
func checkCertEdb[C any](cert ClosedModelCert, leaves LeafVerifier[C], ctx C) *certErr {
	extensional := leaves.Extensional()
	provider, hasProvider := any(leaves).(EdbSnapshotProvider[C])
	for _, pred := range cert.Scope.Predicates {
		if !extensional.Contains(pred) {
			continue // an IDB predicate — bound by support/closure, not the EDB gate.
		}
		var rows []GroundLiteral
		if t, ok := cert.Table(pred); ok {
			rows = t.Rows
		}
		recomputed := EdbTableHash(pred, rows)
		if !hasProvider {
			return &certErr{CertEdbMismatch, fmt.Sprintf(
				"no live EDB snapshot attested for sealed extensional predicate %q", pred.String())}
		}
		attested, ok := provider.EdbSnapshot(pred, ctx)
		if !ok {
			return &certErr{CertEdbMismatch, fmt.Sprintf(
				"no live EDB snapshot attested for sealed extensional predicate %q", pred.String())}
		}
		if attested != recomputed {
			return &certErr{CertEdbMismatch, fmt.Sprintf(
				"sealed extensional table %q does not match the live EDB snapshot", pred.String())}
		}
	}
	return nil
}

// checkCertSupport (§3.5). Every sealed IDB fact has a support edge (E ⊆ least model).
// Extensional (EDB) facts are exempt — they are the well-founded base case, vouched by
// the §3.6 EDB-snapshot gate.
func checkCertSupport(view certView, place certPlace, program Program, theory Theory, extensional *PredicateSet) *certErr {
	cert := view.cert
	unsupported := func(detail string) *certErr { return &certErr{CertUnsupported, detail} }

	// §3.5 RANK CONSISTENCY pre-pass. Pin each sealed fact's support rank to the rank on
	// its OWN edge. A fact with two edges carrying DIFFERENT ranks is ill-formed.
	factEdgeRank := map[string]uint32{}
	for _, edge := range cert.Supports.Edges {
		key := string(GroundKey(edge.Fact))
		if existing, ok := factEdgeRank[key]; ok {
			if existing != edge.Rank {
				return unsupported(fmt.Sprintf("fact %q has inconsistent edge ranks %d and %d",
					edge.Fact.Pred.String(), existing, edge.Rank))
			}
		} else {
			factEdgeRank[key] = edge.Rank
		}
	}

	// Track which facts have a valid support edge — to enforce "no junk".
	covered := map[string]struct{}{}

	for _, edge := range cert.Supports.Edges {
		if !cert.Scope.Seals(edge.Fact.Pred) {
			return unsupported(fmt.Sprintf("support edge fact predicate %q is not sealed by the cert scope",
				edge.Fact.Pred.String()))
		}
		table, ok := cert.Table(edge.Fact.Pred)
		if !ok {
			return unsupported("support edge fact has no sealed extension")
		}
		if !table.Contains(edge.Fact) {
			return unsupported("support edge fact absent from its sealed table")
		}
		clause, ok := program.Clause(edge.Clause)
		if !ok {
			return unsupported(fmt.Sprintf("support edge cites unknown clause %q", edge.Clause.String()))
		}
		head, ok := clause.Head.Substitute(edge.Subst).AsGround()
		if !ok {
			return unsupported("support clause head not ground under subst")
		}
		if !head.Equal(edge.Fact) {
			return unsupported("support clause head != supported fact")
		}
		if len(edge.BodyRefs) != len(clause.Body) {
			return unsupported(fmt.Sprintf("support edge has %d body refs != clause body length %d",
				len(edge.BodyRefs), len(clause.Body)))
		}
		for k := range clause.Body {
			bodyLit := clause.Body[k]
			// #2258 L3.3b: a count body literal is resolved by a CountLowerRef against the strictly
			// lower certificate it reads (the scope gate admitted it only over such a table).
			if bodyLit.IsCount() {
				ref, ok := edge.BodyRefs[k].(CountLowerRef)
				if !ok {
					return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity (a count needs a CountLower ref)", k))
				}
				if e := resolveCountLower(k, bodyLit.CountVal, ref.Cert, edge.Subst, view, place); e != nil {
					return e
				}
				continue
			}
			inner, _ := bodyLit.AsInner()
			grounded, ok := inner.Substitute(edge.Subst).AsGround()
			if !ok {
				return unsupported(fmt.Sprintf("support body literal %d not ground under subst", k))
			}
			if e := resolveSupportRef(k, bodyLit, edge.BodyRefs[k], grounded, edge.Rank, view, place, theory, factEdgeRank, extensional); e != nil {
				return e
			}
		}
		covered[string(GroundKey(edge.Fact))] = struct{}{}
	}

	// No junk: every IDB fact in every extension must be covered by a support edge.
	for _, table := range cert.Extensions {
		if extensional.Contains(table.Pred) {
			continue // EDB predicate — covered by the EDB snapshot, not support.
		}
		for _, fact := range table.Rows {
			if _, ok := covered[string(GroundKey(fact))]; !ok {
				return unsupported(fmt.Sprintf("sealed fact %q has no support edge (junk / unfounded)",
					fact.Pred.String()))
			}
		}
	}
	return nil
}

// resolveSupportRef resolves one body reference of a support edge, enforcing the
// polarity match with the body literal and the rank-consistent strict same-stratum
// descent (§3.5).
func resolveSupportRef(k int, bodyLit BodyLit, bodyRef SupportRef, grounded GroundLiteral, factRank uint32, view certView, place certPlace, theory Theory, factEdgeRank map[string]uint32, extensional *PredicateSet) *certErr {
	cert := view.cert
	unsupported := func(detail string) *certErr { return &certErr{CertUnsupported, detail} }
	switch ref := bodyRef.(type) {
	case SameStratumRef:
		if bodyLit.IsNeg() {
			return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity", k))
		}
		if !ref.Fact.Equal(grounded) {
			return unsupported(fmt.Sprintf("support body ref %d fact != grounded body literal", k))
		}
		if ref.Rank >= factRank {
			return unsupported(fmt.Sprintf("support body ref %d rank %d not strictly < fact rank %d (unfounded)", k, ref.Rank, factRank))
		}
		// The dep must itself be supported at exactly the claimed rank.
		depKey := string(GroundKey(ref.Fact))
		actual, ok := factEdgeRank[depKey]
		if !ok {
			return unsupported(fmt.Sprintf("support body ref %d same-stratum dep has no support edge (cannot anchor rank)", k))
		}
		if actual != ref.Rank {
			return unsupported(fmt.Sprintf("support body ref %d claims rank %d but dep is supported at rank %d (fabricated rank)", k, ref.Rank, actual))
		}
		if t, ok := cert.Table(ref.Fact.Pred); ok && t.Contains(ref.Fact) {
			return nil
		}
		return unsupported(fmt.Sprintf("same-stratum dep %d absent from its sealed table", k))
	case LowerStratumRef:
		if bodyLit.IsNeg() {
			return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity", k))
		}
		lower, e := checkSupportRefCert(k, ref.Cert, ref.Atom.Pred, view, place)
		if e != nil {
			return e
		}
		if !ref.Atom.Equal(grounded) {
			return unsupported(fmt.Sprintf("support body ref %d lower atom != grounded body literal", k))
		}
		// #2258 (a): a strictly lower certificate is exact on its own (verified first), so a
		// positive dependency on one of its IDB facts needs no rank anchor here.
		if lower != nil {
			if lower.table.Contains(ref.Atom) {
				return nil
			}
			return unsupported(fmt.Sprintf("lower-stratum dep %d absent from certificate %d's sealed table", k, lower.index))
		}
		// INTRA-PREFIX BAN: a LowerStratum ref to a sealed INTENSIONAL predicate is
		// illegal — an intra-prefix IDB dependency must go through the rank-anchored
		// SameStratum path. A sealed EXTENSIONAL (EDB) predicate IS a legitimate lower
		// base case (acyclic), so a LowerStratum ref to it is allowed.
		if cert.Scope.Seals(ref.Atom.Pred) && !extensional.Contains(ref.Atom.Pred) {
			return unsupported(fmt.Sprintf(
				"support body ref %d: intra-prefix positive dependency on sealed intensional predicate %q must be cited as SameStratum with strict rank descent, not LowerStratum",
				k, ref.Atom.Pred.String()))
		}
		if t, ok := cert.Table(ref.Atom.Pred); ok && t.Contains(ref.Atom) {
			return nil
		}
		return unsupported(fmt.Sprintf("lower-stratum dep %d absent from the sealed table", k))
	case BuiltinRef:
		if bodyLit.IsNeg() {
			return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity", k))
		}
		if !ref.Atom.Equal(grounded) {
			return unsupported(fmt.Sprintf("support body ref %d builtin atom != grounded body literal", k))
		}
		if !theory.Owns(ref.Atom.Pred) {
			return unsupported(fmt.Sprintf("support builtin ref %d predicate not theory-owned", k))
		}
		// A stop is refused by name (#3126), never read as the literal's truth.
		verdict := readGround(DecideGround(theory, ref.Atom))
		if verdict.arm == groundHolds {
			return nil
		}
		if verdict.arm == groundNotDecided && !verdict.disowned() {
			return &certErr{BuiltinNotDecided, verdict.cause.Kind().Tag()}
		}
		return unsupported(fmt.Sprintf("support builtin ref %d does not hold", k))
	case NegLowerRef:
		if !bodyLit.IsNeg() {
			return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity", k))
		}
		lower, e := checkSupportRefCert(k, ref.Cert, ref.Atom.Pred, view, place)
		if e != nil {
			return e
		}
		if !ref.Atom.Equal(grounded) {
			return unsupported(fmt.Sprintf("support body ref %d neg-lower atom != grounded body literal", k))
		}
		if lower != nil {
			if lower.table.Contains(ref.Atom) {
				return unsupported(fmt.Sprintf("neg-lower dep %d is PRESENT in certificate %d's sealed table (negation fails)", k, lower.index))
			}
			return nil
		}
		if cert.Scope.Seals(ref.Atom.Pred) {
			return unsupported(fmt.Sprintf(
				"support body ref %d: NegLower negated dependency on sealed predicate %q is intra-prefix (negation must target a strictly-lower, separately-sealed stratum)",
				k, ref.Atom.Pred.String()))
		}
		t, ok := cert.Table(ref.Atom.Pred)
		if !ok {
			return unsupported(fmt.Sprintf("neg-lower dep %d predicate is not sealed", k))
		}
		if t.Contains(ref.Atom) {
			return unsupported(fmt.Sprintf("neg-lower dep %d is PRESENT in the sealed table (negation fails)", k))
		}
		return nil
	case CountLowerRef:
		// A count's ref is resolved by resolveCountLower; cited here, for a literal that is not a
		// count, its kind does not match the body literal.
		return unsupported(fmt.Sprintf("support body ref %d kind does not match body literal polarity", k))
	default:
		// The certificate is untrusted: nil, or a foreign type embedding SupportRef, is refused
		// by name (#3074, seat:caa's ruling).
		return &certErr{UnknownNodeKind, fmt.Sprintf("support body ref %d of type %T is none of the known support ref kinds", k, bodyRef)}
	}
}

// certPlace is where a certificate sits in its derivation's ClosedWorld: its own index and the
// world's length. A lower-stratum support ref names a cert index, and #2258 C3 checks it against
// this. Mirrors rs CertPlace.
type certPlace struct {
	own      int
	worldLen int
}

// citedLower is the strictly lower certificate a cross-certificate support ref resolved to: its
// ClosedWorld index and its sealed table for the ref's predicate.
type citedLower struct {
	index int
	table RelationTable
}

// checkSupportRefCert is #2258: the cert index a LowerStratum / NegLower support ref names must be
// one this checker can honour. An index outside ClosedWorld is cert_out_of_range, as for a Neg
// premise (C3). The ref's OWN cert resolves against its own tables, as it always has (nil). Any
// other index must be the certificate the ref's predicate RESOLVED to (#2258 (a)): the unique,
// exact, Valid certificate at a strictly lower level that seals it, whose table is returned.
// Validity precedes citation because statuses are computed in level order before support runs.
// Anything else is cert_unsupported. Mirrors rs.
func checkSupportRefCert(k int, cited CertId, pred Symbol, view certView, place certPlace) (*citedLower, *certErr) {
	idx, ok := cited.Offset(place.worldLen)
	if !ok {
		return nil, &certErr{CertOutOfRange, fmt.Sprintf("support body ref %d cites cert %d out of range %d", k, cited.Index(), place.worldLen)}
	}
	if idx == place.own {
		return nil, nil
	}
	if j, ok := view.lowerIndex(pred); ok && j == idx {
		if t, ok := view.table(pred); ok {
			return &citedLower{index: idx, table: t}, nil
		}
	}
	return nil, &certErr{CertUnsupported, fmt.Sprintf(
		"support body ref %d cites cert %d, which is neither its own cert %d nor the unique exact certificate at a strictly lower level sealing %q (#2258 (a))",
		k, idx, place.own, pred.String())}
}

// checkCertClosure is §3.3 CLOSURE: least model ⊆ E, by a checker JOIN over the sealed
// extensions of the TRUSTED defining-clause set (#1829). For EVERY clause in the whole
// program (via the trusted Program.ForEachClause) whose head is sealed by cert.Scope, join
// its positive sealed body literals over their sealed tables; every tuple the join emits
// is a grounding whose body is true against E (+ the pinned Theory), so its head MUST be
// present in E, else cert_not_closed. A satisfied grounding whose head value escapes the
// domain is cert_out_of_domain.
//
// SOUNDNESS. The defining-clause set is taken from the trusted program enumeration — NOT
// from the attacker-chosen support witness — and the program digest (recomputed in §3.1)
// commits to the COMPLETE clause set, so an attacker cannot hide a defining clause.
//
// WHY A JOIN DEMANDS EXACTLY WHAT THE ENUMERATION DEMANDED. The self-enumeration this
// replaced visited |∪domains|^vars groundings per clause and evaluated the body at each.
// Two gates that run BEFORE closure make the join's obligation set equal to that one:
// §3.2's SAFETY gate (checkScopeDownwardClosed) — every variable of a sealed-head clause
// occurs in a positive body literal whose predicate is sealed and not theory-owned, so the
// join binds every variable and every theory or negated literal reaches a point at which
// it is ground; and §3.4's DOMAIN COVERAGE (checkCertDomainCoverage) — every sealed-table
// value lies in ∪domains, so every tuple the join emits is a point of the enumeration's
// own space. A grounding the enumeration would have found satisfied has, for each positive
// sealed literal, a row of that literal's table matching it — exactly a tuple the join
// emits. Neither direction under-fires. Mirrors Rust's check_cert_closure.
func checkCertClosure(view certView, program Program, theory Theory, limits CheckLimits) *certErr {
	cert := view.cert
	groundings := 0
	joins := 0
	var err *certErr
	program.ForEachClause(func(_ ClauseId, clause Clause) {
		if err != nil {
			return
		}
		if !cert.Scope.Seals(clause.Head.Pred) {
			return
		}
		// ADR 0030 D2: closure is NOT verified for a table in PartialScope — it is a lower bound
		// sealed at a round-budget trip, so a satisfied grounding whose head it omits is the
		// truth of the mark, not a defect. Support is still verified; no Neg/Count may cite it
		// (the 3b gates); checkCertPartialScope keeps every COMPLETE table's closure meaningful.
		if cert.IsPartial(clause.Head.Pred) {
			return
		}
		if e := joinGroundings(clause, view, theory, limits, &groundings, &joins); e != nil {
			err = e
		}
	})
	return err
}

// joinPlan is the join plan of ONE sealed-scope clause (#1829). The order is pinned —
// identically in the three cores, because the join-step count depends on it:
//
//   - a POSITIVE body literal whose predicate is sealed by the scope and not theory-owned
//     is a BINDER: it is iterated over its sealed extension, in declared order, unifying on
//     a repeated variable (runs(R, R) binds R on the first occurrence and filters on the
//     second);
//   - a COUNT over a strictly lower certificate's relation (#2258 L3.3b) is a COUNT STAGE, due
//     at the FIRST point its filter's variables are bound: before any binder if the filter is
//     ground, else right after the binder that binds the last of them. It binds its result
//     variable (or tests it, if already bound), and costs one join step per lower row it scans;
//   - every other literal — a theory literal of either polarity, or a negated sealed
//     literal (unreachable past §3.2's intra-scope gate, evaluated soundly if met) — is a
//     FILTER, evaluated at the FIRST point all its variables are bound: before any binder
//     if it is ground or reads only the results of counts due there, else right after the
//     binder whose point first binds the last of them (a count due at a point binds its result
//     there).
//
// At each point the count stages run first, in declared order, then the filters, in declared
// order. A count-free clause's plan is exactly what it was before counts were admitted.
//
// §3.2's safety gate guarantees that point exists for every filter and that the head is
// ground once every binder has bound; a clause that reaches here without that property is
// refused cert_scope_incomplete rather than enumerated over anything. Mirrors Rust's
// JoinPlan / plan_join.
type joinPlan struct {
	// leading holds the steps due before any row is examined: counts over a ground filter,
	// then filters that are ground as written or read only those counts' results.
	leading []joinStep
	// binders holds the binders in declared order.
	binders []Goal
	// steps[i] holds the steps due once binders[i] has bound.
	steps [][]joinStep
}

// joinStep is one step of a closure join that is not a binder: a filter literal, or (#2258
// L3.3b) a count over a strictly lower certificate's relation (isCount).
type joinStep struct {
	isCount bool
	filter  BodyLit
	count   CountLit
}

// runStep runs one step at its evaluation point: a filter is decided (filterOutcome), a count
// folds and binds or tests its result (countStage), recording what it bound in newly. #3165: the
// step's outcome is three-valued, since a theory filter may not be decided.
func runStep(step joinStep, subst Subst, view certView, theory Theory, limits CheckLimits, joins *int, newly *[]VarId) (closureTruth, *certErr) {
	if step.isCount {
		ok, e := countStage(step.count, subst, view, limits, joins, newly)
		return truthOf(ok), e
	}
	return filterOutcome(step.filter, subst, view, theory, limits, joins)
}

// closureTruth is a closure literal's, or a body's, three-valued truth (#3165), in the completion
// algebra.
type closureTruth = completion.GroundOutcome[completion.NoCallerLimit]

// truthOf is a decided truth value in the completion algebra.
func truthOf(holds bool) closureTruth {
	if holds {
		return completion.Completed[completion.Decision, completion.NoCallerLimit](completion.Holds())
	}
	return completion.Completed[completion.Decision, completion.NoCallerLimit](completion.Fails(completion.FalseUnsatisfied))
}

// bodyContinues is what a tuple's body, folded so far with completion.And, lets the join do
// (#3165). false prunes the tuple: a decided false makes the rule instance hold whatever the head,
// and it absorbs a literal-scoped stop (F and U is F). true continues, the body true so far or not
// decided at a scope another literal's false may still absorb. A stop no false can absorb is
// refused at once (builtin_not_decided): the instance's truth cannot be established.
//
// The join prunes at the FIRST decided false and evaluates nothing after it, as its pinned cost
// model requires, so a stop in a later literal is never seen. That is sound: the false is a
// completed decision, and the instance it falsifies holds whatever the later literal is. Rust's
// body_continues.
func bodyContinues(body closureTruth) (bool, *certErr) {
	return completion.MatchOutcome[completion.NoCallerLimit, bodyStep](body, bodyCases{}).result()
}

type bodyStep struct {
	cont bool
	err  *certErr
}

func (s bodyStep) result() (bool, *certErr) { return s.cont, s.err }

type bodyCases struct{}

func (bodyCases) Holds() bodyStep {
	return bodyStep{cont: true}
}

func (bodyCases) Fails(completion.FalseCode) bodyStep {
	return bodyStep{cont: false}
}

func (bodyCases) LimitExceeded(completion.NoCallerLimit) bodyStep {
	return bodyStep{err: &certErr{BuiltinNotDecided, completion.MalformedOutcome().Kind().Tag()}}
}

func (bodyCases) NotCompleted(cause completion.NonCompletion) bodyStep {
	if !cause.Kind().IsFault() && cause.Scope().Absorbable() {
		return bodyStep{cont: true}
	}
	return bodyStep{err: &certErr{BuiltinNotDecided, cause.Kind().Tag()}}
}

// undecidedCause is the cause of a body that is not decided, ok=false for a decided one.
func undecidedCause(body closureTruth) (completion.NonCompletion, bool) {
	return completion.MatchOutcome[completion.NoCallerLimit, undecided](body, undecidedCases{}).result()
}

type undecided struct {
	cause completion.NonCompletion
	ok    bool
}

func (u undecided) result() (completion.NonCompletion, bool) { return u.cause, u.ok }

type undecidedCases struct{}

func (undecidedCases) Holds() undecided {
	return undecided{}
}

func (undecidedCases) Fails(completion.FalseCode) undecided {
	return undecided{}
}

func (undecidedCases) LimitExceeded(completion.NoCallerLimit) undecided {
	return undecided{cause: completion.MalformedOutcome(), ok: true}
}

func (undecidedCases) NotCompleted(cause completion.NonCompletion) undecided {
	return undecided{cause: cause, ok: true}
}

// allIn reports whether every variable of vars is in set.
func allIn(vars, set map[VarId]struct{}) bool {
	for v := range vars {
		if _, ok := set[v]; !ok {
			return false
		}
	}
	return true
}

func planJoin(clause Clause, view certView, theory Theory) (joinPlan, *certErr) {
	// A positive literal on a predicate this cert seals (and no theory owns), or reads from a
	// strictly lower certificate (#2258 (a)), is a BINDER over that sealed table.
	isBinder := func(bl BodyLit) bool {
		if bl.IsNeg() {
			return false
		}
		g, ok := bl.AsInner()
		return ok && ((view.cert.Scope.Seals(g.Pred) && !theory.Owns(g.Pred)) || view.readsLower(g.Pred))
	}
	var plan joinPlan
	// The variables bound once binder i has bound: the cumulative set, in declared order.
	var boundAfter []map[VarId]struct{}
	bound := map[VarId]struct{}{}
	for _, bl := range clause.Body {
		// A count is not a binder: it is a count stage, placed below (#2258 L3.3b).
		if !isBinder(bl) {
			continue
		}
		g, _ := bl.AsInner()
		collectVarsGoal(g, bound)
		snapshot := make(map[VarId]struct{}, len(bound))
		for v := range bound {
			snapshot[v] = struct{}{}
		}
		boundAfter = append(boundAfter, snapshot)
		plan.binders = append(plan.binders, g)
		plan.steps = append(plan.steps, nil)
	}
	// #2258 L3.3b: each count stage at the first point its filter is bound, and the results it
	// binds there. available[i] is then everything bound once point i has run.
	leadingResults := map[VarId]struct{}{}
	resultsAt := make([]map[VarId]struct{}, len(plan.binders))
	for i := range resultsAt {
		resultsAt[i] = map[VarId]struct{}{}
	}
	for _, bl := range clause.Body {
		if !bl.IsCount() {
			continue
		}
		count := bl.CountVal
		vars := map[VarId]struct{}{}
		for _, e := range count.Filter {
			collectVarsTerm(e.Term, vars)
		}
		if len(vars) == 0 {
			plan.leading = append(plan.leading, joinStep{isCount: true, count: count})
			collectVarsTerm(count.Count, leadingResults)
			continue
		}
		placed := false
		for i, b := range boundAfter {
			if allIn(vars, b) {
				plan.steps[i] = append(plan.steps[i], joinStep{isCount: true, count: count})
				collectVarsTerm(count.Count, resultsAt[i])
				placed = true
				break
			}
		}
		if !placed {
			return plan, &certErr{CertScopeIncomplete, fmt.Sprintf(
				"closure count over predicate %q has a filter variable no positive sealed literal binds (unsafe existential)", count.Pred.Pred.String())}
		}
	}
	available := make([]map[VarId]struct{}, len(plan.binders))
	seen := map[VarId]struct{}{}
	for v := range leadingResults {
		seen[v] = struct{}{}
	}
	for i := range plan.binders {
		for v := range boundAfter[i] {
			seen[v] = struct{}{}
		}
		for v := range resultsAt[i] {
			seen[v] = struct{}{}
		}
		snapshot := make(map[VarId]struct{}, len(seen))
		for v := range seen {
			snapshot[v] = struct{}{}
		}
		available[i] = snapshot
	}
	for _, bl := range clause.Body {
		if isBinder(bl) || bl.IsCount() {
			continue
		}
		g, ok := bl.AsInner()
		if !ok {
			continue
		}
		vars := map[VarId]struct{}{}
		collectVarsGoal(g, vars)
		if allIn(vars, leadingResults) {
			plan.leading = append(plan.leading, joinStep{filter: bl})
			continue
		}
		placed := false
		for i, b := range available {
			if allIn(vars, b) {
				plan.steps[i] = append(plan.steps[i], joinStep{filter: bl})
				placed = true
				break
			}
		}
		if !placed {
			return plan, &certErr{CertScopeIncomplete, fmt.Sprintf(
				"closure body literal on predicate %q has a variable no positive sealed literal binds (unsafe existential)", g.Pred.String())}
		}
	}
	return plan, nil
}

// joinGroundings joins one sealed-scope clause over the sealed extensions, checking the
// closure obligation on every tuple it emits. The two counters are the certificate's cost
// model, pinned across the three cores: a GROUNDING is one body-true tuple the join emits;
// a JOIN STEP is one candidate examined at one body literal — a table row offered to a
// binder, or the current tuple offered to a filter. Both trip incrementally: cert_budget_exceeded
// the moment the count exceeds MaxRuleGroundings / MaxJoinSteps, or cert_decl_mismatch (#2335)
// the moment it exceeds the certificate's OWN DECLARATION of them (#1852). The pre-scan gate has
// already established
// declared <= budget, so the declaration is the tighter wall, a lying declaration is caught
// like the other three fields' are, and a scan is never paid past min(declared, budget).
// Mirrors Rust's join_groundings.
func joinGroundings(clause Clause, view certView, theory Theory, limits CheckLimits, groundings, joins *int) *certErr {
	plan, e := planJoin(clause, view, theory)
	if e != nil {
		return e
	}
	subst := Subst{}
	// What a leading count binds stays bound for the whole clause, so nothing is undone.
	var leadingBound []VarId
	// #3165: the body folded so far, three-valued. A leading filter's stop is carried into every
	// tuple of the clause.
	body := truthOf(true)
	for _, step := range plan.leading {
		outcome, e := runStep(step, subst, view, theory, limits, joins, &leadingBound)
		if e != nil {
			return e
		}
		body = completion.And(body, outcome)
		cont, e := bodyContinues(body)
		if e != nil {
			return e
		}
		if !cont {
			return nil
		}
	}
	return joinStage(clause, plan, 0, body, subst, view, theory, limits, groundings, joins)
}

func joinStage(clause Clause, plan joinPlan, stage int, body closureTruth, subst Subst, view certView, theory Theory, limits CheckLimits, groundings, joins *int) *certErr {
	cert := view.cert
	if stage == len(plan.binders) {
		// Every binder has bound and every filter has passed: one body-true tuple, or (#3165) one
		// whose body is not decided, which the counters count the same way.
		*groundings++
		if *groundings > limits.MaxRuleGroundings {
			return &certErr{CertBudgetExceeded, fmt.Sprintf("counted rule_groundings %d exceeds budget %d", *groundings, limits.MaxRuleGroundings)}
		}
		if uint64(*groundings) > cert.LimitsDecl.RuleGroundings {
			return &certErr{CertDeclMismatch, fmt.Sprintf("actual rule_groundings %d exceeds declared %d", *groundings, cert.LimitsDecl.RuleGroundings)}
		}
		head, ok := clause.Head.Substitute(subst).AsGround()
		if !ok {
			// §3.2 binds every head variable through a binder, so this cannot happen.
			return &certErr{CertNotClosed, "closure head not ground under join"}
		}
		// #3165: a body that is not decided holds the instance only through a present head. If
		// the head is absent (or cannot be), the instance's truth is not established: refused by
		// name, never read as closed and never as a violation.
		cause, undecidedBody := undecidedCause(body)
		for _, arg := range head.Args {
			if _, ok := cert.DomainContaining(arg); !ok {
				if undecidedBody {
					return &certErr{BuiltinNotDecided, cause.Kind().Tag()}
				}
				return &certErr{CertOutOfDomain, "satisfied grounding produces a head value outside the sealed domain"}
			}
		}
		if t, ok := cert.Table(head.Pred); !ok || !t.Contains(head) {
			if undecidedBody {
				return &certErr{BuiltinNotDecided, cause.Kind().Tag()}
			}
			return &certErr{CertNotClosed, fmt.Sprintf(
				"satisfied grounding of a scope rule has head %q absent from E", head.Pred.String())}
		}
		return nil
	}
	goal := plan.binders[stage]
	table, ok := view.table(goal.Pred)
	if !ok {
		return &certErr{CertScopeIncomplete, fmt.Sprintf(
			"closure body literal on predicate %q is sealed by the scope but has no sealed extension (undecidable)", goal.Pred.String())}
	}
	for _, row := range table.Rows {
		if e := countJoinStep(joins, cert, limits); e != nil {
			return e
		}
		var newly []VarId
		var result *certErr
		if bindRow(goal, row, subst, &newly) {
			pass := true
			tuple := body
			for _, step := range plan.steps[stage] {
				// A count stage's result is recorded in newly too, so it is undone below.
				outcome, e := runStep(step, subst, view, theory, limits, joins, &newly)
				if e != nil {
					result = e
					break
				}
				tuple = completion.And(tuple, outcome)
				cont, e := bodyContinues(tuple)
				if e != nil {
					result = e
					break
				}
				if !cont {
					pass = false
					break
				}
			}
			if result == nil && pass {
				result = joinStage(clause, plan, stage+1, tuple, subst, view, theory, limits, groundings, joins)
			}
		}
		for _, v := range newly {
			delete(subst, v)
		}
		if result != nil {
			return result
		}
	}
	return nil
}

// bindRow unifies a binder's arguments against one sealed row under subst: a bound
// variable or a constant must EQUAL the row's value at that position; an unbound variable
// is bound to it (recorded in newly so the caller can undo it). False on the first mismatch.
func bindRow(goal Goal, row GroundLiteral, subst Subst, newly *[]VarId) bool {
	if !row.Pred.Equal(goal.Pred) || len(row.Args) != len(goal.Args) {
		return false
	}
	for i, term := range goal.Args {
		if !unifyGround(term, FromValue(row.Args[i]), subst, newly) {
			return false
		}
	}
	return true
}

func unifyGround(term, ground Term, subst Subst, newly *[]VarId) bool {
	switch t := term.(type) {
	case VarTerm:
		if bound, ok := subst[t.id]; ok {
			return bound.Equal(ground)
		}
		subst[t.id] = ground
		*newly = append(*newly, t.id)
		return true
	case AtomTerm:
		return t.Equal(ground)
	case TupleTerm:
		g, ok := ground.(TupleTerm)
		if !ok || len(g.children) != len(t.children) {
			return false
		}
		for i, c := range t.children {
			if !unifyGround(c, g.children[i], subst, newly) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

// countJoinStep charges one join step and trips cert_budget_exceeded the moment the count
// exceeds the run's budget, or, past that, cert_decl_mismatch (#2335) the moment it exceeds the
// certificate's own declared JoinSteps (#1852). The budget is tested first so that at declared == budget the budget wording
// wins; the pre-scan gate guarantees declared <= budget, so the declaration can only be the
// tighter of the two, and the scan is bounded by it.
func countJoinStep(joins *int, cert ClosedModelCert, limits CheckLimits) *certErr {
	*joins++
	if *joins > limits.MaxJoinSteps {
		return &certErr{CertBudgetExceeded, fmt.Sprintf("counted join_steps %d exceeds budget %d", *joins, limits.MaxJoinSteps)}
	}
	if uint64(*joins) > cert.LimitsDecl.JoinSteps {
		return &certErr{CertDeclMismatch, fmt.Sprintf("actual join_steps %d exceeds declared %d", *joins, cert.LimitsDecl.JoinSteps)}
	}
	return nil
}

// filterOutcome evaluates one FILTER literal at its evaluation point: it must be ground there
// (§3.2), and is decided against E (+ the pinned Theory) with polarity by evalBodyLiteral.
// Costs one join step. Never a silent false: a literal that is not ground at its point is a
// HARD error (cert_scope_incomplete), the same backstop the enumeration carried. #3165: the
// outcome is three-valued, since a theory literal may not be decided.
func filterOutcome(bodyLit BodyLit, subst Subst, view certView, theory Theory, limits CheckLimits, joins *int) (closureTruth, *certErr) {
	if e := countJoinStep(joins, view.cert, limits); e != nil {
		return closureTruth{}, e
	}
	inner, _ := bodyLit.AsInner()
	grounded, ok := inner.Substitute(subst).AsGround()
	if !ok {
		return closureTruth{}, &certErr{CertScopeIncomplete, fmt.Sprintf(
			"closure body literal on predicate %q is not ground at its evaluation point (unsafe existential)", bodyLit.Pred().String())}
	}
	return evalBodyLiteral(bodyLit, grounded, view, theory)
}

// evalBodyLiteral reports (true) iff one grounded body literal is satisfied against E
// (+ theory), with polarity: a Pos literal must be present (sealed-table membership or
// Holds); a Neg literal must be ABSENT from its sealed table — this cert's own, or the exact
// table of the strictly lower certificate it reads the predicate from (#2258 (a)). An
// undecidable literal — a predicate neither sealed for this cert nor theory-owned — is a HARD
// error (cert_scope_incomplete).
func evalBodyLiteral(bodyLit BodyLit, grounded GroundLiteral, view certView, theory Theory) (closureTruth, *certErr) {
	undecidable := func() *certErr {
		return &certErr{CertScopeIncomplete, fmt.Sprintf(
			"closure body literal on predicate %q is neither sealed nor theory-owned (undecidable)", grounded.Pred.String())}
	}
	if !bodyLit.IsNeg() {
		if theory.Owns(grounded.Pred) {
			return theoryTruth(theory, grounded)
		}
		if t, ok := view.table(grounded.Pred); ok {
			return truthOf(t.Contains(grounded)), nil
		}
		return closureTruth{}, undecidable()
	}
	// Negated body literal: \+ b is true iff b does NOT Hold / is ABSENT, and a b that is not
	// decided leaves \+ b not decided (not(U) = U, #3165).
	if theory.Owns(grounded.Pred) {
		truth, err := theoryTruth(theory, grounded)
		if err != nil {
			return closureTruth{}, err
		}
		return completion.Not(truth), nil
	}
	if t, ok := view.table(grounded.Pred); ok {
		return truthOf(!t.Contains(grounded)), nil
	}
	return closureTruth{}, undecidable()
}

// theoryTruth is a theory-owned literal's truth inside the closure (#3022 step 4, research 0028
// A8; #3165): the theory's ground verdict (DecideGround), through the ONE conversion into the
// algebra (completion.DecisionOf). Holds is true, Fails false, and a stop stays NOT DECIDED, never
// false: the join folds it and refuses the instance unless a false absorbs it or the head is
// present. The disowning fault (NotMine after Owns said yes) is an inconsistent theory, and it
// REFUSES by name (predicate_partition_violation, as a Builtin node's does), never reads as false:
// a positive filter read false would let the closure under-fire and pass a table that is not
// closed. So does an outcome no constructor could have built (a nil or unknown TheoryOutcome). rs
// theory_truth.
func theoryTruth(theory Theory, grounded GroundLiteral) (closureTruth, *certErr) {
	ground := DecideGround(theory, grounded)
	verdict := readGround(ground)
	if verdict.disowned() {
		return closureTruth{}, &certErr{PredicatePartitionViolation, fmt.Sprintf(
			"closure body literal on predicate %q: the theory owns it but returned NotMine", grounded.Pred.String())}
	}
	if verdict.arm == groundNotDecided && verdict.cause.Kind() == completion.KindMalformedOutcome {
		return closureTruth{}, &certErr{PredicatePartitionViolation, fmt.Sprintf(
			"closure body literal on predicate %q: the theory owns it but returned no outcome it could have built", grounded.Pred.String())}
	}
	return completion.DecisionOf(ground), nil
}

// verifyNegPremise verifies a single Neg { Atom, Cert, Nonmember } premise against the
// (already memoized) certificate status — the per-Neg obligations of ADR 0007 §4:
//  1. the cited cert index is in range (cert_out_of_range);
//  2. the cert is Valid (else surface its failure code);
//  3. the negated predicate is sealed by the cert scope (neg_atom_not_sealed);
//  4. the negated predicate is in a STRICTLY LOWER stratum than the rule head
//     (neg_stratum_not_lower) — i.e. the head predicate is NOT sealed by the cert's
//     lower-stratum scope (stratified negation looks only downward);
//  5. the atom is ground + within a supplied finite domain (neg_atom_ill_typed);
//  6. the atom is ABSENT from the sealed table (neg_atom_present if present).
func verifyNegPremise(atom GroundLiteral, certID CertId, _ NonMemberProof, headPred Symbol, deriv Derivation, certStatus []certStatus) Outcome {
	idx, ok := certID.Offset(len(deriv.ClosedWorld))
	if !ok {
		return reject(CertOutOfRange, fmt.Sprintf("neg premise cites cert %d out of range %d", certID.Index(), len(deriv.ClosedWorld)))
	}
	cert := deriv.ClosedWorld[idx]

	// 2. the cert must be Valid (reuse the memoized status).
	if st := certStatus[idx]; !st.valid {
		return reject(st.code, st.detail)
	}

	// 3. predicate sealed by the cert scope.
	if !cert.Scope.Seals(atom.Pred) {
		return reject(NegAtomNotSealed, "negated predicate is not sealed by the cited certificate")
	}

	// 3b. sealed EXACTLY (ADR 0030 D2): a table in PartialScope is a lower bound of its
	//     least-model relation, so absence from it proves nothing — a later round could derive
	//     the atom. Sealed, but not sealed exactly, sits between "not sealed" (3) and "not
	//     lower" (4). Mirrors rs verify_neg_premise.
	if cert.IsPartial(atom.Pred) {
		return reject(NegAtomPartial, "negated predicate's sealed table is marked PARTIAL (a lower bound) — absence from it proves nothing (ADR 0030 D2)")
	}

	// 4. strictly lower stratum: the RULE HEAD predicate must NOT be in the cert's
	//    (lower) scope.
	if cert.Scope.Seals(headPred) {
		return reject(NegStratumNotLower, "rule head predicate is in the same (or lower) sealed stratum as the negated atom")
	}

	// 5. ground + well-typed within a supplied finite domain.
	for _, arg := range atom.Args {
		if _, ok := cert.DomainContaining(arg); !ok {
			return reject(NegAtomIllTyped, "negated atom argument is outside the certificate's finite domain")
		}
	}

	// 6. ABSENT from the sealed relation (else \+ fails — the atom IS present).
	table, ok := cert.Table(atom.Pred)
	if !ok {
		return reject(NegAtomNotSealed, "negated predicate sealed but has no extension table")
	}
	if table.Contains(atom) {
		return reject(NegAtomPresent, "negated atom IS present in the sealed relation")
	}

	return Accept()
}

// isNullValue reports whether v is the canonical null() marker (ADR 0023 Phase 0). With
// ontos's nullary-compound convention, null() is Tuple[Atom("null")] — the same shape a
// nullary goal p() reads as. count_distinct EXCLUDES a projected value equal to this
// marker (SQL-style). Recognized structurally so the go mirror does not depend on a newer
// ontos null() constructor — the same shape the rs oracle's is_null_value recognizes.
func isNullValue(v core.Value) bool {
	t, ok := v.(core.Tuple)
	if !ok {
		return false
	}
	items := t.Items()
	if len(items) != 1 {
		return false
	}
	a, ok := items[0].(core.Atom)
	if !ok {
		return false
	}
	return string(a.Bytes()) == "null"
}

// verifyCountPremise verifies a single Count { Pred, Filter, Project, K, Cert } premise
// against the (already memoized) certificate status — the per-Count obligations of ADR
// 0023 §"what the checker verifies". A structural clone of verifyNegPremise (steps 1–4
// identical: cert in range + Valid, predicate sealed, strictly-lower stratum); step 5
// swaps the membership test for a counted projection — recompute n over the proven-exact
// RelationTable and require n == K, else count_mismatch. Mirrors Rust's verify_count_premise.
func verifyCountPremise(pred PredicateRef, filter []GroundFilterEntry, project ProjectSpec, k core.Value, certID CertId, headPred Symbol, deriv Derivation, certStatus []certStatus) Outcome {
	// 1. cert index in range.
	idx, ok := certID.Offset(len(deriv.ClosedWorld))
	if !ok {
		return reject(CertOutOfRange, fmt.Sprintf("count premise cites cert %d out of range %d", certID.Index(), len(deriv.ClosedWorld)))
	}
	cert := deriv.ClosedWorld[idx]

	// 2. the cert must be Valid (reuse the memoized status — support+closure already
	//    proved the sealed relation EXACT; the count does not re-prove exactness).
	if st := certStatus[idx]; !st.valid {
		return reject(st.code, st.detail)
	}

	// 3. predicate sealed by the cert scope (matched by name; arity is checked in 5).
	if !cert.Scope.Seals(pred.Pred) {
		return reject(NegAtomNotSealed, "counted predicate is not sealed by the cited certificate")
	}

	// 3b. sealed EXACTLY (ADR 0030 D2): a cardinality over a lower bound is itself a lower
	//     bound, never the claimed k — the count twin of NegAtomPartial.
	if cert.IsPartial(pred.Pred) {
		return reject(CountOverPartial, "counted predicate's sealed table is marked PARTIAL (a lower bound) — a count over it is a lower bound, never the claimed k (ADR 0030 D2)")
	}

	// 4. strictly lower stratum: the RULE HEAD predicate must NOT be sealed by the cert's
	//    (lower) scope — a count may only depend on a strictly lower stratum.
	if cert.Scope.Seals(headPred) {
		return reject(CountStratumNotLower, "rule head predicate is in the same (or lower) sealed stratum as the counted relation")
	}

	// 5. recompute n over the sealed table.
	table, ok := cert.Table(pred.Pred)
	if !ok {
		return reject(NegAtomNotSealed, "counted predicate sealed but has no extension table")
	}
	arity := int(table.Arity)

	// 5·#581 ARITY AGREEMENT. The counted relation is matched by name AND arity: a
	//     PredicateRef whose arity disagrees with the sealed table would otherwise count
	//     rows of a DIFFERENT-arity relation under the same name → count_attr_out_of_range.
	if int(pred.Arity) != arity {
		return reject(CountAttrOutOfRange, fmt.Sprintf("count predicate arity %d does not match the sealed table arity %d", pred.Arity, arity))
	}

	// 5a. filter well-typed: each position is within arity and its value is ground +
	//     within the cert's finite domain.
	for _, e := range filter {
		if int(e.Pos) >= arity {
			return reject(CountAttrOutOfRange, fmt.Sprintf("count filter position %d is outside predicate arity %d", e.Pos, arity))
		}
		if _, ok := cert.DomainContaining(e.Value); !ok {
			return reject(NegAtomIllTyped, "count filter value is outside the certificate's finite domain")
		}
	}

	// 5b. projection attr within arity — for EVERY column-bearing kind (Distinct, and the
	//     #587 sum/min/max folds), not just count_distinct. Rows bears no column.
	if project.HasColumn() && int(project.Attr) >= arity {
		return reject(CountAttrOutOfRange, fmt.Sprintf("aggregate projection attr %d is outside predicate arity %d", project.Attr, arity))
	}

	// 5c. ONE LINEAR SCAN over the proven-exact rows: select the rows matching the filter,
	//     then fold per the projection kind:
	//       - Rows ⇒ count the matching rows.
	//       - Distinct{attr} ⇒ count distinct projected values (deduped by the canonical
	//         codec key, null() excluded; ADR 0023 Phase 0).
	//       - Sum/Min/Max{attr} (#587) ⇒ read each matching row's column attr as a canonical
	//         int (a non-int — including null() — is count_attr_out_of_range, v1 is
	//         integer-only). Sum folds (empty ⇒ 0); Min/Max take the integer extremum over
	//         the BigInt total order, rejecting agg_empty_undefined on ZERO matching rows.
	//     The recomputed result is a BigInt compared against the claimed k in 5d.
	//     The fold is ADR 0023's one aggregate semantics (evaluateAggregate), the one a closure
	//     count stage and a CountLower support ref evaluate too (#2258 L3.3b).
	recomputed, ce := evaluateAggregate(table.Rows, filter, project)
	if ce != nil {
		return reject(ce.code, ce.detail)
	}

	// 5d. compare the recomputed BigInt result against the claimed k (the canonical int
	//     embedding) — mismatch is count_mismatch.
	claimed, err := data.ReadInt(k)
	if err != nil {
		return reject(CountMismatch, "count premise k is not a canonical int value")
	}
	if claimed.Cmp(recomputed) != 0 {
		return reject(CountMismatch, fmt.Sprintf("claimed aggregate %s != recomputed %s", claimed.String(), recomputed.String()))
	}

	return Accept()
}
