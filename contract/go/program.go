// §2 Program — clauses as data, not engine. [FIRM]
//
// A Clause is head :- body₀, …, bodyₙ (an empty body is a rule-fact). A consumer's
// whole policy *is* a Program — data — so swapping the engine never touches the
// policy. check validates only the clauses a derivation cites: the single-method
// lookup Program.Clause is all the checker requires.
package contract

import (
	"bytes"
	"sort"
)

// ClauseId is an opaque clause handle. For v1 its only contract is *stable +
// lookup-able*. It is deliberately NOT yet a canonical hash (§9). A consumer that
// already has a canonical hash (e.g. arche) may use it here. Held as a comparable
// value type so it can be a map key (mirroring Rust's deriving Ord/Hash).
type ClauseId struct {
	handle string
}

// NewClauseId builds a ClauseId from a handle.
func NewClauseId(handle string) ClauseId { return ClauseId{handle: handle} }

// String returns the clause handle.
func (c ClauseId) String() string { return c.handle }

// Polarity tags a body literal as positive, negated, or a certifiable aggregate
// (ADR 0007 / ADR 0023). Sibling of Rust's BodyLit enum discriminant.
type Polarity int

const (
	// Pos is a positive body literal p(t…).
	Pos Polarity = iota
	// Neg is a negated body literal \+ p(t…) — discharged by a closed-model
	// certificate (ADR 0007), never by a derivation node.
	Neg
	// Count is a certifiable count/count_distinct body literal (ADR 0023) —
	// discharged by recomputing the cardinality over a closed-model certificate,
	// never by a derivation node. Its payload lives in BodyLit.Count, not BodyLit.Lit.
	Count
)

// PredicateRef is an ARITY-SENSITIVE reference to the sealed relation a certifiable
// aggregate counts over (ADR 0023, #581). A counted relation is matched by name AND
// arity — obs/3 and obs/2 are different relations — so a wrong-arity count cannot slip
// past name agreement alone (a mismatch is count_attr_out_of_range). Go sibling of
// Rust's PredicateRef. Held as comparable fields so PredicateRef is a value type.
type PredicateRef struct {
	Pred  Symbol
	Arity uint32
}

// NewPredicateRef builds an arity-sensitive predicate reference.
func NewPredicateRef(pred Symbol, arity uint32) PredicateRef {
	return PredicateRef{Pred: pred, Arity: arity}
}

// Equal reports whether two predicate refs name the same relation (same predicate
// bytes AND same arity).
func (p PredicateRef) Equal(other PredicateRef) bool {
	return p.Pred.Equal(other.Pred) && p.Arity == other.Arity
}

// ProjectKind is what a certifiable aggregate folds over a sealed relation's matching
// rows (ADR 0023). Distinct predicates, not a flag. Go sibling of Rust's ProjectSpec
// enum discriminant. ProjectRows counts; the remaining four carry a 0-based column
// index Attr they project/fold over (count_distinct, sum, min, max).
type ProjectKind int

const (
	// ProjectRows is `count`: count the rows matching the filter (no projection).
	ProjectRows ProjectKind = iota
	// ProjectDistinct is `count_distinct`: count the distinct values of one projected
	// attribute (column Attr) across the matching rows, deduped by the canonical codec
	// key and EXCLUDING null() (SQL-style; ADR 0023 Phase 0).
	ProjectDistinct
	// ProjectSum is `sum`: the integer sum of column Attr over the matching rows (ADR
	// 0023 #587). v1 is INTEGER-ONLY over the proven-exact deduped rows; the empty sum
	// is 0. A non-int column value is count_attr_out_of_range.
	ProjectSum
	// ProjectMin is `min`: the integer minimum of column Attr over the matching rows
	// (ADR 0023 #587). v1 is INTEGER-ONLY; the min of an EMPTY set is undefined →
	// agg_empty_undefined. A non-int column value is count_attr_out_of_range.
	ProjectMin
	// ProjectMax is `max`: the integer maximum of column Attr over the matching rows
	// (ADR 0023 #587). v1 is INTEGER-ONLY; the max of an EMPTY set is undefined →
	// agg_empty_undefined. A non-int column value is count_attr_out_of_range.
	ProjectMax
)

// ProjectSpec carries the aggregate projection: ProjectRows (count) or a column-bearing
// fold (count_distinct / sum / min / max) with a 0-based attribute index. Go sibling of
// Rust's ProjectSpec. Attr is meaningful only for the column-bearing kinds; out of range
// is count_attr_out_of_range.
type ProjectSpec struct {
	Kind ProjectKind
	Attr uint32
}

// Rows is the `count` projection.
func Rows() ProjectSpec { return ProjectSpec{Kind: ProjectRows} }

// Distinct is the `count_distinct` projection over attribute attr.
func Distinct(attr uint32) ProjectSpec { return ProjectSpec{Kind: ProjectDistinct, Attr: attr} }

// Sum is the `sum` fold over integer column attr (ADR 0023 #587).
func Sum(attr uint32) ProjectSpec { return ProjectSpec{Kind: ProjectSum, Attr: attr} }

// Min is the `min` fold over integer column attr (ADR 0023 #587).
func Min(attr uint32) ProjectSpec { return ProjectSpec{Kind: ProjectMin, Attr: attr} }

// Max is the `max` fold over integer column attr (ADR 0023 #587).
func Max(attr uint32) ProjectSpec { return ProjectSpec{Kind: ProjectMax, Attr: attr} }

// HasColumn reports whether this projection bears a column index (everything but Rows).
// Sibling of Rust's ProjectSpec::attr() returning Some for the column-bearing variants.
func (p ProjectSpec) HasColumn() bool { return p.Kind != ProjectRows }

// Equal reports structural identity of two projection specs. The Attr is compared for
// every column-bearing kind (Distinct/Sum/Min/Max), not just Distinct.
func (p ProjectSpec) Equal(other ProjectSpec) bool {
	if p.Kind != other.Kind {
		return false
	}
	if p.HasColumn() {
		return p.Attr == other.Attr
	}
	return true
}

// CountFilterEntry is one (position, term) of a count filter: it requires the counted
// row's argument at Pos to equal the (grounded) Term. Go sibling of Rust's filter pair.
type CountFilterEntry struct {
	Pos  uint32
	Term Term
}

// CountLit is a certifiable count / count_distinct body literal (ADR 0023). It is NOT a
// derivation node: like a negated literal, it is discharged as a checked side-condition
// against a sealed ClosedModelCert by verifyCountPremise — the searcher proposes the
// cardinality, the gate re-derives it over a relation it has independently proven exact.
// Go sibling of Rust's CountLit<Term>.
type CountLit struct {
	// Pred is the sealed relation whose rows are counted — matched by name AND arity.
	Pred PredicateRef
	// Filter is the ground/bound-position filter (caller order preserved; treated
	// positionally, not as a set). An empty filter counts every row of Pred.
	Filter []CountFilterEntry
	// Project is Rows (count) or Distinct (count_distinct of one column).
	Project ProjectSpec
	// Count is the result slot — the claimed cardinality k, as a term that binds a head var.
	Count Term
}

// Substitute applies a grounding substitution to the filter terms and the count slot,
// preserving the predicate and projection (which are structural, not substituted).
func (c CountLit) Substitute(subst Subst) CountLit {
	filter := make([]CountFilterEntry, len(c.Filter))
	for i, e := range c.Filter {
		filter[i] = CountFilterEntry{Pos: e.Pos, Term: e.Term.Substitute(subst)}
	}
	return CountLit{Pred: c.Pred, Filter: filter, Project: c.Project, Count: c.Count.Substitute(subst)}
}

// BodyLit is a clause body literal carrying polarity (ADR 0007 / ADR 0023) — Pos for a
// positive subgoal p(t…), Neg for a negated subgoal \+ p(t…), Count for a certifiable
// aggregate. Go sibling of Rust's BodyLit<Term> enum.
//
// Additive (ADR 0007 / ADR 0023): today's account is exactly an all-Pos body. The
// account codec (account.go) reads a Pos literal byte-identically to the bare
// goalAsTerm(goal) (no wrapper), so existing positive clause ids are unchanged; a Neg
// literal and a Count literal each get a distinct tagged reading, so a body with no
// Count literal encodes byte-identically to the pre-amendment account. A Count literal's
// payload lives in CountVal (Lit is unused for a Count).
type BodyLit struct {
	Polarity Polarity
	Lit      Goal
	CountVal CountLit
}

// PosLit lifts a goal to a positive body literal.
func PosLit(g Goal) BodyLit { return BodyLit{Polarity: Pos, Lit: g} }

// NegLit lifts a goal to a negated body literal.
func NegLit(g Goal) BodyLit { return BodyLit{Polarity: Neg, Lit: g} }

// CountLitBody lifts a CountLit to a count body literal (ADR 0023).
//
// Lit IS INTENTIONALLY LEFT UNSET — do not "fix" this by populating it. See logos#723 and
// thesmos#409. A Count carries no single underlying Goal (its payload is CountVal), so the
// zero value is the honest encoding, and Rust's BodyLit::Count(CountLit) carries no such
// field at all. Our ts core currently populates it with the counted predicate's name; that
// divergence is the open question in #723, and empty-in-both is the direction under
// consideration — not populate-in-both.
//
// HISTORICAL — A CONSUMER GATE ONCE STOOD ON THIS FIELD BEING EMPTY. DISCHARGED 2026-07-27;
// NO LIVE DEPENDENCY REMAINS, AND THIS IMPOSES NO ORDERING ON ANYONE TODAY. Kept because the
// hazard recurs, not because it is open.
//
// What it was: thesmos's go admissibility gate (core/go/semantics: ruleAdmissible) guarded
// polarity only with IsNeg(), then read the literal's goal predicate through the since-deleted
// Inner() accessor (#2733) and rejected on the empty symbol — so
// a count-bearing rule-fact was refused *because* this was unset, through a check written for
// malformed literals. Populating this field would have silently turned a tri-core 1-admit
// into 2-admit over attacker-supplied bytes. The commit doing it would have been small,
// correct, and would not have mentioned authorization.
//
// Why it is gone: that gate now requires the GOOD variant (`b.Polarity != logos.Pos`) instead
// of enumerating the bad ones, so it reads no field off a non-Pos literal and is indifferent
// to what this holds. Note their first cut was `IsNeg() || IsCount()` — correct that day and
// still an enumeration, which a fourth polarity would fall through; requiring Pos fails closed
// instead. The hazard ended by construction rather than by sequencing, which is why there is
// no ordering rule here to obey.
//
// Raised by Alethe (3ad6fef1@fleet) via assay@lab and cca@thesmos, verified against thesmos
// main; released by d86216ae/f5a28473 within the hour.
func CountLitBody(c CountLit) BodyLit { return BodyLit{Polarity: Count, CountVal: c} }

// AsInner returns the underlying goal of a Pos/Neg body literal and true, or the zero
// Goal and false for a Count. It is TOTAL (#728, the same additive shape
// as IsPos in #722), the go face of rust's as_inner() -> Option<&Literal> and ts's
// asInner(): Goal | null. A WHITELIST over the polarity (the IsPos doctrine): a future
// non-Pos/Neg polarity yields ok=false, never a sentinel. Prefer this wherever the body
// may carry a Count — any clause decoded from bytes (#727 established a Count round-trips
// the clause codec): the absent case lands in the caller's control flow identically in
// every core, instead of hitting a per-core failure mode.
func (b BodyLit) AsInner() (Goal, bool) {
	if b.Polarity == Pos || b.Polarity == Neg {
		return b.Lit, true
	}
	return Goal{}, false
}

// IsPos reports whether this is a plain positive body literal.
//
// Prefer this over "not IsNeg and not IsCount" when gating on positive-only bodies. A
// consumer that admits by ruling out the known non-positive variants is writing a
// BLACKLIST: every polarity added here later is admitted by default, silently, in every
// consumer that has not been updated. IsPos is total over the polarity — it stays correct
// for variants that do not exist yet — so a positive-Horn gate (arche PROTOCOL 3.10a) can
// be expressed as the whitelist it actually is. That matters most where the clause is
// attacker-supplied, since the default must be deny.
func (b BodyLit) IsPos() bool { return b.Polarity == Pos }

// IsNeg reports whether this is a negated body literal.
//
// NOT a building block for a positive-Horn gate. "not IsNeg and not IsCount" is a
// BLACKLIST: it admits every polarity added later, silently, in every consumer that has
// not been updated. Use IsPos, which is total over the polarity and stays correct for
// variants that do not exist yet — the reasoning is on IsPos.
func (b BodyLit) IsNeg() bool { return b.Polarity == Neg }

// IsCount reports whether this is a certifiable count body literal.
//
// NOT a building block for a positive-Horn gate — see IsNeg, and use IsPos.
func (b BodyLit) IsCount() bool { return b.Polarity == Count }

// Pred returns the predicate symbol this body literal is over — the underlying goal's
// predicate for Pos/Neg, or the counted relation's predicate for Count. Total over all
// variants (unlike Inner). Mirrors Rust's BodyLit::pred.
func (b BodyLit) Pred() Symbol {
	if b.Polarity == Count {
		return b.CountVal.Pred.Pred
	}
	return b.Lit.Pred
}

// ── first-class binding & dependency modes (research-doc 0009) ──────────────────
//
// The analyzer's range-restriction (safety) and dependency-graph passes must know, per body
// form, WHICH variables it binds, WHICH must already be bound, and WHAT dependency edge it
// contributes. These three total methods make those modes first-class metadata of the form
// itself, so a new body form declares its semantics here once and every pass reads them
// uniformly — retiring the ad-hoc IsCount()/IsNeg()/Inner() split. Mirrors rs BodyLit's
// binding_terms / required_terms / dependency.

// BindingTerms returns the argument terms whose variables this literal BINDS (range-restriction
// outputs): a positive atom binds all its arguments; a negation binds nothing; a count binds only
// its result term.
func (b BodyLit) BindingTerms() []Term {
	switch b.Polarity {
	case Pos:
		return b.Lit.Args
	case Count:
		return []Term{b.CountVal.Count}
	case Neg:
		return nil
	default:
		// UNKNOWN polarity (#996) — fail closed: assume it binds NOTHING. Until this arm
		// existed, `default` WAS the Pos case, so a polarity this core had never seen was
		// answered as the most permissive one we have.
		return nil
	}
}

// RequiredTerms returns the argument terms whose variables must ALREADY be positively bound for
// this literal to be safe (range-restriction inputs): a positive atom requires nothing (it binds);
// a negation requires all its arguments bound; a count requires its filter/group variables bound
// (its result is exempt — that is what it binds).
func (b BodyLit) RequiredTerms() []Term {
	switch b.Polarity {
	case Pos:
		return nil
	case Count:
		terms := make([]Term, 0, len(b.CountVal.Filter))
		for _, e := range b.CountVal.Filter {
			terms = append(terms, e.Term)
		}
		return terms
	case Neg:
		return b.Lit.Args
	default:
		// UNKNOWN polarity (#996) — fail closed: assume it can evaluate NOTHING on its own,
		// so every argument term must already be positively bound. The permissive answer
		// (nil, the old `default: // Pos`) told range restriction this literal was safe
		// unconditionally.
		return b.Lit.Args
	}
}

// Dependency returns the predicate this literal reads and whether its dependency edge is
// NON-MONOTONE: a negation or an aggregate both read a sealed, strictly-lower stratum, so the
// stratifier treats them identically. hasNegation (a per-stratum closed-world obligation) stays a
// Neg-only query via IsNeg — an aggregate adds a non-monotone edge but no closed-world obligation.
func (b BodyLit) Dependency() (Symbol, bool) {
	switch b.Polarity {
	case Pos:
		return b.Lit.Pred, false
	case Count:
		return b.CountVal.Pred.Pred, true
	case Neg:
		return b.Lit.Pred, true
	default:
		// UNKNOWN polarity (#996) — fail closed: assume it BREAKS monotonicity and force the
		// stratum barrier. The old `default: // Pos` returned false here, so an unseen
		// polarity reached the stratifier claiming to need no barrier at all.
		return b.Lit.Pred, true
	}
}

// Substitute applies a grounding substitution to the underlying literal, preserving
// polarity (the polarity is structural, not substituted).
func (b BodyLit) Substitute(subst Subst) BodyLit {
	if b.Polarity == Count {
		return BodyLit{Polarity: Count, CountVal: b.CountVal.Substitute(subst)}
	}
	return BodyLit{Polarity: b.Polarity, Lit: b.Lit.Substitute(subst)}
}

// Clause is head :- body₀, …, bodyₙ. The head is a Goal; each body literal is a
// polarity-tagged BodyLit (positive or negated). They contain variables — that is
// what makes a clause a *rule* rather than a ground fact. An empty body is a
// rule-fact.
type Clause struct {
	Head Goal
	Body []BodyLit
}

// NewClause builds a Clause from a head and positive body goals (each read as a
// Pos body literal), so every existing positive-body call site is unchanged.
func NewClause(head Goal, body ...Goal) Clause {
	lits := make([]BodyLit, len(body))
	for i, g := range body {
		lits[i] = PosLit(g)
	}
	return Clause{Head: head, Body: lits}
}

// NewClauseLits builds a Clause from a head and explicit polarity-tagged body
// literals (the general form mirroring Rust's Clause::new over BodyLit).
func NewClauseLits(head Goal, body ...BodyLit) Clause {
	return Clause{Head: head, Body: append([]BodyLit(nil), body...)}
}

// WithNeg builds head :- pos₀, …, \+ neg₀, … — a clause with explicit positive and
// negated body literals (ADR 0007). Positive literals are appended first, then the
// negated ones, so the body order is [pos…, neg…]. Mirrors Rust's Clause::with_neg.
func WithNeg(head Goal, pos []Goal, neg []Goal) Clause {
	body := make([]BodyLit, 0, len(pos)+len(neg))
	for _, g := range pos {
		body = append(body, PosLit(g))
	}
	for _, g := range neg {
		body = append(body, NegLit(g))
	}
	return Clause{Head: head, Body: body}
}

// Fact builds a rule-fact: a clause with an empty body.
func Fact(head Goal) Clause {
	return Clause{Head: head, Body: nil}
}

// Program is the capability check requires of a program: look a cited clause up by id
// (§2 "local checking"), and — for ADR-0007 certifiable negation — enumerate the
// whole clause set. Whole-program predicate-partition hygiene (§4.4) is a consumer /
// program-loading responsibility, not a per-check obligation. The second result of
// Clause is false when the id is unknown.
//
// ADR 0007 closure soundness. Certifying a negated premise \+ r(a) requires the
// checker to enumerate *every* clause defining a sealed predicate — the support
// witness's cited clauses are attacker-chosen and cannot be trusted to be complete (a
// non-cited defining clause could hide a derivable head). So Program carries
// ForEachClause, a *trusted* whole-program iteration in canonical clause-id order. A
// program that exposes an *empty* enumeration is fail-closed — the closure check then
// finds no defining clauses and (if any sealed predicate a \+ cites has no enumerated
// clause) the cert is rejected, never wrongly accepted.
//
// Go has no default interface methods (unlike the Rust trait, which defaults
// for_each_clause to a no-op), so ForEachClause is a required member. The only
// in-tree implementer is MapProgram; the kernel threads a MapProgram, never its own
// Program. A consumer with a custom Program that does not yet enumerate may implement
// ForEachClause as a no-op (fail-closed) until it wants certifiable negation.
type Program interface {
	Clause(id ClauseId) (Clause, bool)

	// ForEachClause calls f with every (id, clause) of the program, in canonical
	// clause-id byte order. The closure check (ADR 0007) drives over this to find all
	// clauses defining a sealed predicate.
	ForEachClause(f func(id ClauseId, clause Clause))
}

// MapProgram is a straightforward in-memory Program (a ClauseId → Clause map).
// Provided for tests, fixtures, and simple consumers; an engine may back Program by
// a store.
type MapProgram struct {
	clauses map[ClauseId]Clause
}

// NewMapProgram builds an empty MapProgram.
func NewMapProgram() *MapProgram {
	return &MapProgram{clauses: make(map[ClauseId]Clause)}
}

// With inserts a clause and returns the program (builder style).
func (p *MapProgram) With(id ClauseId, clause Clause) *MapProgram {
	p.clauses[id] = clause
	return p
}

// Insert adds or replaces a clause by id.
func (p *MapProgram) Insert(id ClauseId, clause Clause) {
	p.clauses[id] = clause
}

// Clause looks up a clause by id; the second result is false if absent.
func (p *MapProgram) Clause(id ClauseId) (Clause, bool) {
	c, ok := p.clauses[id]
	return c, ok
}

// ForEachClause calls f with every (id, clause) in canonical clause-id byte order —
// the trusted whole-program enumeration the ADR-0007 closure check needs. The order
// matches Iter (and Rust's BTreeMap-backed for_each_clause), so the enumeration is
// deterministic and byte-identical across {rs,go,ts}.
func (p *MapProgram) ForEachClause(f func(id ClauseId, clause Clause)) {
	for _, e := range p.Iter() {
		f(e.ID, e.Clause)
	}
}

// Len is the number of clauses in the program.
func (p *MapProgram) Len() int { return len(p.clauses) }

// IsEmpty reports whether the program has no clauses.
func (p *MapProgram) IsEmpty() bool { return len(p.clauses) == 0 }

// ClauseEntry is one (id, clause) pair of a program, the element type of the ordered
// enumeration Iter returns. Sibling of Rust's (&ClauseId, &Clause) iterator item and
// the TS [ClauseId, Clause] tuple.
type ClauseEntry struct {
	ID     ClauseId
	Clause Clause
}

// Iter returns the program's (id, clause) entries in CANONICAL ORDER — ascending by
// the clause-id's UTF-8 bytes (lexicographic). This is the same total order the program
// (de)serialization (program_serde.go ProgramToValue) sorts entries by, Rust's
// BTreeMap<ClauseId>-backed MapProgram::iter yields, and TS's MapProgram.iter yields —
// so the enumeration is DETERMINISTIC and BYTE-IDENTICAL across {rs,go,ts}. A raw map
// range would be nondeterministic in Go (map iteration order is randomized), so the sort
// is load-bearing: a consumer assembling a request straight from the program (e.g. stele's
// read-gate search assembler) gets identical bytes tri-core.
//
// The returned slice is freshly allocated and owned by the caller. Clause ids are unique
// (map keys), so the order is total and unambiguous.
func (p *MapProgram) Iter() []ClauseEntry {
	entries := make([]ClauseEntry, 0, len(p.clauses))
	for id, clause := range p.clauses {
		entries = append(entries, ClauseEntry{ID: id, Clause: clause})
	}
	sort.Slice(entries, func(i, j int) bool {
		return bytes.Compare([]byte(entries[i].ID.handle), []byte(entries[j].ID.handle)) < 0
	})
	return entries
}
