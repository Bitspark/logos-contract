//! #2759 (`seat:caa`'s design gate; research 0028 row A15): the CONSTRUCTOR-ACYCLIC fragment's
//! cycle test, in the checker's tier so there is ONE computation. `check` runs it over a
//! certificate's sealed scope (§3.2's constructor-acyclic gate, `check::cert`), and the certifying
//! producer's seal plan (`logos_core::producer::SealPlan::sealed_compounds`), which the kernel's
//! resolver reads to derive the function-symbol level at admission, runs it over the plan's sealed
//! relations. go (`ScopeGraph`) and ts (`ScopeGraph`) carry the same function, and their kernels
//! call it the same way.
//!
//! A CONSTRUCTING rule is one whose head carries an OPEN compound (`Term::is_open_compound`): it
//! wraps a variable in a function symbol (`ok(tag(X)) :- ...`). It lies on a dependency cycle when
//! its head predicate is reachable from one of its own body predicates through the scope's clauses.
//! Such a rule can rebuild what it built, without bound, so the fragment excludes it.
//!
//! What acyclicity discharges is FINITENESS of the relevant model, whose seed is the ground program
//! values and the input's sub-terms (research 0028 row A9). It discharges nothing else: matching
//! completeness, domain coverage, support, stratification, aggregates and the budget are each
//! still checked by their own gate.

use std::collections::{BTreeMap, BTreeSet};

use crate::literal::{Goal, Symbol};
use crate::program::{BodyLit, Clause, CountLit};
use crate::term::{Term, VarId};

/// The context a sealed clause is classified in (#3067, research 0028 row A15; `seat:caa`'s ruling
/// Q2): the relations its certificate seals, and the relations it reads from a strictly lower
/// certificate. ONE type: `check` builds it from a certificate and the lower certificates it
/// resolves, and the seal plan builds it from the certificate layers it plans.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SealContext {
    /// The relations the clause's own certificate seals.
    pub seals: BTreeSet<Symbol>,
    /// The relations the clause reads from a strictly lower certificate.
    pub reads_lower: BTreeSet<Symbol>,
}

/// The relations a scope's sealed clauses READ without sealing them (#3067 increment 3, research
/// 0028 row A15; `seat:caa`'s ruling Q1): the ONE computation behind a [`SealContext`]'s
/// `reads_lower`. `check` builds it over the bound program and resolves each read to a strictly
/// lower certificate; the seal plan builds it over the program and reads each from a lower layer
/// it planned. Both then take the context from [`Self::context`], so the two hold one value, and a
/// round trip between them checks that their INPUTS agree.
///
/// A read is a body literal's relation (a counted literal's included, #2258 L3.3b) of a clause the
/// scope seals the head of, that the scope does not seal and the theory does not decide live.
/// Reads keep their first-occurrence order (clause order, then body order), the order `check`
/// resolves them in, so its first refusal names the same relation it always has.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ScopeReads {
    reads: Vec<Symbol>,
}

impl ScopeReads {
    /// No reads yet.
    pub fn new() -> Self {
        ScopeReads::default()
    }

    /// Record `clause`'s reads when the scope seals its head. `seals` is the scope's own relations,
    /// and `served_by` the relations a bound theory OWNS, which the read gate counts as served rather
    /// than read: `Theory::owns` in `check` and the producer, and at admission the arithmetic
    /// builtins the program uses.
    pub fn add(
        &mut self,
        clause: &Clause,
        seals: &dyn Fn(&Symbol) -> bool,
        served_by: &dyn Fn(&Symbol) -> bool,
    ) {
        if !seals(&clause.head.pred) {
            return;
        }
        for lit in &clause.body {
            let pred = lit.pred();
            if !seals(pred) && !served_by(pred) && !self.reads.contains(pred) {
                self.reads.push(pred.clone());
            }
        }
    }

    /// Reads stated by hand, for a context a test names directly (`vectors/fragment.json`'s replay).
    #[cfg(test)]
    pub(crate) fn stated(reads: Vec<Symbol>) -> Self {
        ScopeReads { reads }
    }

    /// The reads, in first-occurrence order.
    pub fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.reads.iter()
    }

    /// The scope's clause context: the relations it seals, and every read `lower` provides, a
    /// strictly lower certificate for `check`, a lower layer for the plan.
    pub fn context(&self, seals: BTreeSet<Symbol>, lower: &dyn Fn(&Symbol) -> bool) -> SealContext {
        SealContext {
            reads_lower: self
                .reads
                .iter()
                .filter(|pred| lower(pred))
                .cloned()
                .collect(),
            seals,
        }
    }
}

/// Why a sealed clause is outside the certifiable fragment: the FIRST gate it fails, in the one
/// order [`classify_sealed_clause`] declares, with that gate's subject.
///
/// Every variant is `#[non_exhaustive]` (#3067's closure guard, `seat:caa`): only this crate, where
/// the one classification lives, can construct a value, and every other crate matches with `..`.
/// So a second classifier elsewhere cannot produce the value a producer's decline carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outside {
    /// A count over a relation no strictly lower certificate seals. `same_scope` when the clause's
    /// own certificate seals it: the table under construction.
    #[non_exhaustive]
    CountNotLower { pred: Symbol, same_scope: bool },
    /// A count whose filter or result carries an open compound (the function-free count gate).
    #[non_exhaustive]
    CountOpenCompound { pred: Symbol },
    /// The clause's head constructs an open compound on a dependency cycle through `through`.
    #[non_exhaustive]
    ConstructorCycle { through: Symbol },
    /// A body literal over a relation that is neither sealed, theory-owned, nor read lower.
    #[non_exhaustive]
    Unserved { pred: Symbol },
    /// A `\+` over a relation the clause's own certificate seals.
    #[non_exhaustive]
    IntraScopeNegation { pred: Symbol },
    /// A count filter variable that no positive sealed literal binds.
    #[non_exhaustive]
    UnboundCountFilter { pred: Symbol, var: VarId },
    /// A variable that no positive sealed literal, nor a count's result, binds.
    #[non_exhaustive]
    UnboundVariable { var: VarId },
}

/// Whether a count's filter or result carries an OPEN compound (the function-free count gate,
/// #2294). The seal plan reads it too, to ask whether a seal carries an open compound at all.
pub fn count_has_open_compound(count: &CountLit<Term>) -> bool {
    count.count.is_open_compound() || count.filter.iter().any(|(_, t)| t.is_open_compound())
}

/// THE classification of one sealed clause (#3067; `seat:caa`'s rulings Q1 to Q3): `None` inside
/// the certifiable fragment, else the first gate it fails. `graph` is the scope's dependency graph
/// (built over the program with `ctx.seals` as its scope).
///
/// The theory is read in TWO directions (`seat:caa`'s ruling on #3067 increment 2, Q1), because a
/// theory owning more predicates refuses LESS in the read gate and MORE in range restriction:
/// `served_by` says which relations a theory decides live, for the read gate; `binds_nothing` says
/// which relations bind no variable, for range restriction. `check` and a producer pass the bound
/// theory's ownership for both, so one set serves them. A caller that sees only part of the theory
/// passes what it knows for each reading; the kernel's resolver, which cannot see a consumer theory,
/// reads the theories the kernel ships for its planning level, and leaves the exact decision to the
/// certifying provider, which binds the theory (#3211).
///
/// The gates run in ONE order, the checker's, declared here and never restated by a caller:
///
/// 1. the count gate, per count literal in body order: it reads a strictly lower certificate
///    ([`Outside::CountNotLower`]), and its terms carry no open compound
///    ([`Outside::CountOpenCompound`]);
/// 2. the constructor-cycle gate ([`Outside::ConstructorCycle`], [`ScopeGraph`]);
/// 3. the read gate, per body literal in body order: the relation is sealed, served by a theory
///    (`served_by`) or read lower ([`Outside::Unserved`]), and a `\+` never reads this
///    certificate's own table ([`Outside::IntraScopeNegation`]);
/// 4. range restriction: every count filter variable, count by count in body order
///    ([`Outside::UnboundCountFilter`]), then every variable of the clause
///    ([`Outside::UnboundVariable`]), is bound by a positive literal over a relation the
///    certificate seals or reads lower and that binds (not `binds_nothing`); a count then binds its
///    result. Where several variables are unbound it names the first in name order.
pub fn classify_sealed_clause(
    clause: &Clause,
    ctx: &SealContext,
    graph: &ScopeGraph,
    served_by: &dyn Fn(&Symbol) -> bool,
    binds_nothing: &dyn Fn(&Symbol) -> bool,
) -> Option<Outside> {
    // 1. The count gate (ADR 0023; #2258 L3.3b, the `NegLower` rule). A count reads the table of the
    // unique, exact, Valid certificate at a strictly lower level that seals its relation. One over a
    // relation THIS certificate seals would read the table under construction, circular for a
    // non-monotone operator, and one over a theory-owned or unsealed relation has no exact table.
    // Its filter and result terms stay function-free (#2294).
    for count in clause.body.iter().filter_map(BodyLit::as_count) {
        let pred = &count.pred.pred;
        if !ctx.reads_lower.contains(pred) {
            return Some(Outside::CountNotLower {
                pred: pred.clone(),
                same_scope: ctx.seals.contains(pred),
            });
        }
        if count_has_open_compound(count) {
            return Some(Outside::CountOpenCompound { pred: pred.clone() });
        }
    }
    // 2. The constructor-acyclic gate (#2759). An open compound in a BODY literal is a destructuring
    // pattern the closure join binds by unifying it with a sealed row, and one in the HEAD of a
    // clause on no dependency cycle fires a bounded number of times, so the sealed model is finite.
    // A constructing rule ON a cycle can rebuild what it built without bound, and no finite table
    // is evidence of its model. A ground compound is a constant: it constructs nothing.
    if ScopeGraph::constructs(clause) {
        if let Some(through) = graph.cycle_through(clause) {
            return Some(Outside::ConstructorCycle { through });
        }
    }
    // 3. The read gate: every body literal is decidable against a table this certificate seals, a
    // theory, or a strictly lower certificate (#2258 (a)), which is what the closure's body
    // evaluation relies on. A `\+` over this certificate's own table would evaluate a same-stratum
    // negation against the table under construction: stratified negation reads only a strictly
    // lower, separately sealed one.
    for lit in &clause.body {
        let Some(goal) = lit.as_inner() else { continue };
        let pred = &goal.pred;
        let sealed = ctx.seals.contains(pred);
        if !sealed && !served_by(pred) && !ctx.reads_lower.contains(pred) {
            return Some(Outside::Unserved { pred: pred.clone() });
        }
        if lit.is_neg() && sealed {
            return Some(Outside::IntraScopeNegation { pred: pred.clone() });
        }
    }
    // 4. Range restriction ("safe, range-restricted"). Only a POSITIVE literal over a finite,
    // enumerable sealed relation binds: one this certificate seals or reads lower, and that no
    // theory owns (`binds_nothing`). For `check` a relation read lower is never theory-owned (the
    // partition gate refuses a certificate sealing one), so the second test changes nothing there;
    // a plan read with a theory the caller cannot bind can put one of its relations in a lower
    // layer, and it binds nothing there too (#3067). A variable bound only in the head, only under
    // `\+`, or only by a theory literal ranges over values no sealed table confines, so closure could under-fire on an unbounded builtin
    // existential. A count reads the rows its filter selects, so its filter variables must be bound
    // first, and it then binds its result.
    let mut bound: BTreeSet<VarId> = BTreeSet::new();
    for lit in &clause.body {
        if lit.is_neg() {
            continue;
        }
        let Some(goal) = lit.as_inner() else { continue };
        let pred = &goal.pred;
        if (ctx.seals.contains(pred) || ctx.reads_lower.contains(pred)) && !binds_nothing(pred) {
            goal_vars(goal, &mut bound);
        }
    }
    for count in clause.body.iter().filter_map(BodyLit::as_count) {
        let mut filter: BTreeSet<VarId> = BTreeSet::new();
        for (_, term) in &count.filter {
            term_vars(term, &mut filter);
        }
        if let Some(var) = filter.into_iter().find(|v| !bound.contains(v)) {
            return Some(Outside::UnboundCountFilter {
                pred: count.pred.pred.clone(),
                var,
            });
        }
    }
    for count in clause.body.iter().filter_map(BodyLit::as_count) {
        term_vars(&count.count, &mut bound);
    }
    let mut all: BTreeSet<VarId> = BTreeSet::new();
    goal_vars(&clause.head, &mut all);
    for lit in &clause.body {
        if let Some(goal) = lit.as_inner() {
            goal_vars(goal, &mut all);
        } else if let Some(count) = lit.as_count() {
            for (_, term) in &count.filter {
                term_vars(term, &mut all);
            }
            term_vars(&count.count, &mut all);
        }
    }
    all.into_iter()
        .find(|v| !bound.contains(v))
        .map(|var| Outside::UnboundVariable { var })
}

fn goal_vars(goal: &Goal, out: &mut BTreeSet<VarId>) {
    for term in &goal.args {
        term_vars(term, out);
    }
}

fn term_vars(term: &Term, out: &mut BTreeSet<VarId>) {
    let mut work: Vec<&Term> = vec![term];
    while let Some(t) = work.pop() {
        match t {
            Term::Var(v) => {
                out.insert(v.clone());
            }
            Term::Tuple(children) => work.extend(children.iter()),
            Term::Atom(_) => {}
        }
    }
}

/// The dependency graph of a scope, built one clause at a time: an edge from each in-scope clause's
/// head to every body literal predicate (positive or negated) that is in scope. A count reads a
/// relation a strictly lower certificate seals, never one of its own scope, so it adds no edge.
/// Keyed by name, as a certificate's scope is.
#[derive(Clone, Debug, Default)]
pub struct ScopeGraph {
    edges: BTreeMap<Symbol, BTreeSet<Symbol>>,
}

impl ScopeGraph {
    /// An empty graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one clause of the program. A clause whose head is out of scope adds nothing.
    pub fn add(&mut self, clause: &Clause, in_scope: &dyn Fn(&Symbol) -> bool) {
        if !in_scope(&clause.head.pred) {
            return;
        }
        let out = self.edges.entry(clause.head.pred.clone()).or_default();
        for goal in clause.body.iter().filter_map(BodyLit::as_inner) {
            if in_scope(&goal.pred) {
                out.insert(goal.pred.clone());
            }
        }
    }

    /// Whether `clause` CONSTRUCTS: its head carries an open compound.
    pub fn constructs(clause: &Clause) -> bool {
        clause.head.args.iter().any(Term::is_open_compound)
    }

    /// The first body predicate of `clause`, in body order, from which the clause's own head
    /// predicate is reachable in this graph (itself included): the clause lies on a dependency cycle
    /// through it. `None` when the clause is on no cycle.
    pub fn cycle_through(&self, clause: &Clause) -> Option<Symbol> {
        let head = &clause.head.pred;
        clause
            .body
            .iter()
            .filter_map(BodyLit::as_inner)
            .map(|goal| &goal.pred)
            .find(|from| self.reaches(from, head))
            .cloned()
    }

    /// Whether `to` is reachable from `from` along the edges, `from` itself included.
    fn reaches(&self, from: &Symbol, to: &Symbol) -> bool {
        let mut seen: BTreeSet<&Symbol> = BTreeSet::new();
        let mut work: Vec<&Symbol> = vec![from];
        while let Some(pred) = work.pop() {
            if pred == to {
                return true;
            }
            if !seen.insert(pred) {
                continue;
            }
            if let Some(next) = self.edges.get(pred) {
                work.extend(next.iter());
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::ScopeGraph;
    use crate::literal::{Goal, Symbol};
    use crate::program::Clause;
    use crate::term::Term;

    fn graph(clauses: &[Clause], scope: &[&str]) -> ScopeGraph {
        let in_scope = |p: &Symbol| scope.iter().any(|s| p.bytes() == s.as_bytes());
        let mut g = ScopeGraph::new();
        for c in clauses {
            g.add(c, &in_scope);
        }
        g
    }

    #[test]
    fn a_constructor_on_its_own_cycle_is_found_and_one_beside_it_is_not_2759() {
        let x = || Term::var("X");
        let s = |t: Term| Term::tuple([Term::atom(b"s".to_vec()), t]);
        // nat(s(X)) :- nat(X). is on nat's cycle; tag(s(X)) :- c(X). is not.
        let nat = Clause::new(Goal::new("nat", [s(x())]), [Goal::new("nat", [x()])]);
        let tag = Clause::new(Goal::new("tag", [s(x())]), [Goal::new("c", [x()])]);
        let g = graph(&[nat.clone(), tag.clone()], &["nat", "tag", "c"]);
        assert!(ScopeGraph::constructs(&nat) && ScopeGraph::constructs(&tag));
        assert_eq!(g.cycle_through(&nat), Some(Symbol::from("nat")));
        assert_eq!(g.cycle_through(&tag), None);
        // A cycle through an out-of-scope clause is not a cycle of the scope: p(s(X)) :- q(X) and
        // q(X) :- p(X). With both in scope p lies on the cycle through q; with only p in scope,
        // q's clause adds no edge and the cycle does not close. (A clause whose body names its
        // own head is a cycle whatever the scope: `cycle_through` reads "from itself included".)
        let p = Clause::new(Goal::new("p", [s(x())]), [Goal::new("q", [x()])]);
        let q = Clause::new(Goal::new("q", [x()]), [Goal::new("p", [x()])]);
        assert_eq!(
            graph(&[p.clone(), q.clone()], &["p", "q"]).cycle_through(&p),
            Some(Symbol::from("q"))
        );
        assert_eq!(graph(&[p.clone(), q], &["p"]).cycle_through(&p), None);
    }
}
