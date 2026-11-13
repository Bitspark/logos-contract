//! ADR 0031 D5 (#1821 P9 I5a): the ANNOTATED closed-model check. **[PROPOSED · additive]**
//!
//! [`check_annotated_closed_model`] takes an [`AnnotatedClosedModelCert`] and the semiring the
//! checker holds. It verifies the certificate exactly as the boolean check does, then recomputes
//! every intensional row's element as the least solution of the annotated system and compares it
//! with the claim. Rulings Q14 and Q15 on #1821 fix the order of its steps, its refusals and its
//! scope; `vectors/annotated_closed_model.json` pins all three cores to them.
//!
//! What an accepted verdict says, and what it does not:
//!
//! - It is RELATIVE TO THE SEMIRING'S IDENTITY: the elements are recomputed with the semiring the
//!   checker was handed, after its computed identity ([`semiring_identity`]) was found equal to
//!   the one the certificate names. The verdict says nothing about another semiring.
//! - It does NOT attest an EXTENSIONAL table's elements. They are premises, bound by the
//!   certificate's digest and read as claimed; the verdict names their tables `unattested`
//!   (#1821 Q15 condition 1).
//! - It names the law it relied on: [`AnnotationLaw::KleeneLeastFixpoint`] when the ground
//!   dependency graph is cyclic, none when it is acyclic and the solution is unique.
//!
//! The groundings are the closure join's own. The join records each grounding where it emits one
//! ([`super::cert`]'s `closure_groundings`), so there is no second join to drift from the first.
//! `ClosedModelCert`, its wire and the boolean check are unchanged, and no [`RejectionCode`] is
//! added: the annotation refusals are their own [`AnnotationCode`] (ADR 0003, additive).

use super::cert::{closure_groundings, Emitted, WorldProgram};
use super::cert_stack::resolve_lower_seals;
use super::{chain_over, report::Tally, CertContext, CheckProfile, RejectionCode, Verdict};
use crate::annotated_cert::AnnotatedClosedModelCert;
use crate::cert::ClosedModelCert;
use crate::literal::{escaped_name, GroundLiteral, Symbol};
use crate::program::{BodyLit, Clause, ClauseId, CompleteProgram, Program};
use crate::semiring::{semiring_identity, Semiring, SemiringAnswer};
use crate::spi::{ComponentIdentity, PredicateSet, Theory};
use crate::term::Subst;
use ontos_core::Value;
use std::collections::HashMap;

/// The law an accepted annotated check relied on to call its solution the least one (ADR 0031
/// D5; #1821 Q15). The verdict names it as a claim, never as a hidden premise.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AnnotationLaw {
    /// The ground dependency graph over the intensional rows has a cycle (a self-loop counts), so
    /// the claimed elements were compared with the fixed point Kleene iteration from `zero`
    /// reached: the least one in the semiring's natural order.
    KleeneLeastFixpoint,
}

impl AnnotationLaw {
    /// The law's wire name: `kleene_least_fixpoint`.
    pub fn name(self) -> &'static str {
        match self {
            AnnotationLaw::KleeneLeastFixpoint => "kleene_least_fixpoint",
        }
    }
}

/// Why [`check_annotated_closed_model`] refused a certificate's annotations (ADR 0031 D5). A
/// refusal of the certificate itself is [`AnnotatedOutcome::RejectCert`], with the boolean check's
/// [`RejectionCode`] unchanged; these codes are additive and never a `RejectionCode`, whose set is
/// FIRM and closed (ADR 0003).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AnnotationCode {
    /// The checker's semiring identity is not the one the certificate names.
    IdentityMismatch,
    /// Outside what the check covers: a partial scope, a negated or count literal in a scope
    /// clause, or a grounding whose body is not decided.
    Unsupported,
    /// The annotations are not one table per sealed table, in order, with one element per row, or
    /// a claimed element is not an element of the semiring.
    Shape,
    /// No fixed point within (IDB rows + 1) rounds.
    NotConverged,
    /// An intensional row's claimed element is not the least solution's.
    Mismatch,
    /// A semiring operation answered that an operand is not an element.
    NotAnElement,
    /// A semiring operation stopped at a capacity bound its carrier declares.
    Stopped,
    /// The semiring operations exceeded `max_join_steps`.
    BudgetExceeded,
}

impl AnnotationCode {
    /// The code's wire name, as `vectors/annotated_closed_model.json` spells it.
    pub fn code(self) -> &'static str {
        match self {
            AnnotationCode::IdentityMismatch => "annotation_identity_mismatch",
            AnnotationCode::Unsupported => "annotation_unsupported",
            AnnotationCode::Shape => "annotation_shape",
            AnnotationCode::NotConverged => "annotation_not_converged",
            AnnotationCode::Mismatch => "annotation_mismatch",
            AnnotationCode::NotAnElement => "semiring_not_an_element",
            AnnotationCode::Stopped => "semiring_stopped",
            AnnotationCode::BudgetExceeded => "annotation_budget_exceeded",
        }
    }
}

/// A sealed row a refusal names: the predicate of its table and its index in that table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnnotatedRow {
    /// The predicate of the row's table.
    pub pred: Symbol,
    /// The row's index in its table, in the table's row order.
    pub index: usize,
}

/// The verdict of [`check_annotated_closed_model`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnnotatedOutcome {
    /// The certificate passed the boolean check and every intensional row's claimed element is
    /// the least solution's, relative to the semiring's identity.
    Accept {
        /// [`AnnotationLaw::KleeneLeastFixpoint`] when the ground dependency graph is cyclic;
        /// `None` when it is acyclic, where the solution is unique.
        law: Option<AnnotationLaw>,
        /// The extensional tables' predicates, in the certificate's table order. Their elements
        /// are premises the digest binds: this verdict never attests them (#1821 Q15).
        unattested: Vec<Symbol>,
    },
    /// The boolean check refused the certificate, with its code and detail unchanged.
    RejectCert {
        /// The boolean check's code.
        code: RejectionCode,
        /// The boolean check's detail.
        detail: String,
    },
    /// The certificate passed the boolean check and its annotations were refused.
    Reject {
        /// Why.
        code: AnnotationCode,
        /// The row the refusal names, where it names one.
        row: Option<AnnotatedRow>,
        /// Free text for a reader.
        detail: String,
    },
}

impl AnnotatedOutcome {
    /// Whether the verdict is [`AnnotatedOutcome::Accept`].
    pub fn is_accept(&self) -> bool {
        matches!(self, AnnotatedOutcome::Accept { .. })
    }
}

/// Check an annotated closed-model certificate (ADR 0031 D5; #1821 Q14, Q15). Total; the first
/// failing step is the verdict:
///
/// 1. **Identity.** [`semiring_identity`] of `semiring` must equal `annotated.semiring`, or
///    `annotation_identity_mismatch`. The verdict is RELATIVE TO THAT IDENTITY.
/// 2. **The boolean check.** [`check_closed_model_chain`](crate::check_closed_model_chain) over
///    the one-certificate world `[annotated.cert]`; its refusal is `RejectCert`, unchanged.
/// 3. **Unsupported.** A partial scope, or a scope clause with a negated or count literal.
/// 4. **Shape.** One annotation table per sealed table, in order, for its predicate, with one
///    element per row; then every claimed element must be an element of `semiring`.
/// 5. **Groundings.** The closure join's body-true groundings of every scope clause whose head is
///    not extensional; one whose body is not decided is `annotation_unsupported`. Within a row the
///    groundings are folded in ascending codec order of
///    `Tuple[Atom(clause id), Tuple[Tuple[Atom(var), value]...]]`.
/// 6. **The least solution**, by Jacobi rounds from `zero`, bounded at (IDB rows + 1) rounds: a
///    row is the `add`-fold of its groundings, each the `mul`-fold, from `one`, of its positive
///    non-theory body literals in body order. An extensional literal reads its CLAIMED element (a
///    premise); an intensional one its previous-round value. Each `add` or `mul` is one step
///    against `max_join_steps`.
/// 7. **Mismatch.** The first intensional row whose claim differs from the solution.
/// 8. **Accept**, naming the law relied on and the extensional tables as `unattested`: the
///    verdict does NOT attest extensional elements (#1821 Q15 condition 1).
pub fn check_annotated_closed_model<C>(
    program: &dyn Program,
    annotated: &AnnotatedClosedModelCert,
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_context: &CertContext,
    semiring: &dyn Semiring,
) -> AnnotatedOutcome {
    match verdict(program, annotated, ctx, profile, cert_context, semiring) {
        Ok(verdict) | Err(verdict) => verdict,
    }
}

/// A step's result: its value, or the verdict that ends the check.
type Checked<T> = Result<T, AnnotatedOutcome>;

fn verdict<C>(
    program: &dyn Program,
    annotated: &AnnotatedClosedModelCert,
    ctx: &C,
    profile: &CheckProfile<C>,
    cert_context: &CertContext,
    semiring: &dyn Semiring,
) -> Checked<AnnotatedOutcome> {
    let cert = &annotated.cert;
    // 1. IDENTITY, before anything else is read.
    let held = semiring_identity(semiring);
    if held != annotated.semiring {
        let (held, named) = (identity_name(&held), identity_name(&annotated.semiring));
        let detail = format!("the checker holds semiring {held}, the certificate names {named}");
        return refused(AnnotationCode::IdentityMismatch, None, detail);
    }
    // 2. THE BOOLEAN CHECK, a one-certificate world, over one inventory of the program.
    let source = WorldProgram::new(program);
    let world = std::slice::from_ref(cert);
    // The annotated check returns no work report (checker SPI v2's report is `check`'s), so the
    // boolean check's tally is local and dropped.
    let mut tally = Tally::default();
    let boolean = chain_over(&source, world, ctx, profile, cert_context, &mut tally);
    if let Verdict::Reject { code, detail } = boolean {
        return Err(AnnotatedOutcome::RejectCert { code, detail });
    }
    let Some(trusted) = source.inventory() else {
        // Unreachable: the boolean check refuses a program with no complete enumeration.
        let code = RejectionCode::CertScopeIncomplete;
        let detail = String::from("program does not supply complete clause enumeration");
        return Err(AnnotatedOutcome::RejectCert { code, detail });
    };
    let clauses = scope_clauses(cert, trusted);
    // 3. UNSUPPORTED. The second gate is unreachable after step 2 in a one-certificate world (a
    //    certificate cannot negate or count its own seal); it stays as a defensive gate.
    if cert.partial_scope.is_some() {
        let detail = "a partial scope (ADR 0030) is a lower bound, with no least annotation";
        return refused(AnnotationCode::Unsupported, None, detail);
    }
    for (id, clause) in &clauses {
        if clause.body.iter().any(|b| b.is_neg() || b.is_count()) {
            let name = escaped_name(id.as_str().as_bytes());
            let detail = format!("scope clause {name} has a negated or count literal");
            return refused(AnnotationCode::Unsupported, None, detail);
        }
    }
    // 4. SHAPE.
    shape(annotated, semiring)?;
    // 5. GROUNDINGS, from the closure join.
    let rows = Rows::new(cert, profile.leaves.extensional());
    let groundings = collect_groundings(&rows, &clauses, trusted, profile)?;
    // 6. THE LEAST SOLUTION.
    let limit = profile.limits.max_join_steps;
    let solution = least_solution(annotated, &rows, &groundings, semiring, limit)?;
    // 7. MISMATCH, the first intensional row in table and row order.
    for (value, &place) in solution.iter().zip(&rows.idb) {
        if value != claimed(annotated, place) {
            let detail = "the claimed element is not the least solution's";
            return refused(AnnotationCode::Mismatch, Some(rows.name(place)), detail);
        }
    }
    // 8. ACCEPT.
    let cycle = cyclic(&groundings);
    let law = cycle.then_some(AnnotationLaw::KleeneLeastFixpoint);
    let mut unattested = Vec::new();
    for (table, edb) in cert.extensions.iter().zip(&rows.edb) {
        if *edb {
            unattested.push(table.pred.clone());
        }
    }
    Ok(AnnotatedOutcome::Accept { law, unattested })
}

/// A refusal of the annotations.
fn refused<T>(
    code: AnnotationCode,
    row: Option<AnnotatedRow>,
    detail: impl Into<String>,
) -> Checked<T> {
    let detail = detail.into();
    Err(AnnotatedOutcome::Reject { code, row, detail })
}

/// A refusal the closure join's own machinery raised, reported as the boolean check's verdict.
/// Step 2 has run the same join over the same clauses, so none is expected here.
fn join_refused((code, detail): (RejectionCode, String)) -> AnnotatedOutcome {
    AnnotatedOutcome::RejectCert { code, detail }
}

/// A semiring identity as a refusal's detail names it.
fn identity_name(identity: &ComponentIdentity) -> String {
    let id = escaped_name(&identity.id);
    let version = escaped_name(&identity.version);
    format!("{id}@{version}")
}

/// The trusted program's clauses whose head the certificate's scope seals, in enumeration order.
fn scope_clauses(cert: &ClosedModelCert, trusted: &dyn CompleteProgram) -> Vec<(ClauseId, Clause)> {
    let mut clauses = Vec::new();
    trusted.for_each_clause(&mut |id, clause| {
        if cert.scope.seals(&clause.head.pred) {
            clauses.push((id.clone(), clause.clone()));
        }
    });
    clauses
}

/// Step 4: one annotation table per sealed table, in order, for its predicate, with one element
/// per row; then, in table and row order, every claimed element an element of the semiring.
fn shape(annotated: &AnnotatedClosedModelCert, semiring: &dyn Semiring) -> Checked<()> {
    let tables = &annotated.cert.extensions;
    let annotations = &annotated.annotations;
    if annotations.len() != tables.len() {
        let (got, want) = (annotations.len(), tables.len());
        let detail = format!("{got} annotation tables for {want} sealed tables");
        return refused(AnnotationCode::Shape, None, detail);
    }
    for (table, annotation) in tables.iter().zip(annotations) {
        let name = escaped_name(table.pred.bytes());
        if annotation.pred != table.pred {
            let detail = format!("sealed table {name} is not annotated in its place");
            return refused(AnnotationCode::Shape, None, detail);
        }
        if annotation.elements.len() != table.rows.len() {
            let detail = format!("sealed table {name} does not have one element per row");
            return refused(AnnotationCode::Shape, None, detail);
        }
    }
    for (table, annotation) in tables.iter().zip(annotations) {
        for (index, element) in annotation.elements.iter().enumerate() {
            if !semiring.is_element(element) {
                let detail = "the claimed element is not an element of the semiring";
                let row = AnnotatedRow {
                    pred: table.pred.clone(),
                    index,
                };
                return refused(AnnotationCode::Shape, Some(row), detail);
            }
        }
    }
    Ok(())
}

/// Where a sealed row sits: its table's index in `cert.extensions`, and its index in the table.
#[derive(Clone, Copy)]
struct Place {
    table: usize,
    row: usize,
}

/// The sealed rows of one certificate, indexed for the annotated check.
struct Rows<'a> {
    cert: &'a ClosedModelCert,
    /// Every sealed row, by value, to the place of its first occurrence.
    places: HashMap<&'a GroundLiteral, Place>,
    /// Per table of `cert.extensions`: whether it is extensional.
    edb: Vec<bool>,
    /// Per table: the intensional position of its first row (read for an intensional table).
    first: Vec<usize>,
    /// The intensional rows: every row of a table that is not extensional, in table order then
    /// row order.
    idb: Vec<Place>,
}

impl<'a> Rows<'a> {
    fn new(cert: &'a ClosedModelCert, extensional: &PredicateSet) -> Self {
        let mut rows = Rows {
            cert,
            places: HashMap::new(),
            edb: Vec::new(),
            first: Vec::new(),
            idb: Vec::new(),
        };
        for (table, sealed) in cert.extensions.iter().enumerate() {
            let edb = extensional.contains(&sealed.pred);
            rows.edb.push(edb);
            rows.first.push(rows.idb.len());
            for (row, fact) in sealed.rows.iter().enumerate() {
                rows.places.entry(fact).or_insert(Place { table, row });
                if !edb {
                    rows.idb.push(Place { table, row });
                }
            }
        }
        rows
    }

    /// The place of a sealed row; `None` for a literal no table holds.
    fn place(&self, fact: &GroundLiteral) -> Option<Place> {
        self.places.get(fact).copied()
    }

    /// The intensional position of an intensional row.
    fn position(&self, place: Place) -> usize {
        self.first[place.table] + place.row
    }

    /// A row as a refusal names it.
    fn name(&self, place: Place) -> AnnotatedRow {
        let pred = self.cert.extensions[place.table].pred.clone();
        let index = place.row;
        AnnotatedRow { pred, index }
    }
}

/// The element `annotated` claims for the row at `place`. Step 4 has made it exist.
fn claimed(annotated: &AnnotatedClosedModelCert, place: Place) -> &Value {
    &annotated.annotations[place.table].elements[place.row]
}

/// What one factor of a grounding reads.
#[derive(Clone, Copy)]
enum Factor {
    /// An extensional row: its claimed element, a premise.
    Premise(Place),
    /// An intensional row, by intensional position: its value in the previous round.
    Derived(usize),
}

impl Factor {
    /// The intensional position this factor reads, if it reads one.
    fn derived(self) -> Option<usize> {
        match self {
            Factor::Premise(_) => None,
            Factor::Derived(position) => Some(position),
        }
    }
}

/// One grounding of an intensional row: its canonical key and its factors, in body order.
struct Grounding {
    key: Vec<u8>,
    factors: Vec<Factor>,
}

/// Step 5: every intensional row's groundings, in key order. Each is a body-true grounding the
/// closure join emits for a scope clause whose head is not extensional ([`closure_groundings`]),
/// on the plan, the binders and the counters [`super::cert`]'s closure check uses.
fn collect_groundings<C>(
    rows: &Rows<'_>,
    clauses: &[(ClauseId, Clause)],
    trusted: &dyn CompleteProgram,
    profile: &CheckProfile<C>,
) -> Checked<Vec<Vec<Grounding>>> {
    let cert = rows.cert;
    let theory = profile.theory.as_ref();
    let extensional = profile.leaves.extensional();
    // A one-certificate world reads nothing from below: the view holds the certificate's tables.
    let world = std::slice::from_ref(cert);
    let view = match resolve_lower_seals(cert, 0, world, None, trusted, theory) {
        Ok(view) => view,
        Err(refusal) => return Err(join_refused(refusal)),
    };
    let mut per_row: Vec<Vec<Grounding>> = rows.idb.iter().map(|_| Vec::new()).collect();
    let mut counts = (0, 0);
    for (id, clause) in clauses {
        if extensional.contains(&clause.head.pred) {
            continue;
        }
        let emitted = closure_groundings(clause, &view, theory, &profile.limits, &mut counts);
        for Emitted { subst, decided } in emitted.map_err(join_refused)? {
            if !decided {
                let name = escaped_name(id.as_str().as_bytes());
                let detail = format!("a grounding of scope clause {name} has an undecided body");
                return refused(AnnotationCode::Unsupported, None, detail);
            }
            let (position, found) = emitted_grounding(rows, id, clause, &subst, theory)?;
            per_row[position].push(found);
        }
    }
    for row in &mut per_row {
        row.sort_by(|a, b| a.key.as_slice().cmp(b.key.as_slice()));
    }
    Ok(per_row)
}

/// One emitted grounding: the intensional position of its head row, and its key and factors.
fn emitted_grounding(
    rows: &Rows<'_>,
    id: &ClauseId,
    clause: &Clause,
    subst: &Subst,
    theory: &dyn Theory,
) -> Checked<(usize, Grounding)> {
    // Each refusal below is unreachable after step 2: the join binds every variable from a sealed
    // row, and the closure check found every body-true grounding's head in its table.
    let name = escaped_name(id.as_str().as_bytes());
    let Some(key) = grounding_key(id, subst) else {
        let detail = format!("a grounding of scope clause {name} binds a term that is not ground");
        return refused(AnnotationCode::Unsupported, None, detail);
    };
    let head = clause.head.substitute(subst).as_ground();
    let Some(place) = head.and_then(|head| rows.place(&head)) else {
        let detail = format!("a grounding of scope clause {name} has a head no table holds");
        return refused(AnnotationCode::Unsupported, None, detail);
    };
    let mut factors = Vec::new();
    for lit in &clause.body {
        // Step 3 refused a negated or count literal; a theory literal carries no element.
        let BodyLit::Pos(goal) = lit else { continue };
        if theory.owns(&goal.pred) {
            continue;
        }
        let fact = goal.substitute(subst).as_ground();
        let Some(at) = fact.and_then(|fact| rows.place(&fact)) else {
            let detail = format!("a grounding of scope clause {name} reads a row no table holds");
            return refused(AnnotationCode::Unsupported, None, detail);
        };
        let factor = if rows.edb[at.table] {
            Factor::Premise(at)
        } else {
            Factor::Derived(rows.position(at))
        };
        factors.push(factor);
    }
    Ok((rows.position(place), Grounding { key, factors }))
}

/// A grounding's canonical key (#1821 Q15 condition 3): the codec bytes of `Tuple[Atom(clause
/// id), Tuple[Tuple[Atom(var), quote(image)], ...]]`, each image in the certificate wire's term
/// reading ([`quote`](crate::reify::quote)), the variables in ascending byte order of their names.
/// A [`Subst`] iterates in that order: `VarId` orders names as strings, by bytes. `None` when an
/// image is not ground.
fn grounding_key(id: &ClauseId, subst: &Subst) -> Option<Vec<u8>> {
    let mut bindings = Vec::with_capacity(subst.len());
    for (var, term) in subst {
        term.erase_ground()?;
        let name = Value::atom(var.as_str().as_bytes());
        bindings.push(Value::tuple([name, crate::reify::quote(term)]));
    }
    let clause = Value::atom(id.as_str().as_bytes());
    let key = Value::tuple([clause, Value::tuple(bindings)]);
    Some(ontos_codec::encode(&key))
}

/// The semiring operations a check has charged, against its budget.
struct Steps {
    taken: usize,
    max: usize,
}

impl Steps {
    /// Charge one operation, then run it. An answer that is not an element refuses, naming the
    /// intensional row being computed.
    fn apply(
        &mut self,
        rows: &Rows<'_>,
        at: Place,
        op: impl FnOnce() -> SemiringAnswer,
    ) -> Checked<Value> {
        self.taken += 1;
        if self.taken > self.max {
            let max = self.max;
            let detail = format!("the semiring operations exceed max_join_steps {max}");
            return refused(AnnotationCode::BudgetExceeded, None, detail);
        }
        match op() {
            SemiringAnswer::Element(value) => Ok(value),
            SemiringAnswer::NotAnElement => {
                let detail = "a semiring operation answered that an operand is not an element";
                refused(AnnotationCode::NotAnElement, Some(rows.name(at)), detail)
            }
            SemiringAnswer::Stopped(cause) => {
                let kind = cause.kind().tag();
                let detail = format!("a semiring operation stopped: {kind}");
                refused(AnnotationCode::Stopped, Some(rows.name(at)), detail)
            }
        }
    }
}

/// Step 6: the least solution, by Jacobi rounds from `zero`, bounded at (IDB rows + 1) rounds.
/// Within a round every row reads the previous round's values; the iteration stops at the first
/// round that changes no row (value equality).
fn least_solution(
    annotated: &AnnotatedClosedModelCert,
    rows: &Rows<'_>,
    groundings: &[Vec<Grounding>],
    semiring: &dyn Semiring,
    max_steps: usize,
) -> Checked<Vec<Value>> {
    let (zero, one) = (semiring.zero(), semiring.one());
    let mut prev = vec![zero.clone(); rows.idb.len()];
    let mut steps = Steps {
        taken: 0,
        max: max_steps,
    };
    for _round in 0..=rows.idb.len() {
        let mut next = Vec::with_capacity(prev.len());
        for (&at, row) in rows.idb.iter().zip(groundings) {
            let mut sum = zero.clone();
            for grounding in row {
                let mut product = one.clone();
                for factor in &grounding.factors {
                    let value = match *factor {
                        Factor::Premise(place) => claimed(annotated, place),
                        Factor::Derived(position) => &prev[position],
                    };
                    product = steps.apply(rows, at, || semiring.mul(&product, value))?;
                }
                sum = steps.apply(rows, at, || semiring.add(&sum, &product))?;
            }
            next.push(sum);
        }
        if next == prev {
            return Ok(next);
        }
        prev = next;
    }
    let bound = rows.idb.len() + 1;
    let detail = format!("no fixed point within {bound} rounds");
    refused(AnnotationCode::NotConverged, None, detail)
}

/// The intensional positions a row's groundings read: its edges in the ground dependency graph.
fn successors(row: &[Grounding]) -> Vec<usize> {
    let factors = row.iter().flat_map(|g| &g.factors);
    factors.filter_map(|f| f.derived()).collect()
}

/// Step 8: whether the ground dependency graph has a cycle, a self-loop included. Its edges run
/// from each grounding's head row to each of its intensional factor rows. Kahn's construction:
/// the graph is acyclic exactly when repeatedly removing a row no remaining edge enters removes
/// every row.
fn cyclic(groundings: &[Vec<Grounding>]) -> bool {
    let mut edges = Vec::with_capacity(groundings.len());
    for row in groundings {
        edges.push(successors(row));
    }
    let mut entering = vec![0usize; edges.len()];
    for &to in edges.iter().flatten() {
        entering[to] += 1;
    }
    let mut ready = Vec::new();
    for (row, count) in entering.iter().enumerate() {
        if *count == 0 {
            ready.push(row);
        }
    }
    let mut removed = 0usize;
    while let Some(row) = ready.pop() {
        removed += 1;
        for &to in &edges[row] {
            entering[to] -= 1;
            if entering[to] == 0 {
                ready.push(to);
            }
        }
    }
    removed < edges.len()
}
