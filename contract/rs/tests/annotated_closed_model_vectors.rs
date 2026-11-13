//! Rust replay of the hand-authored oracle `vectors/annotated_closed_model.json` (ADR 0031 D5;
//! #1821 P9 I5a): an annotated closed-model certificate, checked relative to its semiring's
//! identity. The SAME file is replayed by Go (`contract/go/annotated_closed_model_vectors_test.go`)
//! and TS (`contract/ts/test/annotated_closed_model_vectors.test.ts`).
//!
//! The notation is `vectors/negation.json`'s: the `negation_v1` profile (the `lt` theory, with the
//! standard arithmetic theory beside it as the conformance driver binds it; EDB leaves = the
//! top-level `extensional` set, attesting snapshots of the top-level `edb` rows), and each case's
//! cert bound to the context derived from the live program, as `run_negation` binds it. Elements
//! follow `vectors/semiring.json`'s value grammar. Every case compares the outcome's kind, its
//! code, the row where one is given, the law and the unattested tables. Every accepted case is
//! also run under each checker budget raised (R3, `each_budget_raised`), and must keep its
//! verdict.

#[path = "support/proof_budgets.rs"]
mod proof_budgets;

use logos_contract::intval::BigInt;
use logos_contract::{
    annotated_closed_model_cert_as_value, annotated_closed_model_cert_from_value,
    check_annotated_closed_model, edb_table_hash, program_digest, semiring_identity, AlwaysAdmit,
    AnnotatedClosedModelCert, AnnotatedOutcome, AnnotatedTable, AnnotationLaw, ArithmeticTheory,
    BodyLit, CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId,
    ClosedModelCert, ClosureWitness, ComponentIdentity, CompoundTheory, CountingSemiring,
    DecisionCompletion, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LawDeclaration,
    LeafOutcome, LeafVerifier, MapProgram, PredicateSet, RelationTable, Semiring, SemiringAnswer,
    StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term, Theory,
    TheoryGround, TropicalSemiring,
};
use ontos_core::Value;
use serde_json::Value as Json;
use std::collections::{BTreeMap, BTreeSet};

const VECTORS: &str = include_str!("../../../vectors/annotated_closed_model.json");

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("the vector parses")
}

// ================================= the negation_v1 profile =================================

struct LtTheory;
// test-double: consumer(a less-than theory over atoms)
impl Theory for LtTheory {
    logos_contract::cannot_copy!(Theory, "a replay's comparison theory, never copied");
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"lt"
    }
    /// Every decision completes: a byte comparison of two atoms.
    fn completion(&self, _pred: &Symbol) -> DecisionCompletion {
        DecisionCompletion::StopsAreTyped
    }
    fn decide_ground(&self, atom: &GroundLiteral) -> TheoryGround {
        match atom.args.as_slice() {
            [a, b] => match (a.as_atom(), b.as_atom()) {
                (Some(a), Some(b)) if a.bytes() < b.bytes() => TheoryGround::holds(),
                _ => TheoryGround::fails("not_less_than"),
            },
            _ => TheoryGround::fails("lt_arity"),
        }
    }
}

/// The conformance driver's negation theory: `lt`, and the standard arithmetic theory beside it.
fn negation_theory() -> CompoundTheory {
    CompoundTheory::new(vec![Box::new(LtTheory), Box::new(ArithmeticTheory::new())])
}

/// EDB leaves named by the vector's `extensional` list, attesting snapshots of its `edb` rows.
struct NegLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for NegLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _ctx: &()) -> Option<Hash> {
        match self.edb.get(pred.bytes()) {
            Some(rows) => Some(edb_table_hash(pred, rows)),
            None if self.extensional.contains(pred) => Some(edb_table_hash(pred, &[])),
            None => None,
        }
    }
}

/// The fixed non-zero profile, context and theory pins the negation_v1 profile binds; the
/// program pin is recomputed from the live program.
const NEG_PROFILE_PIN: Hash = [1u8; 32];
const NEG_CTX_PIN: Hash = [2u8; 32];
const NEG_THEORY_PIN: Hash = [3u8; 32];

// ===================================== the semirings ======================================

/// `stopping`, `vectors/semiring.json`'s fixture: Counting's carrier, laws, zero and one, with
/// the capacity stop in place of every element an operation would answer.
struct Stopping;

/// Counting's answer, with the capacity stop in place of an element.
fn stopped(counted: SemiringAnswer) -> SemiringAnswer {
    match counted {
        SemiringAnswer::Element(_) => SemiringAnswer::capacity(),
        SemiringAnswer::NotAnElement => SemiringAnswer::NotAnElement,
        SemiringAnswer::Stopped(cause) => SemiringAnswer::Stopped(cause),
    }
}

impl Semiring for Stopping {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"fixture/stopping-semiring".to_vec(),
            b"1".to_vec(),
            [0u8; 32],
        )
    }

    fn laws(&self) -> LawDeclaration {
        CountingSemiring::new().laws()
    }

    fn zero(&self) -> Value {
        CountingSemiring::new().zero()
    }

    fn one(&self) -> Value {
        CountingSemiring::new().one()
    }

    fn is_element(&self, value: &Value) -> bool {
        CountingSemiring::new().is_element(value)
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        stopped(CountingSemiring::new().add(a, b))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        stopped(CountingSemiring::new().mul(a, b))
    }
}

/// `fold_order`, the vector's TEST semiring: every atom is an element, zero and one are the
/// empty atom, and both `add` and `mul` concatenate the left operand's bytes and the right's, so
/// a fold in another order gives another element. No law is declared.
struct FoldOrder;

/// The atom of `a`'s bytes then `b`'s; no element when either operand is not an atom.
fn concatenated(a: &Value, b: &Value) -> SemiringAnswer {
    let (Some(a), Some(b)) = (a.as_atom(), b.as_atom()) else {
        return SemiringAnswer::NotAnElement;
    };
    let mut bytes = a.bytes().to_vec();
    bytes.extend_from_slice(b.bytes());
    SemiringAnswer::Element(Value::atom(bytes))
}

impl Semiring for FoldOrder {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(b"fixture/fold-order".to_vec(), b"1".to_vec(), [0u8; 32])
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration::default()
    }

    fn zero(&self) -> Value {
        Value::atom(Vec::new())
    }

    fn one(&self) -> Value {
        Value::atom(Vec::new())
    }

    fn is_element(&self, value: &Value) -> bool {
        value.as_atom().is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        concatenated(a, b)
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        concatenated(a, b)
    }
}

/// The semiring a case names.
fn semiring(name: &str) -> Box<dyn Semiring> {
    match name {
        "counting" => Box::new(CountingSemiring::new()),
        "tropical" => Box::new(TropicalSemiring::new()),
        "stopping" => Box::new(Stopping),
        "fold_order" => Box::new(FoldOrder),
        other => panic!("unknown semiring {other:?}"),
    }
}

// ===================================== the notation =======================================

fn array(j: &Json) -> &[Json] {
    j.as_array().expect("an array")
}

fn text(j: &Json) -> &str {
    j.as_str().expect("a string")
}

fn count(j: &Json) -> u64 {
    j.as_u64().expect("a count")
}

fn small(j: &Json) -> u32 {
    u32::try_from(count(j)).expect("a count that fits u32")
}

fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

fn symbol_text(s: &Symbol) -> &str {
    std::str::from_utf8(s.bytes()).expect("a UTF-8 symbol")
}

fn term(j: &Json) -> Term {
    if let Some(s) = j.get("atom_str").and_then(Json::as_str) {
        return Term::atom(s.as_bytes().to_vec());
    }
    if let Some(v) = j.get("var").and_then(Json::as_str) {
        return Term::var(v);
    }
    if let Some(items) = j.get("tuple").and_then(Json::as_array) {
        return Term::tuple(items.iter().map(term));
    }
    panic!("a term is atom_str, var or tuple: {j}");
}

fn goal(j: &Json) -> Goal {
    let args: Vec<Term> = array(&j["args"]).iter().map(term).collect();
    Goal::new(text(&j["pred"]), args)
}

fn ground(j: &Json) -> GroundLiteral {
    goal(j).as_ground().expect("a ground literal")
}

fn ground_value(j: &Json) -> Value {
    term(j).erase_ground().expect("a ground value")
}

fn program(j: &Json) -> MapProgram {
    let mut program = MapProgram::new();
    for (id, clause) in j.as_object().expect("the program is an object") {
        let head = goal(&clause["head"]);
        let body = array(&clause["body"]).iter();
        let body: Vec<BodyLit<Term>> = body.map(|lit| BodyLit::Pos(goal(lit))).collect();
        program = program.with(id.as_str(), Clause { head, body });
    }
    program
}

fn prefix(j: &Json) -> StratumPrefix {
    let predicates = array(&j["predicates"]).iter().map(|p| sym(text(p)));
    // Verbatim, as the conformance driver reads it: the vector's order is carried as authored.
    StratumPrefix {
        level: small(&j["level"]),
        predicates: predicates.collect(),
    }
}

fn subst(j: &Json) -> Subst {
    let mut subst = Subst::new();
    for (var, image) in j.as_object().expect("a substitution is an object") {
        subst.insert(var.as_str().into(), term(image));
    }
    subst
}

fn support_ref(j: &Json) -> SupportRef {
    if let Some(s) = j.get("same_stratum") {
        let fact = ground(&s["fact"]);
        let rank = small(&s["rank"]);
        return SupportRef::SameStratum { fact, rank };
    }
    if let Some(s) = j.get("lower_stratum") {
        let cert = CertId::from(count(&s["cert"]));
        let atom = ground(&s["atom"]);
        return SupportRef::LowerStratum { cert, atom };
    }
    if let Some(s) = j.get("builtin") {
        let atom = ground(&s["atom"]);
        return SupportRef::Builtin { atom };
    }
    panic!("a support ref is same_stratum, lower_stratum or builtin: {j}");
}

fn support_edge(j: &Json) -> SupportEdge {
    SupportEdge {
        fact: ground(&j["fact"]),
        clause: ClauseId::new(text(&j["clause"])),
        subst: subst(&j["subst"]),
        body_refs: array(&j["body_refs"]).iter().map(support_ref).collect(),
        rank: small(&j["rank"]),
    }
}

fn size_decl(j: &Json) -> CertSizeDecl {
    CertSizeDecl {
        cert_facts: count(&j["cert_facts"]),
        domain_values: count(&j["domain_values"]),
        support_edges: count(&j["support_edges"]),
        rule_groundings: count(&j["rule_groundings"]),
        join_steps: count(&j["join_steps"]),
        cert_bytes: count(&j["cert_bytes"]),
    }
}

/// A case's cert in negation.json's notation, bound to `bound` as `run_negation` binds a cert
/// that sets no pin of its own. Collections are carried verbatim, never canonicalized.
fn cert(j: &Json, bound: &CertContext) -> ClosedModelCert {
    let mut domains = Vec::new();
    for d in array(&j["domains"]) {
        let type_tag = sym(text(&d["type_tag"]));
        let values = array(&d["values"]).iter().map(ground_value).collect();
        domains.push(FiniteDomain { type_tag, values });
    }
    let mut extensions = Vec::new();
    for t in array(&j["extensions"]) {
        let (pred, arity) = (sym(text(&t["pred"])), small(&t["arity"]));
        let rows = array(&t["rows"]).iter().map(ground).collect();
        extensions.push(RelationTable { pred, arity, rows });
    }
    let supports = array(&j["supports"]).iter().map(support_edge).collect();
    ClosedModelCert {
        scope: prefix(&j["scope"]),
        program_hash: bound.program_hash,
        profile_hash: bound.profile_hash,
        ctx_hash: bound.ctx_hash,
        theory_config_hash: bound.theory_config_hash,
        edb_snapshot_hashes: Vec::new(),
        domains,
        extensions,
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: j.get("partial_scope").map(prefix),
        limits_decl: size_decl(&j["limits_decl"]),
    }
}

/// An element in `vectors/semiring.json`'s value grammar.
fn element(j: &Json) -> Value {
    if let Some(n) = j.get("int").and_then(Json::as_i64) {
        return int(n);
    }
    if let Some(parts) = j.get("decimal").and_then(Json::as_array) {
        let label = Value::atom(b"decimal".to_vec());
        let (mantissa, exponent) = (whole(&parts[0]), whole(&parts[1]));
        return Value::tuple([label, int(mantissa), int(exponent)]);
    }
    if let Some(a) = j.get("atom").and_then(Json::as_str) {
        return Value::atom(a.as_bytes().to_vec());
    }
    if let Some(items) = j.get("tuple").and_then(Json::as_array) {
        return Value::tuple(items.iter().map(element));
    }
    panic!("an element is int, decimal, atom or tuple: {j}");
}

fn whole(j: &Json) -> i64 {
    j.as_i64().expect("an i64 integer")
}

/// The frozen ontos-data `int` embedding of `n`.
fn int(n: i64) -> Value {
    let term = BigInt::from_i128(i128::from(n)).to_int_term();
    term.erase_ground().expect("an int term is ground")
}

fn annotations(j: &Json) -> Vec<AnnotatedTable> {
    let mut tables = Vec::new();
    for t in array(j) {
        let pred = sym(text(&t["pred"]));
        let elements = array(&t["elements"]).iter().map(element).collect();
        tables.push(AnnotatedTable { pred, elements });
    }
    tables
}

// ======================================= the replay =======================================

/// The vector's program, profile parts and bound context, shared by every case.
struct Replay {
    program: MapProgram,
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
    bound: CertContext,
}

impl Replay {
    fn new(doc: &Json) -> Self {
        let program = program(&doc["program"]);
        let extensional = array(&doc["extensional"]).iter().map(|p| sym(text(p)));
        let mut edb = BTreeMap::new();
        for (pred, rows) in doc["edb"].as_object().expect("edb is an object") {
            let rows: Vec<GroundLiteral> = array(rows).iter().map(ground).collect();
            edb.insert(pred.as_bytes().to_vec(), rows);
        }
        let digest = program_digest(&program);
        let bound = CertContext::new(digest, NEG_PROFILE_PIN, NEG_CTX_PIN, NEG_THEORY_PIN);
        Replay {
            program,
            extensional: extensional.collect(),
            edb,
            bound,
        }
    }

    fn profile(&self, limits: CheckLimits) -> CheckProfile<()> {
        let leaves = NegLeaves {
            extensional: self.extensional.clone(),
            edb: self.edb.clone(),
        };
        CheckProfile {
            theory: Box::new(negation_theory()),
            leaves: Box::new(leaves),
            admit: Box::new(AlwaysAdmit),
            limits,
        }
    }

    /// The case's annotated cert, naming the identity of its `cert_semiring`.
    fn annotated(&self, case: &Json) -> AnnotatedClosedModelCert {
        let named = semiring(text(&case["cert_semiring"]));
        AnnotatedClosedModelCert {
            cert: cert(&case["cert"], &self.bound),
            semiring: semiring_identity(named.as_ref()),
            annotations: annotations(&case["annotations"]),
        }
    }

    /// The check of the case's annotated cert, holding the case's `semiring`, under `limits`.
    fn check(&self, case: &Json, limits: CheckLimits) -> AnnotatedOutcome {
        let annotated = self.annotated(case);
        let held = semiring(text(&case["semiring"]));
        let profile = self.profile(limits);
        let (program, bound, held) = (&self.program, &self.bound, held.as_ref());
        check_annotated_closed_model(program, &annotated, &(), &profile, bound, held)
    }
}

/// The outcome's kind and code, as the vector names them.
fn names(outcome: &AnnotatedOutcome) -> (&'static str, Option<&'static str>) {
    match outcome {
        AnnotatedOutcome::Accept { .. } => ("accept", None),
        AnnotatedOutcome::RejectCert { code, .. } => ("reject_cert", Some(code.code())),
        AnnotatedOutcome::Reject { code, .. } => ("reject", Some(code.code())),
    }
}

/// The case's verdict: its kind, its code, the row where the vector names one, the law and the
/// unattested tables.
fn assert_verdict(name: &str, want: &str, expected: &Json, got: &AnnotatedOutcome) {
    match (want, got) {
        ("accept", AnnotatedOutcome::Accept { law, unattested }) => {
            let law = law.map(AnnotationLaw::name);
            assert_eq!(law, expected["law"].as_str(), "{name}: law");
            let named: Vec<&str> = unattested.iter().map(symbol_text).collect();
            let listed: Vec<&str> = array(&expected["unattested"]).iter().map(text).collect();
            assert_eq!(named, listed, "{name}: unattested");
        }
        ("reject", AnnotatedOutcome::Reject { code, row, .. }) => {
            assert_eq!(code.code(), text(&expected["code"]), "{name}: code");
            if let Some(want_row) = expected.get("row") {
                let Some(row) = row else {
                    panic!("{name}: the verdict names no row");
                };
                let pred = text(&want_row["pred"]);
                assert_eq!(symbol_text(&row.pred), pred, "{name}: the row's predicate");
                let index = u64::try_from(row.index).ok();
                assert_eq!(index, want_row["index"].as_u64(), "{name}: the row's index");
            }
        }
        ("reject_cert", AnnotatedOutcome::RejectCert { code, .. }) => {
            assert_eq!(code.code(), text(&expected["code"]), "{name}: code");
        }
        (want, got) => panic!("{name}: want {want}, got {got:?}"),
    }
}

#[test]
fn every_annotated_case_reproduces_its_verdict() {
    let doc = vectors();
    let replay = Replay::new(&doc);
    let cases = array(&doc["cases"]);
    let n = cases.len();
    assert!(n >= 14, "{n} cases; the vector has at least 14");
    let r3_raised = proof_budgets::r3_raised();
    let limits = CheckLimits::default();
    let (mut expected_names, mut ran) = (BTreeSet::new(), BTreeSet::new());
    let mut raised_cases = 0usize;
    for case in cases {
        let name = text(&case["name"]);
        let want = text(&case["outcome"]);
        let expected = &case["expected"];
        expected_names.insert(want);
        expected_names.extend(expected["code"].as_str());
        let outcome = replay.check(case, limits);
        let (kind, code) = names(&outcome);
        ran.insert(kind);
        ran.extend(code);
        assert_verdict(name, want, expected, &outcome);
        // R3 (#2733): an accepted case keeps its verdict under every checker budget raised, alone
        // and together. The raise is the declared table's (vectors/allowances.json).
        if want == "accept" {
            raised_cases += 1;
            let variants = proof_budgets::each_budget_raised(limits, r3_raised);
            for (budget, raised) in variants {
                let again = replay.check(case, raised);
                assert_eq!(again, outcome, "{name}: raising {budget} moved it");
            }
        }
    }
    assert!(raised_cases > 0, "no accepted case is in R3's domain");
    assert_eq!(ran, expected_names, "every kind and code ran");
}

/// `v`'s tuple with item `i` replaced by `item`.
fn replaced(v: &Value, i: usize, item: Value) -> Value {
    let mut items = v.as_tuple().expect("a tuple").items().to_vec();
    items[i] = item;
    Value::tuple(items)
}

#[test]
fn every_annotated_cert_round_trips_its_wire_and_the_decoder_is_closed() {
    let doc = vectors();
    let replay = Replay::new(&doc);
    let cases = array(&doc["cases"]);
    for case in cases {
        let name = text(&case["name"]);
        let annotated = replay.annotated(case);
        let wire = annotated_closed_model_cert_as_value(&annotated);
        let decoded = annotated_closed_model_cert_from_value(&wire);
        assert_eq!(decoded, Ok(annotated), "{name}: the wire round-trips");
    }
    // The decoder is CLOSED: each of these differs from a valid wire in one place, and is refused.
    let wire = annotated_closed_model_cert_as_value(&replay.annotated(&cases[0]));
    let items = wire.as_tuple().expect("the wire is a tuple").items();
    let table = items[3].as_tuple().expect("a tuple").items()[0].clone();
    let with_table = |table: Value| replaced(&wire, 3, Value::tuple([table]));
    let pred = Value::atom(b"e".to_vec());
    let tag = replaced(&wire, 0, Value::atom(b"closed".to_vec()));
    let arity = Value::tuple(items[..3].to_vec());
    let raw = replaced(&items[2], 2, Value::atom([0u8; 32]));
    let digest = replaced(&wire, 2, raw);
    let identity = replaced(&wire, 2, Value::tuple(items[2..3].to_vec()));
    let triple = with_table(Value::tuple([pred.clone(), Value::tuple([]), pred]));
    let tuple_pred = with_table(replaced(&table, 0, Value::tuple([])));
    let refused = [
        ("another tag", tag),
        ("another arity", arity),
        ("a raw digest, not its hex", digest),
        ("an identity of one item", identity),
        ("a table of three items", triple),
        ("a predicate that is not an atom", tuple_pred),
    ];
    for (what, malformed) in refused {
        let decoded = annotated_closed_model_cert_from_value(&malformed);
        assert!(decoded.is_err(), "{what} is refused, got {decoded:?}");
    }
}
