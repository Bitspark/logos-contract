//! Rust replay of the cross-core ADR-0023 certifiable-aggregation vector
//! `vectors/aggregation.json` (Phase 5, #585, epic #579). Each hand-authored case is run
//! through `check_with_cert_context` under the `aggregation_v1` profile and asserted
//! against the pinned oracle outcome. The SAME file drives the go and ts replays — one
//! oracle (this rs side, per the #464 lesson: rs is the oracle, never go≡ts mutual) pins
//! all three cores.
//!
//! The `aggregation_v1` profile (from the vector's note): NO theory (`NoTheory` owns
//! nothing); EDB leaves = the top-level `extensional` set, attesting an EDB-of-record
//! snapshot from the top-level `edb` map (§3.6); Context = unit. The bound context is
//! DERIVED (recomputed program_hash + fixed non-zero profile/ctx/theory pins); each cert
//! auto-binds to it (no case sets an explicit pin). Certs are named in a top-level `certs`
//! map and selected per case by `cert` (a key, or `null` ⇒ no cert supplied).
//!
//! THE CORE GUARANTEE this replay pins tri-core is the adversarial tamper case
//! `tamper_wrong_k_over_valid_cert`: a derivation claiming a wrong `k` over an otherwise
//! VALID cert MUST be rejected `count_mismatch` — the dual-conformance law for count.

use logos_contract::{
    check_with_cert_context, check_with_cert_memo, edb_table_hash, intval::BigInt, program_digest,
    CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId,
    ClosedModelCert, ClosureWitness, CountLit, Derivation, Evidence, FiniteDomain, Goal,
    GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, Outcome,
    PredicateRef, PredicateSet, Premise, ProjectSpec, RelationTable, StratumPrefix, Subst,
    SupportEdge, SupportRef, SupportWitness, Symbol, Term, Theory, TheoryOutcome, WorldMemo,
};
use ontos_core::Value;
use serde_json::Value as Json;
use std::collections::BTreeMap;

// ================================= the aggregation_v1 profile =================================

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Fails {
            code: "no_theory".into(),
        }
    }
}

/// A `LeafVerifier` attesting a fixed EDB-of-record snapshot for each extensional
/// predicate (so the §3.6 EDB-binding gate can bind the sealed table to the live EDB).
struct AggLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for AggLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
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

// =================================== authoring notation ===================================
// Mirrors the negation_vectors decoders, extended with the count premise / count body
// literal shapes (see the vector's `note`).

fn term_from_json(j: &Json) -> Term {
    if let Some(s) = j.get("atom_str").and_then(Json::as_str) {
        return Term::atom(s.as_bytes().to_vec());
    }
    if let Some(v) = j.get("var").and_then(Json::as_str) {
        return Term::var(v);
    }
    // #587: the canonical ontos `int` ground value (a sealed numeric column for sum/min/max).
    if let Some(n) = j.get("int").and_then(Json::as_i64) {
        return Term::from_value(&int_value(n as i128));
    }
    // #2813: the canonical ontos `decimal` embedding (#331, the term.json notation), for the
    // frozen decimal-column rows and the non-int `k` row.
    if let Some(d) = j.get("decimal") {
        let s = d.as_str().expect("decimal value is a string");
        return logos_contract::BigDecimal::from_decimal_str(s)
            .unwrap_or_else(|| panic!("decimal {s:?} is not a decimal literal"))
            .to_decimal_term();
    }
    if let Some(items) = j.get("tuple").and_then(Json::as_array) {
        return Term::tuple(items.iter().map(term_from_json));
    }
    panic!("term must be atom_str/var/int/decimal/tuple: {j}");
}

fn ground_value(j: &Json) -> Value {
    term_from_json(j)
        .erase_ground()
        .expect("value must be ground")
}

fn goal_from_json(j: &Json) -> Goal {
    let pred = j.get("pred").and_then(Json::as_str).expect("pred");
    let args: Vec<Term> = j
        .get("args")
        .and_then(Json::as_array)
        .map(|a| a.iter().map(term_from_json).collect())
        .unwrap_or_default();
    Goal::new(pred, args)
}

fn ground_from_json(j: &Json) -> GroundLiteral {
    goal_from_json(j)
        .as_ground()
        .expect("literal must be ground")
}

fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

/// The canonical ontos/data `int` ground value for an integer drawn from the vector
/// (`{"int": N}` or a bare number in `subst`).
fn int_value(n: i128) -> Value {
    BigInt::from_i128(n)
        .to_int_term()
        .erase_ground()
        .expect("ground int")
}

fn pred_ref_from_json(j: &Json) -> PredicateRef {
    let name = j.get("name").and_then(Json::as_str).expect("pred name");
    let arity = j.get("arity").and_then(Json::as_u64).expect("pred arity") as u32;
    PredicateRef::new(name, arity)
}

fn project_from_json(j: &Json) -> ProjectSpec {
    if j.as_str() == Some("rows") {
        return ProjectSpec::Rows;
    }
    if let Some(attr) = j.get("distinct").and_then(Json::as_u64) {
        return ProjectSpec::Distinct { attr: attr as u32 };
    }
    // #587 integer folds: {sum:<attr>} / {min:<attr>} / {max:<attr>}.
    if let Some(attr) = j.get("sum").and_then(Json::as_u64) {
        return ProjectSpec::Sum { attr: attr as u32 };
    }
    if let Some(attr) = j.get("min").and_then(Json::as_u64) {
        return ProjectSpec::Min { attr: attr as u32 };
    }
    if let Some(attr) = j.get("max").and_then(Json::as_u64) {
        return ProjectSpec::Max { attr: attr as u32 };
    }
    panic!("project must be 'rows' or {{distinct|sum|min|max:<attr>}}: {j}");
}

/// A clause body literal: a positive goal or a `count_lit` count body literal.
fn body_lit_from_json(j: &Json) -> logos_contract::BodyLit<Term> {
    if let Some(c) = j.get("count_lit") {
        let filter: Vec<(u32, Term)> = c
            .get("filter")
            .and_then(Json::as_array)
            .map(|a| {
                a.iter()
                    .map(|e| {
                        let pos = e.get("pos").and_then(Json::as_u64).expect("filter pos") as u32;
                        // a clause-body filter binds a variable (or a ground atom_str).
                        let term = if let Some(v) = e.get("var") {
                            term_from_json(&serde_json::json!({ "var": v }))
                        } else {
                            term_from_json(e)
                        };
                        (pos, term)
                    })
                    .collect()
            })
            .unwrap_or_default();
        let count = term_from_json(c.get("count").expect("count slot"));
        return logos_contract::BodyLit::Count(CountLit {
            pred: pred_ref_from_json(c.get("pred").expect("count_lit pred")),
            filter,
            project: project_from_json(c.get("project").expect("project")),
            count,
        });
    }
    logos_contract::BodyLit::Pos(goal_from_json(j))
}

/// A derivation premise: a bare positive node index, or a `count` count premise.
fn premise_from_json(j: &Json) -> Premise {
    if let Some(n) = j.as_u64() {
        return Premise::pos((n as usize) as u64);
    }
    let c = j.get("count").expect("premise is an int or a {count:..}");
    let filter: Vec<(u32, Value)> = c
        .get("filter")
        .and_then(Json::as_array)
        .map(|a| {
            a.iter()
                .map(|e| {
                    let pos = e.get("pos").and_then(Json::as_u64).expect("filter pos") as u32;
                    (pos, ground_value(e.get("value").expect("filter value")))
                })
                .collect()
        })
        .unwrap_or_default();
    // `k` is a bare int (the canonical `int` embedding) or, #2813, any value in the term notation
    // (a non-int claim). Any other shape, or a missing `k`, is a vector error, never a default.
    let k = match c.get("k") {
        Some(n) if n.is_i64() => int_value(i128::from(n.as_i64().expect("i64 k"))),
        Some(t) if t.is_object() => ground_value(t),
        other => panic!("count k must be an int or a term object, got {other:?}"),
    };
    let cert = c.get("cert").and_then(Json::as_u64).expect("count cert") as usize;
    Premise::Count {
        pred: pred_ref_from_json(c.get("pred").expect("count pred")),
        filter,
        project: project_from_json(c.get("project").expect("project")),
        k,
        cert: CertId(cert as u64),
    }
}

fn subst_from_json(j: &Json) -> Subst {
    let mut subst: Subst = BTreeMap::new();
    for (name, term) in j.as_object().expect("subst object") {
        // A subst image is a term notation OR a bare {"int": N} (the count result).
        let t = if let Some(n) = term.get("int").and_then(Json::as_i64) {
            Term::from_value(&int_value(n as i128))
        } else {
            term_from_json(term)
        };
        subst.insert(name.clone().into(), t);
    }
    subst
}

fn node_from_json(j: &Json) -> Node {
    let conclusion = ground_from_json(j.get("conclusion").expect("conclusion"));
    match j.get("kind").and_then(Json::as_str).expect("kind") {
        "rule" => {
            let subst = subst_from_json(j.get("subst").expect("subst"));
            let premises = j
                .get("premises")
                .and_then(Json::as_array)
                .map(|a| a.iter().map(premise_from_json).collect())
                .unwrap_or_default();
            Node::Rule {
                conclusion,
                clause: ClauseId::new(j.get("clause").and_then(Json::as_str).expect("clause")),
                subst,
                premises,
                meta: NodeMeta::none(),
            }
        }
        "builtin" => Node::Builtin { conclusion },
        "leaf" => Node::Leaf {
            conclusion,
            evidence: Evidence::none(),
        },
        other => panic!("unknown node kind {other}"),
    }
}

fn cert_from_json(j: &Json, ctx: &CertContext) -> ClosedModelCert {
    let scope = j.get("scope").expect("scope");
    let level = scope.get("level").and_then(Json::as_u64).expect("level") as u32;
    let preds: Vec<Symbol> = scope
        .get("predicates")
        .and_then(Json::as_array)
        .map(|a| a.iter().map(|p| sym(p.as_str().unwrap())).collect())
        .unwrap_or_default();
    let domains: Vec<FiniteDomain> = j
        .get("domains")
        .and_then(Json::as_array)
        .map(|a| {
            a.iter()
                .map(|d| {
                    let tag = d.get("type_tag").and_then(Json::as_str).expect("type_tag");
                    let values: Vec<Value> = d
                        .get("values")
                        .and_then(Json::as_array)
                        .map(|vs| vs.iter().map(ground_value).collect())
                        .unwrap_or_default();
                    FiniteDomain::new(sym(tag), values)
                })
                .collect()
        })
        .unwrap_or_default();
    let extensions: Vec<RelationTable> = j
        .get("extensions")
        .and_then(Json::as_array)
        .map(|a| {
            a.iter()
                .map(|e| {
                    let pred = e.get("pred").and_then(Json::as_str).expect("ext pred");
                    let arity = e.get("arity").and_then(Json::as_u64).expect("arity") as u32;
                    let rows: Vec<GroundLiteral> = e
                        .get("rows")
                        .and_then(Json::as_array)
                        .map(|rs| rs.iter().map(ground_from_json).collect())
                        .unwrap_or_default();
                    RelationTable::new(pred, arity, rows)
                })
                .collect()
        })
        .unwrap_or_default();
    let limits = j.get("limits_decl").expect("limits_decl");
    let num = |k: &str| limits.get(k).and_then(Json::as_u64).unwrap_or(0);
    // #2258 L3.3b: a stacked cert carries support edges and may seal PARTIAL.
    let supports: Vec<SupportEdge> = j
        .get("supports")
        .and_then(Json::as_array)
        .map(|a| a.iter().map(support_edge_from_json).collect())
        .unwrap_or_default();
    let partial_scope = j.get("partial_scope").map(|p| {
        let level = p
            .get("level")
            .and_then(Json::as_u64)
            .expect("partial level") as u32;
        let preds: Vec<Symbol> = p
            .get("predicates")
            .and_then(Json::as_array)
            .map(|a| a.iter().map(|q| sym(q.as_str().unwrap())).collect())
            .unwrap_or_default();
        StratumPrefix::new(level, preds)
    });
    ClosedModelCert {
        scope: StratumPrefix::new(level, preds),
        program_hash: ctx.program_hash,
        profile_hash: ctx.profile_hash,
        ctx_hash: ctx.ctx_hash,
        theory_config_hash: ctx.theory_config_hash,
        edb_snapshot_hashes: vec![],
        domains,
        extensions,
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope,
        limits_decl: CertSizeDecl {
            cert_facts: (num("cert_facts") as usize) as u64,
            domain_values: (num("domain_values") as usize) as u64,
            support_edges: (num("support_edges") as usize) as u64,
            rule_groundings: (num("rule_groundings") as usize) as u64,
            join_steps: (num("join_steps") as usize) as u64,
            cert_bytes: num("cert_bytes"),
        },
    }
}

/// A support edge (#2258 L3.3b): `{fact, clause, subst, body_refs, rank}`, the negation.json form.
fn support_edge_from_json(j: &Json) -> SupportEdge {
    SupportEdge {
        fact: ground_from_json(j.get("fact").expect("edge fact")),
        clause: ClauseId::new(j.get("clause").and_then(Json::as_str).expect("edge clause")),
        subst: subst_from_json(j.get("subst").expect("edge subst")),
        body_refs: j
            .get("body_refs")
            .and_then(Json::as_array)
            .expect("edge body_refs")
            .iter()
            .map(support_ref_from_json)
            .collect(),
        rank: j.get("rank").and_then(Json::as_u64).expect("edge rank") as u32,
    }
}

/// A support ref: one of `same_stratum`, `lower_stratum`, `builtin`, `neg_lower`, `count_lower`.
fn support_ref_from_json(j: &Json) -> SupportRef {
    let cert = |r: &Json| {
        CertId((r.get("cert").and_then(Json::as_u64).expect("ref cert") as usize) as u64)
    };
    if let Some(r) = j.get("same_stratum") {
        SupportRef::SameStratum {
            fact: ground_from_json(r.get("fact").expect("ref fact")),
            rank: r.get("rank").and_then(Json::as_u64).expect("ref rank") as u32,
        }
    } else if let Some(r) = j.get("lower_stratum") {
        SupportRef::LowerStratum {
            cert: cert(r),
            atom: ground_from_json(r.get("atom").expect("ref atom")),
        }
    } else if let Some(r) = j.get("builtin") {
        SupportRef::Builtin {
            atom: ground_from_json(r.get("atom").expect("ref atom")),
        }
    } else if let Some(r) = j.get("neg_lower") {
        SupportRef::NegLower {
            cert: cert(r),
            atom: ground_from_json(r.get("atom").expect("ref atom")),
        }
    } else if let Some(r) = j.get("count_lower") {
        SupportRef::CountLower { cert: cert(r) }
    } else {
        panic!("unknown support ref {j:?}");
    }
}

fn load_doc() -> Json {
    // Walk up from the crate dir to the repo root holding vectors/aggregation.json.
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/aggregation.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/aggregation.json");
    }
    let raw = std::fs::read_to_string(dir.join("vectors/aggregation.json")).expect("read vector");
    serde_json::from_str(&raw).expect("parse vector")
}

/// The value R3 raises a budget to, from the declared carrier table (#2733).
fn r3_raised() -> usize {
    let table: Json = serde_json::from_str(include_str!("../../../vectors/allowances.json"))
        .expect("vectors/allowances.json parses");
    table["raised"].as_u64().expect("the table's raised value") as usize
}

#[test]
fn aggregation_vectors_replay() {
    let doc = load_doc();

    // Build the shared program from the vector's `program` map.
    let mut program = MapProgram::new();
    for (id, clause) in doc.get("program").unwrap().as_object().unwrap() {
        let head = goal_from_json(clause.get("head").unwrap());
        let body: Vec<_> = clause
            .get("body")
            .and_then(Json::as_array)
            .map(|a| a.iter().map(body_lit_from_json).collect())
            .unwrap_or_default();
        program = program.with(id.as_str(), Clause { head, body });
    }

    // The extensional set + EDB-of-record snapshots.
    let extensional: Vec<&str> = doc
        .get("extensional")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .map(|p| p.as_str().unwrap())
        .collect();
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    for (pred, rows) in doc.get("edb").unwrap().as_object().unwrap() {
        let grounds: Vec<GroundLiteral> = rows
            .as_array()
            .unwrap()
            .iter()
            .map(ground_from_json)
            .collect();
        edb.insert(pred.as_bytes().to_vec(), grounds);
    }
    // A per-case `limits` override (issue #253's `max_term_depth` among them) lets a case pin a
    // budget; an absent key keeps its default.
    let make_profile = |limits: CheckLimits| CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(AggLeaves {
            extensional: PredicateSet::from_iter(extensional.iter().copied()),
            edb: edb.clone(),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    };

    // The DERIVED bound context (recomputed program hash + fixed non-zero pins).
    let ctx = CertContext::new(program_digest(&program), [1u8; 32], [2u8; 32], [3u8; 32]);
    let certs = doc.get("certs").unwrap().as_object().unwrap();

    let cases = doc.get("cases").unwrap().as_array().unwrap();
    assert!(!cases.is_empty(), "no aggregation cases loaded");

    // #2565: cases whose world went through the memo, so its cross-check is not vacuous.
    let mut memoized_worlds = 0usize;
    let r3_raised = r3_raised();
    let mut raised_cases = 0usize;
    for case in cases {
        let name = case.get("name").and_then(Json::as_str).unwrap();
        let claim = ground_from_json(case.get("claim").unwrap());
        let nodes: Vec<Node> = case
            .get("derivation")
            .unwrap()
            .get("nodes")
            .and_then(Json::as_array)
            .unwrap()
            .iter()
            .map(node_from_json)
            .collect();
        let root = case
            .get("derivation")
            .unwrap()
            .get("root")
            .and_then(Json::as_u64)
            .unwrap() as usize;
        // `certs` (#2258 L3.3b): an ORDERED list of keys into `certs`, index = position. Else
        // `cert`: a key into `certs`, or null/absent ⇒ no cert supplied.
        let closed_world: Vec<ClosedModelCert> = match (case.get("certs"), case.get("cert")) {
            (Some(Json::Array(keys)), _) => keys
                .iter()
                .map(|k| cert_from_json(certs.get(k.as_str().unwrap()).expect("named cert"), &ctx))
                .collect(),
            (_, Some(Json::String(key))) => {
                vec![cert_from_json(certs.get(key).expect("named cert"), &ctx)]
            }
            _ => vec![],
        };
        // #2602 (`seat:caa`'s condition 3): the length reading equals the encoding it measures.
        for cert in &closed_world {
            let mut zeroed = cert.clone();
            zeroed.limits_decl.cert_bytes = 0;
            assert_eq!(
                logos_contract::cert_encoded_bytes(cert),
                ontos_codec::encode(
                    &logos_contract::derivation_wire::closed_model_cert_as_value(&zeroed)
                )
                .len() as u64,
                "{name}: the length reading disagrees with the encoding it measures"
            );
        }
        let deriv = Derivation::with_closed_world(nodes, root as u64, closed_world);

        // Every key of the case's `limits`, read by the budgets' own names (#3376's class: one
        // reader of the object; an absent key keeps its default, an unknown one is refused).
        let mut limits = CheckLimits::default();
        for (key, value) in case
            .get("limits")
            .and_then(Json::as_object)
            .into_iter()
            .flatten()
        {
            let (_, slot) = limits
                .budgets_mut()
                .into_iter()
                .find(|(name, _)| name == key)
                .unwrap_or_else(|| panic!("case {name}: unknown budget {key}"));
            *slot = value.as_u64().expect("a budget is a count") as usize;
        }
        let profile = make_profile(limits);
        let outcome = check_with_cert_context(&program, &claim, &deriv, &(), &profile, &ctx);
        // #2565 term 1: the same case through the checker's world memo, a miss then a hit, is the
        // fresh verdict both times, and one world is verified once.
        let mut memo = WorldMemo::new();
        for pass in ["miss", "hit"] {
            let memoized =
                check_with_cert_memo(&program, &claim, &deriv, &(), &profile, &ctx, &mut memo);
            assert_eq!(
                memoized, outcome,
                "case {name}: the world memo's {pass} diverged"
            );
        }
        // Once, or not at all when a check before any certificate is read (the node cap, root,
        // term depth) decides the case.
        let verified = memo.certificates_verified();
        assert!(
            verified == 0 || verified == deriv.closed_world.len(),
            "case {name}: two checks of one world must verify it at most once, verified {verified}"
        );
        if verified > 0 {
            memoized_worlds += 1;
        }
        let got = match &outcome {
            Outcome::Accept => "accept".to_string(),
            Outcome::Reject { code, .. } => format!("reject:{}", code.code()),
        };
        let want = match case.get("outcome").unwrap() {
            Json::String(s) => s.clone(),
            obj => format!(
                "reject:{}",
                obj.get("reject").and_then(Json::as_str).unwrap()
            ),
        };
        assert_eq!(got, want, "case {name}: got {got}, want {want}");

        // R3 (#2733, the checker's arm): an accepted case stays accepted under each raised budget,
        // alone and together. The raise value is the declared table's (vectors/allowances.json).
        if want == "accept" {
            raised_cases += 1;
            for (budget, raised) in limits.each_budget_raised(r3_raised) {
                let outcome = check_with_cert_context(
                    &program,
                    &claim,
                    &deriv,
                    &(),
                    &make_profile(raised),
                    &ctx,
                );
                assert!(
                    matches!(outcome, Outcome::Accept),
                    "case {name}: raising {budget} changed the verdict: {outcome:?}"
                );
            }
        }
    }
    assert!(raised_cases > 0, "no aggregation case is in R3's domain");
    assert!(
        memoized_worlds > 0,
        "#2565: no aggregation case reached the world memo, so its cross-check proved nothing"
    );
}
