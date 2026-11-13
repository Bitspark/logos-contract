//! #3067 (research 0028 row A15; `seat:caa`'s rulings Q1 to Q3): `vectors/fragment.json` replayed
//! through `check`'s scope gate. Each case states one sealed clause of a program and its context: the
//! relations its certificate seals, the relations it reads from a strictly lower certificate, and the
//! relations a theory owns. The gate refuses the program by the case's `expect` (the first gate the
//! clause fails, and that gate's subject), or admits it when `expect` is null. The go and ts checkers
//! replay the same file.

use super::cert::check_scope_downward_closed;
use super::cert_stack::CertView;
use super::RejectionCode;
use crate::cert::{CertSizeDecl, ClosedModelCert, ClosureWitness, StratumPrefix, SupportWitness};
use crate::fragment::{classify_sealed_clause, Outside, ScopeGraph, SealContext};
use crate::literal::{Goal, GroundLiteral, Symbol};
use crate::program::{BodyLit, Clause, CountLit, MapProgram, PredicateRef, ProjectSpec};
use crate::spi::{Theory, TheoryGround};
use crate::term::{Term, VarId};
use serde_json::Value;

const VECTORS: &str = include_str!("../../../../vectors/fragment.json");

/// The relations a case's theory owns: it decides nothing, and owning is all the gate reads.
struct Owns(Vec<Symbol>);
// test-double: consumer(owns the relations a fragment.json case lists, decides none)
impl Theory for Owns {
    crate::cannot_copy!(
        Theory,
        "a test double: the relations one fragment.json case lists as owned"
    );
    fn owns(&self, pred: &Symbol) -> bool {
        self.0.contains(pred)
    }
    fn decide_ground(&self, _: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
}

fn term(v: &Value) -> Term {
    match v {
        Value::String(s) if s.starts_with(|c: char| c.is_ascii_uppercase()) => {
            Term::var(s.as_str())
        }
        Value::String(s) => Term::atom(s.as_bytes().to_vec()),
        Value::Array(items) => {
            let functor = items[0].as_str().expect("a compound's functor");
            Term::tuple(
                std::iter::once(Term::atom(functor.as_bytes().to_vec()))
                    .chain(items[1..].iter().map(term)),
            )
        }
        other @ (Value::Null | Value::Bool(_) | Value::Number(_) | Value::Object(_)) => {
            panic!("not a term in fragment.json's notation: {other}")
        }
    }
}

fn goal(v: &Value) -> Goal {
    let items = v.as_array().expect("a goal is an array");
    let pred = items[0].as_str().expect("a goal's predicate");
    Goal::new(pred, items[1..].iter().map(term).collect::<Vec<_>>())
}

fn body_lit(v: &Value) -> BodyLit<Term> {
    if let Some(inner) = v.get("neg") {
        return BodyLit::Neg(goal(inner));
    }
    if let Some(count) = v.get("count") {
        let pred = count["pred"].as_str().expect("a count's predicate");
        let arity = count["arity"].as_u64().expect("a count's arity") as u32;
        let filter = count["filter"]
            .as_array()
            .expect("a count's filter")
            .iter()
            .map(|entry| {
                let pos = entry[0].as_u64().expect("a filter position") as u32;
                (pos, term(&entry[1]))
            })
            .collect();
        return BodyLit::Count(CountLit {
            pred: PredicateRef::new(pred, arity),
            filter,
            project: ProjectSpec::Rows,
            count: term(&count["result"]),
        });
    }
    BodyLit::Pos(goal(v))
}

fn clause(v: &Value) -> Clause {
    let body = v
        .get("body")
        .and_then(Value::as_array)
        .map(|lits| lits.iter().map(body_lit).collect())
        .unwrap_or_default();
    Clause {
        head: goal(&v["head"]),
        body,
    }
}

fn symbols(v: &Value) -> Vec<Symbol> {
    v.as_array()
        .expect("a list of relations")
        .iter()
        .map(|s| Symbol::from(s.as_str().expect("a relation's name")))
        .collect()
}

/// A certificate that seals `preds` and carries nothing else: the scope gate reads only its scope.
fn cert(preds: &[Symbol]) -> ClosedModelCert {
    ClosedModelCert {
        scope: StratumPrefix::new(1, preds.iter().cloned()),
        program_hash: [0; 32],
        profile_hash: [0; 32],
        ctx_hash: [0; 32],
        theory_config_hash: [0; 32],
        edb_snapshot_hashes: Vec::new(),
        domains: Vec::new(),
        extensions: Vec::new(),
        supports: SupportWitness(Vec::new()),
        closure: ClosureWitness,
        limits_decl: CertSizeDecl {
            cert_facts: 0,
            domain_values: 0,
            support_edges: 0,
            rule_groundings: 0,
            join_steps: 0,
            cert_bytes: 0,
        },
        decomposition_witness: None,
        partial_scope: None,
    }
}

/// The phrase `check`'s refusal carries for `expect`: the gate, and its subject.
fn phrase(expect: &Value) -> String {
    let field = |key: &str| {
        expect[key]
            .as_str()
            .expect("the gate's subject")
            .to_string()
    };
    match expect["outside"].as_str().expect("the gate's name") {
        "count_not_lower" if expect["same_scope"].as_bool() == Some(true) => format!(
            "contains a count over predicate {:?}, which this same certificate seals",
            field("pred")
        ),
        "count_not_lower" => format!(
            "contains a count over predicate {:?}, which no unique, exact, Valid strictly lower certificate seals",
            field("pred")
        ),
        "count_open_compound" => format!(
            "count over predicate {:?} contains an open compound",
            field("pred")
        ),
        "constructor_cycle" => format!("on a dependency cycle through {:?}", field("through")),
        "unserved" => format!(
            "references predicate {:?} that is neither sealed",
            field("pred")
        ),
        "intra_scope_negation" => format!(
            "negates predicate {:?} sealed by this same prefix",
            field("pred")
        ),
        "unbound_count_filter" => format!(
            "count over predicate {:?} has filter variable {:?} not bound",
            field("pred"),
            field("var")
        ),
        "unbound_variable" => format!("has unsafe variable {:?}:", field("var")),
        other => panic!("fragment.json names an unknown gate: {other}"),
    }
}

#[test]
fn every_fragment_case_is_classified_by_its_first_gate_in_check_3067() {
    let doc: Value = serde_json::from_str(VECTORS).expect("fragment.json parses");
    let cases = doc["cases"].as_array().expect("fragment.json's cases");
    assert!(
        cases.len() >= 20,
        "fragment.json holds its cases: {}",
        cases.len()
    );
    let mut failures: Vec<String> = Vec::new();
    for case in cases {
        let name = case["name"].as_str().expect("a case's name");
        let mut program = MapProgram::new();
        for (i, c) in case["program"]
            .as_array()
            .expect("a case's program")
            .iter()
            .enumerate()
        {
            program.insert(format!("c{i:02}"), clause(c));
        }
        let reads_lower = symbols(&case["reads_lower"]);
        let own = cert(&symbols(&case["seals"]));
        let lower = cert(&reads_lower);
        let view = CertView::with_lower(&own, &lower, &reads_lower);
        let owns = Owns(symbols(&case["owns"]));
        match (
            &case["expect"],
            check_scope_downward_closed(&view, &program, &owns),
        ) {
            (Value::Null, Ok(())) => {}
            (Value::Null, Err((_, detail))) => {
                failures.push(format!(
                    "{name}: inside the fragment, but refused: {detail}"
                ));
            }
            (expect, Ok(())) => failures.push(format!("{name}: expected {expect}, admitted")),
            (expect, Err((code, detail))) => {
                let want = phrase(expect);
                if code != RejectionCode::CertScopeIncomplete || !detail.contains(&want) {
                    failures.push(format!("{name}: expected {want:?}, got {code:?}: {detail}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "fragment.json through check's scope gate:\n{}",
        failures.join("\n")
    );
}

/// The `Outside` a case's `expect` names, or `None` inside the fragment.
fn outside(expect: &Value) -> Option<Outside> {
    if expect.is_null() {
        return None;
    }
    let sym = |key: &str| Symbol::from(expect[key].as_str().expect("the gate's subject"));
    let var = || VarId::new(expect["var"].as_str().expect("the gate's variable"));
    Some(match expect["outside"].as_str().expect("the gate's name") {
        "count_not_lower" => Outside::CountNotLower {
            pred: sym("pred"),
            same_scope: expect["same_scope"].as_bool().expect("same_scope"),
        },
        "count_open_compound" => Outside::CountOpenCompound { pred: sym("pred") },
        "constructor_cycle" => Outside::ConstructorCycle {
            through: sym("through"),
        },
        "unserved" => Outside::Unserved { pred: sym("pred") },
        "intra_scope_negation" => Outside::IntraScopeNegation { pred: sym("pred") },
        "unbound_count_filter" => Outside::UnboundCountFilter {
            pred: sym("pred"),
            var: var(),
        },
        "unbound_variable" => Outside::UnboundVariable { var: var() },
        other => panic!("fragment.json names an unknown gate: {other}"),
    })
}

/// The same file through the contract tier's one function, compared structurally: the clause the
/// case names, in the context it states, over the scope graph `check` would build.
#[test]
fn every_fragment_case_is_classified_by_the_contract_tier_function_3067() {
    let doc: Value = serde_json::from_str(VECTORS).expect("fragment.json parses");
    let cases = doc["cases"].as_array().expect("fragment.json's cases");
    let mut failures: Vec<String> = Vec::new();
    for case in cases {
        let name = case["name"].as_str().expect("a case's name");
        let program: Vec<Clause> = case["program"]
            .as_array()
            .expect("a case's program")
            .iter()
            .map(clause)
            .collect();
        let ctx = SealContext {
            seals: symbols(&case["seals"]).into_iter().collect(),
            reads_lower: symbols(&case["reads_lower"]).into_iter().collect(),
        };
        let mut graph = ScopeGraph::new();
        for c in &program {
            graph.add(c, &|pred: &Symbol| ctx.seals.contains(pred));
        }
        let owned = symbols(&case["owns"]);
        let index = case["clause"]
            .as_u64()
            .expect("the classified clause's index") as usize;
        let owns = |pred: &Symbol| owned.contains(pred);
        let got = classify_sealed_clause(&program[index], &ctx, &graph, &owns, &owns);
        let want = outside(&case["expect"]);
        if got != want {
            failures.push(format!("{name}: expected {want:?}, got {got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "fragment.json through classify_sealed_clause:\n{}",
        failures.join("\n")
    );
}
