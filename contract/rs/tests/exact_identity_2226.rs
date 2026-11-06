//! #2226's rows, after #3022. #2226 added the exact term identity beside the default reify_lists,
//! whose label-tolerant sites ACCEPTED the issue's join, head, hidden and nested diag rows and a root
//! respelled against its claim. #3022 (seat:caa's ruling) makes every certified literal claim exact:
//! every comparison site is structural under EVERY identity, so all five are refused under both, and
//! ctl-same (every spelling alike) is accepted under both. The same inputs are pinned in contract/rs,
//! contract/go and contract/ts.

use logos_contract::{
    check, edb_table_hash, AlwaysAdmit, CheckLimits, CheckProfile, Clause, ClauseId,
    CompoundTheory, Derivation, Evidence, Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier,
    MapProgram, Node, NodeMeta, Outcome, PredicateSet, Premise, Subst, Symbol, Term, TermIdentity,
};
use ontos_core::Value;
use std::collections::BTreeMap;

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
/// `.(a, [])`: the list `[a]`, cons form.
fn cons_a() -> Value {
    Value::tuple([atom("."), atom("a"), atom("[]")])
}
/// `list(a)`: the same list, reified.
fn list_a() -> Value {
    Value::tuple([atom("list"), atom("a")])
}
fn gl(pred: &str, args: &[Value]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().cloned())
}

/// Admits exactly its rows (exact identity) and attests their EDB snapshot.
struct Leaves {
    extensional: PredicateSet,
    rows: Vec<GroundLiteral>,
}
// test-double: consumer(a fixed EDB: admits exactly its rows and attests an EDB snapshot)
impl LeafVerifier<()> for Leaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, atom: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        if self.rows.contains(atom) {
            LeafOutcome::Admit
        } else {
            LeafOutcome::Reject {
                code: "not_admitted".into(),
            }
        }
    }
    fn edb_snapshot(&self, pred: &Symbol, _: &()) -> Option<Hash> {
        let rows: Vec<GroundLiteral> = self
            .rows
            .iter()
            .filter(|row| &row.pred == pred)
            .cloned()
            .collect();
        (!rows.is_empty()).then(|| edb_table_hash(pred, &rows))
    }
}

/// One row: the program, the claim, the derivation (root last), the extensional predicates, and
/// the leaf rows admitted.
struct Fixture {
    program: MapProgram,
    claim: GroundLiteral,
    nodes: Vec<Node>,
    extensional: &'static [&'static str],
    rows: Vec<GroundLiteral>,
}

fn verdict(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Accept => "ACCEPT",
        Outcome::Reject { code, .. } => code.code(),
    }
}

fn run(f: &Fixture, term_identity: TermIdentity) -> Outcome {
    let profile = CheckProfile {
        theory: Box::new(CompoundTheory::new(Vec::new())),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(f.extensional.iter().copied()),
            rows: f.rows.clone(),
        }),
        admit: Box::new(AlwaysAdmit),
        limits: CheckLimits {
            term_identity,
            ..CheckLimits::default()
        },
    };
    let deriv = Derivation::new(f.nodes.clone(), (f.nodes.len() - 1) as u64);
    check(&f.program, &f.claim, &deriv, &(), &profile)
}

fn x(v: Value) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert("X".into(), Term::from_value(&v));
    s
}
fn leaf(conclusion: GroundLiteral) -> Node {
    Node::Leaf {
        conclusion,
        evidence: Evidence::default(),
    }
}
fn rule(conclusion: GroundLiteral, clause: &str, subst: Subst, premises: &[usize]) -> Node {
    Node::Rule {
        conclusion,
        clause: ClauseId::new(clause),
        subst,
        premises: premises.iter().map(|&p| Premise::pos(p as u64)).collect(),
        meta: NodeMeta::default(),
    }
}

/// `twin(X) :- left(X), right(X).` over `left(.(a,[]))` and `right(right_arg)`.
fn twin(right_arg: Value) -> Fixture {
    let v = Term::var("X");
    let rows = vec![gl("left", &[cons_a()]), gl("right", &[right_arg])];
    Fixture {
        program: MapProgram::new().with(
            "twin",
            Clause::new(
                Goal::new("twin", [v.clone()]),
                [Goal::new("left", [v.clone()]), Goal::new("right", [v])],
            ),
        ),
        claim: gl("twin", &[cons_a()]),
        nodes: vec![
            leaf(rows[0].clone()),
            leaf(rows[1].clone()),
            rule(gl("twin", &[cons_a()]), "twin", x(cons_a()), &[0, 1]),
        ],
        extensional: &["left", "right"],
        rows,
    }
}

/// `copy(X) :- seen(X).` over `seen(.(a,[]))`, X = `.(a,[])`, the node concluding `node_arg` and
/// the claim `claim_arg`.
fn copy(node_arg: Value, claim_arg: Value) -> Fixture {
    let v = Term::var("X");
    let rows = vec![gl("seen", &[cons_a()])];
    Fixture {
        program: MapProgram::new().with(
            "copy",
            Clause::new(Goal::new("copy", [v.clone()]), [Goal::new("seen", [v])]),
        ),
        claim: gl("copy", &[claim_arg]),
        nodes: vec![
            leaf(rows[0].clone()),
            rule(gl("copy", &[node_arg]), "copy", x(cons_a()), &[0]),
        ],
        extensional: &["seen"],
        rows,
    }
}

/// `allowed :- seen(list(a)).` over `seen(.(a,[]))`: the conclusion shows neither spelling.
fn hidden() -> Fixture {
    let rows = vec![gl("seen", &[cons_a()])];
    Fixture {
        program: MapProgram::new().with(
            "allowed",
            Clause::new(
                Goal::new("allowed", Vec::<Term>::new()),
                [Goal::new("seen", [Term::from_value(&list_a())])],
            ),
        ),
        claim: gl("allowed", &[]),
        nodes: vec![
            leaf(rows[0].clone()),
            rule(gl("allowed", &[]), "allowed", BTreeMap::new(), &[0]),
        ],
        extensional: &["seen"],
        rows,
    }
}

/// `diag(X) :- pair(p(X, X)).` over the single fact `pair(p(.(a,[]), list(a)))`: X bound to two
/// trees inside one nested term.
fn diag() -> Fixture {
    let v = Term::var("X");
    let rows = vec![gl("pair", &[Value::tuple([atom("p"), cons_a(), list_a()])])];
    Fixture {
        program: MapProgram::new().with(
            "diag",
            Clause::new(
                Goal::new("diag", [v.clone()]),
                [Goal::new(
                    "pair",
                    [Term::tuple([Term::atom(b"p".to_vec()), v.clone(), v])],
                )],
            ),
        ),
        claim: gl("diag", &[cons_a()]),
        nodes: vec![
            leaf(rows[0].clone()),
            rule(gl("diag", &[cons_a()]), "diag", x(cons_a()), &[0]),
        ],
        extensional: &["pair"],
        rows,
    }
}

#[test]
fn every_identity_refuses_every_respelling_3022() {
    let cases = [
        ("ctl-same", twin(cons_a()), "ACCEPT"),
        ("join", twin(list_a()), "instantiation_mismatch"),
        ("head", copy(list_a(), list_a()), "instantiation_mismatch"),
        ("hidden", hidden(), "instantiation_mismatch"),
        ("diag", diag(), "instantiation_mismatch"),
        ("root", copy(cons_a(), list_a()), "root_conclusion_mismatch"),
    ];
    for (id, fixture, exact) in &cases {
        for identity in [TermIdentity::ReifyLists, TermIdentity::Exact] {
            assert_eq!(
                verdict(&run(fixture, identity)),
                *exact,
                "{id} under {}",
                identity.tag()
            );
        }
    }
}

#[test]
fn the_default_term_identity_is_reify_lists_2226() {
    assert_eq!(
        CheckLimits::default().term_identity,
        TermIdentity::ReifyLists
    );
    assert_eq!(TermIdentity::default(), TermIdentity::ReifyLists);
    assert_eq!(TermIdentity::ReifyLists.tag(), "reify_lists");
    assert_eq!(TermIdentity::Exact.tag(), "exact");
}
