//! #2232 / #2227: the premise-match discipline at the two SPELLING-SENSITIVE premise sites (ruled by
//! seat:caa, issuecomment-5811831064). A positive premise that cites a Builtin node, and a Neg
//! premise's atom, must EXACTLY equal the grounded body literal. Rule and Leaf premises keep #277's
//! account equality. The same inputs are pinned in contract/go and contract/ts.

use logos_contract::{
    check, check_with_cert_context, edb_table_hash, program_digest, standard_theory, CertContext,
    CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert,
    ClosureWitness, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome,
    LeafVerifier, MapProgram, Node, NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise,
    RelationTable, StratumPrefix, Subst, SupportWitness, Symbol, Term, Verdict,
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
/// `list(a)`: the list `[a]`, reified form.
fn list_a() -> Value {
    Value::tuple([atom("list"), atom("a")])
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
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

fn profile(extensional: &[&str], rows: Vec<GroundLiteral>) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(standard_theory()),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(extensional.iter().copied()),
            rows,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn verdict(outcome: &Outcome) -> &'static str {
    match &outcome.verdict {
        Verdict::Accept => "ACCEPT",
        Verdict::Reject { code, .. } => code.code(),
    }
}

fn subst(pairs: &[(&str, Value)]) -> Subst {
    let mut s: Subst = BTreeMap::new();
    for (var, value) in pairs {
        s.insert((*var).into(), Term::from_value(value));
    }
    s
}

/// `self_neq(.(a,[]))` from `self_neq(X) :- cand(X), X \== X.`, citing the Builtin node
/// `\==(.(a,[]), second)`.
fn self_neq(second: Value) -> Outcome {
    let cand = GroundLiteral::new("cand", [cons_a()]);
    let x = Term::var("X");
    let program = MapProgram::new().with(
        "self_neq",
        Clause::new(
            Goal::new("self_neq", [x.clone()]),
            [
                Goal::new("cand", [x.clone()]),
                Goal::new("\\==", [x.clone(), x]),
            ],
        ),
    );
    let claim = GroundLiteral::new("self_neq", [cons_a()]);
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: cand.clone(),
                evidence: Evidence::default(),
            },
            Node::Builtin {
                conclusion: GroundLiteral::new("\\==", [cons_a(), second]),
            },
            Node::Rule {
                conclusion: claim.clone(),
                clause: ClauseId::new("self_neq"),
                subst: subst(&[("X", cons_a())]),
                premises: vec![Premise::pos(0), Premise::pos(1)],
                meta: NodeMeta::default(),
            },
        ],
        2,
    );
    check(
        &program,
        &claim,
        &deriv,
        &(),
        &profile(&["cand"], vec![cand]),
    )
}

/// A Builtin node's truth is the term theory's decision on ITS OWN spelling, so it transfers only
/// to that exact spelling.
#[test]
fn a_builtin_cited_premise_matches_exactly_2232() {
    // A, the control: the honest node is decided false by the theory.
    assert_eq!(verdict(&self_neq(cons_a())), "builtin_failed");
    // B: the node is respelled `list(a)`, true in the theory, cited for `.(a,[]) \== .(a,[])`.
    assert_eq!(verdict(&self_neq(list_a())), "instantiation_mismatch");

    // `lst(X) :- seen(X), is_list(X).` over seen(list(a)), citing is_list(.(a,[])).
    let x = Term::var("X");
    let seen = GroundLiteral::new("seen", [list_a()]);
    let lst_program = MapProgram::new().with(
        "lst",
        Clause::new(
            Goal::new("lst", [x.clone()]),
            [
                Goal::new("seen", [x.clone()]),
                Goal::new("is_list", [x.clone()]),
            ],
        ),
    );
    let lst_claim = GroundLiteral::new("lst", [list_a()]);
    let lst = Derivation::new(
        [
            Node::Leaf {
                conclusion: seen.clone(),
                evidence: Evidence::default(),
            },
            Node::Builtin {
                conclusion: GroundLiteral::new("is_list", [cons_a()]),
            },
            Node::Rule {
                conclusion: lst_claim.clone(),
                clause: ClauseId::new("lst"),
                subst: subst(&[("X", list_a())]),
                premises: vec![Premise::pos(0), Premise::pos(1)],
                meta: NodeMeta::default(),
            },
        ],
        2,
    );
    let got = check(
        &lst_program,
        &lst_claim,
        &lst,
        &(),
        &profile(&["seen"], vec![seen]),
    );
    assert_eq!(verdict(&got), "instantiation_mismatch", "is_list respelled");

    // `same(X,Y) :- l(X), r(Y), X == Y.` over l(.(a,[])), r(list(a)), citing ==(.(a,[]), .(a,[])).
    let y = Term::var("Y");
    let l = GroundLiteral::new("l", [cons_a()]);
    let r = GroundLiteral::new("r", [list_a()]);
    let same_program = MapProgram::new().with(
        "same",
        Clause::new(
            Goal::new("same", [x.clone(), y.clone()]),
            [
                Goal::new("l", [x.clone()]),
                Goal::new("r", [y.clone()]),
                Goal::new("==", [x, y]),
            ],
        ),
    );
    let same_claim = GroundLiteral::new("same", [cons_a(), list_a()]);
    let same = Derivation::new(
        [
            Node::Leaf {
                conclusion: l.clone(),
                evidence: Evidence::default(),
            },
            Node::Leaf {
                conclusion: r.clone(),
                evidence: Evidence::default(),
            },
            Node::Builtin {
                conclusion: GroundLiteral::new("==", [cons_a(), cons_a()]),
            },
            Node::Rule {
                conclusion: same_claim.clone(),
                clause: ClauseId::new("same"),
                subst: subst(&[("X", cons_a()), ("Y", list_a())]),
                premises: vec![Premise::pos(0), Premise::pos(1), Premise::pos(2)],
                meta: NodeMeta::default(),
            },
        ],
        3,
    );
    let got = check(
        &same_program,
        &same_claim,
        &same,
        &(),
        &profile(&["l", "r"], vec![l, r]),
    );
    assert_eq!(verdict(&got), "instantiation_mismatch", "== respelled");
}

/// `r :- \+ seen(body).` with a Neg premise atom `seen(premise)`, against a certificate that seals
/// `seen` with exactly `sealed` and the finite domain `domain`.
fn negation(body: Value, sealed: &[Value], premise: Value, domain: &[Value]) -> Outcome {
    let rows: Vec<GroundLiteral> = sealed
        .iter()
        .map(|value| GroundLiteral::new("seen", [value.clone()]))
        .collect();
    let program = MapProgram::new().with(
        "r",
        Clause::with_neg(
            Goal::new("r", Vec::<Term>::new()),
            Vec::<Goal>::new(),
            [Goal::new("seen", [Term::from_value(&body)])],
        ),
    );
    let claim = GroundLiteral::new("r", Vec::<Value>::new());
    let pin: Hash = [1u8; 32];
    let cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("seen")]),
        program_hash: program_digest(&program),
        profile_hash: pin,
        ctx_hash: pin,
        theory_config_hash: pin,
        edb_snapshot_hashes: vec![edb_table_hash(&sym("seen"), &rows)],
        domains: vec![FiniteDomain::new(sym("v"), domain.iter().cloned())],
        extensions: vec![RelationTable::new("seen", 1, rows.clone())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: rows.len() as u64,
            domain_values: domain.len() as u64,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: claim.clone(),
            clause: ClauseId::new("r"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: GroundLiteral::new("seen", [premise]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::default(),
        }],
        0,
        [cert],
    );
    let profile = CheckProfile {
        theory: Box::new(logos_contract::CompoundTheory::new(Vec::new())),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(["seen"]),
            rows,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let context = CertContext::new(program_digest(&program), pin, pin, pin);
    check_with_cert_context(&program, &claim, &deriv, &(), &profile, &context)
}

/// Absence is looked up by exact membership, so the Neg premise atom must be the exact grounded
/// body literal.
#[test]
fn a_neg_premise_atom_matches_exactly_2227() {
    let b = atom("b");
    let cases = [
        (
            "A honest negation (control)",
            negation(cons_a(), &[atom("b")], cons_a(), &[cons_a(), b]),
            "ACCEPT",
        ),
        (
            "B present, exact spelling (control)",
            negation(cons_a(), &[cons_a()], cons_a(), &[cons_a()]),
            "neg_atom_present",
        ),
        (
            "C present, premise respelled list(a)",
            negation(cons_a(), &[cons_a()], list_a(), &[cons_a(), list_a()]),
            "instantiation_mismatch",
        ),
        (
            "D reverse spelling",
            negation(list_a(), &[list_a()], cons_a(), &[list_a(), cons_a()]),
            "instantiation_mismatch",
        ),
    ];
    for (name, got, want) in cases {
        assert_eq!(verdict(&got), want, "{name}");
    }
}
