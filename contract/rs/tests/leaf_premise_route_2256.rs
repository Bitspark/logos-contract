//! #2256: the exact cone (ruled by seat:caa, issuecomment-5813063113). After #2242 a Leaf- or
//! Rule-cited positive premise still matches by account equality, so the substitution can carry
//! the other list spelling into a spelling-sensitive judgment of the same rule instance, or of a
//! higher one through a derived fact. A rule instance whose clause is spelling-sensitive (a Neg
//! literal, a count literal, or any builtin literal) must be exact-grounded: every positive premise
//! equals its cited node's underlying exact fact (a Rule node's instantiated head, not its
//! conclusion label), and every cited node is exact-grounded. #3022 (seat:caa's ruling) then made
//! every certified literal claim exact: every comparison site is structural for every clause, so the
//! exact cone holds by construction, and the positive-only rows #2256 left on #277's account
//! equality are refused too. The same inputs are pinned in contract/go and contract/ts.

use logos_contract::{
    check, check_with_cert_context, edb_table_hash, intval::BigInt, program_digest,
    standard_theory, BodyLit, CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause,
    ClauseId, ClosedModelCert, ClosureWitness, CountLit, Derivation, Evidence, FiniteDomain, Goal,
    GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, NonMemberProof,
    Outcome, PredicateRef, PredicateSet, Premise, ProjectSpec, RelationTable, StratumPrefix, Subst,
    SupportWitness, Symbol, Term, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
/// `list(a)`.
fn list_a() -> Value {
    Value::tuple([atom("list"), atom("a")])
}
/// `.(a, [])`, the same list.
fn cons_a() -> Value {
    Value::tuple([atom("."), atom("a"), atom("[]")])
}
/// `list(x)`.
fn list_x() -> Value {
    Value::tuple([atom("list"), atom("x")])
}
/// `.(x, [])`, the same list.
fn cons_x() -> Value {
    Value::tuple([atom("."), atom("x"), atom("[]")])
}
fn int_v(n: i128) -> Value {
    BigInt::from_i128(n)
        .to_int_term()
        .erase_ground()
        .expect("ground int")
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
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

fn leaf(conclusion: GroundLiteral) -> Node {
    Node::Leaf {
        conclusion,
        evidence: Evidence::default(),
    }
}

fn rule(conclusion: GroundLiteral, clause: &str, subst: Subst, premises: Vec<Premise>) -> Node {
    Node::Rule {
        conclusion,
        clause: ClauseId::new(clause),
        subst,
        premises,
        meta: NodeMeta::default(),
    }
}

fn neg(atom: GroundLiteral) -> Premise {
    Premise::Neg {
        atom,
        cert: CertId(0),
        nonmember: NonMemberProof::DirectLookup,
    }
}

/// Checks `claim` under leaves that admit exactly `rows`. With a domain, the derivation carries
/// one certificate sealing `member` exactly as `rows` hold it, with that finite domain.
fn run(
    program: &MapProgram,
    claim: &GroundLiteral,
    nodes: Vec<Node>,
    root: usize,
    ext: &[&str],
    rows: Vec<GroundLiteral>,
    domain: Option<&[Value]>,
) -> Outcome {
    let sealed: Vec<GroundLiteral> = rows
        .iter()
        .filter(|row| row.pred == sym("member"))
        .cloned()
        .collect();
    let profile = CheckProfile {
        theory: Box::new(standard_theory()),
        leaves: Box::new(Leaves {
            extensional: PredicateSet::from_iter(ext.iter().copied()),
            rows,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let Some(domain) = domain else {
        return check(
            program,
            claim,
            &Derivation::new(nodes, root as u64),
            &(),
            &profile,
        );
    };
    let pin: Hash = [1u8; 32];
    let cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("member")]),
        program_hash: program_digest(program),
        profile_hash: pin,
        ctx_hash: pin,
        theory_config_hash: pin,
        edb_snapshot_hashes: vec![edb_table_hash(&sym("member"), &sealed)],
        domains: vec![FiniteDomain::new(sym("v"), domain.iter().cloned())],
        extensions: vec![RelationTable::new("member", 1, sealed.clone())],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: sealed.len() as u64,
            domain_values: domain.len() as u64,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    let deriv = Derivation::with_closed_world(nodes, root as u64, [cert]);
    let context = CertContext::new(program_digest(program), pin, pin, pin);
    check_with_cert_context(program, claim, &deriv, &(), &profile, &context)
}

/// `unlisted :- name(X), \+ member(X).` over name(name_row), member(list(a)), X bound to `x`, the
/// Neg atom member(neg_arg).
fn n(name_row: Value, x: Value, neg_arg: Value, domain: &[Value]) -> Outcome {
    let var = Term::var("X");
    let program = MapProgram::new().with(
        "unlisted",
        Clause::with_neg(
            Goal::new("unlisted", Vec::<Term>::new()),
            [Goal::new("name", [var.clone()])],
            [Goal::new("member", [var])],
        ),
    );
    let rows = vec![gl("name", &[name_row]), gl("member", &[list_a()])];
    let nodes = vec![
        leaf(rows[0].clone()),
        rule(
            gl("unlisted", &[]),
            "unlisted",
            subst(&[("X", x)]),
            vec![Premise::pos(0), neg(gl("member", &[neg_arg]))],
        ),
    ];
    run(
        &program,
        &gl("unlisted", &[]),
        nodes,
        1,
        &["name", "member"],
        rows,
        Some(domain),
    )
}

/// `conflict :- dep(R1), rev(R2), R1 \== R2.` over dep(list(x)), rev(rev_row), R1 = list(x), R2
/// bound to `r2`, the builtin node `\==(list(x), ne_arg)`.
fn r(rev_row: Value, r2: Value, ne_arg: Value) -> Outcome {
    let (r1v, r2v) = (Term::var("R1"), Term::var("R2"));
    let program = MapProgram::new().with(
        "conflict",
        Clause::new(
            Goal::new("conflict", Vec::<Term>::new()),
            [
                Goal::new("dep", [r1v.clone()]),
                Goal::new("rev", [r2v.clone()]),
                Goal::new("\\==", [r1v, r2v]),
            ],
        ),
    );
    let rows = vec![gl("dep", &[list_x()]), gl("rev", &[rev_row])];
    let nodes = vec![
        leaf(rows[0].clone()),
        leaf(rows[1].clone()),
        Node::Builtin {
            conclusion: gl("\\==", &[list_x(), ne_arg]),
        },
        rule(
            gl("conflict", &[]),
            "conflict",
            subst(&[("R1", list_x()), ("R2", r2)]),
            vec![Premise::pos(0), Premise::pos(1), Premise::pos(2)],
        ),
    ];
    run(
        &program,
        &gl("conflict", &[]),
        nodes,
        3,
        &["dep", "rev"],
        rows,
        None,
    )
}

/// `name2(X) :- name(X).` then `unlisted :- name2(X), \+ member(X).` over name(list(a)),
/// member(list(a)), X bound to `x` in both. With `whole` false only the positive-only intermediate
/// is checked, as the root, with no certificate.
fn launder(x: Value, whole: bool) -> Outcome {
    let var = Term::var("X");
    let program = MapProgram::new()
        .with(
            "name2",
            Clause::new(
                Goal::new("name2", [var.clone()]),
                [Goal::new("name", [var.clone()])],
            ),
        )
        .with(
            "unlisted",
            Clause::with_neg(
                Goal::new("unlisted", Vec::<Term>::new()),
                [Goal::new("name2", [var.clone()])],
                [Goal::new("member", [var])],
            ),
        );
    let rows = vec![gl("name", &[list_a()]), gl("member", &[list_a()])];
    let name2 = gl("name2", std::slice::from_ref(&x));
    let mut nodes = vec![
        leaf(rows[0].clone()),
        rule(
            name2.clone(),
            "name2",
            subst(&[("X", x.clone())]),
            vec![Premise::pos(0)],
        ),
    ];
    let ext = ["name", "member"];
    if !whole {
        return run(&program, &name2, nodes, 1, &ext, rows, None);
    }
    nodes.push(rule(
        gl("unlisted", &[]),
        "unlisted",
        subst(&[("X", x.clone())]),
        vec![Premise::pos(1), neg(gl("member", &[x]))],
    ));
    run(
        &program,
        &gl("unlisted", &[]),
        nodes,
        2,
        &ext,
        rows,
        Some(&[list_a(), cons_a()]),
    )
}

/// `n(N) :- name(X), count(member where arg0 = X) = N.` over name(list(a)), member(list(a)), X
/// bound to `x`, the premise claiming `k` rows.
fn count(x: Value, k: i128) -> Outcome {
    let (var, n) = (Term::var("X"), Term::var("N"));
    let program = MapProgram::new().with(
        "n",
        Clause {
            head: Goal::new("n", [n.clone()]),
            body: vec![
                BodyLit::Pos(Goal::new("name", [var.clone()])),
                BodyLit::Count(CountLit {
                    pred: PredicateRef::new("member", 1),
                    filter: vec![(0, var)],
                    project: ProjectSpec::Rows,
                    count: n,
                }),
            ],
        },
    );
    let rows = vec![gl("name", &[list_a()]), gl("member", &[list_a()])];
    let claim = gl("n", &[int_v(k)]);
    let nodes = vec![
        leaf(rows[0].clone()),
        rule(
            claim.clone(),
            "n",
            subst(&[("X", x.clone()), ("N", int_v(k))]),
            vec![
                Premise::pos(0),
                Premise::Count {
                    pred: PredicateRef::new("member", 1),
                    filter: vec![(0, x)],
                    project: ProjectSpec::Rows,
                    k: int_v(k),
                    cert: CertId(0),
                },
            ],
        ),
    ];
    run(
        &program,
        &claim,
        nodes,
        1,
        &["name", "member"],
        rows,
        Some(&[list_a(), cons_a()]),
    )
}

/// #2226's positive-only rows, refused since #3022.
fn join() -> Outcome {
    let var = Term::var("X");
    let program = MapProgram::new().with(
        "twin",
        Clause::new(
            Goal::new("twin", [var.clone()]),
            [Goal::new("left", [var.clone()]), Goal::new("right", [var])],
        ),
    );
    let rows = vec![gl("left", &[cons_a()]), gl("right", &[list_a()])];
    let claim = gl("twin", &[cons_a()]);
    let nodes = vec![
        leaf(rows[0].clone()),
        leaf(rows[1].clone()),
        rule(
            claim.clone(),
            "twin",
            subst(&[("X", cons_a())]),
            vec![Premise::pos(0), Premise::pos(1)],
        ),
    ];
    run(&program, &claim, nodes, 2, &["left", "right"], rows, None)
}

fn hidden() -> Outcome {
    let program = MapProgram::new().with(
        "allowed",
        Clause::new(
            Goal::new("allowed", Vec::<Term>::new()),
            [Goal::new("seen", [Term::from_value(&list_a())])],
        ),
    );
    let rows = vec![gl("seen", &[cons_a()])];
    let nodes = vec![
        leaf(rows[0].clone()),
        rule(
            gl("allowed", &[]),
            "allowed",
            BTreeMap::new(),
            vec![Premise::pos(0)],
        ),
    ];
    run(
        &program,
        &gl("allowed", &[]),
        nodes,
        1,
        &["seen"],
        rows,
        None,
    )
}

#[test]
fn a_spelling_sensitive_rule_instance_is_exact_grounded_2256() {
    let (a, c) = (list_a(), cons_a());
    let cases = [
        // Rejected: a respelled binding reaches a spelling-sensitive judgment.
        (
            "N1 X = .(a,[]) via leaf name(list(a)), Neg member(.(a,[]))",
            n(a.clone(), c.clone(), c.clone(), &[a.clone(), c.clone()]),
            "instantiation_mismatch",
        ),
        (
            "R1 R2 = .(x,[]) via leaf rev(list(x)), \\==(list(x), .(x,[]))",
            r(list_x(), cons_x(), cons_x()),
            "instantiation_mismatch",
        ),
        (
            "L laundered through the positive-only name2",
            launder(c.clone(), true),
            "instantiation_mismatch",
        ),
        (
            "C count over a respelled X",
            count(c.clone(), 0),
            "instantiation_mismatch",
        ),
        // Rejected since #3022: a positive-only rule's respelled premise is no longer
        // account-equal.
        (
            "L's positive-only intermediate alone",
            launder(c.clone(), false),
            "instantiation_mismatch",
        ),
        ("#2226 join", join(), "instantiation_mismatch"),
        ("#2226 hidden", hidden(), "instantiation_mismatch"),
        // Unchanged.
        (
            "N0 exact spelling, present",
            n(a.clone(), a.clone(), a.clone(), std::slice::from_ref(&a)),
            "neg_atom_present",
        ),
        (
            "N3 #2227's form, Neg atom respelled",
            n(a.clone(), a.clone(), c.clone(), &[a.clone(), c.clone()]),
            "instantiation_mismatch",
        ),
        (
            "R0 exact spelling, \\== fails",
            r(list_x(), list_x(), list_x()),
            "builtin_failed",
        ),
        (
            "R2 #2232's form, builtin node respelled",
            r(list_x(), list_x(), cons_x()),
            "instantiation_mismatch",
        ),
        // Stay accepted: the rule does not reach them.
        (
            "N4 mixed EDB, honest exact binding",
            n(c.clone(), c.clone(), c.clone(), &[a.clone(), c.clone()]),
            "ACCEPT",
        ),
        (
            "R3 mixed EDB, honest exact binding",
            r(cons_x(), cons_x(), cons_x()),
            "ACCEPT",
        ),
        (
            "L's positive-only intermediate, honest exact binding",
            launder(a.clone(), false),
            "ACCEPT",
        ),
        ("C honest count", count(a, 1), "ACCEPT"),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter(|(_, got, want)| verdict(got) != *want)
        .map(|(name, got, want)| format!("{name}: {}, want {want}", verdict(got)))
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}
