//! #2226 step 0 (seat:caa, issuecomment-5812490508): can a certificate SEAL a table row spelled
//! `list(a)` while the leaves admit `.(a,[])`? If so, the now-EXACT negation lookup (#2227) finds
//! the body literal absent and certifies a false negation under the default reading. The same
//! witnesses are pinned in contract/go and contract/ts.
//!
//! Two routes, each with an honest control:
//! - E (extensional `seen`): the cert seals `seen(list(a))`; the leaves attest `seen(.(a,[]))`.
//! - I (intensional `seen(X) :- src(X)` over extensional `src(.(a,[]))`): the cert seals
//!   `seen(list(a))` and supports it (I1) with `X = list(a)`, whose body atom `src(list(a))` the
//!   `src` table does not hold, or (I2) with `X = .(a,[])`, whose grounded head is not the row.
//!
//! Each respelled case is REFUSED, and by the first certificate step its difference reaches (the
//! honest controls pass every step): E1 by the EDB binding, `cert_edb_mismatch`; I1 and I2 by
//! support, `cert_unsupported`. So a sealed row cannot be respelled (seat:caa's source reading on
//! #2226: the certificate modules use no account equality). These pins keep it that way.

use logos_contract::{
    check_with_cert_context, edb_table_hash, program_digest, CertContext, CertId, CertSizeDecl,
    CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness, Derivation,
    Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Node,
    NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise, RelationTable, StratumPrefix, Subst,
    SupportEdge, SupportRef, SupportWitness, Symbol, Term,
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
fn lit(pred: &str, v: Value) -> GroundLiteral {
    GroundLiteral::new(pred, [v])
}
fn subst_x(v: Value) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert("X".into(), Term::from_value(&v));
    s
}

/// Admits exactly the EDB-of-record and attests its snapshot per extensional predicate.
struct Leaves {
    extensional: PredicateSet,
    edb: Vec<GroundLiteral>,
}
// test-double: consumer(a fixed EDB: admits exactly its rows and attests an EDB snapshot)
impl LeafVerifier<()> for Leaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, atom: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        if self.edb.contains(atom) {
            LeafOutcome::Admit
        } else {
            LeafOutcome::Reject {
                code: "not_admitted".into(),
            }
        }
    }
    fn edb_snapshot(&self, pred: &Symbol, _: &()) -> Option<Hash> {
        let rows: Vec<GroundLiteral> = self
            .edb
            .iter()
            .filter(|row| &row.pred == pred)
            .cloned()
            .collect();
        self.extensional
            .contains(pred)
            .then(|| edb_table_hash(pred, &rows))
    }
}

fn verdict(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Accept => "ACCEPT",
        Outcome::Reject { code, .. } => code.code(),
    }
}

/// `r :- \+ seen(.(a,[]))` plus `extra` clauses, checked with a Neg premise `seen(.(a,[]))`
/// (EXACTLY the body literal, so #2227's rule passes) against `cert`.
fn check_negation(
    extra: &[(&str, Clause)],
    extensional: &[&str],
    edb: Vec<GroundLiteral>,
    mut cert: ClosedModelCert,
) -> Outcome {
    let mut program = MapProgram::new().with(
        "r_rule",
        Clause::with_neg(
            Goal::new("r", Vec::<Term>::new()),
            Vec::<Goal>::new(),
            [Goal::new("seen", [Term::from_value(&cons_a())])],
        ),
    );
    for (id, clause) in extra {
        program = program.with(*id, clause.clone());
    }
    let pin: Hash = [1u8; 32];
    cert.program_hash = program_digest(&program);
    cert.profile_hash = pin;
    cert.ctx_hash = pin;
    cert.theory_config_hash = pin;
    let claim = GroundLiteral::new("r", Vec::<Value>::new());
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: claim.clone(),
            clause: ClauseId::new("r_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: lit("seen", cons_a()),
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
            extensional: PredicateSet::from_iter(extensional.iter().copied()),
            edb,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let context = CertContext::new(program_digest(&program), pin, pin, pin);
    check_with_cert_context(&program, &claim, &deriv, &(), &profile, &context)
}

fn cert(
    level: u32,
    tables: Vec<RelationTable>,
    edb_hashes: Vec<Hash>,
    supports: Vec<SupportEdge>,
) -> ClosedModelCert {
    let facts: usize = tables.iter().map(|t| t.rows.len()).sum();
    let edges = supports.len();
    ClosedModelCert {
        scope: StratumPrefix::new(level, tables.iter().map(|t| t.pred.clone())),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: edb_hashes,
        domains: vec![FiniteDomain::new(sym("v"), [cons_a(), list_a()])],
        extensions: tables,
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: facts as u64,
            domain_values: 2,
            support_edges: edges as u64,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    }
}

/// Route E: `seen` is extensional, and the leaves attest `seen(.(a,[]))`.
fn route_e(sealed: Value) -> Outcome {
    let row = lit("seen", sealed);
    let table = RelationTable::new("seen", 1, [row.clone()]);
    let hash = edb_table_hash(&sym("seen"), &[row]);
    check_negation(
        &[],
        &["seen"],
        vec![lit("seen", cons_a())],
        cert(0, vec![table], vec![hash], vec![]),
    )
}

#[test]
fn an_extensional_row_cannot_be_sealed_in_another_spelling_2226() {
    // Control: the honest table holds the body literal, so the negation is refused as present.
    assert_eq!(verdict(&route_e(cons_a())), "neg_atom_present");
    // E1: the sealed row is spelled `list(a)` while the leaves attest `.(a,[])`.
    assert_eq!(verdict(&route_e(list_a())), "cert_edb_mismatch", "E1");
}

/// Route I: `seen(X) :- src(X)` over extensional `src(.(a,[]))`; the cert seals `seen` with
/// `row`, supported with `X = support_x` and a body ref `src(support_x)`.
fn route_i(row: Value, support_x: Value) -> Outcome {
    let seen_clause = Clause::new(
        Goal::new("seen", [Term::var("X")]),
        [Goal::new("src", [Term::var("X")])],
    );
    let src_row = lit("src", cons_a());
    let src_table = RelationTable::new("src", 1, [src_row.clone()]);
    let seen_table = RelationTable::new("seen", 1, [lit("seen", row.clone())]);
    let edge = SupportEdge {
        fact: lit("seen", row),
        clause: ClauseId::new("seen_rule"),
        subst: subst_x(support_x.clone()),
        body_refs: vec![SupportRef::LowerStratum {
            cert: CertId(0),
            atom: lit("src", support_x),
        }],
        rank: 1,
    };
    check_negation(
        &[("seen_rule", seen_clause)],
        &["src"],
        vec![src_row.clone()],
        cert(
            1,
            vec![src_table, seen_table],
            vec![edb_table_hash(&sym("src"), &[src_row])],
            vec![edge],
        ),
    )
}

#[test]
fn an_intensional_row_cannot_be_sealed_in_another_spelling_2226() {
    // Control: the honest seal, supported by `X = .(a,[])`, holds the body literal.
    assert_eq!(verdict(&route_i(cons_a(), cons_a())), "neg_atom_present");
    // I1: the row and its support are both spelled `list(a)`.
    assert_eq!(
        verdict(&route_i(list_a(), list_a())),
        "cert_unsupported",
        "I1"
    );
    // I2: the row is `list(a)`, but its support grounds the head as `seen(.(a,[]))`.
    assert_eq!(
        verdict(&route_i(list_a(), cons_a())),
        "cert_unsupported",
        "I2"
    );
}
