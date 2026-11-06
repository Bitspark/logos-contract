//! #3022 step 4 (research 0028 A8), the negative witness `uabszqyzof` asked for on #3037: a
//! closed-model certificate's closure reads a theory-owned body literal through `theory_truth`, and
//! a theory that OWNS the predicate but decides `NotMine` is refused
//! `predicate_partition_violation`, never read as false. Both polarities are planted, each against
//! its control, a theory that decides `Fails`, which is what `NotMine` used to be read as. The same
//! four cases are pinned in contract/go (`closure_theory_not_mine_3022_test.go`) and contract/ts
//! (`test/closure_theory_not_mine_3022.test.ts`).
//!
//! - positive: `r(X) :- d(X), q(X).` over `d(a)`, `r` sealed EMPTY. Read as false, `NotMine` left
//!   the body false, so the empty table looked closed and the certificate was accepted.
//! - negated: `r(X) :- d(X).` and `r(X) :- d(X), \+ q(X).` over `d(a)`, `r` sealed `{r(a)}`. Read
//!   as false, `NotMine` made `\+ q(a)` TRUE, and the certificate was accepted.

use logos_contract::{
    check_closed_model_chain, edb_table_hash, program_digest, CertContext, CertId, CertSizeDecl,
    CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness, Evidence,
    FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Outcome,
    PredicateSet, RelationTable, StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness,
    Symbol, Term, Theory, TheoryOutcome,
};
use ontos_core::Value;
use std::collections::BTreeMap;

struct QTheory(TheoryOutcome);
// test-double: consumer(owns q and decides it with one fixed outcome)
impl Theory for QTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"q"
    }
    fn decide(&self, _atom: &GroundLiteral) -> TheoryOutcome {
        self.0.clone()
    }
}

struct DLeaves {
    extensional: PredicateSet,
}
// test-double: consumer(admits every leaf and attests d's one-row EDB snapshot)
impl LeafVerifier<()> for DLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _ctx: &()) -> Option<Hash> {
        (pred.bytes() == b"d").then(|| edb_table_hash(pred, &[lit("d")]))
    }
}

fn a() -> Value {
    Value::atom(b"a".to_vec())
}
fn lit(pred: &str) -> GroundLiteral {
    GroundLiteral::new(pred, [a()])
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}
fn x() -> Term {
    Term::var("X")
}

/// One certificate sealing `{d, r}` (`d = {d(a)}`, `r = r_rows`, with `edges`) over `program`,
/// under a theory that decides `q` with `outcome`.
fn chain(
    program: &MapProgram,
    r_rows: Vec<GroundLiteral>,
    edges: Vec<SupportEdge>,
    outcome: TheoryOutcome,
) -> Outcome {
    let pin: Hash = [7u8; 32];
    let cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("d"), sym("r")]),
        program_hash: program_digest(program),
        profile_hash: pin,
        ctx_hash: pin,
        theory_config_hash: pin,
        edb_snapshot_hashes: vec![edb_table_hash(&sym("d"), &[lit("d")])],
        domains: vec![FiniteDomain::new(sym("v"), [a()])],
        limits_decl: CertSizeDecl {
            cert_facts: 1 + r_rows.len() as u64,
            domain_values: 1,
            support_edges: edges.len() as u64,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
        extensions: vec![
            RelationTable::new("d", 1, [lit("d")]),
            RelationTable::new("r", 1, r_rows),
        ],
        supports: SupportWitness(edges),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
    };
    let profile = CheckProfile {
        theory: Box::new(QTheory(outcome)),
        leaves: Box::new(DLeaves {
            extensional: PredicateSet::from_iter(["d"]),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let context = CertContext::new(program_digest(program), pin, pin, pin);
    check_closed_model_chain(program, &[cert], &(), &profile, &context)
}

/// The positive polarity: `q(a)` filters the only clause, and `r` is sealed empty.
fn positive(outcome: TheoryOutcome) -> Outcome {
    let program = MapProgram::new().with(
        "r_q",
        Clause::new(
            Goal::new("r", [x()]),
            [Goal::new("d", [x()]), Goal::new("q", [x()])],
        ),
    );
    chain(&program, vec![], vec![], outcome)
}

/// The negated polarity: `\+ q(a)` filters the second clause, and `r(a)` is sealed, supported by
/// the first.
fn negated(outcome: TheoryOutcome) -> Outcome {
    let program = MapProgram::new()
        .with(
            "r_d",
            Clause::new(Goal::new("r", [x()]), [Goal::new("d", [x()])]),
        )
        .with(
            "r_not_q",
            Clause::with_neg(
                Goal::new("r", [x()]),
                [Goal::new("d", [x()])],
                [Goal::new("q", [x()])],
            ),
        );
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::atom(b"a".to_vec()));
    let edge = SupportEdge {
        fact: lit("r"),
        clause: ClauseId::new("r_d"),
        subst,
        body_refs: vec![SupportRef::LowerStratum {
            cert: CertId(0),
            atom: lit("d"),
        }],
        rank: 1,
    };
    chain(&program, vec![lit("r")], vec![edge], outcome)
}

fn verdict(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Accept => "accept".to_string(),
        Outcome::Reject { code, detail } => format!("{} ({detail})", code.code()),
    }
}

#[test]
fn a_closure_literal_whose_owning_theory_decides_not_mine_is_refused_in_either_polarity_3022() {
    let fails = || TheoryOutcome::Fails {
        code: "q_does_not_hold".into(),
    };
    let cases = [
        ("positive control: q decides Fails", positive(fails()), None),
        (
            "positive witness: q owned, decides NotMine",
            positive(TheoryOutcome::NotMine),
            Some("predicate_partition_violation"),
        ),
        ("negated control: q decides Fails", negated(fails()), None),
        (
            "negated witness: q owned, decides NotMine",
            negated(TheoryOutcome::NotMine),
            Some("predicate_partition_violation"),
        ),
    ];
    // Every mismatch at once, so a failure shows each case rather than the first.
    let mismatches: Vec<String> = cases
        .iter()
        .filter(|(_, outcome, want)| match (want, outcome) {
            (None, Outcome::Accept) => false,
            (Some(code), Outcome::Reject { code: got, .. }) => got.code() != *code,
            _ => true,
        })
        .map(|(name, outcome, want)| {
            format!(
                "{name}: {}, want {}",
                verdict(outcome),
                want.unwrap_or("accept")
            )
        })
        .collect();
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
