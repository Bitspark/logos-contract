//! #3123: an arithmetic expression's depth is never a decided false. Until #3123 each core's
//! evaluator recursed once per level and stopped at 256 levels, and the stop was read as
//! `Fails`, so `not(1 =:= E)` with `E` 257 levels deep could be answered and certified. The walk
//! is iterative now, so a deep expression evaluates; the only depth limit left is the caller's
//! `CheckLimits::max_term_depth`, a completed policy decision `check` makes before any theory.
//!
//! Every witness is placed against `OLD_ARITH_DEPTH_CAP` and carries a control inside it. The same
//! cases are pinned in contract/go (`arithmetic_depth_3123_test.go`) and contract/ts
//! (`test/arithmetic_depth_3123.test.ts`).

use logos_contract::{
    check, check_closed_model_chain, edb_table_hash, intval::BigInt, program_digest,
    ArithmeticTheory, CertContext, CertSizeDecl, CheckLimits, CheckProfile, Clause,
    ClosedModelCert, ClosureWitness, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash,
    LeafOutcome, LeafVerifier, MapProgram, Node, Outcome, PredicateSet, RelationTable,
    StratumPrefix, SupportWitness, Symbol, Term, Theory, TheoryGround, Verdict,
};
use ontos_core::Value;

/// The depth at which the recursive evaluator stopped until #3123: an expression whose innermost
/// operand sits one level past it was read as `Fails`.
const OLD_ARITH_DEPTH_CAP: usize = 256;

/// The depths every witness runs at: a control inside the old cap, and two past it.
const DEPTHS: [(&str, usize); 3] = [
    ("control, inside the old cap", OLD_ARITH_DEPTH_CAP - 56),
    ("one past the old cap", OLD_ARITH_DEPTH_CAP + 1),
    ("well past the old cap", OLD_ARITH_DEPTH_CAP + 50),
];

fn int_t(n: i128) -> Term {
    BigInt::from_i128(n).to_int_term()
}

fn int_v(n: i128) -> Value {
    int_t(n).erase_ground().expect("ground int")
}

/// `'+'('+'(… int(1) …, int(0)), int(0))`: `levels` operators over `int(1)`, value 1. Built in a
/// loop; `Term`'s drop is iterative.
fn deep_one_t(levels: usize) -> Term {
    let mut e = int_t(1);
    for _ in 0..levels {
        e = Term::tuple(vec![Term::atom(b"+".to_vec()), e, int_t(0)]);
    }
    e
}

/// [`deep_one_t`] as a ground value, built in a loop.
fn deep_one_v(levels: usize) -> Value {
    let mut e = int_v(1);
    for _ in 0..levels {
        e = Value::tuple(vec![Value::atom(b"+".to_vec()), e, int_v(0)]);
    }
    e
}

fn decide_ground(pred: &str, lhs: Value, rhs: Value) -> TheoryGround {
    ArithmeticTheory::new().decide_ground(&GroundLiteral::new(pred, [lhs, rhs]))
}

fn holds(outcome: &TheoryGround) -> bool {
    *outcome == TheoryGround::holds()
}

/// The theory decides a deep expression by its value, in both polarities.
#[test]
fn the_theory_decides_a_deep_expression_by_its_value_3123() {
    let mut wrong = Vec::new();
    for (name, levels) in DEPTHS {
        let cases = [
            (
                "1 =:= E holds",
                decide_ground("=:=", int_v(1), deep_one_v(levels)),
                true,
            ),
            (
                "2 =\\= E holds",
                decide_ground("=\\=", int_v(2), deep_one_v(levels)),
                true,
            ),
            (
                "1 =\\= E fails",
                decide_ground("=\\=", int_v(1), deep_one_v(levels)),
                false,
            ),
            (
                "1 is E holds",
                decide_ground("is", int_v(1), deep_one_v(levels)),
                true,
            ),
            (
                "0 < E holds",
                decide_ground("<", int_v(0), deep_one_v(levels)),
                true,
            ),
        ];
        for (what, got, want) in cases {
            if holds(&got) != want {
                wrong.push(format!("{name}: {what}, got {got:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Stack safety: 100,000 levels, decided on a thread whose stack is far too small for one native
/// frame per level. A recursive walk overflows here; the iterative one does not.
#[test]
fn a_hundred_thousand_level_expression_is_decided_on_a_small_stack_3123() {
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let atom = GroundLiteral::new("=:=", [int_v(1), deep_one_v(100_000)]);
            let got = ArithmeticTheory::new().decide_ground(&atom);
            // `ontos_core::Value`'s drop recurses once per level, so the 100,000-level value is
            // leaked rather than dropped on this small stack. The evaluation is what is measured.
            std::mem::forget(atom);
            assert!(holds(&got), "1 =:= E must hold, got {got:?}");
        })
        .expect("spawn the small-stack thread")
        .join()
        .expect("the decision must not overflow a 512 KiB stack");
}

// ------------------------------------------------------------------------------------------
// Through `check`: the theory is reached only under the caller's depth budget.

/// A leaf verifier with an empty extensional set: the Builtin-node checks cite no leaf.
struct NoLeaves {
    extensional: PredicateSet,
}
// test-double: consumer(an empty extensional set; admits nothing because nothing is a leaf)
impl LeafVerifier<()> for NoLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Reject {
            code: "no_leaves".into(),
        }
    }
}

fn arith_profile(limits: CheckLimits) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(ArithmeticTheory::new()),
        leaves: Box::new(NoLeaves {
            extensional: PredicateSet::new(),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    }
}

fn verdict(outcome: &Outcome) -> String {
    match &outcome.verdict {
        Verdict::Accept => "accept".to_string(),
        Verdict::Reject { code, detail } => format!("{} ({detail})", code.code()),
    }
}

/// Check one `Builtin` node concluding `pred(lhs, E)` under `limits`.
fn check_builtin(pred: &str, lhs: i128, levels: usize, limits: CheckLimits) -> Outcome {
    let claim = GroundLiteral::new(pred, [int_v(lhs), deep_one_v(levels)]);
    let deriv = Derivation::new(
        [Node::Builtin {
            conclusion: claim.clone(),
        }],
        0,
    );
    check(
        &MapProgram::new(),
        &claim,
        &deriv,
        &(),
        &arith_profile(limits),
    )
}

/// A `Builtin` node past the old cap is either accepted by its value (the caller's budget covers
/// it) or refused `term_too_deep` by that budget. Never `builtin_failed` for a relation that holds.
#[test]
fn a_deep_builtin_node_is_decided_by_value_or_refused_by_the_callers_budget_3123() {
    let wide = CheckLimits {
        max_term_depth: 1_024,
        ..CheckLimits::default()
    };
    let mut wrong = Vec::new();
    for (name, levels) in DEPTHS {
        // Term depth is the operator levels plus 2 (the int leaf is `int(Atom)`).
        let within_default = levels + 2 <= CheckLimits::default().max_term_depth;
        let cases = [
            (
                "=:=(1, E), default budget",
                check_builtin("=:=", 1, levels, CheckLimits::default()),
                if within_default {
                    None
                } else {
                    Some("term_too_deep")
                },
            ),
            (
                "=:=(1, E), a budget that covers it",
                check_builtin("=:=", 1, levels, wide),
                None,
            ),
            (
                "=\\=(2, E), a budget that covers it",
                check_builtin("=\\=", 2, levels, wide),
                None,
            ),
            // The relation is false, decided by a completed evaluation.
            (
                "=\\=(1, E), a budget that covers it",
                check_builtin("=\\=", 1, levels, wide),
                Some("builtin_failed"),
            ),
        ];
        for (what, got, want) in cases {
            let ok = match (want, &got.verdict) {
                (None, Verdict::Accept) => true,
                (Some(code), Verdict::Reject { code: c, .. }) => c.code() == code,
                _ => false,
            };
            if !ok {
                wrong.push(format!(
                    "{name}: {what}: {}, want {}",
                    verdict(&got),
                    want.unwrap_or("accept")
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

// ------------------------------------------------------------------------------------------
// The certified form: a closed-model certificate's closure reads the comparison through
// `theory_truth`. Sealing `r` EMPTY claims `r(a)` is false; a closure that reads a capacity as
// false accepts that claim, and every negation citing the certificate inherits it.

/// The leaf verifier of the certified form: `d` is the one extensional table.
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
        (pred.bytes() == b"d").then(|| edb_table_hash(pred, &[d_a()]))
    }
}

fn d_a() -> GroundLiteral {
    GroundLiteral::new("d", [Value::atom(b"a".to_vec())])
}

fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

/// One certificate sealing `{d, r}`, with `d = {d(a)}` and `r` EMPTY, over `program`, under the
/// standard arithmetic theory and `limits`.
fn r_sealed_empty(program: &MapProgram, limits: CheckLimits) -> Outcome {
    let pin: Hash = [7u8; 32];
    let cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("d"), sym("r")]),
        program_hash: program_digest(program),
        profile_hash: pin,
        ctx_hash: pin,
        theory_config_hash: pin,
        edb_snapshot_hashes: vec![edb_table_hash(&sym("d"), &[d_a()])],
        domains: vec![FiniteDomain::new(sym("v"), [Value::atom(b"a".to_vec())])],
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 1,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
        extensions: vec![
            RelationTable::new("d", 1, [d_a()]),
            RelationTable::new("r", 1, Vec::<GroundLiteral>::new()),
        ],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
    };
    let profile = CheckProfile {
        theory: Box::new(ArithmeticTheory::new()),
        leaves: Box::new(DLeaves {
            extensional: PredicateSet::from_iter(["d"]),
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    };
    let context = CertContext::new(program_digest(program), pin, pin, pin);
    check_closed_model_chain(program, &[cert], &(), &profile, &context)
}

fn x() -> Term {
    Term::var("X")
}

/// `r(X) :- d(X), pred(lhs, E).`
fn r_if(pred: &str, lhs: i128, levels: usize) -> MapProgram {
    MapProgram::new().with(
        "r_if",
        Clause::new(
            Goal::new("r", [x()]),
            [
                Goal::new("d", [x()]),
                Goal::new(pred, [int_t(lhs), deep_one_t(levels)]),
            ],
        ),
    )
}

/// `r(X) :- d(X), \+ pred(lhs, E).`
fn r_unless(pred: &str, lhs: i128, levels: usize) -> MapProgram {
    MapProgram::new().with(
        "r_unless",
        Clause::with_neg(
            Goal::new("r", [x()]),
            [Goal::new("d", [x()])],
            [Goal::new(pred, [int_t(lhs), deep_one_t(levels)])],
        ),
    )
}

/// `r` sealed empty is a closed-world claim that `r(a)` is false. It is accepted exactly when the
/// comparison in the clause body, read by value, keeps `r(a)` out of the model; when `r(a)` is in
/// the model the table is refused as not closed.
///
/// Either verdict may instead be `term_too_deep`, the caller's budget: the chain path does not
/// apply `max_term_depth` to the program's clauses today (it measures only the certificate's own
/// data), so at the default budget the closure reaches the theory and decides `E` by value. That
/// gap is a budget-enforcement residue named on #3123's PR, not a soundness one, and this test
/// does not pin it either way.
#[test]
fn a_certificate_sealing_r_empty_is_judged_by_the_comparisons_value_3123() {
    let wide = CheckLimits {
        max_term_depth: 1_024,
        ..CheckLimits::default()
    };
    let refused_as =
        |o: &Verdict, code: &str| matches!(o, Verdict::Reject { code: c, .. } if c.code() == code);
    let not_closed =
        |o: &Verdict| refused_as(o, "cert_not_closed") || refused_as(o, "term_too_deep");
    let closed = |o: &Verdict| matches!(o, Verdict::Accept) || refused_as(o, "term_too_deep");
    let mut wrong = Vec::new();
    for (name, levels) in DEPTHS {
        for limits in [CheckLimits::default(), wide] {
            let budget = limits.max_term_depth;
            // (the clause, whether r(a) is in the least model)
            let cases = [
                ("r(X) :- d(X), 1 =:= E", r_if("=:=", 1, levels), true),
                ("r(X) :- d(X), 2 =\\= E", r_if("=\\=", 2, levels), true),
                ("r(X) :- d(X), 1 =\\= E", r_if("=\\=", 1, levels), false),
                (
                    "r(X) :- d(X), \\+ 1 =:= E",
                    r_unless("=:=", 1, levels),
                    false,
                ),
                (
                    "r(X) :- d(X), \\+ 2 =:= E",
                    r_unless("=:=", 2, levels),
                    true,
                ),
            ];
            for (clause, program, r_a_holds) in cases {
                let got = r_sealed_empty(&program, limits);
                // r(a) in the model: sealing r empty must be refused. Otherwise it is accepted.
                let ok = if r_a_holds {
                    not_closed(&got.verdict)
                } else {
                    closed(&got.verdict)
                };
                if !ok {
                    wrong.push(format!(
                        "{name}, max_term_depth {budget}: {clause}: {}, r(a) {}",
                        verdict(&got),
                        if r_a_holds { "holds" } else { "does not hold" }
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
