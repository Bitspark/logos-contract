//! MEASUREMENT PROBE for #1363 — what a sealed absence certificate COSTS at
//! consumer-scale domains, measured rather than reasoned.
//!
//! # The domain here is INVENTED (ADR 0025 D3)
//!
//! It is **shift rostering**: `offered(P,S)` says person `P` may take slot `S`,
//! `withdrawn(P,S)` that the offer was pulled, `clash(P,S)` that taking it conflicts,
//! and `roster(P,S)` that the assignment stands. The consumer question behind #1363 is
//! a universally-quantified negative over a sealed finite domain — "no violation
//! exists" — and rostering is the smallest realistic setting with that exact shape.
//! Nothing here is imported from any consumer; logos names the seam and nothing else
//! (ADR 0025 D1, ADR 0018).
//!
//! # What #1363 asks — and the MEASURED answers, TWICE (the closure gate changed under it)
//!
//! ```text
//! 2026-08-27, the ODOMETER (|∪domains|^vars self-enumeration per scope clause):
//! Axis A   rows 5->20, domain FIXED     bytes 2277 -> 5377     ~210 B/row, LINEAR
//! Axis B   dom 20->160, rows FIXED      bytes 1877 -> 3408     1.8x  (the domain listing)
//!                                       check  44ms -> 2906ms  65x   (~4x per DOUBLING)
//! Q3       whole(20,80) vs 4x(5,20)     check 0.08x, bytes 1.35x
//!
//! 2026-09-10, the JOIN over the sealed extensions (#1829 increment 1):
//! Axis B   dom 20->160, rows FIXED      bytes 1877 -> 3408     1.8x  (unchanged)
//!                                       check 2.4ms -> 10.8ms  4.4x  (was 65x)
//! ```
//!
//!   1. **Size — LINEAR in the sealed relation, and cheap.** ~210 bytes per sealed row.
//!      The domain contributes only its listing. A cert is not where the cost lives.
//!   2. **Check cost — WAS quadratic in the DOMAIN; since #1829 it tracks the TABLE.**
//!      `ClosureWitness` is an empty marker in v1, so the checker verifies closure itself.
//!      The odometer re-enumerated every scope-clause grounding — |person| x |slot| for
//!      this two-variable clause, ~4x per domain doubling. The join iterates the sealed
//!      rows instead (§3.2's safety gate binds every variable through one), so the table,
//!      byte-identical across Axis B, is what the check now scales with; the residual
//!      growth is the domain LISTING being decoded and range-checked. Measured at one
//!      point: **270x less check time at dom=160**, same certificate, same verdict.
//!   3. **Domain factoring — no longer a cost lever.** Sharding converted |D|^2 into
//!      |D|^2/K; with the exponent gone there is nothing for K to divide. Shard for
//!      independent revalidation if you want it, not for check time.
//!
//! # ⭐ THE CONSUMER-SCALE CONSEQUENCE, stated as arithmetic rather than extrapolation
//!
//! The CHECKER no longer needs N^2 for a two-variable clause over a domain of N: it
//! visits the sealed rows and counts a GROUNDING per body-true tuple, a JOIN STEP per
//! candidate examined — both bounded by the tables, not the domain.
//!
//! And since #1829 increment 2 the DECLARED cost is the same count: the producer declares
//! what `logos_contract::closure_join_cost` counts for the certificate it just built — the
//! checker's own join, run without verifying — so `check_cert_budget`'s declared-size gate
//! and the scan agree on one number, and a logos-minted certificate over a 10^5 domain
//! with a small sealed table declares its table's cost, not N^2. (Between increments the
//! producer still declared the odometer's `|U|^vars`, so a logos-produced certificate hit
//! `cert_budget_exceeded` at N ~ 3,162 per typed domain by declaration alone.)
//!
//! ⚠ **BOUND — what this does NOT measure.** Every figure above is from ONE box, one
//! two-variable clause, and domains in the tens-to-hundreds. The two SHAPES are structural
//! (quadratic followed from the self-enumeration, with per-doubling ratios 3.73 / 4.17 /
//! 4.19 agreeing; table-bound follows from the join); the **constants are not portable**,
//! and nothing here was run at the 10^3-10^5 cardinalities #1363 names. The consumer's own
//! seeded measurements (pcb-agent#66) are the other half, and this probe is the shape they
//! should land against.
//!
//! # THE MEASUREMENT IS TWO-AXIS ON PURPOSE
//!
//! A single "make it bigger" sweep cannot separate the two things that grow together in
//! a realistic fixture. `ClosureWitness` is an **empty marker** in v1 (`cert.rs`): the
//! engine ships only `domains` + `extensions`, and the CHECKER re-enumerates every
//! scope-clause grounding over the domains. That predicts a SPLIT — bytes tracking the
//! table, check cost tracking the GROUNDING SPACE — and only varying the two axes
//! independently can show it:
//!
//!   * **Axis A** — vary sealed ROWS, hold the domain fixed.
//!   * **Axis B** — vary DOMAIN values, hold the sealed rows fixed.
//!
//! If both axes moved together, a result consistent with "linear in the cert" would be
//! equally consistent with "quadratic in the domain", and the probe would discriminate
//! nothing.

use logos_contract::{
    check_with_cert_context, closure_join_cost, edb_table_hash, encode_derivation_wire_v1,
    program_digest, CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId,
    ClosedModelCert, ClosureWitness, CompleteProgram, Derivation, Evidence, FiniteDomain, Goal,
    GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, NonMemberProof,
    PredicateSet, Premise, RelationTable, StratumPrefix, Subst, SupportEdge, SupportRef,
    SupportWitness, Symbol, Term, Theory, TheoryGround, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;
use std::time::Instant;

// --------------------------------- helpers ---------------------------------

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn g(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| v(a)))
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s)
}
fn t(s: &str) -> Term {
    Term::atom(s.as_bytes().to_vec())
}
fn subst2(a: (&str, &str), b: (&str, &str)) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert(a.0.into(), t(a.1));
    s.insert(b.0.into(), t(b.1));
    s
}
fn person(i: usize) -> String {
    format!("p{i}")
}
fn slot(i: usize) -> String {
    format!("t{i}")
}

const C_CLASH_RULE: &str = "clash_rule";
const C_ROSTER_RULE: &str = "roster_rule";

/// ```text
/// clash(P,S)  :- withdrawn(P,S).                  (IDB, sealed stratum)
/// roster(P,S) :- offered(P,S), \+ clash(P,S).     (upper stratum, negation)
/// ```
fn base_program() -> MapProgram {
    MapProgram::new()
        .with(
            C_CLASH_RULE,
            Clause::new(
                Goal::new("clash", [Term::var("P"), Term::var("S")]),
                [Goal::new("withdrawn", [Term::var("P"), Term::var("S")])],
            ),
        )
        .with(
            C_ROSTER_RULE,
            Clause::with_neg(
                Goal::new("roster", [Term::var("P"), Term::var("S")]),
                [Goal::new("offered", [Term::var("P"), Term::var("S")])],
                [Goal::new("clash", [Term::var("P"), Term::var("S")])],
            ),
        )
}

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _p: &Symbol) -> bool {
        false
    }
    fn decide_ground(&self, _a: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
}

struct RosterLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for RosterLeaves {
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

/// `withdrawn` EDB = the sealed rows; `offered` EDB = the single claimed assignment.
fn profile(withdrawn_rows: &[GroundLiteral], claimed: &GroundLiteral) -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"withdrawn".to_vec(), withdrawn_rows.to_vec());
    edb.insert(b"offered".to_vec(), vec![claimed.clone()]);
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(RosterLeaves {
            extensional: PredicateSet::from_iter(["offered", "withdrawn"]),
            edb,
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn bound_context(program: &dyn CompleteProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}
fn bind_cert(cert: &mut ClosedModelCert, program: &dyn CompleteProgram) {
    let cx = bound_context(program);
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
}

/// A sealed cert over `{withdrawn, clash}` with `rows` sealed pairs and `dom` values per
/// typed domain. The sealed pairs are drawn from the FIRST `rows` domain values, and the
/// claimed assignment is deliberately OUTSIDE them, so the negation is discharged by
/// genuine absence.
fn sealed_cert(rows: usize, dom: usize) -> (ClosedModelCert, Vec<GroundLiteral>) {
    assert!(
        dom > rows,
        "the claimed pair must fall outside the sealed rows"
    );
    let people: Vec<Value> = (0..dom).map(|i| v(&person(i))).collect();
    let slots: Vec<Value> = (0..dom).map(|i| v(&slot(i))).collect();

    let withdrawn: Vec<GroundLiteral> = (0..rows)
        .map(|i| g("withdrawn", &[&person(i), &slot(i)]))
        .collect();
    let clash: Vec<GroundLiteral> = (0..rows)
        .map(|i| g("clash", &[&person(i), &slot(i)]))
        .collect();

    let supports: Vec<SupportEdge> = (0..rows)
        .map(|i| SupportEdge {
            fact: g("clash", &[&person(i), &slot(i)]),
            clause: ClauseId::new(C_CLASH_RULE),
            subst: subst2(("P", &person(i)), ("S", &slot(i))),
            body_refs: vec![SupportRef::LowerStratum {
                cert: CertId(0),
                atom: g("withdrawn", &[&person(i), &slot(i)]),
            }],
            rank: 1,
        })
        .collect();

    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("withdrawn"), sym("clash")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![
            FiniteDomain::new(sym("person"), people),
            FiniteDomain::new(sym("slot"), slots),
        ],
        extensions: vec![
            RelationTable::new("withdrawn", 2, withdrawn.clone()),
            RelationTable::new("clash", 2, clash),
        ],
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            // Host counts, widened to the protocol's integers (#2735).
            cert_facts: (rows * 2) as u64,
            domain_values: (dom * 2) as u64,
            support_edges: rows as u64,
            // HONEST declarations. The clause `clash(P,S) :- withdrawn(P,S)` has TWO
            // variables over two typed domains, so the checker's self-enumeration visits
            // |person| x |slot| = dom^2 groundings. Declaring the real figure is what makes
            // the budget wall in `CheckLimits` a MEASURED number rather than a guess.
            rule_groundings: (dom * dom + 1_000) as u64,
            join_steps: (2 * dom * dom + 1_000) as u64,
            cert_bytes: 8_000_000,
        },
    };
    bind_cert(&mut cert, &base_program());
    (cert, withdrawn)
}

/// `roster(p_last, t_last) :- offered(...), \+ clash(...)` — the claimed pair is outside
/// the sealed rows, so absence is genuine.
fn roster_derivation(cert: ClosedModelCert, dom: usize) -> (Derivation, GroundLiteral) {
    let (p, s) = (person(dom - 1), slot(dom - 1));
    let claimed = g("offered", &[&p, &s]);
    let nodes = vec![
        Node::Leaf {
            conclusion: claimed.clone(),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("roster", &[&p, &s]),
            clause: ClauseId::new(C_ROSTER_RULE),
            subst: subst2(("P", &p), ("S", &s)),
            premises: vec![
                Premise::pos(0),
                Premise::Neg {
                    atom: g("clash", &[&p, &s]),
                    cert: CertId(0),
                    nonmember: NonMemberProof::DirectLookup,
                },
            ],
            meta: NodeMeta::none(),
        },
    ];
    (Derivation::with_closed_world(nodes, 1, [cert]), claimed)
}

/// One point: `(wire bytes, check micros, accepted?)`.
fn measure(rows: usize, dom: usize) -> (usize, u128, bool) {
    let (cert, withdrawn) = sealed_cert(rows, dom);
    let (deriv, claimed) = roster_derivation(cert, dom);
    let bytes = encode_derivation_wire_v1(&deriv).len();

    let program = base_program();
    let prof = profile(&withdrawn, &claimed);
    let cx = bound_context(&program);
    let goal = g("roster", &[&person(dom - 1), &slot(dom - 1)]);

    let t0 = Instant::now();
    let outcome = check_with_cert_context(&program, &goal, &deriv, &(), &prof, &cx);
    let micros = t0.elapsed().as_micros();
    if let Verdict::Reject { code, detail } = &outcome.verdict {
        println!(
            "   REJECT rows={rows} dom={dom}: {} ({detail})",
            code.code()
        );
    }
    (bytes, micros, outcome.is_accept())
}

// ================================== the probe ==================================

/// **Axis A — vary sealed ROWS, domain FIXED.** Answers #1363 Q1.
#[test]
fn axis_a_cert_bytes_are_linear_in_the_sealed_relation() {
    let dom = 60;
    let mut obs = vec![];
    for rows in [5usize, 10, 20] {
        let (bytes, micros, ok) = measure(rows, dom);
        assert!(
            ok,
            "the fixture must ACCEPT or it measures a rejection path"
        );
        println!("A  rows={rows:4}  dom={dom}  bytes={bytes:8}  check={micros}us");
        obs.push((rows, bytes));
    }
    // Bytes must GROW with the sealed relation (it is carried verbatim), and grow no
    // worse than linearly — the shape a consumer sizing a bundle needs.
    let (r0, b0) = obs[0];
    let (r3, b3) = obs[2];
    assert!(b3 > b0, "bytes must grow with sealed rows");
    let per_row_0 = b0 as f64 / r0 as f64;
    let per_row_3 = b3 as f64 / r3 as f64;
    assert!(
        per_row_3 < per_row_0 * 1.5,
        "bytes/row must not blow up (linear or better): {per_row_0:.0} -> {per_row_3:.0}"
    );
}

/// **Axis B — vary DOMAIN values, sealed rows FIXED.** Answers #1363 Q2, and is the half
/// a one-axis sweep cannot see: the sealed table is byte-identical across these points.
/// Until #1829 the CHECKER re-enumerated the grounding space here (~4x per doubling); the
/// join scans the table, so this now pins that the exponent is GONE.
///
/// #2372: the guard is the checker's own closure-join COUNT, not wall-clock time. A single
/// timing sample per point on a shared runner redded this test on unrelated PRs (19.0x on
/// #2344, 28.1x on #2284, each from ONE descheduled sample). The count is what the odometer
/// inflated, it is deterministic, and it runs the checker's own join code
/// (`closure_join_cost`, the same `join_groundings` `check` runs). Time stays a printed figure.
#[test]
fn axis_b_check_cost_tracks_the_table_not_the_grounding_space() {
    let rows = 5;
    let program = base_program();
    let mut obs = vec![];
    for dom in [20usize, 40, 80, 160] {
        let (bytes, micros, ok) = measure(rows, dom);
        assert!(
            ok,
            "the fixture must ACCEPT or it measures a rejection path"
        );
        let (cert, _) = sealed_cert(rows, dom);
        let (groundings, joins) =
            closure_join_cost(&cert, &program, &NoTheory, &CheckLimits::default())
                .expect("the sealed clause plans and fits the default budget");
        println!(
            "B  rows={rows}  dom={dom:4}  bytes={bytes:8}  groundings={groundings}  joins={joins}  check={micros}us"
        );
        obs.push((dom, bytes, groundings, joins));
    }
    let (d0, b0, g0, j0) = obs[0];
    let (d3, b3, _, _) = obs[3];
    assert_eq!(
        d3,
        d0 * 8,
        "the domain axis must span 8x or it shows little"
    );

    // ⭐ THE SPLIT, and it is what a one-axis sweep cannot show. The sealed TABLE is
    // identical at every point here; only the domain grew 8x. Bytes grow only by the
    // domain LISTING — and since #1829 so does the check, because the closure join
    // iterates the sealed rows rather than the grounding space (|D|^2 for this
    // two-variable clause).
    //
    // Measured 2026-08-27, odometer: bytes 1877 -> 3408 (1.8x), check 43ms -> 2812ms (65x),
    // per-doubling 3.73 / 4.17 / 4.19 — ~4x per doubling, the quadratic.
    // Measured 2026-09-10, join:     bytes unchanged,             check 2.4ms -> 10.8ms (4.4x).
    //
    // The guard is a COUNT (#2372). The only sealed-head clause is `clash(P,S) :-
    // withdrawn(P,S)`, a binder over the 5 sealed rows, so the join does exactly one grounding
    // and one join step per row at EVERY domain size. The odometer's shape would be |D|^2
    // groundings (400 at dom 20, 25 600 at dom 160). The count must not move with the domain
    // at all: an exact equality, no timing margin to tune.
    let byte_growth = b3 as f64 / b0 as f64;
    assert!(
        byte_growth < 4.0,
        "cert bytes must NOT track the domain squared: grew {byte_growth:.1}x over an 8x domain"
    );
    assert_eq!(
        (g0, j0),
        (rows, rows),
        "the closure join visits the sealed rows: one grounding and one join step per row"
    );
    for &(dom, _, groundings, joins) in &obs {
        assert_eq!(
            (groundings, joins),
            (g0, j0),
            "check cost must track the TABLE, not the grounding space: at dom={dom} the closure \
             join did {groundings} groundings / {joins} join steps, against {g0} / {j0} at \
             dom={d0} (the odometer's quadratic shape would be |D|^2; #1829's join must not \
             bring it back)"
        );
    }
}

/// **Q3 — sharding.** K certs over disjoint partitions, versus one cert over the whole
/// domain. Measured whether factoring reduced the dominant cost — it did under the
/// odometer (|D|^2/K); under #1829's join there is no exponent to divide, so this now
/// pins only that sharding is not a PENALTY worth avoiding either.
#[test]
fn q3_sharding_the_domain_reduces_total_check_cost() {
    // #2511: each check is timed as the LEAST of `DRAWS` runs. Once #2551 made the whole cert's
    // check ~8x faster (debug, 22-49 ms on main against 2.7-9.7 ms), the ratio's denominator is a
    // couple of milliseconds, and one contended stretch of a shared runner on a single draw read
    // 7.90x (CI: shards 14.5 ms against ~4-6 ms locally). The least of five is what the shape
    // needs; a spike can no longer decide it.
    const DRAWS: usize = 5;
    let least = |rows, dom| {
        (0..DRAWS)
            .map(|_| measure(rows, dom))
            .reduce(|a, b| (a.0, a.1.min(b.1), a.2 && b.2))
            .expect("DRAWS > 0")
    };
    let (whole_bytes, whole_us, ok) = least(20, 80);
    assert!(ok);
    println!("Q3 WHOLE   rows=20 dom=80    bytes={whole_bytes} check={whole_us}us");

    // The same 80 sealed rows and the same coverage, factored into 8 certs of 10 rows
    // over a 100-value partition each.
    let (mut shard_bytes, mut shard_us) = (0usize, 0u128);
    for _ in 0..4 {
        let (b, us, ok) = least(5, 20);
        assert!(ok);
        shard_bytes += b;
        shard_us += us;
    }
    println!("Q3 SHARDED 4x(rows=5 dom=20)  bytes={shard_bytes} check={shard_us}us");
    let byte_ratio = shard_bytes as f64 / whole_bytes as f64;
    let time_ratio = shard_us as f64 / whole_us.max(1) as f64;
    println!("Q3 ratio: bytes {byte_ratio:.2}x  check {time_ratio:.2}x  (sharded / whole)");

    // ⇒ THE ANSWER TO Q3, twice. Under the odometer sharding converted |D|^2 into
    // K*(|D|/K)^2 = |D|^2/K, so the dominant cost fell by ~K while the bytes rose only by
    // the duplicated per-cert preamble — measured check 0.13x, bytes 1.15x at K=4. Under
    // the join (#1829) the check scans the same rows either way, so the ratio hovers near
    // 1 and is dominated by the K-fold preamble; sharding is no longer a cost lever.
    //
    // Generous bounds again — CI runners are contended, so only the SHAPE is pinned: K
    // shards must not cost dramatically more than the whole (the preamble is small).
    assert!(
        time_ratio < 4.0,
        "sharding must not blow up total check cost: {time_ratio:.2}x"
    );
    assert!(
        byte_ratio < 2.0,
        "sharding must not blow up total bytes: {byte_ratio:.2}x"
    );
}
