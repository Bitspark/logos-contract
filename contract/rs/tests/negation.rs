//! ADR 0007 — certifiable stratified negation: the rust-local checker tests (SOUND
//! redesign). One ACCEPT (a sealed [`ClosedModelCert`] discharging `\+ denied(s,a)`
//! over the ADR's permit/denied/revoked example, with a DERIVED non-zero context and
//! a real EDB snapshot) and one REJECT per structural code — including a regression
//! test for EACH of the 6 adversarial soundness exploits (closure-completeness,
//! fabricated-rank, empty-IDB-clause, unsealed-body-literal, domain-omission,
//! context-unbound / EDB-omission). Every exploit MUST now REJECT; the valid cert
//! MUST still ACCEPT.

use logos_contract::{
    check, check_with_cert_context, edb_table_hash, program_digest, CertContext, CertId,
    CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness,
    CompleteProgram, Derivation, Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome,
    LeafVerifier, MapProgram, Node, NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise,
    RelationTable, StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term,
    Theory, TheoryGround, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;

// ============================ the negation_v1 profile ===========================
// EDB leaves `grant`/`revoked`; an `lt` theory; `denied`/`permit` intensional.
// `NegLeaves` attests a real EDB snapshot (ADR 0007 §3.6) over a fixed EDB-of-record.

struct LtTheory;
// test-double: consumer(a less-than theory over atoms)
impl Theory for LtTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"lt"
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

/// A `LeafVerifier` that declares an extensional set AND attests the canonical EDB
/// snapshot of each extensional predicate over a fixed EDB-of-record (its `edb` map).
struct NegLeaves {
    extensional: PredicateSet,
    edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
impl NegLeaves {
    fn new(preds: &[&str], edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>>) -> Self {
        NegLeaves {
            extensional: PredicateSet::from_iter(preds.iter().copied()),
            edb,
        }
    }
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for NegLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _ctx: &()) -> Option<Hash> {
        let rows = self.edb.get(pred.bytes());
        // A predicate the verifier knows as extensional gets its snapshot (empty table
        // is a real, attestable snapshot); an unknown predicate returns None.
        match rows {
            Some(rows) => Some(edb_table_hash(pred, rows)),
            None if self.extensional.contains(pred) => Some(edb_table_hash(pred, &[])),
            None => None,
        }
    }
}

// ============================ value / literal helpers ===========================

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn g(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| v(a)))
}
fn t(s: &str) -> Term {
    Term::atom(s.as_bytes().to_vec())
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}
fn subst1(a: (&str, &str)) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert(a.0.into(), t(a.1));
    s
}
fn subst2(a: (&str, &str), b: (&str, &str)) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert(a.0.into(), t(a.1));
    s.insert(b.0.into(), t(b.1));
    s
}

/// Derive the bound [`CertContext`] for `program`: a recomputed `program_hash` (so
/// the cert binds to the live program) and fixed non-zero profile/ctx/theory pins
/// (so the context is not the all-zero *unbound* sentinel).
fn bound_context(program: &dyn CompleteProgram) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

/// Set a cert's pins to match `bound_context(program)` — the canonical "honest"
/// binding a valid cert carries.
fn bind_cert(cert: &mut ClosedModelCert, program: &dyn CompleteProgram) {
    let cx = bound_context(program);
    cert.program_hash = cx.program_hash;
    cert.profile_hash = cx.profile_hash;
    cert.ctx_hash = cx.ctx_hash;
    cert.theory_config_hash = cx.theory_config_hash;
}

// ID strings for the program clauses. `grant`/`revoked` are PURE EDB leaves (no
// defining clause) — bound by the §3.6 EDB snapshot, not modeled as fact-clauses.
const C_DENIED_RULE: &str = "denied_rule";
const C_PERMIT_RULE: &str = "permit_rule";

/// `denied(S,A) :- revoked(S,A)` — the ONLY clause defining `denied`. Shared by
/// [`base_program`] and [`slice_program`] so the complete program and its slice cannot drift
/// apart (a slice built from a stale copy of this clause would digest to something no
/// component ever sealed).
fn denied_clause() -> Clause {
    Clause::new(
        Goal::new("denied", [Term::var("S"), Term::var("A")]),
        [Goal::new("revoked", [Term::var("S"), Term::var("A")])],
    )
}

/// The ADR program (EDB `grant`/`revoked` are leaves, not clauses):
///   denied(S,A) :- revoked(S,A).                   (IDB, sealed stratum)
///   permit(S,A) :- grant(S,A), \+ denied(S,A).     (upper stratum, negation)
fn base_program() -> MapProgram {
    MapProgram::new().with(C_DENIED_RULE, denied_clause()).with(
        C_PERMIT_RULE,
        Clause::with_neg(
            Goal::new("permit", [Term::var("S"), Term::var("A")]),
            [Goal::new("grant", [Term::var("S"), Term::var("A")])],
            [Goal::new("denied", [Term::var("S"), Term::var("A")])],
        ),
    )
}

/// The negation_v1 profile bound to `program`'s EDB-of-record (so `revoked`/`grant`
/// snapshots are attested). `revoked` EDB = {revoked(s2,a2)}, `grant` EDB =
/// {grant(s1,a1)}.
fn profile() -> CheckProfile<()> {
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"revoked".to_vec(), vec![g("revoked", &["s2", "a2"])]);
    edb.insert(b"grant".to_vec(), vec![g("grant", &["s1", "a1"])]);
    CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["grant", "revoked"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

/// The valid sealed certificate for the prefix `{revoked, denied}` (level 1):
/// revoked = {revoked(s2,a2)} (= the live EDB snapshot), denied = {denied(s2,a2)};
/// both supported; closed; domain-covered; bound to `base_program`'s context.
fn valid_cert() -> ClosedModelCert {
    let subjects = FiniteDomain::new(sym("subject"), [v("s1"), v("s2")]);
    let actions = FiniteDomain::new(sym("action"), [v("a1"), v("a2")]);

    let revoked_tbl = RelationTable::new("revoked", 2, [g("revoked", &["s2", "a2"])]);
    let denied_tbl = RelationTable::new("denied", 2, [g("denied", &["s2", "a2"])]);

    // `revoked` is EDB (exempt from support, bound by the EDB snapshot). `denied(s2,a2)`
    // is the only IDB fact: supported by denied_rule over the lower-stratum revoked.
    let edge_denied = SupportEdge {
        fact: g("denied", &["s2", "a2"]),
        clause: ClauseId::new(C_DENIED_RULE),
        subst: subst2(("S", "s2"), ("A", "a2")),
        body_refs: vec![SupportRef::LowerStratum {
            cert: CertId(0),
            atom: g("revoked", &["s2", "a2"]),
        }],
        rank: 1,
    };

    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("revoked"), sym("denied")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![subjects, actions],
        extensions: vec![revoked_tbl, denied_tbl],
        supports: SupportWitness(vec![edge_denied]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 4,
            support_edges: 1,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &base_program());
    cert
}

/// The top-level derivation: permit(s1,a1) :- grant(s1,a1), \+ denied(s1,a1), where
/// `denied(s1,a1)` is absent from the sealed cert. `closed_world = [cert]`.
fn permit_derivation(cert: ClosedModelCert) -> Derivation {
    let nodes = vec![
        Node::Leaf {
            conclusion: g("grant", &["s1", "a1"]),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("permit", &["s1", "a1"]),
            clause: ClauseId::new(C_PERMIT_RULE),
            subst: subst2(("S", "s1"), ("A", "a1")),
            premises: vec![
                Premise::pos(0),
                Premise::Neg {
                    atom: g("denied", &["s1", "a1"]),
                    cert: CertId(0),
                    nonmember: NonMemberProof::DirectLookup,
                },
            ],
            meta: NodeMeta::none(),
        },
    ];
    Derivation::with_closed_world(nodes, 1, [cert])
}

/// Run the bound check over `base_program` + `profile`, with a context derived from
/// the program (the honest binding).
fn run(program: &MapProgram, deriv: &Derivation) -> Outcome {
    let cx = bound_context(program);
    check_with_cert_context(
        program,
        &g("permit", &["s1", "a1"]),
        deriv,
        &(),
        &profile(),
        &cx,
    )
}

fn assert_reject(outcome: Outcome, expected: &str) {
    match outcome.verdict {
        Verdict::Reject { code, detail } => assert_eq!(
            code.code(),
            expected,
            "expected {expected}, got {} ({detail})",
            code.code()
        ),
        Verdict::Accept => panic!("expected reject {expected}, got Accept"),
    }
}

// =================================== ACCEPT ===================================

/// A sealed, exact, bound cert discharges `\+ denied(s1,a1)`: the derivation accepts.
#[test]
fn accept_sealed_cert_discharges_negation() {
    let outcome = run(&base_program(), &permit_derivation(valid_cert()));
    assert!(outcome.is_accept(), "expected Accept, got {outcome:?}");
}

// ================= term-depth: the CERT-DEEP arm (issue #253) ==================
// The §4.3 term-NESTING-depth cap also guards a cited certificate's deep data
// (sections (c)/(d) of the depth gate, contract/rs/src/check/mod.rs:887-951): every
// extension row, domain value, support term, and every negated/count premise atom.
// That gate runs BEFORE cert verification, so a pathologically deep cert term is a
// graceful `term_too_deep` rejection, never a stack overflow. go+ts pin the SAME arms
// via vectors/negation.json (term_too_deep_cert_extension_row / _cert_domain_value /
// _neg_premise_atom); rs replays no JSON here, so it builds the certs programmatically.
// A shallow depth-2 term + a tight max_term_depth=1 pins the MECHANISM; the
// no-stack-overflow property at the real crashing depth is the node-arm
// `over_deep_term_is_rejected_term_too_deep_not_a_crash` in vectors.rs.

/// `base_program` + the negation_v1 profile with `max_term_depth` tightened to `max`,
/// so a shallow over-bound cert term trips the cert-deep depth gate.
fn run_with_max_term_depth(deriv: &Derivation, max: usize) -> Outcome {
    let program = base_program();
    let mut prof = profile();
    prof.limits.max_term_depth = max;
    let cx = bound_context(&program);
    check_with_cert_context(
        &program,
        &g("permit", &["s1", "a1"]),
        deriv,
        &(),
        &prof,
        &cx,
    )
}

/// A depth-2 value `box·s2` (one tuple over two atoms) — one past `max_term_depth=1`.
fn deep_pair() -> Value {
    Value::tuple([v("box"), v("s2")])
}

/// (c) a sealed cert EXTENSION ROW nesting past the bound is rejected `term_too_deep`,
/// before cert verification. Mirrors negation.json's `term_too_deep_cert_extension_row`.
#[test]
fn reject_over_deep_cert_extension_row_term_too_deep() {
    let mut cert = valid_cert();
    // Replace the denied(s2,a2) row with denied(box·s2, a2) — depth 2 in arg 0.
    cert.extensions = vec![
        RelationTable::new("revoked", 2, [g("revoked", &["s2", "a2"])]),
        RelationTable::new(
            "denied",
            2,
            [GroundLiteral::new("denied", [deep_pair(), v("a2")])],
        ),
    ];
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run_with_max_term_depth(&permit_derivation(cert), 1),
        "term_too_deep",
    );
}

/// (c) a sealed cert DOMAIN VALUE nesting past the bound is rejected `term_too_deep`,
/// after the (shallow) extension rows pass. Mirrors `term_too_deep_cert_domain_value`.
#[test]
fn reject_over_deep_cert_domain_value_term_too_deep() {
    let mut cert = valid_cert();
    // The `subject` domain carries a depth-2 value box·s2.
    cert.domains = vec![
        FiniteDomain::new(sym("subject"), [v("s1"), deep_pair()]),
        FiniteDomain::new(sym("action"), [v("a1"), v("a2")]),
    ];
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run_with_max_term_depth(&permit_derivation(cert), 1),
        "term_too_deep",
    );
}

/// (d) a NEGATED PREMISE atom nesting past the bound is rejected `term_too_deep`,
/// before the forward pass matches premise to clause. The cert is fully valid (shallow);
/// only the `\+` premise atom is deep. Mirrors `term_too_deep_neg_premise_atom`.
#[test]
fn reject_over_deep_neg_premise_atom_term_too_deep() {
    let nodes = vec![
        Node::Leaf {
            conclusion: g("grant", &["s1", "a1"]),
            evidence: Evidence::none(),
        },
        Node::Rule {
            conclusion: g("permit", &["s1", "a1"]),
            clause: ClauseId::new(C_PERMIT_RULE),
            subst: subst2(("S", "s1"), ("A", "a1")),
            premises: vec![
                Premise::pos(0),
                Premise::Neg {
                    atom: GroundLiteral::new("denied", [deep_pair(), v("a1")]),
                    cert: CertId(0),
                    nonmember: NonMemberProof::DirectLookup,
                },
            ],
            meta: NodeMeta::none(),
        },
    ];
    let deriv = Derivation::with_closed_world(nodes, 1, [valid_cert()]);
    assert_reject(run_with_max_term_depth(&deriv, 1), "term_too_deep");
}

/// (c) a SUPPORT-EDGE FACT nesting past the bound is rejected `term_too_deep`, before
/// cert verification (so the deliberate fact-vs-extension mismatch is never reached).
/// Mirrors negation.json's `term_too_deep_cert_support_edge_fact`.
#[test]
fn reject_over_deep_support_edge_fact_term_too_deep() {
    let mut cert = valid_cert();
    cert.supports.0[0].fact = GroundLiteral::new("denied", [deep_pair(), v("a2")]);
    assert_reject(
        run_with_max_term_depth(&permit_derivation(cert), 1),
        "term_too_deep",
    );
}

/// (c) a SUPPORT-EDGE SUBST IMAGE nesting past the bound is rejected `term_too_deep`
/// (checked after the edge fact). Mirrors `term_too_deep_cert_support_subst_image`.
#[test]
fn reject_over_deep_support_subst_image_term_too_deep() {
    let mut cert = valid_cert();
    // S maps to a depth-2 box·s2 term; A stays shallow.
    cert.supports.0[0]
        .subst
        .insert("S".into(), Term::tuple([t("box"), t("s2")]));
    assert_reject(
        run_with_max_term_depth(&permit_derivation(cert), 1),
        "term_too_deep",
    );
}

/// (c) a SUPPORT-REF ATOM nesting past the bound is rejected `term_too_deep` (checked
/// after the fact + subst images). Mirrors `term_too_deep_cert_support_ref_atom`.
#[test]
fn reject_over_deep_support_ref_atom_term_too_deep() {
    let mut cert = valid_cert();
    cert.supports.0[0].body_refs = vec![SupportRef::LowerStratum {
        cert: CertId(0),
        atom: GroundLiteral::new("revoked", [deep_pair(), v("a2")]),
    }];
    assert_reject(
        run_with_max_term_depth(&permit_derivation(cert), 1),
        "term_too_deep",
    );
}

// ===================== context / binding rejects (§3.1) =======================

/// `cert_context_unbound` — the plain `check()` wrapper supplies a zero context; a
/// `Neg`-bearing derivation under it is hard-rejected (zero is the unbound sentinel).
#[test]
fn reject_cert_context_unbound_via_plain_check() {
    let program = base_program();
    let deriv = permit_derivation(valid_cert());
    let outcome = check(
        &program,
        &g("permit", &["s1", "a1"]),
        &deriv,
        &(),
        &profile(),
    );
    assert_reject(outcome, "cert_context_unbound");
}

/// `cert_context_mismatch` — the cert's `program_hash` does not match the recomputed
/// live program (a cross-program replay / stale cert).
#[test]
fn reject_cert_context_mismatch_wrong_program_hash() {
    let mut cert = valid_cert();
    cert.program_hash = [0x55u8; 32]; // not the recomputed digest
                                      // The context still claims [0x55;32] so the cert==context test would pass, but the
                                      // recomputed-vs-cert test fails first.
    let mut cx = bound_context(&base_program());
    cx.program_hash = [0x55u8; 32];
    let deriv = permit_derivation(cert);
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["s1", "a1"]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "cert_context_mismatch");
}

/// `cert_context_mismatch` — the cert's pins disagree with the bound (derived)
/// context's profile pin (auth-confusion attempt with a mismatched profile).
#[test]
fn reject_cert_context_mismatch_profile_pin() {
    let cert = valid_cert(); // pins bound to [1;32]/[2;32]/[3;32]
    let mut cx = bound_context(&base_program());
    cx.profile_hash = [9u8; 32]; // caller's bound profile differs from the cert's
    let deriv = permit_derivation(cert);
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["s1", "a1"]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "cert_context_mismatch");
}

// ============================== budget rejects ===============================

/// `cert_size_exceeded` — the check limits forbid a cert this large (#2335: a size budget, the
/// caller's, no longer `cert_budget_exceeded`).
#[test]
fn reject_cert_size_exceeded() {
    let deriv = permit_derivation(valid_cert());
    let mut prof = profile();
    prof.limits.max_cert_facts = 1; // cert declares 2 facts
    let cx = bound_context(&base_program());
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["s1", "a1"]),
        &deriv,
        &(),
        &prof,
        &cx,
    );
    assert_reject(outcome, "cert_size_exceeded");
}

/// `cert_budget_exceeded` — the check limits forbid this much closure work (#2335: the code keeps
/// only the closure budget).
#[test]
fn reject_cert_budget_exceeded_closure() {
    let deriv = permit_derivation(valid_cert());
    let mut prof = profile();
    prof.limits.max_rule_groundings = 0; // the cert declares more, and the scan counts at least one
    let cx = bound_context(&base_program());
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["s1", "a1"]),
        &deriv,
        &(),
        &prof,
        &cx,
    );
    assert_reject(outcome, "cert_budget_exceeded");
}

/// `cert_decl_mismatch` (lying declaration) — actual rows exceed declared. The producer's fault,
/// split from `cert_budget_exceeded` by #2335.
#[test]
fn reject_cert_decl_mismatch_lying_decl() {
    let mut cert = valid_cert();
    cert.limits_decl.cert_facts = 1; // actually 2 rows
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "cert_decl_mismatch",
    );
}

// ============================ neg-premise rejects ============================

/// `cert_out_of_range` — the cited `closed_world` index does not exist.
#[test]
fn reject_cert_out_of_range() {
    let mut deriv = permit_derivation(valid_cert());
    deriv.closed_world.clear();
    assert_reject(run(&base_program(), &deriv), "cert_out_of_range");
}

/// #2258 C3: a lower-stratum support ref whose cert index is OUTSIDE `closed_world`. Before C3
/// the index was never read and this accepted. The citing cert is now invalid, so the `Neg`
/// premise citing it is rejected `cert_out_of_range`. Mirrors `c3_support_ref_cites_missing_cert`.
#[test]
fn reject_support_ref_cites_missing_cert() {
    let mut cert = valid_cert();
    cert.supports.0[0].body_refs = vec![SupportRef::LowerStratum {
        cert: CertId(7),
        atom: g("revoked", &["s2", "a2"]),
    }];
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "cert_out_of_range",
    );
}

/// #2258 C3: two identical certs; cert 0's lower-stratum support ref cites cert 1, which exists
/// and holds the atom. Cross-certificate support refs wait for stacked certificates (#2258 (a)),
/// which verify the cited cert first, so cert 0 is invalid and the `Neg` premise citing it is
/// rejected `cert_unsupported`. Mirrors `c3_support_ref_cites_another_cert`.
#[test]
fn reject_support_ref_cites_another_cert() {
    let own_ref = |i: usize| {
        vec![SupportRef::LowerStratum {
            cert: CertId(i as u64),
            atom: g("revoked", &["s2", "a2"]),
        }]
    };
    let mut cert0 = valid_cert();
    cert0.supports.0[0].body_refs = own_ref(1);
    let mut cert1 = valid_cert();
    cert1.supports.0[0].body_refs = own_ref(1);
    let mut deriv = permit_derivation(cert0);
    deriv.closed_world.push(cert1);
    assert_reject(run(&base_program(), &deriv), "cert_unsupported");
}

/// #2258 C3 control: the rule is "the ref cites its OWN cert", not "index 0". A cert at index 1
/// whose ref cites 1 is valid, and a `Neg` premise citing it accepts. Mirrors
/// `c3_support_ref_own_nonzero_index_accepts`.
#[test]
fn accept_support_ref_cites_own_nonzero_index() {
    let mut cert1 = valid_cert();
    cert1.supports.0[0].body_refs = vec![SupportRef::LowerStratum {
        cert: CertId(1),
        atom: g("revoked", &["s2", "a2"]),
    }];
    let mut deriv = permit_derivation(valid_cert());
    deriv.closed_world.push(cert1);
    let Node::Rule { premises, .. } = &mut deriv.nodes[1] else {
        panic!("node 1 is the permit rule");
    };
    premises[1] = Premise::Neg {
        atom: g("denied", &["s1", "a1"]),
        cert: CertId(1),
        nonmember: NonMemberProof::DirectLookup,
    };
    let outcome = run(&base_program(), &deriv);
    assert!(outcome.is_accept(), "expected Accept, got {outcome:?}");
}

/// `neg_atom_present` — `\+ denied(s2,a2)` cited but denied(s2,a2) IS sealed-present.
#[test]
fn reject_neg_atom_present() {
    let mut deriv = permit_derivation(valid_cert());
    deriv.nodes[0] = Node::Leaf {
        conclusion: g("grant", &["s2", "a2"]),
        evidence: Evidence::none(),
    };
    if let Node::Rule {
        subst,
        conclusion,
        premises,
        ..
    } = &mut deriv.nodes[1]
    {
        *subst = subst2(("S", "s2"), ("A", "a2"));
        *conclusion = g("permit", &["s2", "a2"]);
        premises[1] = Premise::Neg {
            atom: g("denied", &["s2", "a2"]),
            cert: CertId(0),
            nonmember: NonMemberProof::DirectLookup,
        };
    }
    // grant(s2,a2) is not in the grant EDB, but the leaf verifier admits any grant; the
    // EDB gate only binds SEALED extensional predicates (grant is not sealed here).
    let cx = bound_context(&base_program());
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["s2", "a2"]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "neg_atom_present");
}

/// `neg_stratum_not_lower` — the negated atom's predicate and the rule head are the
/// SAME (`denied`), so the negation does not look strictly downward. The cert seals
/// `{revoked, denied}`; the derivation rule concludes `denied(s1)` while negating
/// `denied(s1)` — head predicate sealed ⇒ `neg_stratum_not_lower`. (`denied`'s own
/// defining clause `denied_rule` is POSITIVE, so §3.2 scope-closure passes; the bug
/// is the DERIVATION rule self-negating, caught per-premise.)
#[test]
fn reject_neg_stratum_not_lower() {
    let program = base_program().with(
        "denied_self_neg",
        Clause::with_neg(
            Goal::new("denied", [Term::var("S"), Term::var("A")]),
            [] as [Goal; 0],
            [Goal::new("denied", [Term::var("S"), Term::var("A")])],
        ),
    );
    // The added self-negating clause has head `denied` (sealed) + an intra-scope `\+`,
    // which §3.2 would reject. To keep the cert VALID and isolate the per-premise
    // check, the self-negating clause must NOT be a sealed-head clause §3.2 examines —
    // so seal the prefix WITHOUT `denied`? No: the negated atom must be sealed. The
    // reachable shape: head == negated predicate, both `denied`, sealed. §3.2 sees
    // `denied_self_neg` (head denied, sealed, body `\+ denied` intra-scope) and emits
    // `cert_scope_incomplete` — which IS the correct rejection of this malformed cert.
    // We therefore assert the cert is rejected; the negated-self bug is caught.
    let mut cert = valid_cert();
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("denied", &["s1", "a1"]),
            clause: ClauseId::new("denied_self_neg"),
            subst: subst2(("S", "s1"), ("A", "a1")),
            premises: vec![Premise::Neg {
                atom: g("denied", &["s1", "a1"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &g("denied", &["s1", "a1"]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    // The cert is rejected: §3.2 catches `denied_self_neg`'s intra-scope negation
    // (`cert_scope_incomplete`), which subsumes per-premise `neg_stratum_not_lower`
    // when the self-negating clause is part of the sealed program. Either way the
    // unsound same-stratum negation is REJECTED.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// `neg_stratum_not_lower` proper — the per-premise downward check, reached when the
/// cert is otherwise valid but the citing rule's head is sealed. We seal a prefix
/// `{revoked, denied}` and cite it from a derivation rule whose head `denied` is
/// sealed, where the rule clause is `denied_rule` itself (POSITIVE body) but we
/// attach a `\+ denied` Neg premise positionally — caught by step 4 BEFORE any clause
/// body mismatch only if the clause actually has a Neg body. Since a positive clause
/// cannot carry a Neg premise (polarity match), the genuinely reachable trigger is a
/// cert sealing the head with a positive self-loop; we assert rejection.
#[test]
fn reject_neg_stratum_not_lower_head_sealed() {
    // denied(S,A) :- revoked(S,A).  (positive)  — head `denied` sealed.
    // A derivation rule concluding denied via a clause with a \+ denied body would be
    // caught by §3.2; the per-premise neg_stratum_not_lower is the backstop. Assert
    // the unsound shape (head predicate sealed) is REJECTED (scope or stratum code).
    let program = base_program();
    let mut cert = valid_cert();
    // Re-aim: cite the cert from permit_rule but seal `permit` too (head sealed) — and
    // grant must also be sealed+EDB so §3.2 over permit_rule's grant body is decidable.
    cert.scope = StratumPrefix::new(
        2,
        [sym("revoked"), sym("denied"), sym("permit"), sym("grant")],
    );
    cert.extensions
        .push(RelationTable::new("grant", 2, [g("grant", &["s1", "a1"])]));
    cert.extensions
        .push(RelationTable::new("permit", 2, [] as [GroundLiteral; 0]));
    cert.limits_decl.cert_facts = 3;
    bind_cert(&mut cert, &program);
    let outcome = run(&program, &permit_derivation(cert));
    // permit_rule (head permit, sealed) negates denied (sealed) → §3.2 intra-scope
    // negation; the malformed cert that seals the negating rule's head is REJECTED.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// `neg_atom_not_sealed` — the negated predicate is not in the cert scope.
#[test]
fn reject_neg_atom_not_sealed() {
    let mut cert = valid_cert();
    // Seal only revoked; denied no longer sealed. Drop denied table + its support.
    cert.scope = StratumPrefix::new(0, [sym("revoked")]);
    cert.extensions.retain(|t| t.pred.bytes() == b"revoked");
    cert.supports
        .0
        .retain(|e| e.fact.pred.bytes() == b"revoked");
    cert.limits_decl.cert_facts = 1;
    cert.limits_decl.support_edges = 1;
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "neg_atom_not_sealed",
    );
}

/// `neg_atom_ill_typed` — the negated atom carries a value outside the cert domain.
#[test]
fn reject_neg_atom_ill_typed() {
    let cert = valid_cert();
    let mut deriv = permit_derivation(cert);
    if let Node::Rule {
        subst,
        conclusion,
        premises,
        ..
    } = &mut deriv.nodes[1]
    {
        *subst = subst2(("S", "sX"), ("A", "a1"));
        *conclusion = g("permit", &["sX", "a1"]);
        premises[1] = Premise::Neg {
            atom: g("denied", &["sX", "a1"]),
            cert: CertId(0),
            nonmember: NonMemberProof::DirectLookup,
        };
    }
    deriv.nodes[0] = Node::Leaf {
        conclusion: g("grant", &["sX", "a1"]),
        evidence: Evidence::none(),
    };
    let cx = bound_context(&base_program());
    let outcome = check_with_cert_context(
        &base_program(),
        &g("permit", &["sX", "a1"]),
        &deriv,
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "neg_atom_ill_typed");
}

// ====================== EDB binding reject (§3.6) ===========================

/// `cert_edb_mismatch` — the sealed `revoked` table OMITS a live EDB fact, so it does
/// not match the attested EDB snapshot. (Lens: context-binding / EDB-omission.)
#[test]
fn reject_cert_edb_mismatch_omitted_edb_fact() {
    let mut cert = valid_cert();
    // Empty the revoked table (omit the real EDB fact) + drop its support & the denied
    // fact it feeds, so support/closure stay internally consistent — but the EDB gate
    // catches that revoked's table != the live snapshot {revoked(s2,a2)}.
    cert.extensions = vec![
        RelationTable::new("revoked", 2, [] as [GroundLiteral; 0]),
        RelationTable::new("denied", 2, [] as [GroundLiteral; 0]),
    ];
    cert.supports = SupportWitness(vec![]);
    cert.limits_decl.cert_facts = 0;
    cert.limits_decl.support_edges = 0;
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "cert_edb_mismatch",
    );
}

// ====================== support / closure / domain rejects ===================

/// `cert_unsupported` (junk) — a sealed `denied` fact no support edge justifies.
#[test]
fn reject_cert_unsupported_junk_fact() {
    let mut cert = valid_cert();
    cert.extensions = cert
        .extensions
        .into_iter()
        .map(|t| {
            if t.pred.bytes() == b"denied" {
                RelationTable::new(
                    "denied",
                    2,
                    [g("denied", &["s2", "a2"]), g("denied", &["s1", "a1"])],
                )
            } else {
                t
            }
        })
        .collect();
    cert.limits_decl.cert_facts = 3;
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "cert_unsupported",
    );
}

/// `cert_not_closed` — a satisfied grounding's head is missing from the table.
#[test]
fn reject_cert_not_closed_missing_head() {
    let program = base_program();
    // EDB-of-record `revoked` includes BOTH s2a2 and s1a1, so the sealed revoked table
    // (matching it) is EDB-valid; but the cert OMITS the derivable denied(s1,a1).
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(
        b"revoked".to_vec(),
        vec![g("revoked", &["s2", "a2"]), g("revoked", &["s1", "a1"])],
    );
    edb.insert(b"grant".to_vec(), vec![g("grant", &["s1", "a1"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["grant", "revoked"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };

    let mut cert = valid_cert();
    cert.extensions = vec![
        RelationTable::new(
            "revoked",
            2,
            [g("revoked", &["s2", "a2"]), g("revoked", &["s1", "a1"])],
        ),
        RelationTable::new("denied", 2, [g("denied", &["s2", "a2"])]),
    ];
    // revoked is EDB (exempt) — only the denied(s2,a2) IDB fact needs a support edge.
    cert.supports = SupportWitness(vec![SupportEdge {
        fact: g("denied", &["s2", "a2"]),
        clause: ClauseId::new(C_DENIED_RULE),
        subst: subst2(("S", "s2"), ("A", "a2")),
        body_refs: vec![SupportRef::LowerStratum {
            cert: CertId(0),
            atom: g("revoked", &["s2", "a2"]),
        }],
        rank: 1,
    }]);
    cert.limits_decl.cert_facts = 3;
    cert.limits_decl.support_edges = 1;
    bind_cert(&mut cert, &program);
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &g("permit", &["s1", "a1"]),
        &permit_derivation(cert),
        &(),
        &prof,
        &cx,
    );
    // Closure over denied_rule for (s1,a1): body revoked(s1,a1) is true ⇒ head
    // denied(s1,a1) must be present ⇒ missing ⇒ cert_not_closed.
    assert_reject(outcome, "cert_not_closed");
}

/// `cert_out_of_domain` — a sealed extension row carries a value outside ∪domains
/// (the §3.4 domain-coverage gate; the head-value path is below in the exploit test).
#[test]
fn reject_cert_out_of_domain_row_value() {
    let mut cert = valid_cert();
    // Shrink the action domain so a2 (a sealed row value) is no longer covered.
    cert.domains = vec![
        FiniteDomain::new(sym("subject"), [v("s1"), v("s2")]),
        FiniteDomain::new(sym("action"), [v("a1")]), // a2 omitted
    ];
    cert.limits_decl.domain_values = 3;
    bind_cert(&mut cert, &base_program());
    assert_reject(
        run(&base_program(), &permit_derivation(cert)),
        "cert_out_of_domain",
    );
}

// ================================================================================
// ===================  THE 6 ADVERSARIAL EXPLOIT REGRESSIONS  ====================
// Each was a MACHINE-CONFIRMED unsound Accept against the pre-redesign checker; each
// MUST now REJECT with the §7 code.
// ================================================================================

/// Lens 1 — closure-completeness: a non-cited defining clause `d(z):-base(x)` derives
/// d(z) that the cert OMITS from E; the old closure (driven by support-cited clauses)
/// never enumerated it. Now closure enumerates ALL defining clauses of a sealed head
/// from the trusted program → it finds the missing d(z) head → cert_not_closed.
#[test]
fn exploit_closure_completeness_uncited_clause() {
    let program = MapProgram::new()
        .with("base_x", Clause::fact(Goal::new("base", [t("x")])))
        .with("base_y", Clause::fact(Goal::new("base", [t("y")])))
        .with(
            "c_d1",
            Clause::new(
                Goal::new("d", [Term::var("X")]),
                [Goal::new("base", [Term::var("X")])],
            ),
        )
        .with(
            "c_d2",
            Clause::new(Goal::new("d", [t("z")]), [Goal::new("base", [t("x")])]),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("d", [t("z")])],
            ),
        );

    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"base".to_vec(), vec![g("base", &["x"]), g("base", &["y"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["base"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };

    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("base"), sym("d")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("u"), [v("x"), v("y"), v("z")])],
        extensions: vec![
            RelationTable::new("base", 1, [g("base", &["x"]), g("base", &["y"])]),
            RelationTable::new("d", 1, [g("d", &["x"]), g("d", &["y"])]), // OMITS d(z)
        ],
        supports: SupportWitness(vec![
            SupportEdge {
                fact: g("base", &["x"]),
                clause: ClauseId::new("base_x"),
                subst: BTreeMap::new(),
                body_refs: vec![],
                rank: 0,
            },
            SupportEdge {
                fact: g("base", &["y"]),
                clause: ClauseId::new("base_y"),
                subst: BTreeMap::new(),
                body_refs: vec![],
                rank: 0,
            },
            SupportEdge {
                fact: g("d", &["x"]),
                clause: ClauseId::new("c_d1"),
                subst: subst1(("X", "x")),
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("base", &["x"]),
                }],
                rank: 1,
            },
            SupportEdge {
                fact: g("d", &["y"]),
                clause: ClauseId::new("c_d1"),
                subst: subst1(("X", "y")),
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("base", &["y"]),
                }],
                rank: 1,
            },
        ]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 4,
            domain_values: 3,
            support_edges: 4,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);

    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("d", &["z"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    // c_d2 (uncited) derives d(z); closure over ALL defining clauses finds the gap.
    assert_reject(outcome, "cert_not_closed");
}

/// Lens 2 — fabricated same-stratum rank: mutual recursion `p:-q. q:-p.` (LM={}) with
/// edges citing each other at claimed rank 0 < own rank 1. The rank-consistency
/// pre-pass requires the claimed rank to EQUAL the dep's own edge rank (1≠0) → reject.
#[test]
fn exploit_fabricated_same_stratum_rank() {
    let program = MapProgram::new()
        .with(
            "p_rule",
            Clause::new(Goal::new("p", []), [Goal::new("q", [])]),
        )
        .with(
            "q_rule_def",
            Clause::new(Goal::new("q", []), [Goal::new("p", [])]),
        )
        .with(
            "top_rule",
            Clause::with_neg(Goal::new("top", []), [] as [Goal; 0], [Goal::new("p", [])]),
        );

    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("p"), sym("q")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![],
        extensions: vec![
            RelationTable::new("p", 0, [g("p", &[])]),
            RelationTable::new("q", 0, [g("q", &[])]),
        ],
        supports: SupportWitness(vec![
            SupportEdge {
                fact: g("p", &[]),
                clause: ClauseId::new("p_rule"),
                subst: BTreeMap::new(),
                body_refs: vec![SupportRef::SameStratum {
                    fact: g("q", &[]),
                    rank: 0, // FABRICATED: q's own edge rank is 1
                }],
                rank: 1,
            },
            SupportEdge {
                fact: g("q", &[]),
                clause: ClauseId::new("q_rule_def"),
                subst: BTreeMap::new(),
                body_refs: vec![SupportRef::SameStratum {
                    fact: g("p", &[]),
                    rank: 0, // FABRICATED: p's own edge rank is 1
                }],
                rank: 1,
            },
        ]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 0,
            support_edges: 2,
            rule_groundings: 10,
            join_steps: 10,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);

    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("top", &[]),
            clause: ClauseId::new("top_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("p", &[]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&[], BTreeMap::new())),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("top", &[]), &deriv, &(), &prof, &cx);
    assert_reject(outcome, "cert_unsupported");
}

/// The classic `p:-p` trap (kept): {p} is closed but unfounded; the same-stratum edge
/// cites p at rank 0 = p's own rank 0 (consistent) but NOT strictly < 0 → reject.
#[test]
fn exploit_p_implies_p_trap() {
    let program = MapProgram::new()
        .with(
            "p_self",
            Clause::new(Goal::new("p", []), [Goal::new("p", [])]),
        )
        .with(
            "q_rule",
            Clause::with_neg(Goal::new("q", []), [] as [Goal; 0], [Goal::new("p", [])]),
        );
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("p")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![],
        extensions: vec![RelationTable::new("p", 0, [g("p", &[])])],
        supports: SupportWitness(vec![SupportEdge {
            fact: g("p", &[]),
            clause: ClauseId::new("p_self"),
            subst: BTreeMap::new(),
            body_refs: vec![SupportRef::SameStratum {
                fact: g("p", &[]),
                rank: 0,
            }],
            rank: 0,
        }]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 0,
            support_edges: 1,
            rule_groundings: 10,
            join_steps: 10,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("p", &[]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&[], BTreeMap::new())),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    assert_reject(outcome, "cert_unsupported");
}

/// Lens 3 — empty-IDB-clause: `denied(S):-revoked(S)` derives denied(s2) but the cert
/// seals denied={} and cites no denied edge. The old closure (support-cited clauses)
/// never enumerated denied_rule. Now closure enumerates it from the program → the
/// satisfied grounding denied(s2):-revoked(s2) has a missing head → cert_not_closed.
#[test]
fn exploit_empty_idb_defining_clause() {
    let program = MapProgram::new()
        .with(
            "revoked_fact",
            Clause::fact(Goal::new("revoked", [t("s2")])),
        )
        .with(
            "denied_rule",
            Clause::new(
                Goal::new("denied", [Term::var("S")]),
                [Goal::new("revoked", [Term::var("S")])],
            ),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("denied", [t("s2")])],
            ),
        );
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"revoked".to_vec(), vec![g("revoked", &["s2"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["revoked"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("revoked"), sym("denied")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("s2")])],
        extensions: vec![
            RelationTable::new("revoked", 1, [g("revoked", &["s2"])]),
            RelationTable::new("denied", 1, [] as [GroundLiteral; 0]), // EMPTY
        ],
        supports: SupportWitness(vec![SupportEdge {
            fact: g("revoked", &["s2"]),
            clause: ClauseId::new("revoked_fact"),
            subst: BTreeMap::new(),
            body_refs: vec![],
            rank: 0,
        }]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 1,
            support_edges: 1,
            rule_groundings: 100,
            join_steps: 100,
            cert_bytes: 512,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("denied", &["s2"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    assert_reject(outcome, "cert_not_closed");
}

/// Lens 3b — unsealed positive body literal: `denied(S):-base(S)` where `base` is a
/// real extensional EDB predicate the cert does NOT seal. The old closure treated the
/// unsealed `base(s1)` as false and under-fired. Now §3.2 scope-closure rejects the
/// cert: denied's defining clause touches an unsealed, non-theory predicate.
#[test]
fn exploit_unsealed_body_literal() {
    let program = MapProgram::new()
        .with("pre_fact", Clause::fact(Goal::new("pre", [t("s9")])))
        .with(
            "denied_pre",
            Clause::new(
                Goal::new("denied", [Term::var("S")]),
                [Goal::new("pre", [Term::var("S")])],
            ),
        )
        .with(
            "denied_base",
            Clause::new(
                Goal::new("denied", [Term::var("S")]),
                [Goal::new("base", [Term::var("S")])],
            ),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("denied", [t("s1")])],
            ),
        );
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"pre".to_vec(), vec![g("pre", &["s9"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        // `base` is extensional but NOT sealed by the cert below.
        leaves: Box::new(NegLeaves::new(&["pre", "base"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("pre"), sym("denied")]), // base NOT sealed
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("s1"), v("s9")])],
        extensions: vec![
            RelationTable::new("pre", 1, [g("pre", &["s9"])]),
            RelationTable::new("denied", 1, [g("denied", &["s9"])]),
        ],
        supports: SupportWitness(vec![
            SupportEdge {
                fact: g("pre", &["s9"]),
                clause: ClauseId::new("pre_fact"),
                subst: BTreeMap::new(),
                body_refs: vec![],
                rank: 0,
            },
            SupportEdge {
                fact: g("denied", &["s9"]),
                clause: ClauseId::new("denied_pre"),
                subst: subst1(("S", "s9")),
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("pre", &["s9"]),
                }],
                rank: 1,
            },
        ]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 2,
            support_edges: 2,
            rule_groundings: 100,
            join_steps: 100,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("denied", &["s1"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    // denied_base's body `base(S)` is unsealed & not theory-owned ⇒ prefix not
    // downward-closed.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// Lens 4 (Round 2) — domain omission via an un-domain-checked builtin ref.
/// `flag(Y):-lt(Y,s1)`, `link(X,Y):-src(X),lt(Y,s1)`; the cert smuggles `m` through a
/// Builtin support ref while OMITTING `m` from every domain. The SAFETY gate (Round 3)
/// now catches the unsafe existential `Y` (bound only by the builtin `lt`) FIRST with
/// `cert_scope_incomplete` — the more precise root-cause rejection, which subsumes the
/// Round-2 `cert_out_of_domain` (both are sound rejections of the same exploit).
#[test]
fn exploit_domain_omission_via_builtin_ref() {
    let program = MapProgram::new()
        .with("src_s1", Clause::fact(Goal::new("src", [t("s1")])))
        .with(
            "flag_rule",
            Clause::new(
                Goal::new("flag", [Term::var("Y")]),
                [Goal::new("lt", [Term::var("Y"), t("s1")])],
            ),
        )
        .with(
            "link_rule",
            Clause::new(
                Goal::new("link", [Term::var("X"), Term::var("Y")]),
                [
                    Goal::new("src", [Term::var("X")]),
                    Goal::new("lt", [Term::var("Y"), t("s1")]),
                ],
            ),
        )
        .with(
            "denied_rule",
            Clause::new(
                Goal::new("denied", [Term::var("X")]),
                [
                    Goal::new("link", [Term::var("X"), Term::var("Y")]),
                    Goal::new("flag", [Term::var("Y")]),
                ],
            ),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("denied", [t("s1")])],
            ),
        );
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"src".to_vec(), vec![g("src", &["s1"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["src"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("src"), sym("flag"), sym("link"), sym("denied")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("s1"), v("s2")])], // `m` OMITTED
        extensions: vec![
            RelationTable::new("src", 1, [g("src", &["s1"])]),
            RelationTable::new("flag", 1, [g("flag", &["m"])]),
            RelationTable::new("link", 2, [g("link", &["s1", "m"])]),
            RelationTable::new("denied", 1, [] as [GroundLiteral; 0]),
        ],
        supports: SupportWitness(vec![
            SupportEdge {
                fact: g("src", &["s1"]),
                clause: ClauseId::new("src_s1"),
                subst: BTreeMap::new(),
                body_refs: vec![],
                rank: 0,
            },
            SupportEdge {
                fact: g("flag", &["m"]),
                clause: ClauseId::new("flag_rule"),
                subst: subst1(("Y", "m")),
                body_refs: vec![SupportRef::Builtin {
                    atom: g("lt", &["m", "s1"]),
                }],
                rank: 1,
            },
            SupportEdge {
                fact: g("link", &["s1", "m"]),
                clause: ClauseId::new("link_rule"),
                subst: subst2(("X", "s1"), ("Y", "m")),
                body_refs: vec![
                    SupportRef::LowerStratum {
                        cert: CertId(0),
                        atom: g("src", &["s1"]),
                    },
                    SupportRef::Builtin {
                        atom: g("lt", &["m", "s1"]),
                    },
                ],
                rank: 1,
            },
        ]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 3,
            domain_values: 2,
            support_edges: 3,
            rule_groundings: 10_000,
            join_steps: 100_000,
            cert_bytes: 8_192,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("denied", &["s1"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    // `Y` is bound only by the builtin `lt` (unsafe) ⇒ the safety gate rejects first.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// Lens 5/6 — context-binding & EDB omission: a cert with an EMPTY `revoked` table
/// (omitting the real EDB fact) accepted under the zero-context `check()`. Now the
/// plain `check()` hard-rejects cert_context_unbound (covered above); under a bound
/// context, the EDB gate catches the omitted fact as cert_edb_mismatch (covered by
/// `reject_cert_edb_mismatch_omitted_edb_fact`). This test asserts the bound-context
/// EDB path on the exact exploit shape (2-arg revoked/denied).
#[test]
fn exploit_edb_omission_bound_context() {
    let program = base_program();
    let mut cert = valid_cert();
    cert.extensions = vec![
        RelationTable::new("revoked", 2, [] as [GroundLiteral; 0]), // omit revoked(s2,a2)
        RelationTable::new("denied", 2, [] as [GroundLiteral; 0]),
    ];
    cert.supports = SupportWitness(vec![]);
    cert.limits_decl.cert_facts = 0;
    cert.limits_decl.support_edges = 0;
    bind_cert(&mut cert, &program);
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(
        &program,
        &g("permit", &["s1", "a1"]),
        &permit_derivation(cert),
        &(),
        &profile(),
        &cx,
    );
    assert_reject(outcome, "cert_edb_mismatch");
}

// ================================================================================
// ============  ROUND 3: ADMISSIBLE-FRAGMENT GATE REGRESSIONS  ===================
// 4 NEW machine-confirmed unsound Accepts (the checker proved the model obligations
// but did NOT enforce ADR 0007's admissible fragment). Each MUST now REJECT.
// ================================================================================

/// Round-3 Lens "neg-premise" — PARTITION gate. A theory-owned (builtin) predicate
/// `lt` is placed in the cert scope with a FABRICATED empty table; `\+ lt(0,1)` reads
/// the empty table and accepts though lt(0,1) Holds. The partition gate now rejects:
/// a stratum prefix may not seal a theory-owned predicate (builtins are decided live).
#[test]
fn exploit_partition_theory_owned_in_scope() {
    // risky(X) :- \+ lt(0, X).  (head risky NOT sealed; lt theory-owned)
    let program = MapProgram::new().with(
        "r1",
        Clause::with_neg(
            Goal::new("risky", [Term::var("X")]),
            [] as [Goal; 0],
            [Goal::new("lt", [t("0"), Term::var("X")])],
        ),
    );
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&[], BTreeMap::new())),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("lt")]), // theory-owned pred sealed (illegal)
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("0"), v("1")])],
        extensions: vec![RelationTable::new("lt", 2, [] as [GroundLiteral; 0])], // FABRICATED empty
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 0,
            domain_values: 2,
            support_edges: 0,
            rule_groundings: 100,
            join_steps: 100,
            cert_bytes: 512,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("risky", &["1"]),
            clause: ClauseId::new("r1"),
            subst: subst1(("X", "1")),
            premises: vec![Premise::Neg {
                atom: g("lt", &["0", "1"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("risky", &["1"]), &deriv, &(), &prof, &cx);
    // lt is theory-owned ⇒ may not be sealed ⇒ the partition gate rejects.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// Round-3 Lens "support-rank" — LowerStratum intra-prefix laundering. `p:-q. q:-p.`
/// (LM={}) sealed E={p,q}, with the intra-prefix positive cycle cited as `LowerStratum`
/// (a rank-free escape hatch) instead of `SameStratum`. The intra-prefix ban now
/// rejects a LowerStratum ref to a sealed INTENSIONAL predicate ⇒ cert_unsupported.
#[test]
fn exploit_lowerstratum_intra_prefix_cycle() {
    let program = MapProgram::new()
        .with("c_p", Clause::new(Goal::new("p", []), [Goal::new("q", [])]))
        .with("c_q", Clause::new(Goal::new("q", []), [Goal::new("p", [])]))
        .with(
            "win",
            Clause::with_neg(Goal::new("win", []), [] as [Goal; 0], [Goal::new("p", [])]),
        );
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&[], BTreeMap::new())), // p,q are IDB, no EDB
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(0, [sym("p"), sym("q")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![],
        extensions: vec![
            RelationTable::new("p", 0, [g("p", &[])]),
            RelationTable::new("q", 0, [g("q", &[])]),
        ],
        supports: SupportWitness(vec![
            SupportEdge {
                fact: g("p", &[]),
                clause: ClauseId::new("c_p"),
                subst: BTreeMap::new(),
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("q", &[]),
                }],
                rank: 0,
            },
            SupportEdge {
                fact: g("q", &[]),
                clause: ClauseId::new("c_q"),
                subst: BTreeMap::new(),
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("p", &[]),
                }],
                rank: 0,
            },
        ]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 2,
            domain_values: 0,
            support_edges: 2,
            rule_groundings: 10,
            join_steps: 10,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("win", &[]),
            clause: ClauseId::new("win"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("p", &[]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("win", &[]), &deriv, &(), &prof, &cx);
    // The intra-prefix positive cycle laundered through LowerStratum is rejected.
    assert_reject(outcome, "cert_unsupported");
}

/// Round-3 Lens "closure-body-truth" — SAFETY gate. `denied(X):-src(X),lt(m,Y),lt(Y,o)`
/// has a body-only existential `Y` bound only by the builtin `lt`; the witness `Y='n'`
/// lies outside ∪domains, so closure under-fired and `\+ denied(s1)` was accepted
/// though denied(s1) ∈ LM. The safety gate now rejects: `Y` is not bound by any
/// positive sealed-relation body literal ⇒ cert_scope_incomplete.
#[test]
fn exploit_unsafe_existential_builtin_var() {
    let program = MapProgram::new()
        .with("src_s1", Clause::fact(Goal::new("src", [t("s1")])))
        .with(
            "denied_rule",
            Clause::new(
                Goal::new("denied", [Term::var("X")]),
                [
                    Goal::new("src", [Term::var("X")]),
                    Goal::new("lt", [t("m"), Term::var("Y")]),
                    Goal::new("lt", [Term::var("Y"), t("o")]),
                ],
            ),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("denied", [t("s1")])],
            ),
        );
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(b"src".to_vec(), vec![g("src", &["s1"])]);
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["src"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("src"), sym("denied")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("s1"), v("m"), v("o")])], // 'n' OMITTED
        extensions: vec![
            RelationTable::new("src", 1, [g("src", &["s1"])]),
            RelationTable::new("denied", 1, [] as [GroundLiteral; 0]), // EMPTY
        ],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 3,
            support_edges: 0,
            rule_groundings: 10_000,
            join_steps: 100_000,
            cert_bytes: 8_192,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: g("denied", &["s1"]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    // `Y` is an unsafe existential (bound only by the builtin lt) ⇒ safety gate rejects.
    assert_reject(outcome, "cert_scope_incomplete");
}

/// Round-3 Lens "domain-finiteness". `r(box(box(X))):-e(box(X))` binds `X` to a STRICT
/// SUB-TERM of the EDB compound `box(secret)`; that sub-term `secret` is in NO
/// whole-argument domain value, so the self-enumerating closure under-fired and
/// `\+ r(box(box(secret)))` was accepted though r(box(box(secret))) ∈ LM. The function-free
/// gate rejected it `cert_scope_incomplete`. Since #2759 (the constructor-acyclic fragment)
/// the scope gate admits it, and the closure join rejects the under-sealed cert
/// `cert_not_closed` (vectors/negation.json's `round3_structural_subterm_under_fire`).
#[test]
fn exploit_structural_subterm_under_fire() {
    // box(inner) compound term, and the two whole-argument compound VALUES it builds.
    let boxed = |inner: Term| Term::tuple([Term::atom(b"box".to_vec()), inner]);
    let val_box1 = boxed(t("secret")).erase_ground().expect("ground"); // box(secret)
    let val_box2 = boxed(boxed(t("secret"))).erase_ground().expect("ground"); // box(box(secret))

    let program = MapProgram::new()
        .with("e_fact", Clause::fact(Goal::new("e", [boxed(t("secret"))])))
        .with(
            // r(box(box(X))) :- e(box(X)).  — X unifies with the SUB-term `secret`.
            "r_rule",
            Clause::new(
                Goal::new("r", [boxed(boxed(Term::var("X")))]),
                [Goal::new("e", [boxed(Term::var("X"))])],
            ),
        )
        .with(
            "q_rule",
            Clause::with_neg(
                Goal::new("q", []),
                [] as [Goal; 0],
                [Goal::new("r", [Term::from_value(&val_box2)])],
            ),
        );
    // e is the EDB-of-record leaf; its snapshot covers e(box(secret)).
    let mut edb: BTreeMap<Vec<u8>, Vec<GroundLiteral>> = BTreeMap::new();
    edb.insert(
        b"e".to_vec(),
        vec![GroundLiteral::new("e", [val_box1.clone()])],
    );
    let prof = CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(NegLeaves::new(&["e"], edb)),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    };
    let mut cert = ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("e"), sym("r")]),
        program_hash: [0u8; 32],
        profile_hash: [0u8; 32],
        ctx_hash: [0u8; 32],
        theory_config_hash: [0u8; 32],
        edb_snapshot_hashes: vec![],
        // whole-arg values: box(secret) and box(box(secret)); `secret` OMITTED.
        domains: vec![FiniteDomain::new(
            sym("u"),
            [val_box1.clone(), val_box2.clone()],
        )],
        extensions: vec![
            RelationTable::new("e", 1, [GroundLiteral::new("e", [val_box1.clone()])]),
            RelationTable::new("r", 1, [] as [GroundLiteral; 0]), // CLAIMED EMPTY
        ],
        supports: SupportWitness(vec![]),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: None,
        limits_decl: CertSizeDecl {
            cert_facts: 1,
            domain_values: 2,
            support_edges: 0,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
    };
    bind_cert(&mut cert, &program);
    let deriv = Derivation::with_closed_world(
        [Node::Rule {
            conclusion: g("q", &[]),
            clause: ClauseId::new("q_rule"),
            subst: BTreeMap::new(),
            premises: vec![Premise::Neg {
                atom: GroundLiteral::new("r", [val_box2.clone()]),
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    );
    let cx = bound_context(&program);
    let outcome = check_with_cert_context(&program, &g("q", &[]), &deriv, &(), &prof, &cx);
    // #2759: r_rule constructs on no cycle, so the scope gate admits it; the closure JOIN binds X by
    // unifying e(box(X)) with the sealed row, emits the satisfied grounding, and finds its head
    // r(box(box(secret))) absent from the claimed-empty table ⇒ cert_not_closed. The under-fire this
    // exploit found cannot recur, now that the join (#1829) replaced the self-enumeration.
    assert_reject(outcome, "cert_not_closed");
}

// ============ canonical form: gate 1b (issue #839, struct-literal certs) ============
// The cert's three binary-searched collections carry a sorted+deduped invariant that
// pub fields let a struct literal violate silently: `contains`/`seals` then report
// present values absent per lookup luck (the consumer-measured symptom: an arbitrary
// `cert_out_of_domain` with every correct value in the list). Gate 1b rejects the
// malformed representation deterministically, with a detail naming the constructor,
// before any gate consults a lookup.

/// An unsorted `FiniteDomain` struct literal is rejected by the canonical-form gate
/// (deterministic `cert_out_of_domain` naming `FiniteDomain::new`), never admitted to
/// defeat binary-search membership.
#[test]
fn reject_non_canonical_domain_struct_literal() {
    let mut cert = valid_cert();
    // s2 before s1: compiles fine, violates the sorted+deduped invariant.
    cert.domains[0] = FiniteDomain {
        type_tag: sym("subject"),
        values: vec![v("s2"), v("s1")],
    };
    let outcome = run(&base_program(), &permit_derivation(cert));
    match outcome.verdict {
        Verdict::Reject { code, detail } => {
            assert_eq!(code.code(), "cert_out_of_domain", "wrong code ({detail})");
            assert!(
                detail.contains("FiniteDomain::new"),
                "detail must name the canonicalizing constructor, got: {detail}"
            );
        }
        Verdict::Accept => panic!("expected reject, got Accept"),
    }
}

/// A duplicated domain value (sorted but not deduped) is likewise non-canonical.
#[test]
fn reject_duplicated_domain_value_struct_literal() {
    let mut cert = valid_cert();
    cert.domains[0] = FiniteDomain {
        type_tag: sym("subject"),
        values: vec![v("s1"), v("s1"), v("s2")],
    };
    cert.limits_decl.domain_values = 5;
    let outcome = run(&base_program(), &permit_derivation(cert));
    assert_reject(outcome, "cert_out_of_domain");
}

/// An unsorted scope-predicate struct literal is rejected (`cert_scope_incomplete`
/// with a detail naming `StratumPrefix::new`), never admitted to defeat `seals`.
#[test]
fn reject_non_canonical_scope_struct_literal() {
    let mut cert = valid_cert();
    // byte order: "denied" < "revoked", so this literal is reversed.
    cert.scope = StratumPrefix {
        level: 1,
        predicates: vec![sym("revoked"), sym("denied")],
    };
    let outcome = run(&base_program(), &permit_derivation(cert));
    match outcome.verdict {
        Verdict::Reject { code, detail } => {
            assert_eq!(
                code.code(),
                "cert_scope_incomplete",
                "wrong code ({detail})"
            );
            assert!(
                detail.contains("StratumPrefix::new"),
                "detail must name the canonicalizing constructor, got: {detail}"
            );
        }
        Verdict::Accept => panic!("expected reject, got Accept"),
    }
}

/// Unsorted extension rows are rejected (`cert_unsupported` with a detail naming
/// `RelationTable::new`), never admitted to defeat table membership.
#[test]
fn reject_non_canonical_extension_rows_struct_literal() {
    let mut cert = valid_cert();
    // ground_key order puts denied(s1,a1) first; this literal is reversed.
    cert.extensions[1] = RelationTable {
        pred: sym("denied"),
        arity: 2,
        rows: vec![g("denied", &["s2", "a2"]), g("denied", &["s1", "a1"])],
    };
    cert.limits_decl.cert_facts = 3;
    let outcome = run(&base_program(), &permit_derivation(cert));
    match outcome.verdict {
        Verdict::Reject { code, detail } => {
            assert_eq!(code.code(), "cert_unsupported", "wrong code ({detail})");
            assert!(
                detail.contains("RelationTable::new"),
                "detail must name the canonicalizing constructor, got: {detail}"
            );
        }
        Verdict::Accept => panic!("expected reject, got Accept"),
    }
}

/// research 0028 A18 (#3024), duplicate handling: a scope predicate repeated in SORTED order is
/// non-canonical too, because the invariant is strictly increasing. Same gate, same code as the
/// misorder (`vectors/negation.json` cert_canonical_scope_duplicated, which go and ts replay).
#[test]
fn reject_duplicated_scope_predicate_struct_literal() {
    let mut cert = valid_cert();
    cert.scope = StratumPrefix {
        level: 1,
        predicates: vec![sym("denied"), sym("denied"), sym("revoked")],
    };
    let outcome = run(&base_program(), &permit_derivation(cert));
    match outcome.verdict {
        Verdict::Reject { code, detail } => {
            assert_eq!(
                code.code(),
                "cert_scope_incomplete",
                "wrong code ({detail})"
            );
            assert!(
                detail.contains("StratumPrefix::new"),
                "detail must name the canonicalizing constructor, got: {detail}"
            );
        }
        Verdict::Accept => panic!("expected reject, got Accept"),
    }
}

/// research 0028 A18 (#3024): the same extension row twice, in sorted order, is refused by the
/// canonical-form gate exactly as a misorder is (`vectors/negation.json`
/// cert_canonical_rows_duplicated).
#[test]
fn reject_duplicated_extension_row_struct_literal() {
    let mut cert = valid_cert();
    cert.extensions[1] = RelationTable {
        pred: sym("denied"),
        arity: 2,
        rows: vec![g("denied", &["s1", "a1"]), g("denied", &["s1", "a1"])],
    };
    cert.limits_decl.cert_facts = 3;
    let outcome = run(&base_program(), &permit_derivation(cert));
    match outcome.verdict {
        Verdict::Reject { code, detail } => {
            assert_eq!(code.code(), "cert_unsupported", "wrong code ({detail})");
            assert!(
                detail.contains("RelationTable::new"),
                "detail must name the canonicalizing constructor, got: {detail}"
            );
        }
        Verdict::Accept => panic!("expected reject, got Accept"),
    }
}

// ================ ADR 0029 D9 / #1567 — the scope is a SET, and level is INERT ================
// D9 says `ClosedModelCert.scope` "generalizes from a prefix to a downward-closed set" and calls
// that the one item touching the contract surface. G2 (#1567) read the code and found the
// generalization is a semantic NO-OP: `check` reads the scope as a set at 11 sites and consults
// `level` at zero. These three tests upgrade that READ to a MEASUREMENT, with a live control.

/// `base_program` plus an UNSEALED sibling at the sealed stratum: `audited(S,A) :- revoked(S,A)`
/// sits at the same level as `denied`, so `{revoked, denied}` is no longer the level-1 PREFIX.
fn base_program_with_unsealed_sibling() -> MapProgram {
    base_program().with(
        "audited_rule",
        Clause::new(
            Goal::new("audited", [Term::var("S"), Term::var("A")]),
            [Goal::new("revoked", [Term::var("S"), Term::var("A")])],
        ),
    )
}

/// THE MEASUREMENT: a downward-closed NON-prefix scope is accepted exactly as a prefix is.
#[test]
fn non_prefix_downward_closed_scope_is_accepted_1567() {
    let program = base_program_with_unsealed_sibling();
    let mut cert = valid_cert();
    bind_cert(&mut cert, &program);
    let outcome = run(&program, &permit_derivation(cert));
    assert!(
        outcome.is_accept(),
        "a downward-closed scope that is NOT the stratum prefix must be accepted; got {outcome:?}"
    );
}

/// For a SINGLE certificate with a FULL scope (no `partial_scope`, nothing stacked), `level` is
/// not consulted: the same cert with a wrong level, in both directions, accepts. If a change makes
/// check read `level` for this certificate, this reds.
///
/// NARROWED by #3424 (research 0035 lane 8, B17). This test was named `scope_level_is_inert_1567`
/// and claimed `level` is never consulted; it built one full-scope cert only, so it stayed green
/// when the claim stopped holding. Since #1708 a partial scope must sit at its certificate's own
/// level, and since #2344 stacked certificates are verified in level order and read only a strictly
/// lower seal: there, `level` IS consulted and a wrong one changes the verdict. Those cases are
/// `a_certificates_scope_level_is_read_once_it_carries_a_partial_scope_3424`
/// (adr0030_partial_scope_guard.rs) and stacked_scope_level_3424.rs, with go and ts counterparts.
#[test]
fn scope_level_is_inert_for_a_single_full_scope_certificate_1567() {
    for level in [0u32, 7u32] {
        let mut cert = valid_cert();
        cert.scope = StratumPrefix::new(level, cert.scope.predicates.clone());
        bind_cert(&mut cert, &base_program());
        let outcome = run(&base_program(), &permit_derivation(cert));
        assert!(
            outcome.is_accept(),
            "level {level} (true prefix level is 1) must not change the verdict; got {outcome:?}"
        );
    }
}

/// CONTROL — the gate is LIVE and inspects CLAUSES: dropping `revoked` from the scope leaves
/// `denied`'s body referencing an unsealed, non-theory predicate, so the set is not
/// downward-closed and the cert is refused. Without this, the two accepts above could be a
/// gate that accepts anything.
#[test]
fn non_downward_closed_scope_is_rejected_1567() {
    let mut cert = valid_cert();
    cert.scope = StratumPrefix::new(1, [sym("denied")]);
    bind_cert(&mut cert, &base_program());
    let outcome = run(&base_program(), &permit_derivation(cert));
    assert_reject(outcome, "cert_scope_incomplete");
}

// ===================== ADR 0029 D10 / gate G5 — the RED case =====================
//
// D10 (ACCEPTED 2026-09-02): a negation certificate may be sealed over a COMPONENT's
// downward-closed program, tied to the witness that proves the ideal is closed in the
// complete program. Today it may not: `check_cert_context` recomputes `program_hash` over
// the COMPLETE live clause set (ADR 0007 §3.1), so a cert sealed over the slice is refused.
// That refusal is what these tests pin — RED-first, per G5. ⚠ The first assertion below STAYS
// red after D10, by ruling (seat:caa 2026-09-03, errata): it seals the slice while declaring NO
// decomposition, and D10's own rule is that slicing alone never buys admission. The case that goes
// GREEN is the `d10_g5_*` twin that carries the witness on both sides — in the vector it is
// `d10_slice_seal_replays_under_its_own_decomposition`, pinned by the guard at the end of this
// section. The vector's old `d10_expected: {accept: true}` landing pin was REMOVED rather than
// flipped: the design it described (recompute the analysis, derive the slice per the witness) is
// unbuildable at this tier (ADR 0004), so the pin encoded a promise that could never be kept.

/// The downward-closed SLICE of the ideal `{revoked, denied}`: the clauses defining its
/// INTENSIONAL members. `revoked` is EDB — a dependency-edge target, never a stratum member
/// (ADR 0007) — so it contributes no clause; `permit_rule` is the UPPER stratum and is out.
/// So the slice is exactly `{denied_rule}`.
fn slice_program() -> MapProgram {
    MapProgram::new().with(C_DENIED_RULE, denied_clause())
}

/// An arbitrary but fixed witness digest. The contract tier never interprets this value — it
/// compares 32 bytes for equality — so any distinct pair of arrays exercises the branch.
const W_A: Hash = [0xD1; 32];
const W_B: Hash = [0xD2; 32];

/// [`run`], but the caller declares that it ran under decomposition `w` (ADR 0029 D10).
fn run_decomposed(program: &MapProgram, deriv: &Derivation, w: Hash) -> Outcome {
    let cx = bound_context(program).with_decomposition(w);
    check_with_cert_context(
        program,
        &g("permit", &["s1", "a1"]),
        deriv,
        &(),
        &profile(),
        &cx,
    )
}

/// A cert sealed over the SLICE and tied to decomposition `w`.
fn slice_sealed_cert(w: Hash) -> ClosedModelCert {
    let mut cert = valid_cert();
    bind_cert(&mut cert, &base_program());
    cert.program_hash = program_digest(&slice_program());
    cert.decomposition_witness = Some(w);
    cert
}

fn hex32(h: Hash) -> String {
    h.iter().map(|b| format!("{b:02x}")).collect()
}

/// **THE G5 RED ASSERTION, NOW SHARPER RATHER THAN FLIPPED.** Landed in unit 1 (#1618) as *a
/// slice-sealed cert is refused today*, when the checker had no notion of a decomposition at all.
///
/// D10 did NOT flip it, and that is the point: this cert seals the slice while declaring NO
/// decomposition, so `check_cert_context` takes the `(None, _)` arm and pins the COMPLETE program
/// exactly as before. What the test now pins is stronger than what it pinned before — **slicing
/// alone never buys admission; the decomposition must be DECLARED on both ends.** The green twin
/// below is the case D10 actually opens.
#[test]
fn d10_g5_slice_sealed_cert_is_refused_today() {
    let mut cert = valid_cert();
    // The ONLY departure from `valid_cert`: sealed over the slice, not the whole program.
    cert.program_hash = program_digest(&slice_program());
    let outcome = run(&base_program(), &permit_derivation(cert));
    assert_reject(outcome, "cert_context_mismatch");
}

/// ANTI-VACUITY for the red assertion: it says nothing unless the two digests actually
/// differ. If the slice digested to the same value as the complete program, the case above
/// would be an ordinary accept wearing a reject's name.
#[test]
fn d10_g5_the_slice_digest_differs_from_the_complete_digest() {
    assert_ne!(
        program_digest(&slice_program()),
        program_digest(&base_program()),
        "the D10 red case is vacuous unless the slice and the complete program digest apart"
    );
}

/// CONTROL — the refusal above is about the PIN, not about slicing being malformed: the
/// same cert with the complete-program pin restored is ACCEPTED. Without this, the red
/// assertion is compatible with `valid_cert` having been broken by the edit.
#[test]
fn d10_g5_the_same_cert_with_the_complete_pin_is_accepted() {
    let mut cert = valid_cert();
    cert.program_hash = program_digest(&slice_program());
    cert.program_hash = program_digest(&base_program()); // put the honest pin back
    let outcome = run(&base_program(), &permit_derivation(cert));
    assert!(
        outcome.is_accept(),
        "the cert is otherwise valid; only the program_hash pin makes it fail — got {outcome:?}"
    );
}

// ===================== ADR 0029 D10 / gate G5 — the GREEN case =====================

/// **THE G5 GREEN TWIN.** The same slice seal the red case above uses, now tied to a
/// decomposition the caller's bound context also declares — and it is ACCEPTED. This is the
/// capability D10 adds, and it is the assertion that was red before the checker change.
#[test]
fn d10_g5_a_slice_seal_replays_under_its_own_decomposition() {
    let cert = slice_sealed_cert(W_A);
    let outcome = run_decomposed(&base_program(), &permit_derivation(cert), W_A);
    assert!(
        outcome.is_accept(),
        "a slice seal must replay under the decomposition that authorized it; got {outcome:?}"
    );
}

/// **CONTROL — the pin is load-bearing, not decorative.** The same cert under a DIFFERENT
/// decomposition is refused. Without this, the green twin is satisfiable by a checker that
/// accepts any slice seal whenever the context declares any decomposition at all.
#[test]
fn d10_g5_a_slice_seal_under_a_different_decomposition_is_refused() {
    let cert = slice_sealed_cert(W_A);
    let outcome = run_decomposed(&base_program(), &permit_derivation(cert), W_B);
    assert_reject(outcome, "cert_context_mismatch");
}

/// **CONTROL — the other direction.** A slice seal cannot discharge a negation in a run that
/// declares no decomposition. This is the arm that keeps a component's cert from leaking into a
/// whole-program check, which is the whole hazard D10 had to avoid re-opening.
#[test]
fn d10_g5_a_slice_seal_cannot_discharge_in_a_whole_program_run() {
    let cert = slice_sealed_cert(W_A);
    let outcome = run(&base_program(), &permit_derivation(cert));
    assert_reject(outcome, "cert_context_mismatch");
}

/// **CONTROL — D10 does not disturb the whole-program path.** An ordinary cert (no seal) is still
/// accepted even when the CALLER declares a decomposition: the `(None, _)` arm ignores the
/// context's pin entirely. Without this, D10 could have made every existing cert conditional on
/// the caller not decomposing.
#[test]
fn d10_g5_a_whole_program_cert_is_unaffected_by_a_decomposed_context() {
    let mut cert = valid_cert();
    bind_cert(&mut cert, &base_program());
    assert!(cert.decomposition_witness.is_none());
    let outcome = run_decomposed(&base_program(), &permit_derivation(cert), W_A);
    assert!(
        outcome.is_accept(),
        "a whole-program cert must be unaffected by the caller's decomposition; got {outcome:?}"
    );
}

/// **CONTROL — THE LOAD-BEARING ONE: the closure gate still fires on the slice path.** A slice
/// seal whose scope is NOT downward-closed is refused under its own name, `cert_scope_incomplete`
/// — never `cert_context_mismatch`. That is what makes a slice seal sound at all: the ideal is
/// still proved closed in the COMPLETE program, and D10 narrows only which clause set the PIN
/// covers. If this ever reds as a context mismatch, D10 has started admitting unclosed slices.
#[test]
fn d10_g5_a_slice_seal_does_not_relax_downward_closure() {
    let mut cert = slice_sealed_cert(W_A);
    // drop `revoked` from the scope: `denied`'s body then references an unsealed, non-theory
    // predicate, so the sealed set is not downward-closed in the complete program.
    cert.scope = StratumPrefix::new(1, [sym("denied")]);
    let outcome = run_decomposed(&base_program(), &permit_derivation(cert), W_A);
    assert_reject(outcome, "cert_scope_incomplete");
}

/// ANTI-VACUITY for the green twin: it says nothing unless the slice pin is the one being
/// honoured. If the slice and the complete program digested alike, the twin would pass under a
/// checker that never looked at `decomposition_witness`.
#[test]
fn d10_g5_the_green_twin_is_not_vacuous() {
    assert_ne!(
        program_digest(&slice_program()),
        program_digest(&base_program()),
        "the D10 green case is vacuous unless the slice and the complete program digest apart"
    );
    let cert = slice_sealed_cert(W_A);
    assert_eq!(
        cert.program_hash,
        program_digest(&slice_program()),
        "the green twin must actually be sealed over the SLICE"
    );
}

/// DRIFT GUARD for `vectors/negation.json`'s `d10_slice_seal_cert_context_mismatch` — the
/// PERMANENT red case: the slice digest it pins is MACHINE-DERIVED (a digest cannot be
/// hand-authored), so it is recomputed here from that vector's OWN one-clause slice and compared. The vector's
/// `denied_rule` is ARITY 1 (`denied(S) :- revoked(S)`), distinct from this file's arity-2
/// fixture — so the guard also asserts the vector's clause really has that shape, and a
/// change to either the clause or the pin reds here instead of drifting silently.
///
/// ⭐ **This guard is the ONLY thing that pins the digest's VALUE, and that is measured, not
/// assumed.** The go/ts replay of that case pins the REFUSAL, not the hex: perturbing the
/// pinned digest by one byte leaves the go replay GREEN — every hash that is not the live
/// program's produces the same `cert_context_mismatch` — while it reds THIS test. (The one
/// wrong pin the replay does catch is a hex that coincides with the complete program's
/// digest: the checker would then ACCEPT and the replay would fail loudly.) Neither half is
/// sufficient alone.
#[test]
fn d10_g5_vector_pins_the_recomputed_slice_digest() {
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/negation.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/negation.json");
    }
    let raw = std::fs::read_to_string(dir.join("vectors/negation.json")).expect("read vector");
    let doc: serde_json::Value = serde_json::from_str(&raw).expect("parse vector");

    // (a) the vector's `denied_rule` is the arity-1 clause this guard rebuilds.
    let rule = &doc["program"]["denied_rule"];
    assert_eq!(
        rule["head"]["pred"], "denied",
        "vector denied_rule head predicate"
    );
    assert_eq!(
        rule["head"]["args"].as_array().map(Vec::len),
        Some(1),
        "vector denied_rule head arity"
    );
    assert_eq!(
        rule["body"][0]["pred"], "revoked",
        "vector denied_rule body predicate"
    );
    assert_eq!(
        rule["body"][0]["args"].as_array().map(Vec::len),
        Some(1),
        "vector denied_rule body arity"
    );

    // (b) the pinned hex is exactly `program_digest` of that one-clause program.
    let json_slice = MapProgram::new().with(
        "denied_rule",
        Clause::new(
            Goal::new("denied", [Term::var("S")]),
            [Goal::new("revoked", [Term::var("S")])],
        ),
    );
    let case = doc["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|c| c["name"] == "d10_slice_seal_cert_context_mismatch")
        .expect("the D10 red case is present");
    assert_eq!(
        case["derivation"]["closed_world"][0]["program_hash"]
            .as_str()
            .expect("pinned program_hash"),
        hex32(program_digest(&json_slice)),
        "the vector's pinned slice digest drifted from the recomputed one"
    );

    // (c) the refusal, and WHY IT IS FINAL (errata, seat:caa 2026-09-03): the case declares no
    //     decomposition, so under D10 it correctly stays refused forever. The old `d10_expected`
    //     landing pin is gone; re-adding it, or a witness, reds here.
    assert_eq!(case["outcome"]["reject"], "cert_context_mismatch");
    assert!(
        case.get("d10_expected").is_none(),
        "the red case is PERMANENT — `d10_expected` was removed by the D10 errata and must stay gone"
    );
    assert!(
        case["derivation"]["closed_world"][0]
            .get("decomposition_witness")
            .is_none(),
        "the red case must declare NO decomposition — that is the whole reason its verdict is final"
    );
    // and the case must NOT override the context — the derived (complete-program) context
    // is precisely what the slice pin has to disagree with.
    assert!(
        case.get("cert_context").is_none(),
        "the D10 case must use the derived context, not an override"
    );
}

/// DRIFT GUARD for the GREEN twin, `d10_slice_seal_replays_under_its_own_decomposition`: it is
/// the red case PLUS the witness on both sides and nothing else. Pinned structurally rather than
/// by prose — the two cases' derivations must be byte-identical, the green cert must equal the
/// red cert once its witness is removed, the same machine-derived slice digest must be pinned,
/// the witness must be carried identically on cert and context, and the verdict must be Accept.
/// A green case that drifted from its twin (a second clause, a different scope, an overridden
/// pin) would still replay green in go/ts while pinning something other than "D10 admits THIS
/// seal under ITS decomposition" — this is what stops that.
#[test]
fn d10_g5_vector_green_twin_is_the_red_case_plus_the_witness() {
    let mut dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/negation.json").exists() {
            break;
        }
        assert!(dir.pop(), "could not locate vectors/negation.json");
    }
    let raw = std::fs::read_to_string(dir.join("vectors/negation.json")).expect("read vector");
    let doc: serde_json::Value = serde_json::from_str(&raw).expect("parse vector");
    let cases = doc["cases"].as_array().expect("cases");
    let find = |name: &str| {
        cases
            .iter()
            .find(|c| c["name"] == name)
            .unwrap_or_else(|| panic!("vector case {name} is present"))
    };
    let red = find("d10_slice_seal_cert_context_mismatch");
    let green = find("d10_slice_seal_replays_under_its_own_decomposition");

    // (a) the verdict D10 exists to produce, in the vector every core replays.
    assert_eq!(
        green["outcome"], "accept",
        "the green twin is ACCEPTED under its own decomposition"
    );

    // (b) the witness is carried IDENTICALLY on the cert and the bound context — the (Some a,
    //     Some b), a == b arm — and nothing else about the context is overridden.
    let w_cert = green["derivation"]["closed_world"][0]["decomposition_witness"]
        .as_str()
        .expect("green cert carries a decomposition_witness");
    let cx = green["cert_context"]
        .as_object()
        .expect("green case binds a cert_context");
    assert_eq!(
        cx.len(),
        1,
        "only the decomposition is overridden; every other pin stays derived"
    );
    assert_eq!(
        cx["decomposition_witness"], w_cert,
        "cert and context carry the SAME witness"
    );
    assert_eq!(w_cert.len(), 64, "a 32-byte witness digest, hex");
    assert_eq!(
        w_cert,
        hex32(W_A),
        "the vector's witness is this file's W_A, so the arms line up"
    );

    // (c) the SAME machine-derived slice digest as the red case — recomputed, never copied.
    let json_slice = MapProgram::new().with(
        "denied_rule",
        Clause::new(
            Goal::new("denied", [Term::var("S")]),
            [Goal::new("revoked", [Term::var("S")])],
        ),
    );
    assert_eq!(
        green["derivation"]["closed_world"][0]["program_hash"]
            .as_str()
            .expect("pin"),
        hex32(program_digest(&json_slice)),
        "the green twin's pinned slice digest drifted from the recomputed one"
    );

    // (d) byte-identical to the red case EXCEPT the seal: same claim, same derivation nodes,
    //     same cert once the witness is removed.
    assert_eq!(green["claim"], red["claim"]);
    assert_eq!(green["derivation"]["nodes"], red["derivation"]["nodes"]);
    assert_eq!(green["derivation"]["root"], red["derivation"]["root"]);
    let mut stripped = green["derivation"]["closed_world"][0].clone();
    stripped
        .as_object_mut()
        .expect("cert object")
        .remove("decomposition_witness");
    assert_eq!(
        stripped, red["derivation"]["closed_world"][0],
        "the green cert must be the red cert plus the witness and NOTHING else"
    );
}

// ============================ #2565: the world memo ============================
// `seat:caa`'s ruling on #2565 term 1: the checker's `WorldMemo` may serve a closed world's
// verification again only for an EQUAL world under the same program, profile and ctx objects, the
// same `CertContext` and the same `CheckLimits`; anything else re-verifies. Each row below compares
// the memo's verdict with a fresh `check_with_cert_context`, to the byte.
mod world_memo_2565 {
    use super::*;
    use logos_contract::{check_with_cert_memo, WorldMemo};

    fn permit() -> GroundLiteral {
        g("permit", &["s1", "a1"])
    }

    fn fresh(
        program: &MapProgram,
        prof: &CheckProfile<()>,
        claim: &GroundLiteral,
        deriv: &Derivation,
    ) -> Outcome {
        check_with_cert_context(program, claim, deriv, &(), prof, &bound_context(program))
    }

    /// One change each to the valid certificate: a table row, a domain value, a support edge's
    /// rank, a pin, a size declaration.
    fn mutations() -> Vec<(&'static str, ClosedModelCert)> {
        let row = {
            let mut c = valid_cert();
            c.extensions[1] = RelationTable::new(
                "denied",
                2,
                [g("denied", &["s1", "a1"]), g("denied", &["s2", "a2"])],
            );
            c
        };
        let domain = {
            let mut c = valid_cert();
            c.domains[0] = FiniteDomain::new(sym("subject"), [v("s1"), v("s3")]);
            c
        };
        let rank = {
            let mut c = valid_cert();
            c.supports.0[0].rank = 2;
            c
        };
        let pin = {
            let mut c = valid_cert();
            c.program_hash[0] ^= 1;
            c
        };
        let size = {
            let mut c = valid_cert();
            c.limits_decl.cert_facts = 3;
            c
        };
        vec![
            ("a table row", row),
            ("a domain value", domain),
            ("a support rank", rank),
            ("a pin", pin),
            ("a size declaration", size),
        ]
    }

    #[test]
    fn a_world_cited_by_many_answers_is_verified_once_2565() {
        let program = base_program();
        let prof = profile();
        let cx = bound_context(&program);
        let deriv = permit_derivation(valid_cert());
        let mut memo = WorldMemo::new();
        for _ in 0..5 {
            let outcome =
                check_with_cert_memo(&program, &permit(), &deriv, &(), &prof, &cx, &mut memo);
            assert_eq!(outcome.verdict, Verdict::Accept);
        }
        assert_eq!(
            memo.certificates_verified(),
            1,
            "five answers citing one certificate verify it once"
        );
    }

    #[test]
    fn a_changed_certificate_is_a_miss_with_the_fresh_verdict_2565() {
        let program = base_program();
        let prof = profile();
        let cx = bound_context(&program);
        let valid = permit_derivation(valid_cert());
        let mut memo = WorldMemo::new();
        let first = check_with_cert_memo(&program, &permit(), &valid, &(), &prof, &cx, &mut memo);
        assert_eq!(first.verdict, Verdict::Accept);
        // The control, exact: which single changes a fresh check rejects. The other two (a support
        // rank still above its premises', a size declaration above the real size) are changes the
        // checker ACCEPTS, and they must miss all the same: the memo keys on the certificate, never
        // on the verdict.
        let rejecting = ["a table row", "a domain value", "a pin"];
        for (what, cert) in mutations() {
            let before = memo.certificates_verified();
            let deriv = permit_derivation(cert);
            let memoized =
                check_with_cert_memo(&program, &permit(), &deriv, &(), &prof, &cx, &mut memo);
            let expected = fresh(&program, &prof, &permit(), &deriv);
            assert_eq!(
                memoized, expected,
                "{what}: the memo's verdict is not the fresh one"
            );
            assert_eq!(
                memo.certificates_verified(),
                before + 1,
                "{what}: a changed certificate must miss"
            );
            assert_eq!(
                expected.verdict != Verdict::Accept,
                rejecting.contains(&what),
                "{what}: the control's expected verdict, {expected:?}"
            );
            // And the valid world after it misses again, with its own verdict.
            let back =
                check_with_cert_memo(&program, &permit(), &valid, &(), &prof, &cx, &mut memo);
            assert_eq!(
                back.verdict,
                Verdict::Accept,
                "{what}: the valid world after a mutation"
            );
        }
    }

    #[test]
    fn a_world_in_another_order_is_a_miss_2565() {
        let program = base_program();
        let prof = profile();
        let cx = bound_context(&program);
        let (valid, other) = (valid_cert(), mutations().swap_remove(1).1);
        let mut ab = permit_derivation(valid.clone());
        ab.closed_world = vec![valid.clone(), other.clone()].into();
        let mut ba = permit_derivation(valid.clone());
        ba.closed_world = vec![other, valid].into();
        let mut memo = WorldMemo::new();
        for deriv in [&ab, &ba, &ab] {
            let memoized =
                check_with_cert_memo(&program, &permit(), deriv, &(), &prof, &cx, &mut memo);
            assert_eq!(memoized, fresh(&program, &prof, &permit(), deriv));
        }
        assert_eq!(
            memo.certificates_verified(),
            6,
            "each reordering re-verifies both certificates"
        );
    }

    #[test]
    fn a_profile_differing_only_in_limits_is_a_miss_2565() {
        let program = base_program();
        let prof = profile();
        let mut tight = profile();
        tight.limits.max_cert_facts = 1; // the valid certificate seals two facts
        let cx = bound_context(&program);
        let deriv = permit_derivation(valid_cert());
        // The control: the limits alone change the fresh verdict.
        assert_eq!(
            fresh(&program, &prof, &permit(), &deriv).verdict,
            Verdict::Accept
        );
        let tight_fresh = fresh(&program, &tight, &permit(), &deriv);
        assert_ne!(
            tight_fresh.verdict,
            Verdict::Accept,
            "the tighter limit must reject"
        );

        let mut memo = WorldMemo::new();
        let loose = check_with_cert_memo(&program, &permit(), &deriv, &(), &prof, &cx, &mut memo);
        assert_eq!(loose.verdict, Verdict::Accept);
        let tightened =
            check_with_cert_memo(&program, &permit(), &deriv, &(), &tight, &cx, &mut memo);
        assert_eq!(tightened, tight_fresh);
        let again = check_with_cert_memo(&program, &permit(), &deriv, &(), &prof, &cx, &mut memo);
        assert_eq!(again.verdict, Verdict::Accept);
        assert_eq!(
            memo.certificates_verified(),
            3,
            "each change of profile re-verifies"
        );
    }

    #[test]
    fn a_mixed_sequence_through_one_memo_is_the_fresh_sequence_2565() {
        let program = base_program();
        let prof = profile();
        let cx = bound_context(&program);
        let grant = g("grant", &["s1", "a1"]);
        let positive = Derivation::new(
            vec![Node::Leaf {
                conclusion: grant.clone(),
                evidence: Evidence::none(),
            }],
            0,
        );
        let valid = permit_derivation(valid_cert());
        let muts = mutations();
        let row = permit_derivation(muts[0].1.clone());
        let domain = permit_derivation(muts[1].1.clone());
        let pin = permit_derivation(muts[3].1.clone());
        let permit_claim = permit();
        let steps: Vec<(&GroundLiteral, &Derivation)> = vec![
            (&permit_claim, &valid),  // miss 1
            (&grant, &positive),      // no world: the slot is not touched
            (&permit_claim, &valid),  // hit
            (&permit_claim, &row),    // miss 2
            (&permit_claim, &valid),  // miss 3
            (&grant, &positive),      // no world
            (&permit_claim, &domain), // miss 4
            (&permit_claim, &domain), // hit
            (&permit_claim, &valid),  // miss 5
            (&permit_claim, &pin),    // miss 6
            (&permit_claim, &valid),  // miss 7
        ];
        let mut memo = WorldMemo::new();
        for (i, (claim, deriv)) in steps.iter().enumerate() {
            let memoized = check_with_cert_memo(&program, claim, deriv, &(), &prof, &cx, &mut memo);
            assert_eq!(memoized, fresh(&program, &prof, claim, deriv), "step {i}");
        }
        assert_eq!(
            fresh(&program, &prof, &grant, &positive).verdict,
            Verdict::Accept,
            "the positive control accepts"
        );
        assert_eq!(
            memo.certificates_verified(),
            7,
            "seven misses, two hits, and positive answers never evict the world"
        );
    }
}
