//! ADR 0030 gate G2 — the landed state of the RED-first cases (`b1d3d5a7`, the D10 discipline).
//!
//! The five `negation.json` cases and the `derivation_wire.json` case (e) were landed RED
//! first: each pinned the pre-0030 verdict in `outcome` and the ADR 0030 verdict in a side
//! field, `adr0030_expected`. The implementing change flipped `outcome`, deleted the side
//! field, and bumped `CHECKER_VERSION` 2→3 in the same release. These tests are the drift
//! guards on the LANDED shape:
//!
//! - the five cases carry EXACTLY the ADR 0030 verdict in `outcome`, NO side field, a
//!   `partial_scope` on every cert (canonical, a sub-scope of `scope`, never an extensional
//!   predicate — D1's three invariants as far as JSON can state them), and the derived
//!   context (no override);
//! - the rs checker flips the two cases the mark flips in OPPOSITE directions BECAUSE OF THE
//!   MARK and nothing else — (a) accept → `neg_atom_partial`, (d2) `cert_not_closed` → accept —
//!   with the unmarked cert as the control in each (the same derivation, `partial_scope: None`,
//!   still gives the pre-0030 verdict);
//! - the wire case (e) is now POSITIVE: the twelve-element cert decodes to a cert carrying both
//!   the D10 witness and the partial sub-scope, its bytes are still DERIVED from the frozen
//!   ten-element cert (two trailing elements appended, nothing else moved), the eleven-element
//!   form still decodes, and the THIRTEEN-element twin is refused by ARITY — the closed
//!   posture moved by exactly one slot.
//!
//! The tri-core verdicts themselves are pinned where every other vector's are: the go and ts
//! replays and the three conformance CLIs replay the cases against `outcome`.

use logos_contract::derivation_wire::{decode_derivation_wire_v1, digest_atom};
use logos_contract::{
    check_with_cert_context, edb_table_hash, program_digest, CertContext, CertId, CertSizeDecl,
    CheckLimits, CheckProfile, Clause, ClauseId, ClosedModelCert, ClosureWitness, Derivation,
    Evidence, FiniteDomain, Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier, MapProgram, Node,
    NodeMeta, NonMemberProof, Outcome, PredicateSet, Premise, Program, RelationTable,
    StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term, Theory,
    TheoryOutcome,
};
use ontos_core::Value;
use serde_json::{json, Value as Json};
use std::collections::BTreeMap;
use std::path::PathBuf;

// ================================ the vectors ================================

fn vectors_dir() -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if dir.join("vectors/negation.json").exists() {
            return dir.join("vectors");
        }
        assert!(dir.pop(), "could not locate vectors/negation.json");
    }
}

fn load(name: &str) -> Json {
    let raw = std::fs::read_to_string(vectors_dir().join(name))
        .unwrap_or_else(|e| panic!("read vectors/{name}: {e}"));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse vectors/{name}: {e}"))
}

fn find<'a>(doc: &'a Json, list: &str, name: &str) -> &'a Json {
    let hits: Vec<&Json> = doc[list]
        .as_array()
        .unwrap_or_else(|| panic!("`{list}` is a list"))
        .iter()
        .filter(|c| c["name"] == name)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "case {name} must appear exactly once in `{list}`"
    );
    hits[0]
}

/// The five landed cases: (name, the ADR 0030 verdict — now `outcome`).
fn landed_cases() -> [(&'static str, Json); 5] {
    [
        (
            "adr0030_neg_over_partial_table",
            json!({ "reject": "neg_atom_partial" }),
        ),
        (
            "adr0030_count_over_partial_table",
            json!({ "reject": "count_over_partial" }),
        ),
        (
            "adr0030_partial_scope_not_upward_closed",
            json!({ "reject": "cert_partial_scope_invalid" }),
        ),
        (
            "adr0030_partial_table_cited_only_positively",
            json!("accept"),
        ),
        (
            "adr0030_lower_bound_table_not_closed_but_marked_partial",
            json!("accept"),
        ),
    ]
}

/// Every landed case carries the ADR 0030 verdict as `outcome`, no side field, a canonical
/// `partial_scope` inside its `scope` on every cert, no extensional predicate marked partial,
/// and the derived context.
#[test]
fn adr0030_landed_cases_carry_the_adr_verdict_and_no_side_field() {
    let doc = load("negation.json");
    let extensional: Vec<&str> = doc["extensional"]
        .as_array()
        .expect("extensional list")
        .iter()
        .map(|e| e.as_str().expect("extensional name"))
        .collect();
    for (name, verdict) in landed_cases() {
        let case = find(&doc, "cases", name);
        assert_eq!(
            case["outcome"], verdict,
            "{name}: the ADR 0030 verdict drifted"
        );
        assert!(
            case.get("adr0030_expected").is_none(),
            "{name}: the RED-first side field must be GONE once the verdict is `outcome`"
        );
        assert!(
            case.get("cert_context").is_none(),
            "{name}: the cases use the DERIVED context, never an override"
        );
        let certs = case["derivation"]["closed_world"]
            .as_array()
            .expect("closed_world");
        assert!(
            !certs.is_empty(),
            "{name}: every case carries a certificate"
        );
        for cert in certs {
            let scope: Vec<&str> = cert["scope"]["predicates"]
                .as_array()
                .expect("scope predicates")
                .iter()
                .map(|p| p.as_str().expect("predicate name"))
                .collect();
            let partial: Vec<&str> = cert["partial_scope"]["predicates"]
                .as_array()
                .unwrap_or_else(|| panic!("{name}: every case's cert carries `partial_scope`"))
                .iter()
                .map(|p| p.as_str().expect("predicate name"))
                .collect();
            assert!(
                !partial.is_empty(),
                "{name}: `partial_scope` names at least one table"
            );
            assert!(
                partial.windows(2).all(|w| w[0] < w[1]),
                "{name}: `partial_scope.predicates` must be sorted + deduped by byte order (D1.1, #839)"
            );
            for p in &partial {
                assert!(
                    scope.contains(p),
                    "{name}: `partial_scope` ⊆ `scope` (D1.1): {p}"
                );
                assert!(
                    !extensional.contains(p),
                    "{name}: an extensional table is never partial (D1.3): {p}"
                );
            }
            assert_eq!(
                cert["partial_scope"]["level"], cert["scope"]["level"],
                "{name}: the partial sub-scope names the sealed prefix's own level"
            );
        }
    }
}

// ============================ the rs checker ============================
//
// The vector's own program, rebuilt: `denied(S) :- revoked(S)`, `qa :- \+ denied(s1)` and
// `qr :- \+ revoked(s1)`; `revoked` is the only extensional predicate the cases touch.

struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _: &Symbol) -> bool {
        false
    }
    fn decide(&self, _: &GroundLiteral) -> TheoryOutcome {
        TheoryOutcome::Fails {
            code: "no_theory".into(),
        }
    }
}

struct RevokedLeaves {
    extensional: PredicateSet,
    revoked: Vec<GroundLiteral>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for RevokedLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _: &GroundLiteral, _: &Evidence, _: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _: &()) -> Option<Hash> {
        if pred.bytes() == b"revoked" {
            Some(edb_table_hash(pred, &self.revoked))
        } else if self.extensional.contains(pred) {
            Some(edb_table_hash(pred, &[]))
        } else {
            None
        }
    }
}

fn v(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn g(pred: &str, args: &[&str]) -> GroundLiteral {
    GroundLiteral::new(pred, args.iter().map(|a| v(a)))
}
fn sym(s: &str) -> Symbol {
    Symbol::new(s.as_bytes().to_vec())
}

fn program() -> MapProgram {
    MapProgram::new()
        .with(
            "denied_rule",
            Clause::new(
                Goal::new("denied", [Term::var("S")]),
                [Goal::new("revoked", [Term::var("S")])],
            ),
        )
        .with(
            "q_denied_s1",
            Clause::with_neg(
                Goal::new("qa", []),
                [],
                [Goal::new("denied", [Term::atom(b"s1".to_vec())])],
            ),
        )
        .with(
            "q_notrevoked",
            Clause::with_neg(
                Goal::new("qr", []),
                [],
                [Goal::new("revoked", [Term::atom(b"s1".to_vec())])],
            ),
        )
}

fn profile() -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(RevokedLeaves {
            extensional: PredicateSet::from_iter(["revoked"]),
            revoked: vec![g("revoked", &["s2"])],
        }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn bound_context(program: &dyn Program) -> CertContext {
    CertContext::new(program_digest(program), [1u8; 32], [2u8; 32], [3u8; 32])
}

/// The `{denied, revoked}` cert of the cases. `denied_rows` is the sealed `denied` table:
/// `[denied(s2)]` for an exact seal, `[]` for the lower bound of case (d2). `partial` is the
/// ADR 0030 mark — `Some({1, [denied]})` for the landed cases, `None` for the pre-0030 control.
fn cert(
    program: &dyn Program,
    denied_rows: Vec<GroundLiteral>,
    partial: Option<StratumPrefix>,
) -> ClosedModelCert {
    let supports: Vec<SupportEdge> = denied_rows
        .iter()
        .map(|fact| {
            let mut subst: Subst = BTreeMap::new();
            subst.insert("S".into(), Term::atom(b"s2".to_vec()));
            SupportEdge {
                fact: fact.clone(),
                clause: ClauseId::new("denied_rule"),
                subst,
                body_refs: vec![SupportRef::LowerStratum {
                    cert: CertId(0),
                    atom: g("revoked", &["s2"]),
                }],
                rank: 1,
            }
        })
        .collect();
    let cx = bound_context(program);
    ClosedModelCert {
        scope: StratumPrefix::new(1, [sym("denied"), sym("revoked")]),
        program_hash: cx.program_hash,
        profile_hash: cx.profile_hash,
        ctx_hash: cx.ctx_hash,
        theory_config_hash: cx.theory_config_hash,
        edb_snapshot_hashes: vec![],
        domains: vec![FiniteDomain::new(sym("d"), [v("s1"), v("s2")])],
        extensions: vec![
            RelationTable::new("revoked", 1, [g("revoked", &["s2"])]),
            RelationTable::new("denied", 1, denied_rows),
        ],
        limits_decl: CertSizeDecl {
            cert_facts: (1 + supports.len()) as u64,
            domain_values: 2,
            support_edges: supports.len() as u64,
            rule_groundings: 1_000,
            join_steps: 10_000,
            cert_bytes: 4_096,
        },
        supports: SupportWitness(supports),
        closure: ClosureWitness,
        decomposition_witness: None,
        partial_scope: partial,
    }
}

fn denied_partial() -> Option<StratumPrefix> {
    Some(StratumPrefix::new(1, [sym("denied")]))
}

fn neg_derivation(
    head: &str,
    clause: &str,
    atom: GroundLiteral,
    cert: ClosedModelCert,
) -> Derivation {
    Derivation::with_closed_world(
        vec![Node::Rule {
            conclusion: g(head, &[]),
            clause: ClauseId::new(clause),
            subst: Subst::new(),
            premises: vec![Premise::Neg {
                atom,
                cert: CertId(0),
                nonmember: NonMemberProof::DirectLookup,
            }],
            meta: NodeMeta::none(),
        }],
        0,
        [cert],
    )
}

fn run(claim: &str, deriv: &Derivation) -> Outcome {
    let program = program();
    let cx = bound_context(&program);
    check_with_cert_context(&program, &g(claim, &[]), deriv, &(), &profile(), &cx)
}

fn code_of(outcome: Outcome) -> String {
    match outcome {
        Outcome::Accept => "accept".to_string(),
        Outcome::Reject { code, .. } => code.code().to_string(),
    }
}

/// Case (a): `qa :- \+ denied(s1)` over the `{denied, revoked}` cert with `denied` marked
/// partial — `neg_atom_partial` (D2: absence from a lower bound proves nothing). CONTROL: the
/// same derivation over the unmarked cert is still the pre-0030 accept, so the mark is the
/// only thing that flipped it.
#[test]
fn adr0030_case_a_neg_over_a_partial_table_is_refused_because_of_the_mark() {
    let program = program();
    let marked = neg_derivation(
        "qa",
        "q_denied_s1",
        g("denied", &["s1"]),
        cert(&program, vec![g("denied", &["s2"])], denied_partial()),
    );
    assert_eq!(code_of(run("qa", &marked)), "neg_atom_partial");
    let unmarked = neg_derivation(
        "qa",
        "q_denied_s1",
        g("denied", &["s1"]),
        cert(&program, vec![g("denied", &["s2"])], None),
    );
    assert_eq!(
        code_of(run("qa", &unmarked)),
        "accept",
        "control: an exact seal of the same tables is still accepted"
    );
}

/// Case (d2): the same cert with `denied` sealed EMPTY — a genuine lower bound of the least
/// model `{denied(s2)}` — marked partial, and a negation over the COMPLETE table only
/// (`qr :- \+ revoked(s1)`): ACCEPT, because D2 does not verify closure for a partial table.
/// CONTROL: unmarked, closure runs over the lower bound, the enumeration of `denied_rule`
/// derives `denied(s2)` which the table omits, and the cert is refused `cert_not_closed`.
#[test]
fn adr0030_case_d2_lower_bound_marked_partial_is_accepted_because_closure_is_skipped() {
    let program = program();
    let marked = neg_derivation(
        "qr",
        "q_notrevoked",
        g("revoked", &["s1"]),
        cert(&program, Vec::new(), denied_partial()),
    );
    assert_eq!(code_of(run("qr", &marked)), "accept");
    let unmarked = neg_derivation(
        "qr",
        "q_notrevoked",
        g("revoked", &["s1"]),
        cert(&program, Vec::new(), None),
    );
    assert_eq!(
        code_of(run("qr", &unmarked)),
        "cert_not_closed",
        "control: the unmarked lower bound is still refused by closure"
    );
}

/// D1.3 at the checker, not only at the JSON: marking the EXTENSIONAL table partial is
/// `cert_partial_scope_invalid` — and it is refused before any table is consulted, so the
/// verdict is the same whether `denied` is exact or empty.
#[test]
fn adr0030_marking_an_extensional_table_partial_is_refused_by_shape() {
    let program = program();
    for rows in [vec![g("denied", &["s2"])], Vec::new()] {
        let deriv = neg_derivation(
            "qr",
            "q_notrevoked",
            g("revoked", &["s1"]),
            cert(
                &program,
                rows,
                Some(StratumPrefix::new(1, [sym("revoked")])),
            ),
        );
        assert_eq!(code_of(run("qr", &deriv)), "cert_partial_scope_invalid");
    }
}

/// #3424 (research 0035 lane 8, B17): the certificate's OWN scope level is read once the
/// certificate carries a partial scope (#1708). Case (d2)'s marked cert, whose partial scope sits
/// at level 1, accepts at level 1; the same cert at level 0 or 7 is `cert_partial_scope_invalid`.
/// A single full-scope certificate does not read its level
/// (`scope_level_is_inert_for_a_single_full_scope_certificate_1567` in negation.rs): the partial
/// scope is what makes the level load-bearing.
#[test]
fn a_certificates_scope_level_is_read_once_it_carries_a_partial_scope_3424() {
    let program = program();
    let at = |level: u32| {
        let mut c = cert(&program, Vec::new(), denied_partial());
        c.scope = StratumPrefix::new(level, c.scope.predicates.clone());
        neg_derivation("qr", "q_notrevoked", g("revoked", &["s1"]), c)
    };
    assert_eq!(
        code_of(run("qr", &at(1))),
        "accept",
        "control: the partial scope's own level"
    );
    for level in [0u32, 7] {
        assert_eq!(
            code_of(run("qr", &at(level))),
            "cert_partial_scope_invalid",
            "level {level} under a level-1 partial scope"
        );
    }
}

/// D1.1 at the checker: a `partial_scope` at a level other than the sealed prefix's own, or
/// naming a predicate the scope does not seal, is `cert_partial_scope_invalid`.
#[test]
fn adr0030_partial_scope_off_level_or_outside_the_scope_is_refused_by_shape() {
    let program = program();
    for partial in [
        StratumPrefix::new(0, [sym("denied")]),
        StratumPrefix::new(1, [sym("qa")]),
    ] {
        let deriv = neg_derivation(
            "qr",
            "q_notrevoked",
            g("revoked", &["s1"]),
            cert(&program, vec![g("denied", &["s2"])], Some(partial)),
        );
        assert_eq!(code_of(run("qr", &deriv)), "cert_partial_scope_invalid");
    }
}

// =============================== the wire case (e) ===============================

fn hex_to_bytes(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "hex must be even length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex digit"))
        .collect()
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The twelve-element cert of the positive fixture `closed_world_count_partial` is the frozen
/// `closed_world_count` ten-element cert with a D10 witness digest (`d1` × 32) and a
/// `StratumPrefix {1, [sealed]}` appended — the exact position ADR 0030 D4 gives
/// `partial_scope`. It DECODES to a cert carrying both; the eleven-element form (the D10
/// witness alone) still decodes; the thirteen-element twin is refused by ARITY. The bytes are
/// derived here from the frozen fixture rather than trusted: the cert tuple is the LAST element
/// of the stream, so the derivation is one arity byte and the appended encodings.
#[test]
fn adr0030_wire_case_e_twelve_elements_decode_and_thirteen_are_refused_by_arity() {
    let doc = load("derivation_wire.json");
    let ten = hex_to_bytes(
        find(&doc, "positive", "closed_world_count")["wire_hex"]
            .as_str()
            .expect("wire_hex"),
    );
    let twelve = hex_to_bytes(
        find(&doc, "positive", "closed_world_count_partial")["wire_hex"]
            .as_str()
            .expect("wire_hex"),
    );
    let thirteen = hex_to_bytes(
        find(
            &doc,
            "malformed",
            "adr0030_cert_thirteen_elements_closed_posture",
        )["wire_hex"]
            .as_str()
            .expect("wire_hex"),
    );
    // The RED-first malformed twin of the twelve-element cert is GONE: its bytes now live in
    // the positive list under `closed_world_count_partial`.
    assert_eq!(
        doc["malformed"]
            .as_array()
            .expect("malformed list")
            .iter()
            .filter(|c| c["name"] == "adr0030_cert_twelve_elements_partial_scope")
            .count(),
        0,
        "the RED-first twelve-element malformed entry must not survive the flip"
    );

    // LANDED: ten and twelve decode; twelve carries both trailing elements.
    decode_derivation_wire_v1(&ten).expect("the frozen ten-element fixture decodes");
    let decoded = decode_derivation_wire_v1(&twelve).expect("twelve elements decode (ADR 0030 D4)");
    assert_eq!(
        decoded.closed_world[0].decomposition_witness,
        Some([0xd1u8; 32])
    );
    assert_eq!(
        decoded.closed_world[0].partial_scope,
        Some(StratumPrefix::new(1, [sym("sealed")]))
    );

    // DERIVED: locate the ten-element cert header (Tuple(10) whose first element is the
    // two-element scope tuple) — it must be unique, or the splice below would be a guess.
    let header10 = [0x01u8, 0x0a, 0x01, 0x02];
    let at: Vec<usize> = ten
        .windows(4)
        .enumerate()
        .filter(|(_, w)| *w == header10)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        at.len(),
        1,
        "the ten-element cert header is unique in the frozen bytes"
    );
    let witness = ontos_codec::encode(&digest_atom(&[0xd1u8; 32]));
    let prefix = ontos_codec::encode(&Value::tuple([
        ontos_data::encode_int(1),
        Value::tuple([Value::atom(b"sealed".to_vec())]),
    ]));
    let mut derived = ten.clone();
    derived[at[0] + 1] = 0x0c;
    derived.extend(&witness);
    derived.extend(&prefix);
    assert_eq!(
        to_hex(&derived),
        to_hex(&twelve),
        "the positive twelve-element bytes are the frozen cert plus exactly the two trailing elements"
    );

    // THIRTEEN: the twelve-element bytes with one more Atom appended and the arity bumped —
    // refused, and by ARITY: the closed posture moved by exactly one slot.
    let mut derived13 = twelve.clone();
    derived13[at[0] + 1] = 0x0d;
    derived13.extend(ontos_codec::encode(&Value::atom(b"x".to_vec())));
    assert_eq!(
        to_hex(&derived13),
        to_hex(&thirteen),
        "the thirteen-element twin is the twelve-element bytes plus one trailing Atom"
    );
    let err = decode_derivation_wire_v1(&thirteen).expect_err("thirteen elements are refused");
    // #2630: the arity refusal names EVERY count a certificate takes, not one of them.
    assert_eq!(
        format!("{err}"),
        "decode closed_world.cert: 13 elements, expected 10, 11 or 12",
        "the refusal must be the closed-posture arity check"
    );

    // CONTROL: the eleven-element form (the D10 witness alone) still decodes, with no partial
    // sub-scope.
    let mut eleven = ten.clone();
    eleven[at[0] + 1] = 0x0b;
    eleven.extend(&witness);
    let decoded = decode_derivation_wire_v1(&eleven).expect("eleven elements decode (D10)");
    assert_eq!(
        decoded.closed_world[0].decomposition_witness,
        Some([0xd1u8; 32])
    );
    assert_eq!(decoded.closed_world[0].partial_scope, None);
}
