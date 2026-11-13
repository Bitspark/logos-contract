//! account-v2 list reification (#277), after #3022 — the CHECKER half of the opt-in cons→`list`
//! reification (#159). Every certified literal claim is EXACT (#3022, `seat:caa`'s ruling): a
//! derivation whose nodes conclude the **reified** `list(…)` spelling of a cons-form instance is
//! REFUSED by `check()`, under every term identity, because the reified conclusion is not the
//! instantiated head. The reified spelling is presentation, a `PresentedFact` beside the exact fact.
//! Every negative (wrong-claim / improper / genuinely-distinct) case still REJECTS, and every default
//! (cons) derivation accepts exactly as before.
//!
//! These are rust-local adversarial tests over the FIRM checker. They establish:
//!   1. REFUSED (#3022) — a reified `wrap(list(a,b))` Rule conclusion over the cons-form
//!      program, whatever the claim's spelling.
//!   2. REJECT — a reified conclusion claiming the WRONG list (`list(b,a)`), and an
//!      improper tail spelled as `list` (no false accept).
//!   3. BIJECTION — `canonicalize_lists` never conflates two distinct sequences, keeps
//!      `[]` distinct from `list()`, and round-trips deep nesting.
//!   4. ADDITIVE — the default (cons / non-list) derivations accept exactly as before;
//!      a cons-form claim still rejects a genuinely different cons-form root.

use logos_contract::{
    canonicalize_lists, check, CheckLimits, CheckProfile, Clause, ClauseId, Derivation, Evidence,
    Goal, GroundLiteral, LeafOutcome, LeafVerifier, MapProgram, Node, NodeMeta, PredicateSet,
    Premise, Subst, Symbol, Term, Theory, TheoryGround, Verdict,
};
use ontos_core::Value;
use std::collections::BTreeMap;

// ----------------------------- profile + helpers -----------------------------

/// A theory that owns nothing (no builtins needed here).
struct NoTheory;
// test-double: consumer(owns no predicate)
impl Theory for NoTheory {
    logos_contract::cannot_copy!(
        Theory,
        "a test double: declines to copy, as the defaulted method did before #2722"
    );
    fn owns(&self, _pred: &Symbol) -> bool {
        false
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::disowned()
    }
}

/// A `LeafVerifier` whose extensional set is `src`. It admits any `src` leaf whose
/// argument, **after cons↔`list` canonicalization**, is in its cons-form EDB-of-record
/// — exercising the "a reified leaf matches the cons-form EDB" obligation of #277 via
/// the public [`canonicalize_lists`] primitive (the SAME bijection `check` uses).
struct SrcLeaves {
    extensional: PredicateSet,
    /// The EDB-of-record, in the FROZEN cons form (what a default producer emits).
    edb_cons: Vec<GroundLiteral>,
}
impl SrcLeaves {
    fn new(edb_cons: Vec<GroundLiteral>) -> Self {
        SrcLeaves {
            extensional: PredicateSet::from_iter(["src"]),
            edb_cons,
        }
    }
}
// test-double: consumer(a fixed EDB matched modulo list spelling)
impl LeafVerifier<()> for SrcLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        // Reify-aware EDB match: a reified `src(list(a,b))` leaf matches the cons-form
        // EDB row `src([a,b])` because their canonical forms agree.
        let canon = |g: &GroundLiteral| GroundLiteral {
            pred: g.pred.clone(),
            args: g.args.iter().map(canonicalize_lists).collect(),
        };
        let want = canon(atom);
        if self.edb_cons.iter().any(|row| canon(row) == want) {
            LeafOutcome::Admit
        } else {
            LeafOutcome::Reject {
                code: "not_in_edb".into(),
            }
        }
    }
}

fn profile(leaves: SrcLeaves) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(NoTheory),
        leaves: Box::new(leaves),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits: CheckLimits::default(),
    }
}

fn atomv(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}
fn nilv() -> Value {
    atomv("[]")
}
fn consv(head: Value, tail: Value) -> Value {
    Value::tuple([atomv("."), head, tail])
}
/// A *proper* cons list `[e0, e1, …]`, right-folded onto `[]` — the FROZEN surface form.
fn cons_list(elems: &[Value]) -> Value {
    let mut acc = nilv();
    for e in elems.iter().rev() {
        acc = consv(e.clone(), acc);
    }
    acc
}
/// The ontos/data flat `list` embedding `list(e0, …)` — the REIFIED form.
fn list_embed(elems: &[Value]) -> Value {
    let mut items = Vec::with_capacity(elems.len() + 1);
    items.push(atomv("list"));
    items.extend_from_slice(elems);
    Value::tuple(items)
}
fn gl(pred: &str, arg: Value) -> GroundLiteral {
    GroundLiteral::new(pred, [arg])
}
/// The program `wrap(X) :- src(X).` — `src` extensional, `wrap` intensional. Both the
/// head and the body literal are written with a WHOLE-argument variable `X`, so the
/// grounding `subst` binds `X` to the cons-form list term (the surface identity).
fn wrap_program() -> MapProgram {
    MapProgram::new().with(
        "wrap_rule",
        Clause::new(
            Goal::new("wrap", [Term::var("X")]),
            [Goal::new("src", [Term::var("X")])],
        ),
    )
}
/// `subst {X = <cons-form list term>}` — the grounding the engine recorded (its subst
/// images are the FROZEN cons surface form; only the per-conclusion EMISSION is reified).
fn subst_x_conslist(elems: &[Value]) -> Subst {
    let mut s: Subst = BTreeMap::new();
    s.insert("X".into(), Term::from_value(&cons_list(elems)));
    s
}

// ======================= 1. THE REIFIED SPELLING IS REFUSED (#3022) ========================

/// A `src(list(a,b))` leaf + a `wrap(list(a,b))` Rule conclusion, over the cons-form program
/// `wrap(X):-src(X)` with the cons-form subst `{X=[a,b]}`, is REFUSED against the reified claim
/// `wrap(list(a,b))`: the conclusion is not the instantiated head `wrap([a,b])`. #277 accepted it
/// under account equality; #3022 made every certified claim exact.
#[test]
fn reified_list_derivation_is_refused_3022() {
    let elems = [atomv("a"), atomv("b")];
    let program = wrap_program();
    // The EDB-of-record is the cons form (what a default store holds).
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&elems))]);

    // The REIFIED nodes: both conclusions are in `list(…)` form.
    let src_list = gl("src", list_embed(&elems));
    let wrap_list = gl("wrap", list_embed(&elems));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: src_list,
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: wrap_list.clone(),
                clause: ClauseId::new("wrap_rule"),
                subst: subst_x_conslist(&elems),
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    // The claim is the reified form (a consumer that speaks the `list` profile).
    let outcome = check(&program, &wrap_list, &deriv, &(), &profile(leaves));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(code.code(), "instantiation_mismatch"),
        Verdict::Accept => panic!("a reified conclusion is not the instantiated head (#3022)"),
    }
}

/// Cross-spelling: the SAME reified derivation against a CONS-form claim (`wrap([a,b])`) is
/// refused at its own head, before the root is read (#3022).
#[test]
fn reified_node_is_refused_before_a_cons_claim_is_read_3022() {
    let elems = [atomv("a"), atomv("b")];
    let program = wrap_program();
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&elems))]);
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: gl("src", list_embed(&elems)),
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: gl("wrap", list_embed(&elems)),
                clause: ClauseId::new("wrap_rule"),
                subst: subst_x_conslist(&elems),
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    let cons_claim = gl("wrap", cons_list(&elems));
    let outcome = check(&program, &cons_claim, &deriv, &(), &profile(leaves));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(code.code(), "instantiation_mismatch"),
        Verdict::Accept => panic!("a reified node is refused at its own head (#3022)"),
    }
}

/// The DEFAULT (non-reified, all-cons) derivation still accepts exactly as before — the
/// change is additive, never altering an existing verdict.
#[test]
fn default_cons_derivation_still_accepts() {
    let elems = [atomv("a"), atomv("b")];
    let program = wrap_program();
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&elems))]);
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: gl("src", cons_list(&elems)),
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: gl("wrap", cons_list(&elems)),
                clause: ClauseId::new("wrap_rule"),
                subst: subst_x_conslist(&elems),
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    let cons_claim = gl("wrap", cons_list(&elems));
    let outcome = check(&program, &cons_claim, &deriv, &(), &profile(leaves));
    assert_eq!(
        outcome.verdict,
        Verdict::Accept,
        "the frozen cons-form derivation must still accept (additive)"
    );
}

// ================================ 2. REJECT ===============================

/// A reified conclusion that claims the WRONG list (`list(b,a)` instead of `list(a,b)`)
/// is still REJECTED — canonicalization never makes two DISTINCT sequences equal.
#[test]
fn reified_wrong_order_list_is_rejected() {
    let program = wrap_program();
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&[atomv("a"), atomv("b")]))]);
    // subst binds X = [a,b], but the Rule claims wrap(list(b,a)) — a different sequence.
    let wrong = gl("wrap", list_embed(&[atomv("b"), atomv("a")]));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: gl("src", list_embed(&[atomv("a"), atomv("b")])),
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: wrong.clone(),
                clause: ClauseId::new("wrap_rule"),
                subst: subst_x_conslist(&[atomv("a"), atomv("b")]),
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    let outcome = check(&program, &wrong, &deriv, &(), &profile(leaves));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(
            code.code(),
            "instantiation_mismatch",
            "a wrong-order reified list must REJECT (no conflation)"
        ),
        Verdict::Accept => panic!("wrong-order reified list was wrongly ACCEPTED (unsound)"),
    }
}

/// A claim spelled as an improper `list`-looking compound vs a proper cons list must NOT
/// be conflated: `wrap(list(a,b))` (a proper-list embedding) is distinct from
/// `wrap([a|b])` (an improper cons), so claiming the proper one for an improper subst
/// REJECTS.
#[test]
fn improper_tail_not_conflated_with_proper_list() {
    let program = wrap_program();
    // subst binds X to the IMPROPER cons `[a|b]` = .(a,b); a reified emission leaves it
    // as the cons (improper is never reified), so the honest conclusion is wrap([a|b]).
    let improper = consv(atomv("a"), atomv("b"));
    let mut subst: Subst = BTreeMap::new();
    subst.insert("X".into(), Term::from_value(&improper));
    let leaves = SrcLeaves::new(vec![gl("src", improper.clone())]);
    // The Rule DISHONESTLY claims wrap(list(a,b)) (a proper 2-list) for the improper subst.
    let dishonest = gl("wrap", list_embed(&[atomv("a"), atomv("b")]));
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: gl("src", improper),
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: dishonest.clone(),
                clause: ClauseId::new("wrap_rule"),
                subst,
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    let outcome = check(&program, &dishonest, &deriv, &(), &profile(leaves));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(code.code(), "instantiation_mismatch"),
        Verdict::Accept => {
            panic!("an improper cons claimed as a proper list was wrongly ACCEPTED (unsound)")
        }
    }
}

/// A genuinely different cons-form root still rejects a cons-form claim — the additive
/// canonicalization does not loosen the default non-list comparison.
#[test]
fn default_distinct_cons_still_rejects() {
    let program = wrap_program();
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&[atomv("a")]))]);
    let deriv = Derivation::new(
        [
            Node::Leaf {
                conclusion: gl("src", cons_list(&[atomv("a")])),
                evidence: Evidence::default(),
            },
            Node::Rule {
                conclusion: gl("wrap", cons_list(&[atomv("a")])),
                clause: ClauseId::new("wrap_rule"),
                subst: subst_x_conslist(&[atomv("a")]),
                premises: vec![Premise::pos(0)],
                meta: NodeMeta::default(),
            },
        ],
        1,
    );
    // Claim a DIFFERENT list than the root concludes.
    let other_claim = gl("wrap", cons_list(&[atomv("z")]));
    let outcome = check(&program, &other_claim, &deriv, &(), &profile(leaves));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(code.code(), "root_conclusion_mismatch"),
        Verdict::Accept => panic!("a distinct cons root matched the claim (unsound)"),
    }
}

// ============================ 3. BIJECTION ============================
// Direct adversarial properties of the canonicalization primitive.

/// `canonicalize_lists` is the IDENTITY on a bare nil `[]` and on the `list()` empty
/// embedding, and keeps the TWO empty spellings DISTINCT (no conflation of `[]`/`list()`).
#[test]
fn empty_list_and_nil_stay_distinct() {
    assert_eq!(
        canonicalize_lists(&nilv()),
        nilv(),
        "[] is left as the bare atom"
    );
    assert_eq!(
        canonicalize_lists(&list_embed(&[])),
        list_embed(&[]),
        "list() is left as the empty embedding"
    );
    assert_ne!(
        canonicalize_lists(&nilv()),
        canonicalize_lists(&list_embed(&[])),
        "[] and list() must NOT canonicalize to the same value"
    );
}

/// The cons↔`list` correspondence is a bijection: a proper cons list and its `list`
/// embedding canonicalize to the SAME value, and DISTINCT sequences to DISTINCT values.
#[test]
fn cons_and_list_are_bijective_no_conflation() {
    let ab = [atomv("a"), atomv("b")];
    let ba = [atomv("b"), atomv("a")];
    // same sequence, two spellings → equal canonical form.
    assert_eq!(
        canonicalize_lists(&cons_list(&ab)),
        canonicalize_lists(&list_embed(&ab))
    );
    assert_eq!(canonicalize_lists(&cons_list(&ab)), list_embed(&ab));
    // distinct sequences → distinct canonical forms (no conflation).
    assert_ne!(
        canonicalize_lists(&cons_list(&ab)),
        canonicalize_lists(&cons_list(&ba))
    );
    // a list of length 1 vs 2 never conflate.
    assert_ne!(
        canonicalize_lists(&cons_list(&[atomv("a")])),
        canonicalize_lists(&cons_list(&ab))
    );
}

/// Idempotent: canonicalizing an already-`list` value (or a re-canonicalized cons) is a
/// no-op.
#[test]
fn canonicalize_is_idempotent() {
    let v = cons_list(&[atomv("a"), atomv("b")]);
    let once = canonicalize_lists(&v);
    let twice = canonicalize_lists(&once);
    assert_eq!(once, twice);
    let already = list_embed(&[atomv("a")]);
    assert_eq!(canonicalize_lists(&already), already);
}

/// Improper cons `[a|b]` is NOT a proper list → left as the cons tuple (children
/// canonicalized), never collapsed onto a `list`.
#[test]
fn improper_cons_is_not_reified() {
    let improper = consv(atomv("a"), atomv("b"));
    assert_eq!(canonicalize_lists(&improper), improper);
    assert_ne!(
        canonicalize_lists(&improper),
        list_embed(&[atomv("a"), atomv("b")])
    );
}

/// `list` used as a genuine data functor IS, by the ontos/data profile, the canonical
/// sequence — so a `list(a,b)` compound and the cons `[a,b]` ARE account-equal (the
/// intended reification semantics, not an unsound merge). A NON-list compound headed by
/// a different functor is untouched.
#[test]
fn nonlist_compound_untouched_but_list_functor_is_a_sequence() {
    // f(a, b) is not a list — identity (children canonicalized only).
    let f = Value::tuple([atomv("f"), atomv("a"), atomv("b")]);
    assert_eq!(canonicalize_lists(&f), f);
    // f([a]) → f(list(a)): the inner cons list reifies, the f-compound does not.
    let f_with_list = Value::tuple([atomv("f"), cons_list(&[atomv("a")])]);
    let expected = Value::tuple([atomv("f"), list_embed(&[atomv("a")])]);
    assert_eq!(canonicalize_lists(&f_with_list), expected);
}

/// Deep nesting round-trips: a list of lists canonicalizes recursively, and equality is
/// preserved through the nesting.
#[test]
fn deep_nested_lists_canonicalize_recursively() {
    // [[a], [b, c]] in cons form ↔ list(list(a), list(b, c)).
    let inner1 = cons_list(&[atomv("a")]);
    let inner2 = cons_list(&[atomv("b"), atomv("c")]);
    let outer_cons = cons_list(&[inner1, inner2]);
    let expected = list_embed(&[
        list_embed(&[atomv("a")]),
        list_embed(&[atomv("b"), atomv("c")]),
    ]);
    assert_eq!(canonicalize_lists(&outer_cons), expected);
    // and the `list`-spelling of the same nested sequence canonicalizes to the same.
    let outer_list = list_embed(&[
        cons_list(&[atomv("a")]),
        list_embed(&[atomv("b"), atomv("c")]),
    ]);
    assert_eq!(canonicalize_lists(&outer_list), expected);
}

/// Reify-aware EDB matching: a reified `src(list(a,b))` leaf is admitted against a
/// cons-form EDB row `src([a,b])` (the leaf path #277 calls out), while a leaf NOT in
/// the EDB (any spelling) is rejected.
#[test]
fn reified_leaf_matches_cons_edb() {
    let program = wrap_program();
    let leaves = SrcLeaves::new(vec![gl("src", cons_list(&[atomv("a"), atomv("b")]))]);
    // A standalone reified leaf, checked directly as the root.
    let leaf_list = gl("src", list_embed(&[atomv("a"), atomv("b")]));
    let deriv = Derivation::new(
        [Node::Leaf {
            conclusion: leaf_list.clone(),
            evidence: Evidence::default(),
        }],
        0,
    );
    let outcome = check(&program, &leaf_list, &deriv, &(), &profile(leaves));
    assert_eq!(
        outcome.verdict,
        Verdict::Accept,
        "a reified leaf must match the cons-form EDB-of-record"
    );

    // A reified leaf NOT in the EDB is rejected (the canonicalization does not admit junk).
    let leaves2 = SrcLeaves::new(vec![gl("src", cons_list(&[atomv("a"), atomv("b")]))]);
    let absent = gl("src", list_embed(&[atomv("z")]));
    let deriv2 = Derivation::new(
        [Node::Leaf {
            conclusion: absent.clone(),
            evidence: Evidence::default(),
        }],
        0,
    );
    let outcome = check(&program, &absent, &deriv2, &(), &profile(leaves2));
    match outcome.verdict {
        Verdict::Reject { code, .. } => assert_eq!(code.code(), "leaf_rejected"),
        Verdict::Accept => panic!("a leaf absent from the EDB was wrongly admitted"),
    }
}
