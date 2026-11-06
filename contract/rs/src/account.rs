//! Account codec — the canonical, **FROZEN** encoding of account artifacts
//! (§2a `quote` byte form · §9 `ClauseId` canonical hash).
//!
//! This is the §9 "later, additive binding" the contract deferred: it freezes the
//! [`quote`](crate::reify::quote) byte form and defines the canonical `ClauseId` as
//! the SHA-256 of the domain-separated, `ontos-codec` bytes of a clause `quote`d
//! into a ground ontos value.
//!
//! **Syntactic (§9 decision, 2026-06-01).** Variable names are part of the
//! encoding — there is **no alpha-normalization**. `p(X) :- q(X)` and
//! `p(Y) :- q(Y)` are distinct clauses with distinct ids. This matches the
//! incumbent (arche's clause hash encodes `Var` names) and keeps the binding
//! simple (no canonical-renaming pass). A future alpha-normalizing id, if ever
//! wanted, is a *new* versioned binding, never an edit to this one.

use crate::literal::Goal;
use crate::program::{BodyLit, Clause, ClauseId, CountLit, ProjectSpec};
use crate::reify::{quote, reify};
use crate::term::Term;
use ontos_core::Value;
use sha2::{Digest, Sha256};

/// Domain separator for a canonical clause hash (so a clause id can never collide
/// with another hash over the same bytes).
pub const CLAUSE_PREFIX: &[u8] = b"logos/account/clause/v1\n";

/// Tag byte sealing the **negated** body-literal reading (ADR 0007). A `Neg(g)`
/// reads as `Tuple[Atom(NEG_TAG), goal_as_term(g)]` — a 2-tuple whose first child is
/// this single-byte atom. A positive `goal_as_term(g)` is `Tuple[Atom(pred), args…]`
/// whose first child is the **predicate** atom. The two readings are distinct only
/// because `0x00` is not a valid predicate name: a `Symbol` itself accepts any bytes, so
/// a positive literal with predicate `0x00` WOULD read as a `Neg`. This reading is
/// therefore injective only over clauses without a reserved predicate, and every ingress
/// refuses one ([`reserved_predicate`](crate::reserved_predicate): `program_serde`, the
/// prelude loader, the kernel's analysis front door; #2247). The tag mirrors the `reify`
/// tag discipline (a leading 1-byte atom seals the shape).
const NEG_TAG: u8 = 0x00;

/// Tag byte sealing the **count** body-literal reading (ADR 0023). A `Count(c)` reads
/// as `Tuple[Atom([COUNT_TAG]), Atom(pred), <filter>, <project>, count_term]` — a
/// 5-tuple whose first child is this single-byte atom, distinct from both a positive
/// reading (first child = the predicate atom, which is never `0x01` because every ingress
/// refuses that predicate, #2247) and the `Neg` reading
/// (first child = `Atom([NEG_TAG=0x00])`). So a body with no `Count` literal encodes
/// byte-identically to the pre-amendment account.
const COUNT_TAG: u8 = 0x01;

/// Account-codec reading of a [`ProjectSpec`] (ADR 0023 + #587): `Rows` ⇒ `Atom("rows")`,
/// `Distinct { attr }` ⇒ `Tuple[Atom("distinct"), int(attr)]`, and the `min`/`max`/`sum`
/// folds ⇒ `Tuple[Atom("sum"|"min"|"max"), int(attr)]`. The `rows`/`distinct` readings are
/// **byte-identical to the pre-#587 codec** (the new tags are additive), so every existing
/// count clause id is unchanged.
fn project_as_term(project: &ProjectSpec) -> Term {
    let attr_tag = |tag: &[u8], attr: u32| {
        Term::Tuple(vec![
            Term::Atom(tag.to_vec()),
            crate::intval::BigInt::from_i128(i128::from(attr)).to_int_term(),
        ])
    };
    match project {
        ProjectSpec::Rows => Term::Atom(b"rows".to_vec()),
        ProjectSpec::Distinct { attr } => attr_tag(b"distinct", *attr),
        ProjectSpec::Sum { attr } => attr_tag(b"sum", *attr),
        ProjectSpec::Min { attr } => attr_tag(b"min", *attr),
        ProjectSpec::Max { attr } => attr_tag(b"max", *attr),
    }
}

/// Inverse of [`project_as_term`].
fn project_from_term(term: &Term) -> Option<ProjectSpec> {
    match term {
        Term::Atom(bytes) if bytes.as_slice() == b"rows" => Some(ProjectSpec::Rows),
        Term::Tuple(children) => {
            let [Term::Atom(tag), attr_term] = children.as_slice() else {
                return None;
            };
            let attr = crate::intval::BigInt::from_int_term(attr_term)?.to_i128()?;
            let attr = u32::try_from(attr).ok()?;
            match tag.as_slice() {
                b"distinct" => Some(ProjectSpec::Distinct { attr }),
                b"sum" => Some(ProjectSpec::Sum { attr }),
                b"min" => Some(ProjectSpec::Min { attr }),
                b"max" => Some(ProjectSpec::Max { attr }),
                _ => None,
            }
        }
        Term::Atom(_) | Term::Var(_) => None,
    }
}

/// Account-codec reading of an arity-sensitive [`PredicateRef`] (ADR 0023, #581): the
/// 2-tuple `Tuple[Atom(pred), int(arity)]`. Pinning the arity in the account bytes makes
/// `obs/3` and `obs/2` distinct counted relations — a wrong-arity count cannot share a
/// clause id with the right-arity one.
fn predicate_ref_as_term(pref: &crate::program::PredicateRef) -> Term {
    Term::Tuple(vec![
        Term::Atom(pref.pred.bytes().to_vec()),
        crate::intval::BigInt::from_i128(i128::from(pref.arity)).to_int_term(),
    ])
}

/// Inverse of [`predicate_ref_as_term`].
fn predicate_ref_from_term(term: &Term) -> Option<crate::program::PredicateRef> {
    let Term::Tuple(children) = term else {
        return None;
    };
    let [pred_term, arity_term] = children.as_slice() else {
        return None;
    };
    let Term::Atom(pred) = pred_term else {
        return None;
    };
    let arity = crate::intval::BigInt::from_int_term(arity_term)?.to_i128()?;
    Some(crate::program::PredicateRef {
        pred: crate::literal::Symbol::new(pred.clone()),
        arity: u32::try_from(arity).ok()?,
    })
}

/// Account-codec reading of a [`CountLit`] (ADR 0023): the sealed 5-tuple
/// `Tuple[Atom([COUNT_TAG]), pred_ref, filter, project, count]`, where `pred_ref` is the
/// arity-sensitive `Tuple[Atom(pred), int(arity)]` (#581), `filter` is
/// `Tuple[ Tuple[int(pos), term], … ]` (caller order preserved) and `project`/`count`
/// read via [`project_as_term`] / the raw term.
fn count_lit_as_term(c: &CountLit<Term>) -> Term {
    let filter = Term::Tuple(
        c.filter
            .iter()
            .map(|(pos, t)| {
                Term::Tuple(vec![
                    crate::intval::BigInt::from_i128(i128::from(*pos)).to_int_term(),
                    t.clone(),
                ])
            })
            .collect(),
    );
    Term::Tuple(vec![
        Term::Atom(vec![COUNT_TAG]),
        predicate_ref_as_term(&c.pred),
        filter,
        project_as_term(&c.project),
        c.count.clone(),
    ])
}

/// Inverse of [`count_lit_as_term`].
fn count_lit_from_term(children: &[Term]) -> Option<CountLit<Term>> {
    let [_tag, pred_term, filter_term, project_term, count_term] = children else {
        return None;
    };
    let pred = predicate_ref_from_term(pred_term)?;
    let Term::Tuple(filter_entries) = filter_term else {
        return None;
    };
    let mut filter = Vec::with_capacity(filter_entries.len());
    for entry in filter_entries {
        let Term::Tuple(pair) = entry else {
            return None;
        };
        let [pos_term, value_term] = pair.as_slice() else {
            return None;
        };
        let pos = crate::intval::BigInt::from_int_term(pos_term)?.to_i128()?;
        filter.push((u32::try_from(pos).ok()?, value_term.clone()));
    }
    Some(CountLit {
        pred,
        filter,
        project: project_from_term(project_term)?,
        count: count_term.clone(),
    })
}

/// The labeled-compound reading of a goal `p(a…)` as a `Term`: `Tuple[Atom(p), a…]`
/// (§1.1). A nullary goal `p()` is `Tuple[Atom(p)]` (arity 1) — distinct from the
/// bare atom `p`.
fn goal_as_term(goal: &Goal) -> Term {
    let mut children = Vec::with_capacity(goal.args.len() + 1);
    children.push(Term::Atom(goal.pred.bytes().to_vec()));
    children.extend(goal.args.iter().cloned());
    Term::Tuple(children)
}

/// The reading of one polarity-tagged body literal (ADR 0007).
///
/// **Byte-compat invariant.** A [`BodyLit::Pos`] reads **byte-identically to the
/// bare `goal_as_term(g)`** — no wrapper, no tag — so every pre-amendment positive
/// clause id is unchanged. A [`BodyLit::Neg`] reads as the sealed 2-tuple
/// `Tuple[Atom(NEG_TAG), goal_as_term(g)]`, which can never collide with a positive
/// reading (see [`NEG_TAG`]).
fn body_lit_as_term(lit: &BodyLit<Term>) -> Term {
    match lit {
        BodyLit::Pos(g) => goal_as_term(g),
        BodyLit::Neg(g) => Term::Tuple(vec![Term::Atom(vec![NEG_TAG]), goal_as_term(g)]),
        BodyLit::Count(c) => count_lit_as_term(c),
    }
}

/// A clause `head :- b₀, …, bₙ` as a `Term`: `Tuple[ head, Tuple[b₀, …, bₙ] ]`
/// (a 2-tuple of the head reading and the ordered body readings; empty body =
/// `Tuple[head, Tuple[]]`). Each body literal reads via [`body_lit_as_term`], so an
/// all-positive body is byte-identical to the pre-ADR-0007 encoding.
fn clause_as_term(clause: &Clause) -> Term {
    Term::Tuple(vec![
        goal_as_term(&clause.head),
        Term::Tuple(clause.body.iter().map(body_lit_as_term).collect()),
    ])
}

/// The canonical ground ontos value of a clause: `quote(clause_as_term(clause))`.
/// Total (every clause has one) and injective on distinct clauses (`quote` is
/// injective; the labeled-compound reading is unambiguous).
pub fn clause_value(clause: &Clause) -> Value {
    quote(&clause_as_term(clause))
}

/// The partial inverse of [`clause_value`]: recover the [`Clause`] whose canonical
/// ground value is `value`, or `None` if `value` is not in the image of
/// [`clause_value`]. Used by the program (de)serialization ([`program_serde`]) to
/// read a clause back out of an ontos `Value` without re-deriving its `ClauseId`.
///
/// The decode mirrors [`clause_as_term`] exactly:
/// `value` must `reify` to `Tuple[ head_term, Tuple[ body_term… ] ]`, where
/// `head_term` is the labeled compound `Tuple[Atom(pred), arg…]` (arity ≥ 1) and
/// each `body_term` is either the bare `goal_as_term` (positive) or the sealed
/// 2-tuple `Tuple[Atom([NEG_TAG]), goal_as_term]` (negated). The polarity rule is the
/// producer's: a body term is **negated** iff it is a 2-tuple whose first child is
/// exactly the single-byte atom `Atom([NEG_TAG])` — the reading [`body_lit_as_term`]
/// commits to. This is injective only over clauses without a reserved predicate, which every
/// ingress refuses (#2247, [`reserved_predicate`](crate::reserved_predicate)).
///
/// [`program_serde`]: crate::program_serde
pub fn clause_from_value(value: &Value) -> Option<Clause> {
    let term = reify(value)?;
    let Term::Tuple(parts) = &term else {
        return None;
    };
    let [head_term, body_term] = parts.as_slice() else {
        return None;
    };
    let head = goal_from_term(head_term)?;
    let Term::Tuple(body_lits) = body_term else {
        return None;
    };
    let mut body = Vec::with_capacity(body_lits.len());
    for lit in body_lits {
        body.push(body_lit_from_term(lit)?);
    }
    Some(Clause { head, body })
}

/// Inverse of [`goal_as_term`]: read `Tuple[Atom(pred), arg…]` back into a [`Goal`].
/// The first child is the predicate atom; the rest are the argument terms (which may
/// themselves contain `Var`s — this is a clause head/body literal, not a ground one).
/// `None` if the term is not a tuple headed by an atom (arity ≥ 1).
fn goal_from_term(term: &Term) -> Option<Goal> {
    let Term::Tuple(children) = term else {
        return None;
    };
    let (head, args) = children.split_first()?;
    let Term::Atom(pred) = head else {
        return None;
    };
    Some(Goal {
        pred: crate::literal::Symbol::new(pred.clone()),
        args: args.to_vec(),
    })
}

/// Inverse of [`body_lit_as_term`]: a 2-tuple whose first child is exactly
/// `Atom([NEG_TAG])` is a [`BodyLit::Neg`] over the second child's goal; anything else
/// is read as a [`BodyLit::Pos`] over the whole term's goal.
fn body_lit_from_term(term: &Term) -> Option<BodyLit<Term>> {
    if let Term::Tuple(children) = term {
        // A `Neg` reading is the 2-tuple `[Atom([NEG_TAG]), goal]`.
        if let [Term::Atom(tag), inner] = children.as_slice() {
            if tag.as_slice() == [NEG_TAG] {
                return Some(BodyLit::Neg(goal_from_term(inner)?));
            }
        }
        // A `Count` reading (ADR 0023) is the 5-tuple led by `Atom([COUNT_TAG])`.
        if let [Term::Atom(tag), ..] = children.as_slice() {
            if tag.as_slice() == [COUNT_TAG] {
                return Some(BodyLit::Count(count_lit_from_term(children)?));
            }
        }
    }
    Some(BodyLit::Pos(goal_from_term(term)?))
}

/// The canonical, **frozen** bytes of a clause: `ontos-codec(quote(clause))`.
pub fn clause_bytes(clause: &Clause) -> Vec<u8> {
    ontos_codec::encode(&clause_value(clause))
}

impl ClauseId {
    /// The canonical `ClauseId` of a clause — lowercase-hex
    /// `SHA-256(CLAUSE_PREFIX ‖ ontos-codec(quote(clause)))` (§9, syntactic).
    ///
    /// Stable and cross-language: any binding that follows this encoding computes
    /// the same id for the same clause. The id satisfies the v1 `ClauseId`
    /// contract (stable + lookup-able) and is additionally a canonical hash.
    pub fn canonical(clause: &Clause) -> ClauseId {
        let mut hasher = Sha256::new();
        hasher.update(CLAUSE_PREFIX);
        hasher.update(clause_bytes(clause));
        ClauseId::new(to_hex(&hasher.finalize()))
    }
}

fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(head_pred: &str, head_args: Vec<Term>, body: Vec<Goal>) -> Clause {
        Clause::new(Goal::new(head_pred, head_args), body)
    }

    #[test]
    fn canonical_id_is_deterministic() {
        let c = clause(
            "p",
            vec![Term::var("X")],
            vec![Goal::new("q", [Term::var("X")])],
        );
        assert_eq!(ClauseId::canonical(&c), ClauseId::canonical(&c));
        // 64-char lowercase hex (sha-256).
        assert_eq!(ClauseId::canonical(&c).as_str().len(), 64);
    }

    #[test]
    fn syntactic_in_var_names_no_alpha_normalization() {
        // p(X):-q(X) and p(Y):-q(Y) are DISTINCT clauses with DISTINCT ids (§9).
        let cx = clause(
            "p",
            vec![Term::var("X")],
            vec![Goal::new("q", [Term::var("X")])],
        );
        let cy = clause(
            "p",
            vec![Term::var("Y")],
            vec![Goal::new("q", [Term::var("Y")])],
        );
        assert_ne!(ClauseId::canonical(&cx), ClauseId::canonical(&cy));
    }

    #[test]
    fn distinct_clauses_distinct_ids() {
        let a = Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"b")]));
        let b = Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"c")]));
        let head_vs_body = clause("p", vec![], vec![Goal::new("q", [])]);
        assert_ne!(ClauseId::canonical(&a), ClauseId::canonical(&b));
        assert_ne!(ClauseId::canonical(&a), ClauseId::canonical(&head_vs_body));
    }

    #[test]
    fn body_order_is_significant() {
        let pq = clause("h", vec![], vec![Goal::new("p", []), Goal::new("q", [])]);
        let qp = clause("h", vec![], vec![Goal::new("q", []), Goal::new("p", [])]);
        assert_ne!(ClauseId::canonical(&pq), ClauseId::canonical(&qp));
    }

    #[test]
    fn nullary_goal_distinct_from_bare_atom_arg() {
        // p(q) with q a nullary compound  ≠  p(q) with q a bare atom — the
        // labeled-compound reading keeps a 0-ary functor distinct from an atom.
        let with_compound = Clause::fact(Goal::new("p", [Term::tuple([Term::atom(*b"q")])]));
        let with_atom = Clause::fact(Goal::new("p", [Term::atom(*b"q")]));
        assert_ne!(
            ClauseId::canonical(&with_compound),
            ClauseId::canonical(&with_atom)
        );
    }

    /// Freeze regression: the canonical id of a fixed clause is pinned so the
    /// account-codec byte form cannot drift silently. `edge(a, b).` (a rule-fact).
    #[test]
    fn frozen_clause_id_regression() {
        let c = Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"b")]));
        assert_eq!(ClauseId::canonical(&c).as_str(), FROZEN_EDGE_AB_ID);
    }

    // Pinned below after first computation (the canonical value per the frozen
    // encoding); locks the bytes against drift.
    const FROZEN_EDGE_AB_ID: &str =
        "0fa66252d400869a272c064a66c32d461b30f95f30e1d03a5fb961cb957bead3";

    // ===== ADR 0007 byte-compat: positive ids are UNCHANGED by the BodyLit amendment =====

    /// Every pinned positive clause id from `vectors/account.json` MUST be byte-for-byte
    /// unchanged after the `BodyLit` amendment — a `Pos` body literal reads as the bare
    /// `goal_as_term`, with no wrapper tag. The ids below are the *pre-amendment* frozen
    /// values; if the encoding of a positive body drifted, these would fail.
    #[test]
    fn adr0007_positive_clause_ids_unchanged() {
        // edge(a, b).                                   (frozen: edge_ab_fact)
        let edge_ab = Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"b")]));
        assert_eq!(
            ClauseId::canonical(&edge_ab).as_str(),
            "0fa66252d400869a272c064a66c32d461b30f95f30e1d03a5fb961cb957bead3"
        );
        // reach(X, Y) :- edge(X, Y).                    (frozen: reach_base)
        let reach_base = clause(
            "reach",
            vec![Term::var("X"), Term::var("Y")],
            vec![Goal::new("edge", [Term::var("X"), Term::var("Y")])],
        );
        assert_eq!(
            ClauseId::canonical(&reach_base).as_str(),
            "c52ab14799945827045a4410caed08ca26f2704944da2a6fe48546c096702234"
        );
        // reach(X, Z) :- edge(X, Y), reach(Y, Z).       (frozen: reach_rec)
        let reach_rec = clause(
            "reach",
            vec![Term::var("X"), Term::var("Z")],
            vec![
                Goal::new("edge", [Term::var("X"), Term::var("Y")]),
                Goal::new("reach", [Term::var("Y"), Term::var("Z")]),
            ],
        );
        assert_eq!(
            ClauseId::canonical(&reach_rec).as_str(),
            "d5cb2f8c0811500282cacd5cdf0db22d3356d0eadbdc64e73a149d1c8122dd5d"
        );
        // reach(X, Z) :- edge(X, Z).                    (frozen: reach_base_renamed_Y_to_Z_differs)
        let reach_renamed = clause(
            "reach",
            vec![Term::var("X"), Term::var("Z")],
            vec![Goal::new("edge", [Term::var("X"), Term::var("Z")])],
        );
        assert_eq!(
            ClauseId::canonical(&reach_renamed).as_str(),
            "fff905c2dd63fb17d66bd109e0940df053606dd0270fdfa02b6a43168f5197b1"
        );
    }

    /// A `with_neg` clause's id differs from the same clause read as all-positive
    /// (the `Neg` tag is load-bearing), and is itself pinned so the negated-literal
    /// reading cannot drift. `permit(s,a) :- grant(s,a), \+ denied(s,a).`
    #[test]
    fn adr0007_neg_clause_id_pinned_and_distinct_from_positive() {
        let permit_neg = Clause::with_neg(
            Goal::new("permit", [Term::var("S"), Term::var("A")]),
            [Goal::new("grant", [Term::var("S"), Term::var("A")])],
            [Goal::new("denied", [Term::var("S"), Term::var("A")])],
        );
        // The SAME body literals, but BOTH read as positive.
        let permit_all_pos = clause(
            "permit",
            vec![Term::var("S"), Term::var("A")],
            vec![
                Goal::new("grant", [Term::var("S"), Term::var("A")]),
                Goal::new("denied", [Term::var("S"), Term::var("A")]),
            ],
        );
        // Polarity is part of the id: the negated reading is distinct.
        assert_ne!(
            ClauseId::canonical(&permit_neg),
            ClauseId::canonical(&permit_all_pos)
        );
        // Pin the new Neg-bearing id (locks the NEG_TAG reading against drift).
        assert_eq!(
            ClauseId::canonical(&permit_neg).as_str(),
            FROZEN_PERMIT_NEG_ID
        );
    }

    // Pinned after first computation — the canonical id of
    // `permit(S,A) :- grant(S,A), \+ denied(S,A).` under the NEG_TAG reading.
    const FROZEN_PERMIT_NEG_ID: &str =
        "3670ee8eebbd14d90621ddf82d8244a555562194c64d11dcd9986bcfefed705d";

    // ===== ADR 0023 back-compat: the Count amendment is additive (byte-identical) =====

    /// **Back-compat guard.** A clause with NO `Count` body literal must encode
    /// byte-for-byte as it did before the ADR-0023 `BodyLit::Count` amendment — the
    /// `Count` variant must NEVER change a `Pos`/`Neg` reading. The pinned positive ids
    /// (`adr0007_positive_clause_ids_unchanged`) and the pinned neg id
    /// (`FROZEN_PERMIT_NEG_ID`) already lock the values; this test additionally asserts
    /// the SAME frozen ids hold AFTER the amendment, so a regression that perturbed the
    /// `Pos`/`Neg` byte form (e.g. a stray tag) is caught here too.
    #[test]
    fn adr0023_count_amendment_is_byte_identical_for_non_count_bodies() {
        // edge(a, b).  (the master frozen fact)
        let edge_ab = Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"b")]));
        assert_eq!(ClauseId::canonical(&edge_ab).as_str(), FROZEN_EDGE_AB_ID);
        // The Neg-bearing clause id is unchanged under the amendment.
        let permit_neg = Clause::with_neg(
            Goal::new("permit", [Term::var("S"), Term::var("A")]),
            [Goal::new("grant", [Term::var("S"), Term::var("A")])],
            [Goal::new("denied", [Term::var("S"), Term::var("A")])],
        );
        assert_eq!(
            ClauseId::canonical(&permit_neg).as_str(),
            FROZEN_PERMIT_NEG_ID
        );
    }

    /// A `Count` clause reads to a sealed 5-tuple led by `Atom([COUNT_TAG])`, round-trips
    /// through `clause_value` → `clause_from_value`, and its id is DISTINCT from the same
    /// clause read all-positive (the count tag is load-bearing) and is pinned.
    #[test]
    fn adr0023_count_clause_round_trips_and_id_pinned() {
        // eligible(O) :- count_distinct(obs(O,_,V) filter O@0, project @2, N).
        let count_clause = Clause {
            head: Goal::new("eligible", [Term::var("O")]),
            body: vec![BodyLit::Count(CountLit {
                pred: crate::program::PredicateRef::new(b"obs".to_vec(), 3),
                filter: vec![(0, Term::var("O"))],
                project: ProjectSpec::Distinct { attr: 2 },
                count: Term::var("N"),
            })],
        };
        // Round-trip: encode → decode recovers the exact clause.
        let value = clause_value(&count_clause);
        assert_eq!(clause_from_value(&value), Some(count_clause.clone()));
        // The Count reading is distinct from any all-positive reading (the tag matters):
        // a positive `eligible(O) :- obs(O).` has a different id.
        let positive = Clause::new(
            Goal::new("eligible", [Term::var("O")]),
            [Goal::new("obs", [Term::var("O")])],
        );
        assert_ne!(
            ClauseId::canonical(&count_clause),
            ClauseId::canonical(&positive)
        );
        // Pin the Count-bearing id (locks the COUNT_TAG reading against drift).
        assert_eq!(
            ClauseId::canonical(&count_clause).as_str(),
            FROZEN_COUNT_DISTINCT_ID
        );
    }

    // Pinned after first computation — the canonical id of the count_distinct clause
    // above under the COUNT_TAG reading. Locks the ADR-0023 account byte form.
    const FROZEN_COUNT_DISTINCT_ID: &str =
        "6b05dccf3cd43e49a730129eb0cf5eddce1a12251a1312f1e69b283dd72bafc1";

    /// `ProjectSpec::Rows` (`count`) round-trips and differs from `Distinct`.
    #[test]
    fn adr0023_count_rows_round_trips() {
        let rows_clause = Clause {
            head: Goal::new("eligible", [Term::var("O")]),
            body: vec![BodyLit::Count(CountLit {
                pred: crate::program::PredicateRef::new(b"obs".to_vec(), 3),
                filter: vec![(0, Term::var("O"))],
                project: ProjectSpec::Rows,
                count: Term::var("N"),
            })],
        };
        let value = clause_value(&rows_clause);
        assert_eq!(clause_from_value(&value), Some(rows_clause.clone()));
        // `Rows` and `Distinct` are distinct readings.
        let distinct_clause = Clause {
            head: Goal::new("eligible", [Term::var("O")]),
            body: vec![BodyLit::Count(CountLit {
                pred: crate::program::PredicateRef::new(b"obs".to_vec(), 3),
                filter: vec![(0, Term::var("O"))],
                project: ProjectSpec::Distinct { attr: 2 },
                count: Term::var("N"),
            })],
        };
        assert_ne!(
            ClauseId::canonical(&rows_clause),
            ClauseId::canonical(&distinct_clause)
        );
    }
}
