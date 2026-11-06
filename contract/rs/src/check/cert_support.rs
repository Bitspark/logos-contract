//! §3.5 SUPPORT verification for a closed-model certificate: every sealed IDB fact has a
//! support edge (`E ⊆ least model`), with the rank-consistent strict same-stratum descent and,
//! since #2258 C3, the cert index a lower-stratum ref names. Split out of `cert.rs` as a
//! pure move when C3 took that file past the 2 000 impl-LOC ceiling; the soundness argument is
//! the banner in `cert.rs`, unchanged.

use super::cert::CertPlace;
use super::cert_stack::CertView;
use super::{builtin_not_decided, is_disowned, RejectionCode};
use crate::cert::{CertId, RelationTable, SupportRef};
use crate::completion::{Completion, TheoryDecision};
use crate::literal::GroundLiteral;
use crate::program::{BodyLit, Program};
use crate::spi::{PredicateSet, Theory};
use crate::term::Term;
use std::collections::{HashMap, HashSet};

/// Step 3 — SUPPORT: every sealed IDB fact has a support edge (E ⊆ least model). For
/// each edge: the cited clause, grounded by `subst`, has head == `fact`; every body
/// literal resolves via its `SupportRef` (with the rank-consistent strict same-stratum
/// descent); and every IDB fact in every extension is covered by some edge (no junk).
///
/// **EXTENSIONAL (EDB) facts are exempt** — they are the well-founded base case,
/// vouched by the §3.6 EDB-snapshot gate (which proves the sealed table == the live
/// EDB), so they need no support edge. An edge MAY still cite an extensional fact
/// (e.g. a fact-clause model), which is fine; the exemption is only for the "no junk"
/// coverage so a pure-leaf EDB predicate is not flagged as unsupported.
pub(super) fn check_cert_support(
    view: &CertView<'_>,
    place: CertPlace,
    program: &dyn Program,
    theory: &dyn Theory,
    extensional: &PredicateSet,
) -> Result<(), (RejectionCode, String)> {
    let cert = view.cert;
    let unsupported = |detail: String| (RejectionCode::CertUnsupported, detail);

    // §3.5 RANK CONSISTENCY pre-pass. Pin each sealed fact's support rank to the rank
    // on its OWN edge, so a same-stratum citation cannot fabricate a descending chain
    // unanchored to a real derivation order. A fact with two edges carrying DIFFERENT
    // ranks is itself ill-formed (no consistent well-founded measure) → reject.
    // #2511: keyed by the fact itself (structural equality is the relation the canonical key
    // encodes), so the support check encodes no key and makes no ordered comparison.
    let mut fact_edge_rank: HashMap<&GroundLiteral, u32> = HashMap::new();
    for edge in &cert.supports.0 {
        let key = &edge.fact;
        match fact_edge_rank.get(key) {
            Some(existing) if *existing != edge.rank => {
                return Err(unsupported(format!(
                    "fact {:?} has inconsistent edge ranks {} and {}",
                    String::from_utf8_lossy(edge.fact.pred.bytes()),
                    existing,
                    edge.rank
                )));
            }
            _ => {
                fact_edge_rank.insert(key, edge.rank);
            }
        }
    }

    // Track which facts have a valid support edge — to enforce "no junk" (every
    // extension fact must be covered). Keyed by the fact (#2511).
    let mut covered: HashSet<&GroundLiteral> = HashSet::new();

    for edge in &cert.supports.0 {
        // The supported fact must be a sealed (scope) predicate and present in its table.
        if !cert.scope.seals(&edge.fact.pred) {
            return Err(unsupported(format!(
                "support edge fact predicate {:?} is not sealed by the cert scope",
                String::from_utf8_lossy(edge.fact.pred.bytes())
            )));
        }
        let Some(table) = cert.table(&edge.fact.pred) else {
            return Err(unsupported(
                "support edge fact has no sealed extension".into(),
            ));
        };
        if !view.contains(table, &edge.fact) {
            return Err(unsupported(
                "support edge fact absent from its sealed table".into(),
            ));
        }
        // The cited clause must exist and ground (via subst) to head == fact.
        let Some(clause) = program.clause(&edge.clause) else {
            return Err(unsupported(format!(
                "support edge cites unknown clause {:?}",
                edge.clause.as_str()
            )));
        };
        let Some(head) = clause.head.substitute(&edge.subst).as_ground() else {
            return Err(unsupported(
                "support clause head not ground under subst".into(),
            ));
        };
        if head != edge.fact {
            return Err(unsupported("support clause head != supported fact".into()));
        }
        // One body ref per clause body literal, in body order; each ref resolves.
        if edge.body_refs.len() != clause.body.len() {
            return Err(unsupported(format!(
                "support edge has {} body refs != clause body length {}",
                edge.body_refs.len(),
                clause.body.len()
            )));
        }
        for (k, (body_lit, body_ref)) in clause.body.iter().zip(&edge.body_refs).enumerate() {
            // #2258 L3.3b: a count body literal is resolved by a `CountLower` ref against the
            // strictly lower certificate it reads (step 3 admitted it only over such a table).
            if let BodyLit::Count(count) = body_lit {
                let SupportRef::CountLower { cert: cited } = body_ref else {
                    return Err(unsupported(format!(
                        "support body ref {k} kind does not match body literal polarity (a count needs a CountLower ref)"
                    )));
                };
                super::cert_count::resolve_count_lower(k, count, *cited, &edge.subst, view, place)?;
                continue;
            }
            let Some(grounded) = body_lit
                .substitute(&edge.subst)
                .as_inner()
                .and_then(|goal| goal.as_ground())
            else {
                return Err(unsupported(format!(
                    "support body literal {k} not ground under subst"
                )));
            };
            resolve_support_ref(
                k,
                body_lit,
                body_ref,
                &grounded,
                edge.rank,
                view,
                place,
                theory,
                &fact_edge_rank,
                extensional,
            )?;
        }
        covered.insert(&edge.fact);
    }

    // No junk: every IDB fact in every extension must be covered by a support edge.
    // Extensional (EDB) facts are exempt — they are base facts, bound by the §3.6 EDB
    // snapshot gate, not by support.
    for table in &cert.extensions {
        if extensional.contains(&table.pred) {
            continue; // EDB predicate — covered by the EDB snapshot, not support.
        }
        for fact in &table.rows {
            if !covered.contains(fact) {
                return Err(unsupported(format!(
                    "sealed fact {:?} has no support edge (junk / unfounded)",
                    String::from_utf8_lossy(fact.pred.bytes())
                )));
            }
        }
    }
    Ok(())
}

/// Resolve one body reference of a support edge, enforcing the polarity match with
/// the body literal and the rank-consistent strict same-stratum descent (§3.5).
#[allow(clippy::too_many_arguments)]
fn resolve_support_ref(
    k: usize,
    body_lit: &BodyLit<Term>,
    body_ref: &SupportRef,
    grounded: &GroundLiteral,
    fact_rank: u32,
    view: &CertView<'_>,
    place: CertPlace,
    theory: &dyn Theory,
    fact_edge_rank: &HashMap<&GroundLiteral, u32>,
    extensional: &PredicateSet,
) -> Result<(), (RejectionCode, String)> {
    let cert = view.cert;
    let unsupported = |detail: String| (RejectionCode::CertUnsupported, detail);
    match (body_lit, body_ref) {
        // Positive body literal, same-stratum dependency: present in a sealed table,
        // STRICTLY SMALLER rank than the citing fact (the p:-p / cyclic trap defense),
        // AND the claimed rank must EQUAL the rank at which the dep is ITSELF supported
        // (§3.5 rank consistency — a fabricated descending chain cannot anchor to a
        // real base case, so an unfounded cycle has no consistent rank assignment).
        (BodyLit::Pos(_), SupportRef::SameStratum { fact, rank }) => {
            if fact != grounded {
                return Err(unsupported(format!(
                    "support body ref {k} fact != grounded body literal"
                )));
            }
            if *rank >= fact_rank {
                return Err(unsupported(format!(
                    "support body ref {k} rank {rank} not strictly < fact rank {fact_rank} (unfounded)"
                )));
            }
            // The dep must itself be supported at exactly the claimed rank.
            match fact_edge_rank.get(fact) {
                Some(actual) if *actual == *rank => {}
                Some(actual) => {
                    return Err(unsupported(format!(
                        "support body ref {k} claims rank {rank} but dep is supported at rank {actual} (fabricated rank)"
                    )))
                }
                None => {
                    return Err(unsupported(format!(
                        "support body ref {k} same-stratum dep has no support edge (cannot anchor rank)"
                    )))
                }
            }
            match cert.table(&fact.pred) {
                Some(t) if view.contains(t, fact) => Ok(()),
                _ => Err(unsupported(format!(
                    "same-stratum dep {k} absent from its sealed table"
                ))),
            }
        }
        // Positive body literal, lower-stratum dependency: present in the sealed table it
        // cites — this cert's own (an extensional predicate it seals), or since #2258 (a) the
        // exact table of the strictly lower certificate the predicate resolves to.
        (BodyLit::Pos(_), SupportRef::LowerStratum { cert: cited, atom }) => {
            let lower = check_support_ref_cert(k, *cited, &atom.pred, view, place)?;
            if atom != grounded {
                return Err(unsupported(format!(
                    "support body ref {k} lower atom != grounded body literal"
                )));
            }
            // A strictly lower certificate is exact on its own (verified first), so a positive
            // dependency on one of its IDB facts needs no rank anchor here.
            if let Some((index, table)) = lower {
                return if view.contains(table, atom) {
                    Ok(())
                } else {
                    Err(unsupported(format!(
                        "lower-stratum dep {k} absent from certificate {index}'s sealed table"
                    )))
                };
            }
            // INTRA-PREFIX BAN (support-rank soundness): a `LowerStratum` ref to a
            // sealed INTENSIONAL predicate is illegal — an intra-prefix IDB dependency
            // is, in the worst case, mutually recursive (same SCC), so it MUST go
            // through the rank-anchored `SameStratum` path. Else a positive cycle
            // (p:-q. q:-p.) launders through LowerStratum with no rank gate, sealing an
            // E ⊋ LM. A sealed EXTENSIONAL (EDB) predicate IS a legitimate lower base
            // case (acyclic), so a LowerStratum ref to it is allowed.
            if cert.scope.seals(&atom.pred) && !extensional.contains(&atom.pred) {
                return Err(unsupported(format!(
                    "support body ref {k}: intra-prefix positive dependency on sealed intensional predicate {:?} must be cited as SameStratum with strict rank descent, not LowerStratum",
                    String::from_utf8_lossy(atom.pred.bytes())
                )));
            }
            match cert.table(&atom.pred) {
                Some(t) if view.contains(t, atom) => Ok(()),
                _ => Err(unsupported(format!(
                    "lower-stratum dep {k} absent from the sealed table"
                ))),
            }
        }
        // Positive body literal, builtin: decided Holds by the pinned Theory. A stop is refused by
        // name (#3126), never read as the literal's truth.
        (BodyLit::Pos(_), SupportRef::Builtin { atom }) => {
            if atom != grounded {
                return Err(unsupported(format!(
                    "support body ref {k} builtin atom != grounded body literal"
                )));
            }
            if !theory.owns(&atom.pred) {
                return Err(unsupported(format!(
                    "support builtin ref {k} predicate not theory-owned"
                )));
            }
            match theory.decide_ground(atom) {
                Completion::Completed(TheoryDecision::Holds) => Ok(()),
                Completion::LimitExceeded(never) => match never {},
                Completion::NotCompleted(cause) if !is_disowned(&cause) => {
                    Err(builtin_not_decided(cause))
                }
                Completion::Completed(TheoryDecision::Fails { .. })
                | Completion::NotCompleted(_) => Err(unsupported(format!(
                    "support builtin ref {k} does not hold"
                ))),
            }
        }
        // Negated body literal, lower-stratum negative dep: ABSENT from a STRICTLY
        // LOWER, separately-sealed stratum — since #2258 (a), the exact table of the strictly
        // lower certificate the predicate resolves to. A `NegLower` ref to a predicate sealed
        // by THIS prefix stays illegal (intra-prefix negation laundered through the support
        // witness).
        (BodyLit::Neg(_), SupportRef::NegLower { cert: cited, atom }) => {
            let lower = check_support_ref_cert(k, *cited, &atom.pred, view, place)?;
            if atom != grounded {
                return Err(unsupported(format!(
                    "support body ref {k} neg-lower atom != grounded body literal"
                )));
            }
            if let Some((index, table)) = lower {
                return if view.contains(table, atom) {
                    Err(unsupported(format!(
                        "neg-lower dep {k} is PRESENT in certificate {index}'s sealed table (negation fails)"
                    )))
                } else {
                    Ok(())
                };
            }
            if cert.scope.seals(&atom.pred) {
                return Err(unsupported(format!(
                    "support body ref {k}: NegLower negated dependency on sealed predicate {:?} is intra-prefix (negation must target a strictly-lower, separately-sealed stratum)",
                    String::from_utf8_lossy(atom.pred.bytes())
                )));
            }
            match cert.table(&atom.pred) {
                Some(t) if !view.contains(t, atom) => Ok(()),
                Some(_) => Err(unsupported(format!(
                    "neg-lower dep {k} is PRESENT in the sealed table (negation fails)"
                ))),
                None => Err(unsupported(format!(
                    "neg-lower dep {k} predicate is not sealed"
                ))),
            }
        }
        // Any other (polarity, ref-kind) pairing is a malformed support edge.
        (_, _) => Err(unsupported(format!(
            "support body ref {k} kind does not match body literal polarity"
        ))),
    }
}

/// #2258: the cert index a `LowerStratum` / `NegLower` support ref names must be one this checker
/// can honour. An index outside `closed_world` is `cert_out_of_range`, as for a `Neg` premise
/// (C3). The ref's OWN cert resolves against its own tables, as it always has (`Ok(None)`). Any
/// other index must be the certificate the ref's predicate RESOLVED to (#2258 (a)): the unique,
/// exact, Valid certificate at a strictly lower level that seals it, whose table is returned.
/// Validity precedes citation because statuses are computed in level order before support runs.
/// Anything else is `cert_unsupported`.
pub(super) fn check_support_ref_cert<'a>(
    k: usize,
    cited: CertId,
    pred: &crate::literal::Symbol,
    view: &CertView<'a>,
    place: CertPlace,
) -> Result<Option<(usize, &'a RelationTable)>, (RejectionCode, String)> {
    // A protocol index, an offset only if it names a carried cert (#2735).
    let Some(idx) = cited.offset(place.world_len) else {
        return Err((
            RejectionCode::CertOutOfRange,
            format!(
                "support body ref {k} cites cert {} out of range {}",
                cited.index(),
                place.world_len
            ),
        ));
    };
    if idx == place.own {
        return Ok(None);
    }
    match (view.lower_index(pred), view.table(pred)) {
        (Some(j), Some(table)) if j == idx => Ok(Some((idx, table))),
        _ => Err((
            RejectionCode::CertUnsupported,
            format!(
                "support body ref {k} cites cert {idx}, which is neither its own cert {} nor the unique exact certificate at a strictly lower level sealing {:?} (#2258 (a))",
                place.own,
                String::from_utf8_lossy(pred.bytes())
            ),
        )),
    }
}
