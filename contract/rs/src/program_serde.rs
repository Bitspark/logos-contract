//! §10 Program (de)serialization — a clause [`MapProgram`] ⇄ a ground `ontos::Value`,
//! with **canonical, byte-deterministic** [`ontos-codec-v1`](ontos_codec) output
//! (issue #310). **[STABLE v1 shape · byte form additive over the FROZEN account]**
//!
//! A consumer's whole policy is a [`MapProgram`] — a `ClauseId → Clause` map. To
//! store, transmit, or content-address a *whole program* (not just a single clause)
//! it must become ordinary ground data and back. This is the program-level analogue
//! of the §2a `quote`/`reify` term reification and the §9 per-clause account codec;
//! it **reuses** both, so it introduces no new frozen bytes:
//!
//! ```text
//! program_to_value(p)   = Tuple[ Atom(VERSION), entry₀, entry₁, …, entry_{n-1} ]
//! entryᵢ                = Tuple[ Atom(<clause-id utf8 bytes>), clause_value(clauseᵢ) ]
//! ```
//!
//! where `clause_value` is the **frozen** account encoding ([`clause_value`]) of a
//! clause's `head :- body` (head + polarity-tagged body via the §2a `quote` tags and
//! the ADR-0007 `NEG_TAG`). The entries are emitted in **canonical order — sorted by
//! the clause-id bytes** — so the value (and hence its `ontos-codec-v1` bytes) is
//! **independent of `MapProgram` insertion order**: two programs with the same
//! `(id, clause)` set serialize to byte-identical output. The leading `Atom(VERSION)`
//! domain-separates the shape and lets a future revision be a new tag, never an edit.
//!
//! **Canonical bytes** of a program are therefore
//! `ontos_codec::encode(&program_to_value(p)?)` — the single cross-language pin all
//! three bindings reproduce ([`vectors/program_serde.json`]). `ontos-codec-v1` is the
//! frozen canonical encoding (one byte string per ground value), so the determinism
//! is inherited from it: identical `Value` ⟹ identical bytes, in every core.
//!
//! ## The reserved predicate symbol (why serialization is *fallible*)
//!
//! The frozen account body-literal encoding ([`body_lit_as_term`]) is **not injective**
//! over arbitrary predicate symbols: it reads a positive literal as the bare
//! `goal_as_term(g) = Tuple[Atom(pred), args…]` and a negated one as
//! `Tuple[Atom([NEG_TAG=0x00]), goal_as_term(g)]`. A *positive* literal whose predicate
//! symbol is exactly the single byte `[0x00]` **and** which has exactly one argument
//! therefore encodes to `Tuple[Atom([0x00]), arg]` — byte-identical to a `Neg` reading,
//! so a decoder cannot recover the polarity. (`Symbol`/`Goal` accept arbitrary bytes
//! with no validation, so such a degenerate clause is reachable via the public API.)
//!
//! Because the account encoding is **frozen** (its bytes feed `clause_bytes` /
//! `program_digest`, which are cross-core vectored), the sound fix is to **reserve**
//! the byte `0x00` as the body-literal negation tag: it is **not a valid predicate
//! name** in a serializable program. [`program_to_value`] / [`program_bytes`] therefore
//! **reject** (with [`ProgramSerdeError::ReservedPredicateSymbol`]) any clause whose
//! head or body-literal predicate equals `[NEG_TAG]`, rather than emit ambiguous bytes.
//! Over the **accepted** (`Ok`) programs the round-trip law is then **total**:
//! `program_from_value(program_to_value(p)?)` equals `p`. (A NUL-byte predicate name is
//! degenerate; no real program carries one — the representative byte-pin vector uses
//! none, so its pinned bytes are unaffected.)
//!
//! [`body_lit_as_term`]: crate::account
//! [`vectors/program_serde.json`]: the cross-core byte-pin replayed by
//! `contract/rs/tests/program_serde_vectors.rs` and the Go/TS siblings.

use crate::account::{clause_from_value, clause_value};
use crate::program::{Clause, ClauseId, MapProgram, Program};
use ontos_core::Value;

/// The version/shape tag atom that heads a serialized program (domain separation —
/// distinct from the §2a `quote` tags and the §9 clause prefix). Frozen v1.
pub const PROGRAM_SERDE_VERSION: &[u8] = b"logos/program/v1";

/// The single byte the frozen account encoding reserves as the body-literal **negation
/// tag** (ADR-0007 `NEG_TAG`). A goal whose predicate symbol equals this byte cannot be
/// serialized unambiguously, so it is **not a valid predicate name** in a serializable
/// program (see the module note). Mirrors `account::NEG_TAG`.
pub const RESERVED_PREDICATE_SYMBOL: &[u8] = &[0x00];

/// The single byte the frozen account encoding reserves as the body-literal **count
/// tag** (ADR-0023 `COUNT_TAG`). Like [`RESERVED_PREDICATE_SYMBOL`], a goal whose
/// predicate symbol equals this byte could collide with the sealed count reading, so it
/// is not a valid predicate name in a serializable program. Mirrors `account::COUNT_TAG`.
pub const RESERVED_COUNT_SYMBOL: &[u8] = &[0x01];

/// Every predicate symbol the account encoding reserves (#2247): the negation tag and the count
/// tag. A positive literal whose predicate is one of these reads exactly like the tagged literal,
/// so it shares that literal's clause bytes, canonical id and program digest, and decodes as it.
/// With both excluded from the predicate domain the reading is injective, so every ingress that
/// makes a caller's clause identity-bearing or executable refuses them through
/// [`reserved_predicate`].
pub const RESERVED_PREDICATE_SYMBOLS: [&[u8]; 2] =
    [RESERVED_PREDICATE_SYMBOL, RESERVED_COUNT_SYMBOL];

/// The first reserved predicate symbol (see [`RESERVED_PREDICATE_SYMBOLS`]) `clause` carries: on
/// its head or any body literal, the counted predicate of a count literal included. `None` when it
/// carries none. The one check every ingress shares (#2247).
pub fn reserved_predicate(clause: &Clause) -> Option<&[u8]> {
    std::iter::once(clause.head.pred.bytes())
        .chain(clause.body.iter().map(|lit| lit.pred().bytes()))
        .find(|pred| RESERVED_PREDICATE_SYMBOLS.contains(pred))
}

/// Why a [`Value`] is not a well-formed serialized program (the inverse,
/// [`program_from_value`], is partial). Each variant pins a precise structural
/// failure so a malformed input is *rejected*, never silently coerced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramSerdeError {
    /// The top-level value was not a `Tuple` (so it has no version tag / entries).
    NotATuple,
    /// The leading child was not the expected `Atom(PROGRAM_SERDE_VERSION)`.
    BadVersion,
    /// An entry was not the expected 2-tuple `Tuple[Atom(id), clause_value]`.
    BadEntry,
    /// An entry's clause value was not in the image of [`clause_value`] (it did not
    /// `reify` to a well-formed `head :- body` clause term).
    BadClause,
    /// Two entries carried the same clause id (a `MapProgram` key must be unique).
    DuplicateClauseId(String),
    /// A clause carried a goal (head or body literal) whose predicate symbol equals the
    /// reserved [`RESERVED_PREDICATE_SYMBOL`] (the `NEG_TAG` byte `0x00`), which the
    /// frozen account encoding cannot serialize unambiguously. Carries the offending
    /// clause id and the predicate bytes (lowercase hex) for diagnostics. Returned only
    /// by [`program_to_value`] / [`program_bytes`] (the *encode* direction).
    ReservedPredicateSymbol {
        /// The id of the clause that carried the reserved predicate.
        clause_id: String,
        /// The reserved predicate's bytes, as lowercase hex.
        predicate_hex: String,
    },
}

impl core::fmt::Display for ProgramSerdeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProgramSerdeError::NotATuple => write!(f, "program value is not a Tuple"),
            ProgramSerdeError::BadVersion => {
                write!(f, "program value has a bad/missing version tag")
            }
            ProgramSerdeError::BadEntry => {
                write!(f, "program entry is not a Tuple[Atom(id), clause]")
            }
            ProgramSerdeError::BadClause => write!(f, "program entry's clause value is malformed"),
            ProgramSerdeError::DuplicateClauseId(id) => {
                write!(f, "duplicate clause id in serialized program: {id}")
            }
            ProgramSerdeError::ReservedPredicateSymbol {
                clause_id,
                predicate_hex,
            } => write!(
                f,
                "clause {clause_id} carries a reserved predicate symbol 0x{predicate_hex} \
                 (an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)"
            ),
        }
    }
}

impl std::error::Error for ProgramSerdeError {}

/// Lowercase-hex of a byte slice (for the reserved-symbol diagnostic).
fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// Reject a clause that carries the reserved predicate symbol on its head or any body
/// literal — the encode-time guard that keeps the round-trip total (see the module
/// note). Returns the offending clause's reserved-symbol error, or `Ok(())`.
fn check_no_reserved_predicate(id: &ClauseId, clause: &Clause) -> Result<(), ProgramSerdeError> {
    match reserved_predicate(clause) {
        Some(pred) => Err(ProgramSerdeError::ReservedPredicateSymbol {
            clause_id: id.as_str().to_string(),
            predicate_hex: to_hex(pred),
        }),
        None => Ok(()),
    }
}

/// Serialize a [`MapProgram`] to its canonical ground [`Value`] (§10).
///
/// **Fallible** — returns [`ProgramSerdeError::ReservedPredicateSymbol`] if any clause
/// carries a goal (head or body literal) whose predicate symbol equals the reserved
/// `NEG_TAG` byte `0x00` ([`RESERVED_PREDICATE_SYMBOL`]); such a clause cannot be
/// serialized unambiguously under the frozen account encoding (see the module note). For
/// every **accepted** program there is exactly one canonical value. The clause entries
/// are emitted **sorted by clause-id bytes** (the `BTreeMap` backing `MapProgram` already
/// iterates in `ClauseId` order, which is byte-lexicographic on the id string — the same
/// total order the canonical sort fixes), so the output is independent of how the program
/// was built. The canonical **bytes** are `ontos_codec::encode` of this.
pub fn program_to_value(program: &MapProgram) -> Result<Value, ProgramSerdeError> {
    let mut children = Vec::with_capacity(program.len() + 1);
    children.push(Value::atom(PROGRAM_SERDE_VERSION.to_vec()));
    // `MapProgram` iterates its `BTreeMap` in `ClauseId` (byte-lexicographic) order —
    // the canonical clause order. We collect, then sort defensively by id bytes so the
    // ordering is pinned by THIS function, not only by the backing container. The
    // reserved-predicate guard runs over every clause first (a fail-closed encode).
    let mut entries: Vec<(&ClauseId, Value)> = Vec::with_capacity(program.len());
    for (id, clause) in program.iter() {
        check_no_reserved_predicate(id, clause)?;
        entries.push((id, clause_value(clause)));
    }
    entries.sort_by(|a, b| a.0.as_str().as_bytes().cmp(b.0.as_str().as_bytes()));
    for (id, value) in entries {
        children.push(Value::tuple([
            Value::atom(id.as_str().as_bytes().to_vec()),
            value,
        ]));
    }
    Ok(Value::tuple(children))
}

/// The canonical **bytes** of a program: `ontos-codec-v1(program_to_value(p)?)`. The
/// single cross-language byte-pin (`vectors/program_serde.json`). **Fallible** for the
/// same reserved-predicate reason as [`program_to_value`].
pub fn program_bytes(program: &MapProgram) -> Result<Vec<u8>, ProgramSerdeError> {
    Ok(ontos_codec::encode(&program_to_value(program)?))
}

/// The partial inverse of [`program_to_value`]: rebuild the [`MapProgram`] a value
/// denotes, or a [`ProgramSerdeError`] if `value` is not in the image of
/// `program_to_value` (§10). The round-trip law is **total over accepted programs**:
/// for any `p` that [`program_to_value`] accepts (i.e. carries no reserved predicate
/// symbol), `program_from_value(program_to_value(p).unwrap())` equals `p`. A program
/// with a reserved predicate symbol is rejected at *encode* time, so it never produces
/// a value to invert.
pub fn program_from_value(value: &Value) -> Result<MapProgram, ProgramSerdeError> {
    let Value::Tuple(tuple) = value else {
        return Err(ProgramSerdeError::NotATuple);
    };
    let items = tuple.items();
    let Some((version, entries)) = items.split_first() else {
        return Err(ProgramSerdeError::BadVersion);
    };
    match version.as_atom() {
        Some(a) if a.bytes() == PROGRAM_SERDE_VERSION => {}
        _ => return Err(ProgramSerdeError::BadVersion),
    }
    let mut program = MapProgram::new();
    for entry in entries {
        let Value::Tuple(pair) = entry else {
            return Err(ProgramSerdeError::BadEntry);
        };
        let [id_value, clause_value_v] = pair.items() else {
            return Err(ProgramSerdeError::BadEntry);
        };
        let Some(id_atom) = id_value.as_atom() else {
            return Err(ProgramSerdeError::BadEntry);
        };
        // The id was serialized from a `ClauseId`'s UTF-8 handle bytes; reject a
        // non-UTF-8 id (a `ClauseId` handle is a `String`, so a well-formed program
        // never carries one).
        let id = std::str::from_utf8(id_atom.bytes()).map_err(|_| ProgramSerdeError::BadEntry)?;
        let clause = clause_from_value(clause_value_v).ok_or(ProgramSerdeError::BadClause)?;
        if program.clause(&ClauseId::new(id)).is_some() {
            return Err(ProgramSerdeError::DuplicateClauseId(id.to_string()));
        }
        program.insert(ClauseId::new(id), clause);
    }
    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Goal;
    use crate::program::{Clause, Program};
    use crate::term::Term;

    fn clause(head_pred: &str, head_args: Vec<Term>, body: Vec<Goal>) -> Clause {
        Clause::new(Goal::new(head_pred, head_args), body)
    }

    /// A representative program: facts, a rule with a body, vars, a negated body
    /// literal, a nested compound, an int embedding, and a nullary goal.
    fn representative() -> MapProgram {
        let mut p = MapProgram::new();
        // edge(a, b).
        p.insert(
            ClauseId::new("edge_ab"),
            Clause::fact(Goal::new("edge", [Term::atom(*b"a"), Term::atom(*b"b")])),
        );
        // reach(X, Z) :- edge(X, Y), reach(Y, Z).   (vars + multi-literal body)
        p.insert(
            ClauseId::new("reach_rec"),
            clause(
                "reach",
                vec![Term::var("X"), Term::var("Z")],
                vec![
                    Goal::new("edge", [Term::var("X"), Term::var("Y")]),
                    Goal::new("reach", [Term::var("Y"), Term::var("Z")]),
                ],
            ),
        );
        // permit(S, A) :- grant(S, A), \+ denied(S, A).   (a negated body literal)
        p.insert(
            ClauseId::new("permit"),
            Clause::with_neg(
                Goal::new("permit", [Term::var("S"), Term::var("A")]),
                [Goal::new("grant", [Term::var("S"), Term::var("A")])],
                [Goal::new("denied", [Term::var("S"), Term::var("A")])],
            ),
        );
        // p(pair(q, "x"), int(7)).   (a nested compound + the int embedding + an atom)
        let int7 = Term::tuple([Term::atom(b"int".to_vec()), Term::atom(vec![0x00, 0x07])]);
        p.insert(
            ClauseId::new("nested"),
            Clause::fact(Goal::new(
                "p",
                [
                    Term::tuple([Term::atom(*b"pair"), Term::atom(*b"q"), Term::atom(*b"x")]),
                    int7,
                ],
            )),
        );
        // nullary().   (a 0-ary goal — Tuple[Atom("nullary")], distinct from atom)
        p.insert(
            ClauseId::new("nullary"),
            Clause::fact(Goal::new("nullary", [])),
        );
        p
    }

    fn assert_round_trips(p: &MapProgram) {
        let value = program_to_value(p).expect("serializes");
        let back = program_from_value(&value).expect("round-trips");
        // Same id set and same clause per id.
        let mut ids_p: Vec<String> = Vec::new();
        p.for_each_clause(&mut |id, _| ids_p.push(id.as_str().to_string()));
        let mut ids_b: Vec<String> = Vec::new();
        back.for_each_clause(&mut |id, _| ids_b.push(id.as_str().to_string()));
        assert_eq!(ids_p, ids_b, "clause id sets differ");
        p.for_each_clause(&mut |id, clause| {
            assert_eq!(
                back.clause(id),
                Some(clause),
                "clause {} differs",
                id.as_str()
            );
        });
    }

    #[test]
    fn empty_program_round_trips() {
        let p = MapProgram::new();
        assert_round_trips(&p);
        // The empty program is just the version tag tuple.
        assert_eq!(
            program_to_value(&p).expect("serializes"),
            Value::tuple([Value::atom(PROGRAM_SERDE_VERSION.to_vec())])
        );
    }

    #[test]
    fn representative_program_round_trips() {
        assert_round_trips(&representative());
    }

    #[test]
    fn serialization_is_insertion_order_independent() {
        // Build the SAME (id, clause) set in two different insertion orders; the
        // canonical value (and its bytes) must be byte-identical.
        let mut a = MapProgram::new();
        a.insert(ClauseId::new("z"), Clause::fact(Goal::new("z", [])));
        a.insert(ClauseId::new("a"), Clause::fact(Goal::new("a", [])));
        a.insert(ClauseId::new("m"), Clause::fact(Goal::new("m", [])));
        let mut b = MapProgram::new();
        b.insert(ClauseId::new("a"), Clause::fact(Goal::new("a", [])));
        b.insert(ClauseId::new("m"), Clause::fact(Goal::new("m", [])));
        b.insert(ClauseId::new("z"), Clause::fact(Goal::new("z", [])));
        assert_eq!(
            program_to_value(&a).expect("serializes"),
            program_to_value(&b).expect("serializes")
        );
        assert_eq!(
            program_bytes(&a).expect("serializes"),
            program_bytes(&b).expect("serializes")
        );
    }

    #[test]
    fn reserved_predicate_symbol_is_rejected_on_encode() {
        use crate::literal::Symbol;
        // A POSITIVE body literal whose predicate is the reserved NEG_TAG byte 0x00 with
        // exactly one arg would encode byte-identically to a Neg literal — a silent
        // Pos→Neg flip. The encoder must REJECT it (never emit ambiguous bytes).
        let reserved_pred = Goal {
            pred: Symbol::new(vec![0x00]),
            args: vec![Term::atom(*b"a")],
        };
        let mut body_offender = MapProgram::new();
        body_offender.insert(
            ClauseId::new("c1"),
            Clause::new(Goal::new("p", []), [reserved_pred]),
        );
        match program_to_value(&body_offender) {
            Err(ProgramSerdeError::ReservedPredicateSymbol {
                clause_id,
                predicate_hex,
            }) => {
                assert_eq!(clause_id, "c1");
                assert_eq!(predicate_hex, "00");
            }
            other => panic!("expected ReservedPredicateSymbol, got {other:?}"),
        }
        // program_bytes is fallible for the same reason.
        assert!(program_bytes(&body_offender).is_err());

        // The HEAD is checked too (uniform rule).
        let mut head_offender = MapProgram::new();
        head_offender.insert(
            ClauseId::new("c2"),
            Clause::fact(Goal {
                pred: Symbol::new(vec![0x00]),
                args: vec![Term::atom(*b"x")],
            }),
        );
        assert!(matches!(
            program_to_value(&head_offender),
            Err(ProgramSerdeError::ReservedPredicateSymbol { .. })
        ));
    }

    /// Assert `program_from_value(value)` rejects with exactly `want`.
    fn assert_rejects(value: &Value, want: ProgramSerdeError) {
        match program_from_value(value) {
            Ok(_) => panic!("expected {want:?}, got Ok"),
            Err(got) => assert_eq!(got, want),
        }
    }

    #[test]
    fn from_value_rejects_malformed_input() {
        // Not a tuple.
        assert_rejects(&Value::atom(*b"x"), ProgramSerdeError::NotATuple);
        // Wrong version tag.
        assert_rejects(
            &Value::tuple([Value::atom(*b"wrong")]),
            ProgramSerdeError::BadVersion,
        );
        // A non-tuple entry.
        assert_rejects(
            &Value::tuple([
                Value::atom(PROGRAM_SERDE_VERSION.to_vec()),
                Value::atom(*b"bad"),
            ]),
            ProgramSerdeError::BadEntry,
        );
        // An entry whose clause value is not a quoted clause term.
        assert_rejects(
            &Value::tuple([
                Value::atom(PROGRAM_SERDE_VERSION.to_vec()),
                Value::tuple([Value::atom(*b"id"), Value::atom(*b"not-a-clause")]),
            ]),
            ProgramSerdeError::BadClause,
        );
    }

    #[test]
    fn duplicate_clause_id_is_rejected() {
        let one = clause_value(&Clause::fact(Goal::new("p", [])));
        let dup = Value::tuple([
            Value::atom(PROGRAM_SERDE_VERSION.to_vec()),
            Value::tuple([Value::atom(*b"same"), one.clone()]),
            Value::tuple([Value::atom(*b"same"), one]),
        ]);
        assert_rejects(
            &dup,
            ProgramSerdeError::DuplicateClauseId("same".to_string()),
        );
    }
}
