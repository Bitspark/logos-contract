//! #2247: a positive literal whose predicate is an account tag byte (0x00 negation, 0x01 count)
//! reads exactly like the tagged literal, so it shares that literal's clause bytes, id and program
//! digest. Every ingress refuses it by name (seat:caa, issuecomment-5812420549). The same
//! witnesses are pinned in contract/go and contract/ts; K6, the kernel's analysis front door, is
//! pinned in each kernel.

use logos_contract::{
    load_prelude, program_bytes, program_to_value, reserved_predicate, Clause, Goal, MapProgram,
    PreludeError, ProgramSerdeError, Symbol, Term, RESERVED_PREDICATE_SYMBOLS,
};

/// A goal whose predicate is the raw byte `tag`.
fn tagged(tag: u8, args: Vec<Term>) -> Goal {
    Goal {
        pred: Symbol::new(vec![tag]),
        args,
    }
}

/// K1's B: `p(Y) :- r(Y), <0x00>(q(Y)).`, a positive literal that reads as `\+ q(Y)`.
fn k1_b() -> Clause {
    let y = Term::var("Y");
    Clause::new(
        Goal::new("p", [y.clone()]),
        [
            Goal::new("r", [y.clone()]),
            tagged(0x00, vec![Term::tuple([Term::atom(b"q".to_vec()), y])]),
        ],
    )
}

/// K2's D: `n(N) :- <0x01>(N).`, a positive literal led by the count tag.
fn k2_d() -> Clause {
    Clause::new(
        Goal::new("n", [Term::var("N")]),
        [tagged(0x01, vec![Term::var("N")])],
    )
}

#[test]
fn both_tag_bytes_are_reserved_2247() {
    assert_eq!(RESERVED_PREDICATE_SYMBOLS, [&[0x00u8][..], &[0x01u8][..]]);
    assert_eq!(reserved_predicate(&k1_b()), Some(&[0x00u8][..]));
    assert_eq!(reserved_predicate(&k2_d()), Some(&[0x01u8][..]));
    // A reserved head is caught too, and an ordinary clause carries none.
    let head = Clause::fact(tagged(0x01, vec![Term::atom(b"a".to_vec())]));
    assert_eq!(reserved_predicate(&head), Some(&[0x01u8][..]));
    let ordinary = Clause::fact(Goal::new("p", [Term::atom(b"a".to_vec())]));
    assert_eq!(reserved_predicate(&ordinary), None);
}

#[test]
fn program_serde_refuses_k1_and_k2_by_name_2247() {
    for (name, clause) in [("K1", k1_b()), ("K2", k2_d())] {
        let program = MapProgram::new().with("c", clause);
        for got in [
            program_to_value(&program).map(|_| ()),
            program_bytes(&program).map(|_| ()),
        ] {
            match got {
                Err(ProgramSerdeError::ReservedPredicateSymbol { .. }) => {}
                other => panic!("{name}: got {other:?}, want ReservedPredicateSymbol"),
            }
        }
    }
}

/// K5: a bundle carrying B is refused as `BadClause` BEFORE the digest check. The pinned digest
/// is deliberately wrong, so a `DigestMismatch` here would mean the refusal came too late.
#[test]
fn the_prelude_loader_refuses_a_reserved_predicate_before_the_digest_2247() {
    for tag in [0u8, 1u8] {
        let reserved = char::from(tag).to_string();
        let doc = serde_json::json!({
            "name": "t",
            "version": "0.0.0",
            "program_digest": "00".repeat(32),
            "clauses": [{"clause": {
                "head": {"pred": "p", "args": [{"var": "Y"}]},
                "body": [
                    {"pred": "r", "args": [{"var": "Y"}]},
                    {"pred": reserved, "args": [{"var": "Y"}]},
                ],
            }}],
        })
        .to_string();
        match load_prelude(&doc) {
            Err(PreludeError::BadClause { index: 0, reason }) => {
                assert!(reason.contains("reserved predicate"), "tag {tag}: {reason}")
            }
            other => panic!("tag {tag}: got {other:?}, want BadClause at index 0"),
        }
    }
}
