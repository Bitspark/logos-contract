//! Rust replay of `vectors/decider_completion.json`'s `declarations` (#3142, research 0031 row
//! 13): what each standard decider declares about completing, per theory as `seat:caa` ruled, a
//! compound routing to the owning member, and a theory that declares nothing reading `undeclared`
//! (fail closed). The go (`contract/go/decider_completion_3142_test.go`) and ts
//! (`contract/ts/test/decider_completion_3142.test.ts`) bindings replay the same rows, so the
//! declarations admission reads cannot differ by core.

use logos_contract::list_theory::ListTheory;
use logos_contract::term_theory::TermTheory;
use logos_contract::{
    standard_theory, ArithmeticTheory, GroundLiteral, Symbol, TextTheory, Theory, TheoryGround,
};
use serde_json::Value as Json;

const VECTORS: &str = include_str!("../../../vectors/decider_completion.json");

/// A consumer theory that owns `p` and declares nothing: no `completion`, no identity.
struct DeclaresNothing;
// test-double: consumer(a domain theory that declares nothing about completing)
impl Theory for DeclaresNothing {
    logos_contract::cannot_copy!(Theory, "a test double: never copied");
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"p"
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::holds()
    }
}

/// A consumer theory that owns `q` and declares that a decision may stop and still answer `Fails`:
/// the population the guard still refuses (host builtins until #3506, v1-only deciders). No standard
/// theory declares it after #3313, so the replay carries its own to exercise the kind.
struct StopsUntyped;
// test-double: consumer(a domain theory whose stops still surface as Fails)
impl Theory for StopsUntyped {
    logos_contract::cannot_copy!(Theory, "a test double: never copied");
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"q"
    }
    fn decide_ground(&self, _atom: &GroundLiteral) -> TheoryGround {
        TheoryGround::holds()
    }
    fn completion(&self, _pred: &Symbol) -> logos_contract::DecisionCompletion {
        logos_contract::DecisionCompletion::may_not_complete(
            logos_contract::ComponentIdentity::new(
                b"demo/stops-untyped-theory".to_vec(),
                b"1".to_vec(),
                [0; 32],
            ),
            "a stop surfaces as Fails",
        )
    }
}

fn theory(name: &str) -> Box<dyn Theory> {
    match name {
        "arithmetic" => Box::new(ArithmeticTheory::new()),
        "text" => Box::new(TextTheory::new()),
        "term" => Box::new(TermTheory::new()),
        "list" => Box::new(ListTheory::new()),
        "standard" => Box::new(standard_theory()),
        "undeclared" => Box::new(DeclaresNothing),
        "stops_untyped" => Box::new(StopsUntyped),
        other => panic!("unknown theory {other}"),
    }
}

#[test]
fn every_core_declares_the_same_completion_3142() {
    let v: Json = serde_json::from_str(VECTORS).expect("decider_completion.json parses");
    let rows = v["declarations"].as_array().expect("declarations");
    assert!(!rows.is_empty(), "the declarations section is empty");
    let mut tags = std::collections::BTreeSet::new();
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let t = theory(row["theory"].as_str().expect("theory"));
        let pred = Symbol::from(row["pred"].as_str().expect("pred"));
        let got = t.completion(&pred);
        let want = row["completion"].as_str().expect("completion");
        assert_eq!(got.tag(), want, "{name}: the declaration");
        assert_eq!(
            got.stops_are_typed(),
            want == "stops_are_typed",
            "{name}: stops_are_typed()"
        );
        match row.get("decider").and_then(Json::as_str) {
            Some(decider) => assert_eq!(
                got.decider().map(|d| d.id.as_slice()),
                Some(decider.as_bytes()),
                "{name}: the decider it names"
            ),
            None => assert!(
                got.decider().is_none(),
                "{name}: a completing decider names nobody"
            ),
        }
        tags.insert(want);
    }
    assert_eq!(
        tags.into_iter().collect::<Vec<_>>(),
        ["may_not_complete", "stops_are_typed", "undeclared"],
        "every declaration kind is exercised"
    );
}
