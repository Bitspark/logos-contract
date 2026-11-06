//! #2294 (ruled `seat:caa`): `Term::is_open_compound`, the ONE classification of "compound" the
//! function-free fragment excludes. Identical rows in contract/go and contract/ts.

use logos_contract::Term;

fn atom(s: &str) -> Term {
    Term::atom(s.as_bytes().to_vec())
}

#[test]
fn only_a_tuple_with_a_variable_is_an_open_compound_2294() {
    let f = |t: Term| Term::tuple([atom("f"), t]);
    let g = |t: Term| Term::tuple([atom("g"), t]);
    let text = Term::tuple([atom("utf8-text"), atom("a")]);
    let rows = [
        ("an atom", atom("a"), false),
        ("a variable", Term::var("X"), false),
        ("a string", text, false),
        ("f(a)", f(atom("a")), false),
        ("f(g(a))", f(g(atom("a"))), false),
        ("f(X)", f(Term::var("X")), true),
        ("f(g(X))", f(g(Term::var("X"))), true),
    ];
    for (name, term, open) in rows {
        assert_eq!(term.is_open_compound(), open, "{name}");
    }
}
