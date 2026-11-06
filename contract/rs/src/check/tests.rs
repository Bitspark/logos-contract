//! #2177 A2: the fast path's one-sidedness, as a differential test (`seat:caa`'s ruling on #2177).
//!
//! [`goal_eq_under_subst`] may only conclude EQUAL. The property: wherever it says equal, the
//! allocating path (`substitute` + `as_ground` + structural equality) says equal too. The
//! generator is weighted to near-misses, and the harness is shown RED against deliberately broken
//! fast paths, so a pass is evidence rather than an absence of inputs.
//!
//! Debug builds also re-check every fast "equal" inside `check` itself (`proved_equal_fast`), so
//! the whole `check` test corpus (vectors, tamper, forgery and mutation suites) is a second
//! differential over real derivations.

use super::*;

type FastFn = fn(&Goal, &Subst, &GroundLiteral) -> bool;

fn slow_equal(goal: &Goal, subst: &Subst, lit: &GroundLiteral) -> bool {
    goal.substitute(subst)
        .as_ground()
        .is_some_and(|ground| ground == *lit)
}

/// xorshift64*: deterministic, so a failure reproduces from its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Includes the cons and `list` spellings' own atoms, so accidental list shapes occur too.
const ATOMS: [&[u8]; 7] = [b"a", b"b", b"c", b"[]", b".", b"list", b""];

fn value(rng: &mut Rng, depth: usize) -> Value {
    if depth == 0 || rng.below(3) == 0 {
        Value::atom(ATOMS[rng.below(ATOMS.len() as u64) as usize].to_vec())
    } else {
        let n = rng.below(4) as usize;
        Value::tuple((0..n).map(|_| value(rng, depth - 1)).collect::<Vec<_>>())
    }
}

/// `[v0, v1, …]` in the logos surface spelling (cons cells).
fn cons_list(items: &[Value]) -> Value {
    items
        .iter()
        .rev()
        .fold(Value::atom(b"[]".to_vec()), |tail, head| {
            Value::tuple(vec![Value::atom(b".".to_vec()), head.clone(), tail])
        })
}

/// The same sequence in the flat `list(…)` spelling: a different term from [`cons_list`] (#3022).
fn flat_list(items: &[Value]) -> Value {
    let mut spelled = vec![Value::atom(b"list".to_vec())];
    spelled.extend(items.iter().cloned());
    Value::tuple(spelled)
}

/// Abstract `value` into a term: each subterm is either copied or replaced by a fresh variable
/// bound in `subst` to that subterm's ground image, so the result is equal under `subst`.
fn abstract_value(rng: &mut Rng, value: &Value, subst: &mut Subst, next_var: &mut usize) -> Term {
    if rng.below(3) == 0 {
        let name = format!("V{next_var}");
        *next_var += 1;
        subst.insert(name.clone().into(), Term::from_value(value));
        return Term::var(name);
    }
    match value {
        Value::Atom(atom) => Term::atom(atom.bytes().to_vec()),
        Value::Tuple(tuple) => Term::tuple(
            tuple
                .items()
                .iter()
                .map(|child| abstract_value(rng, child, subst, next_var))
                .collect::<Vec<_>>(),
        ),
    }
}

/// One near-miss mutation of an equal (goal, subst, lit) triple, or none.
fn mutate(rng: &mut Rng, goal: &mut Goal, subst: &mut Subst, lit: &mut GroundLiteral) {
    match rng.below(8) {
        // Left equal.
        0 => {}
        // An unbound variable.
        1 => {
            if let Some(var) = subst.keys().next().cloned() {
                subst.remove(&var);
            }
        }
        // A bound variable whose image is not ground (the image is not substituted again).
        2 => {
            if let Some(var) = subst.keys().next().cloned() {
                subst.insert(var, Term::tuple([Term::var("Unbound")]));
            }
        }
        // A different predicate.
        3 => lit.pred = "other".into(),
        // A different arity.
        4 => lit.args.push(Value::atom(b"a".to_vec())),
        // One argument replaced, usually by a different value.
        5 => {
            if !lit.args.is_empty() {
                let i = rng.below(lit.args.len() as u64) as usize;
                lit.args[i] = value(rng, 2);
            }
        }
        // The same list spelled cons on one side and `list(…)` on the other: unequal on both
        // paths since #3022, where the reify-aware slow path once accepted it.
        6 => {
            let items: Vec<Value> = (0..rng.below(3) + 1).map(|_| value(rng, 1)).collect();
            let (term_side, value_side) = if rng.below(2) == 0 {
                (cons_list(&items), flat_list(&items))
            } else {
                (flat_list(&items), cons_list(&items))
            };
            goal.args.push(Term::from_value(&term_side));
            lit.args.push(value_side);
        }
        // A tuple one item longer on the goal side.
        _ => {
            goal.args
                .push(Term::tuple([Term::atom(*b"a"), Term::atom(*b"b")]));
            lit.args
                .push(Value::tuple(vec![Value::atom(b"a".to_vec())]));
        }
    }
}

struct Tally {
    cases: usize,
    fast_equal: usize,
    slow_only: usize,
}

fn differential(fast: FastFn, seed: u64, cases: usize) -> Result<Tally, String> {
    let mut rng = Rng(seed | 1);
    let mut tally = Tally {
        cases: 0,
        fast_equal: 0,
        slow_only: 0,
    };
    for case in 0..cases {
        let arity = rng.below(4) as usize;
        let mut lit = GroundLiteral::new(
            "p",
            (0..arity).map(|_| value(&mut rng, 3)).collect::<Vec<_>>(),
        );
        let mut subst = Subst::new();
        let mut next_var = 0;
        let args: Vec<Term> = lit
            .args
            .iter()
            .map(|v| abstract_value(&mut rng, v, &mut subst, &mut next_var))
            .collect();
        let mut goal = Goal::new("p", args);
        mutate(&mut rng, &mut goal, &mut subst, &mut lit);

        let fast_says = fast(&goal, &subst, &lit);
        let slow_says = slow_equal(&goal, &subst, &lit);
        if fast_says && !slow_says {
            return Err(format!(
                "case {case} (seed {seed:#x}): fast proved equal, slow did not\n  goal  {goal:?}\n  \
                 subst {subst:?}\n  lit   {lit:?}"
            ));
        }
        tally.cases += 1;
        tally.fast_equal += usize::from(fast_says);
        tally.slow_only += usize::from(slow_says && !fast_says);
    }
    Ok(tally)
}

#[test]
fn the_fast_path_never_proves_equal_where_the_allocating_path_does_not() {
    for seed in [1, 0x2177, 0xC0_FFEE, 0xDEAD_BEEF] {
        let tally =
            differential(goal_eq_under_subst, seed, 20_000).unwrap_or_else(|why| panic!("{why}"));
        // Not vacuous: the fast path proves many equalities.
        assert!(
            tally.fast_equal > tally.cases / 10,
            "seed {seed:#x}: only {} of {} cases were fast-equal; the generator is not exercising \
             the fast path",
            tally.fast_equal,
            tally.cases
        );
        // #3022: both paths are structural, so the slow path proves no equality the fast one
        // misses, and the cons/`list` pairs (mutation 6) are unequal on both. Before #3022 those
        // pairs were the slow path's reify-aware branch.
        assert_eq!(
            tally.slow_only, 0,
            "seed {seed:#x}: the slow path proved equal where the structural fast path did not"
        );
    }
}

/// Broken on purpose: ignores the last argument.
fn skips_the_last_argument(goal: &Goal, subst: &Subst, lit: &GroundLiteral) -> bool {
    let checked = goal.args.len().saturating_sub(1);
    goal.pred == lit.pred
        && goal.args.len() == lit.args.len()
        && goal
            .args
            .iter()
            .zip(&lit.args)
            .take(checked)
            .all(|(term, value)| term_eq_under_subst(term, subst, value))
}

/// Broken on purpose: accepts any bound variable without comparing its image.
fn trusts_any_bound_variable(goal: &Goal, subst: &Subst, lit: &GroundLiteral) -> bool {
    fn walk(term: &Term, subst: &Subst, value: &Value) -> bool {
        match term {
            Term::Var(id) => subst.contains_key(id),
            Term::Atom(bytes) => {
                matches!(value, Value::Atom(atom) if atom.bytes() == bytes.as_slice())
            }
            Term::Tuple(children) => match value {
                Value::Tuple(tuple) => {
                    tuple.items().len() == children.len()
                        && children
                            .iter()
                            .zip(tuple.items())
                            .all(|(child, item)| walk(child, subst, item))
                }
                Value::Atom(_) => false,
            },
        }
    }
    goal.pred == lit.pred
        && goal.args.len() == lit.args.len()
        && goal
            .args
            .iter()
            .zip(&lit.args)
            .all(|(t, v)| walk(t, subst, v))
}

/// The harness must be able to go RED, or its passes prove nothing (`seat:caa`, A2).
#[test]
fn the_differential_goes_red_on_deliberately_broken_fast_paths() {
    let broken: [(&str, FastFn); 2] = [
        ("skips the last argument", skips_the_last_argument),
        ("trusts any bound variable", trusts_any_bound_variable),
    ];
    for (what, fast) in broken {
        assert!(
            differential(fast, 0x2177, 20_000).is_err(),
            "the harness passed a fast path that {what}; it cannot catch a wrong EQUAL"
        );
    }
}
