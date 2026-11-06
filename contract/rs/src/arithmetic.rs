//! `contract::arithmetic` — the standard checkable exact-integer arithmetic [`Theory`]
//! (ADR 0014). **[STABLE-v1 Theory impl.]**
//!
//! This is the Rust home of the arithmetic [`Theory`], moved here from `logos-core` so
//! the checkable theory lives in the contract tier beside the checker SPI — tri-core
//! symmetric with `contract/go/arithmetic.go` and `contract/ts/src/arithmetic.ts`,
//! which already place it here. The search-side builtin SOLVER stays in
//! `logos_core::builtins` (it needs core's unify/`Subst` machinery); it shares THIS
//! module's walk ([`eval_resolving`]), operator semantics ([`apply_operator`]) and the
//! [`BigInt`] int embedding, so `decide` (check) and `solve` (search) agree on every
//! ground atom — the §7 dual-conformance law, byte-frozen in `vectors/arithmetic.json`.
//!
//! # No depth capacity (#3123)
//!
//! The walk is iterative, so an expression's nesting is not a property of the native stack
//! and there is no depth at which evaluation stops. An expression 300 or 100,000 levels deep
//! is a valid expression and evaluates. Until #3123 a recursive evaluator stopped at 256
//! levels and the stop was read as `Fails`, so a capacity became a decided false that a
//! negation or a closure read as knowledge. The only depth limit left is the caller's
//! `CheckLimits::max_term_depth` (`term_too_deep`, a completed policy decision); an expression
//! that reaches this theory is decided by its value.
//!
//! # The numeric domain
//!
//! Two **distinct exact sorts** (#331), each a frozen `ontos-data` embedding:
//!   - **integer** — `int(Atom(sign‖magnitude))`, read/built through [`BigInt`]
//!     (unbounded);
//!   - **decimal** — `decimal(int(mantissa), int(exponent))` = `mantissa × 10^exponent`,
//!     read/built through [`BigDecimal`] (unbounded mantissa, `i128`-bounded scale).
//!
//! There is **no float** — both sorts are exact, preserving structural value equality.
//! `int(5)` and `decimal(5,0)` are different terms, so `is/2` keeps the result's sort
//! (`5 is 2+3.0` fails, `5.0 is 2+3.0` holds), but the comparisons order by **value**
//! across sorts (`2 =:= 2.0` holds). An all-integer expression stays integer; an operand
//! that is a decimal promotes the expression to decimal. `/` is EXACT in both domains
//! (integer: even quotient only; decimal: terminating-in-base-10 only — `1.0/3` fails),
//! and `//` (truncating, toward zero, result `int`) / `mod` (ISO floored, sign of the
//! divisor, result `decimal` when an operand is decimal) are defined over decimals too
//! (ADR 0022 Amendment) — the SAME convention as the integer domain, computed exactly via
//! integer division on scaled mantissas (no decimal `/`, so always terminating).
//!
//! # Two ways an expression has no value to compare (#3161, #3126)
//!
//! - **A [`DomainError`]: the LANGUAGE's answer.** A zero divisor, a non-terminating decimal
//!   `/`, an inexact integer `/`, a leaf that is not a number, an unknown operator, a result
//!   outside ADR 0022's value domain. The expression has no value, so the goal is **false**.
//! - **Not completed: the IMPLEMENTATION stopping.** The exact alignment of two in-domain
//!   decimals past [`MAX_DECIMAL_SCALE_SHIFT`](crate::decval::MAX_DECIMAL_SCALE_SHIFT) is a work
//!   cap: the value exists and was not computed, so the goal is **not decided**, never false.
//!
//! [`eval`] returns an [`Evaluation`], which keeps the two apart. No path converts the second
//! into the first (research 0031 row 3). Byte-identical to the Go/TS mirrors.
//!
//! # Judgments (mirroring the cross-core vectors)
//!
//! `owns(pred)`: by NAME only (any arity) for the seven arithmetic relations. The
//! expression operators (`+ - * / // mod abs min max`) are never goals, so they are
//! NOT owned. `decide_ground(atom)` on a ground atom:
//!   - non-UTF-8 predicate              → `Completed(Fails{arith_unknown_predicate})`
//!   - owned name, arity ≠ 2            → `Completed(Fails{arith_bad_arity})` (e.g. `is/3`)
//!   - registered, evaluates to true    → `Completed(Holds)`
//!   - registered, evaluates to false,
//!     or a [`DomainError`]              → `Completed(Fails{arith_does_not_hold})`
//!   - an evaluation past a work cap    → `NotCompleted(work_cap)` (#3126)
//!
//! The v1 `decide` is derived from it by [`legacy_outcome`](crate::spi::legacy_outcome): the
//! not-completed case is `NotMine`, which every reader refuses by name, never `Fails`.

use std::cmp::Ordering;

use crate::completion::{CauseScope, Completion, NonCompletion, TheoryDecision};
use crate::decval::{BigDecimal, DecimalError};
use crate::engine::NoCallerLimit;
use crate::intval::BigInt;
use crate::spi::legacy_outcome;
use crate::{ComponentIdentity, GroundLiteral, Symbol, Term, Theory, TheoryOutcome};

/// The arithmetic-relation predicate names this theory owns: `is/2` and the six
/// arithmetic comparisons. Owned by NAME only — the expression operators
/// (`+ - * / // mod abs min max`) are never goals, so they are not owned.
const ARITHMETIC_PREDICATES: &[&[u8]] = &[b"is", b"=:=", b"=\\=", b"<", b">", b">=", b"=<"];

/// Whether `pred` names an owned arithmetic relation.
fn owns_name(pred: &Symbol) -> bool {
    ARITHMETIC_PREDICATES.contains(&pred.bytes())
}

/// The [`PredicateSet`](crate::PredicateSet) of the seven arithmetic-relation predicates
/// this theory owns (`is/2` and the six comparisons `=:= =\= < > >= =<`) — the SAME set
/// [`ArithmeticTheory::owns`](ArithmeticTheory) recognizes by name. Exposed as the single
/// source of truth for the producer-side "which builtins to evaluate in a query clause"
/// set (ADR 0023 / #663): the certifiable-aggregation producer binds THIS set so an `is/2`
/// composed after a `count`/`max` (e.g. `N is M + 1`) is evaluated + bound rather than
/// declined, while the gate re-decides each emitted `Builtin` node via the same theory.
pub fn arithmetic_predicate_set() -> crate::PredicateSet {
    ARITHMETIC_PREDICATES
        .iter()
        .map(|bytes| Symbol::new(bytes.to_vec()))
        .collect()
}

/// A numeric value the arithmetic evaluator ([`eval`]) produces and [`apply_operator`]
/// combines: an exact integer ([`BigInt`]) or an exact decimal ([`BigDecimal`]) (#331).
///
/// The two are **distinct sorts** — `int(5)` and `decimal(5,0)` are different canonical
/// terms, so `5 is 2 + 3.0` FAILS while `5.0 is 2 + 3.0` HOLDS (the lowered result keeps
/// its sort, [`to_term`](Num::to_term)). But the comparisons (`=:=`, `<`, …) order by
/// **value** across sorts ([`cmp_value`](Num::cmp_value)), so `2 =:= 2.0` HOLDS.
/// Operators promote int → decimal only when an operand is already a decimal, so an
/// all-integer expression stays integer and is byte-identical to the pre-decimal path.
#[derive(Clone, Debug)]
pub enum Num {
    /// An exact integer.
    Int(BigInt),
    /// An exact decimal `mantissa × 10^exponent`.
    Dec(BigDecimal),
}

impl Num {
    /// Lower to the canonical embedding of the value's sort — `int(…)` for [`Num::Int`],
    /// `decimal(…)` for [`Num::Dec`]. `is/2` binds/compares against this, so the result
    /// sort is preserved (an integral decimal stays `decimal(n,0)`, never collapses to
    /// `int(n)`).
    pub fn to_term(&self) -> Term {
        match self {
            Num::Int(n) => n.to_int_term(),
            Num::Dec(d) => d.to_decimal_term(),
        }
    }

    /// Total **value** order across sorts: integers as integers, decimals as decimals, a
    /// mixed pair by promoting the integer to a decimal — so `2 =:= 2.0` and `2 < 2.5`.
    pub fn cmp_value(&self, other: &Num) -> Ordering {
        match (self, other) {
            (Num::Int(a), Num::Int(b)) => a.cmp(b),
            (Num::Dec(a), Num::Dec(b)) => a.cmp(b),
            (Num::Int(a), Num::Dec(b)) => BigDecimal::from_bigint(a.clone()).cmp(b),
            (Num::Dec(a), Num::Int(b)) => a.cmp(&BigDecimal::from_bigint(b.clone())),
        }
    }

    /// Promote to the decimal domain (for a mixed-sort binary operator).
    fn to_decimal(&self) -> BigDecimal {
        match self {
            Num::Int(n) => BigDecimal::from_bigint(n.clone()),
            Num::Dec(d) => d.clone(),
        }
    }

    /// `-self`, preserving the sort.
    fn negate(&self) -> Num {
        match self {
            Num::Int(n) => Num::Int(n.negate()),
            Num::Dec(d) => Num::Dec(d.negate()),
        }
    }

    /// `|self|`, preserving the sort.
    fn abs(&self) -> Num {
        match self {
            Num::Int(n) => Num::Int(n.abs()),
            Num::Dec(d) => Num::Dec(d.abs()),
        }
    }
}

/// The code a false arithmetic relation names: a relation over values that does not hold, or an
/// expression with no value ([`DomainError::code`]).
const ARITH_DOES_NOT_HOLD: &str = "arith_does_not_hold";

/// Why an arithmetic expression has no value in the language (#3161): every failure ADR 0022
/// defines. The goal over it is **false**, a decided answer. A work cap is not here: it is
/// [`Evaluation`]'s `NotCompleted` arm, because the value exists and was not computed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DomainError {
    /// A leaf that is not a number: a bare atom, a text or other non-number embedding, a
    /// compound whose head is not an operator atom.
    NotANumber,
    /// An operator compound whose `op/arity` is not one of the operators (`2 ^ 3`, `+(1)`).
    UnknownOperator,
    /// A zero divisor for `/`, `//` or `mod`.
    DivisionByZero,
    /// An integer `/` whose operands do not divide evenly (`7 / 2`): no fractional integer.
    InexactDivision,
    /// A decimal `/` whose exact quotient does not terminate in base 10 (`1.0 / 3`).
    NonTerminating,
    /// A decimal result outside the value domain `|exponent| <= MAX_DECIMAL_EXPONENT`.
    OutsideDomain,
}

impl DomainError {
    /// The false code this failure names in `decide_ground` (seat:caa's condition on #3126): the
    /// ONE function a domain failure's code comes from, so search and check name the same failure.
    ///
    /// Every domain failure names `arith_does_not_hold`, the code a false arithmetic relation has
    /// always named in `vectors/arithmetic.json`. The variants are the language's reasons; giving
    /// each its own code is a vocabulary change the shared vectors would pin, and is not made here.
    pub fn code(self) -> &'static str {
        match self {
            DomainError::NotANumber
            | DomainError::UnknownOperator
            | DomainError::DivisionByZero
            | DomainError::InexactDivision
            | DomainError::NonTerminating
            | DomainError::OutsideDomain => ARITH_DOES_NOT_HOLD,
        }
    }
}

impl std::fmt::Display for DomainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            DomainError::NotANumber => "arithmetic operand is not a number",
            DomainError::UnknownOperator => "unknown arithmetic operator",
            DomainError::DivisionByZero => "arithmetic division by zero",
            DomainError::InexactDivision => {
                "inexact integer division (/): operands do not divide evenly"
            }
            DomainError::NonTerminating => "non-terminating decimal division (/)",
            DomainError::OutsideDomain => "decimal result outside the value domain",
        })
    }
}

/// What evaluating an arithmetic expression establishes (#3161, research 0031 row 3):
/// - `Completed(Ok(value))`: the expression's value;
/// - `Completed(Err(domain))`: the language's answer that it has none, so a goal over it is false;
/// - `NotCompleted(cause)`: the evaluator stopped before it knew (a work cap, #3126; an unbound
///   variable in search), so a goal over it is not decided.
///
/// `LimitExceeded` is uninhabited: no caller's limit reaches the evaluator.
pub type Evaluation = Completion<Result<Num, DomainError>, NoCallerLimit>;

/// A value.
fn value(num: Num) -> Evaluation {
    Completion::Completed(Ok(num))
}

/// The language's answer that the expression has no value.
fn no_value(error: DomainError) -> Evaluation {
    Completion::Completed(Err(error))
}

/// A decimal operation's result as an [`Evaluation`]: the ONE place a [`DecimalError`] is sorted
/// into the language's failure or the implementation's stop. The alignment cap is the only stop.
fn decimal_step<T>(result: Result<T, DecimalError>, wrap: fn(T) -> Num) -> Evaluation {
    match result {
        Ok(v) => value(wrap(v)),
        Err(DecimalError::DivisionByZero) => no_value(DomainError::DivisionByZero),
        Err(DecimalError::NonTerminating) => no_value(DomainError::NonTerminating),
        Err(DecimalError::OutsideDomain) => no_value(DomainError::OutsideDomain),
        Err(DecimalError::AlignmentCap) => {
            Completion::NotCompleted(NonCompletion::work_cap(CauseScope::Literal))
        }
    }
}

/// The config-pinned §5 [`Theory`] that owns the arithmetic relations (`is/2`,
/// `=:= =\\= < > >= =<`) and decides a GROUND arithmetic atom by exact-integer
/// evaluation over the frozen `int` embedding. Pure / total / deterministic /
/// config-free — a faithful mirror of the Go/TS bindings.
#[derive(Clone, Copy, Debug, Default)]
pub struct ArithmeticTheory;

impl ArithmeticTheory {
    /// The standard arithmetic theory (no configuration).
    pub fn new() -> Self {
        ArithmeticTheory
    }
}

impl Theory for ArithmeticTheory {
    /// Opt in to the #1023 probe clone. `ArithmeticTheory` is a stateless `Copy` unit, so an
    /// independent copy is the value itself — the probe runs under a theory byte-identical to
    /// the one the provider advertises, which is what keeps the check-profile digest equal.
    fn boxed_clone(&self) -> Result<Box<dyn Theory + Send + Sync>, crate::spi::CopyIncapacity> {
        Ok(Box::new(*self))
    }

    fn owns(&self, pred: &Symbol) -> bool {
        owns_name(pred)
    }

    /// `logos-core/arithmetic-theory@1.0.0`, no config. **The `logos-core/` namespace
    /// is a STABLE IDENTITY, not a path** (ADR 0014): it is byte-frozen in
    /// `vectors/arithmetic.json` and stays exactly this string regardless of the
    /// theory's physical home, so a check profile binding it derives the same digest
    /// tri-core.
    fn identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"logos-core/arithmetic-theory".to_vec(),
            b"1.0.0".to_vec(),
            [0u8; 32],
        )
    }

    /// #3142, PER THEORY (`seat:caa`'s rulings on #3142 and on #3189, Q3): every arithmetic stop
    /// is typed. Its one stop is decimal alignment past
    /// [`MAX_DECIMAL_SCALE_SHIFT`](crate::decval::MAX_DECIMAL_SCALE_SHIFT) (#3126; #3123 removed
    /// the depth capacity), and [`decide_ground`](Theory::decide_ground) answers it
    /// `NotCompleted(work_cap)`, never `Fails` (#3313); `check` refuses that stop by name. So a
    /// `Fails` is always a decided false, and a certified closure may rest on arithmetic. It still
    /// stops, so it is not "complete": the value names the one claim the guard needs.
    fn completion(&self, _pred: &Symbol) -> crate::spi::DecisionCompletion {
        crate::spi::DecisionCompletion::StopsAreTyped
    }

    /// Decide a ground arithmetic atom (#3126). A [`DomainError`] is the language's false; an
    /// evaluation past a work cap is `NotCompleted(work_cap)`, never a false (research 0031).
    fn decide_ground(&self, atom: &GroundLiteral) -> Completion<TheoryDecision, NoCallerLimit> {
        // Not one of ours: `check` routes by `owns`, so this is the theory contradicting its own
        // routing, the fault the default reports for `NotMine`. Stay total.
        if !owns_name(&atom.pred) {
            return Completion::NotCompleted(NonCompletion::inconsistent_theory());
        }
        let name = match std::str::from_utf8(atom.pred.bytes()) {
            Ok(name) => name,
            // A non-UTF-8 predicate cannot be a registered arithmetic relation.
            Err(_) => return fails("arith_unknown_predicate"),
        };
        // The atom is GROUND: lift its Value args to Terms (no Vars appear).
        let args: Vec<Term> = atom.args.iter().map(Term::from_value).collect();
        match name {
            "is" => decide_is(&args),
            "=:=" => decide_compare(&args, |o| o == Ordering::Equal),
            "=\\=" => decide_compare(&args, |o| o != Ordering::Equal),
            "<" => decide_compare(&args, |o| o == Ordering::Less),
            ">" => decide_compare(&args, |o| o == Ordering::Greater),
            ">=" => decide_compare(&args, |o| o != Ordering::Less),
            "=<" => decide_compare(&args, |o| o != Ordering::Greater),
            // Owned name routed here but not handled above — unreachable (the name set
            // is exactly the match arms above), but stay total.
            _ => fails(ARITH_DOES_NOT_HOLD),
        }
    }

    /// The v1 answer, DERIVED from [`decide_ground`](Theory::decide_ground) by the one legacy
    /// adapter. An evaluation past a work cap is `NotMine` there, never `Fails`: every legacy
    /// reader refuses an owned atom's `NotMine` by name, so it fails closed (seat:caa on #3126).
    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome {
        legacy_outcome(self.decide_ground(atom))
    }
}

/// The false arm with `code`.
fn fails(code: &str) -> Completion<TheoryDecision, NoCallerLimit> {
    Completion::Completed(TheoryDecision::Fails { code: code.into() })
}

/// `Holds` when `holds`, else the relation's false.
fn holds_if(holds: bool) -> Completion<TheoryDecision, NoCallerLimit> {
    if holds {
        Completion::Completed(TheoryDecision::Holds)
    } else {
        fails(ARITH_DOES_NOT_HOLD)
    }
}

/// An operand's value, or the decision its evaluation already settles: a [`DomainError`] is the
/// relation's false, named by [`DomainError::code`]; a stop is not decided.
fn operand(evaluation: Evaluation) -> Result<Num, Completion<TheoryDecision, NoCallerLimit>> {
    match evaluation {
        Completion::Completed(Ok(num)) => Ok(num),
        Completion::Completed(Err(error)) => Err(fails(error.code())),
        Completion::LimitExceeded(never) => match never {},
        Completion::NotCompleted(cause) => Err(Completion::NotCompleted(cause)),
    }
}

/// Decide `is/2`: evaluate the RHS and compare the (ground) LHS to the canonical embedding of
/// its value. Mirrors the search-side `builtin_is`:
///   - arity ≠ 2          → `arith_bad_arity` (no `is/N` relation)
///   - RHS has no value   → the [`DomainError`]'s code, `arith_does_not_hold` (the goal fails)
///   - RHS past a work cap → not decided (#3126)
///   - LHS ≠ its value    → `arith_does_not_hold`
///   - LHS == its value   → `Holds`
fn decide_is(args: &[Term]) -> Completion<TheoryDecision, NoCallerLimit> {
    if args.len() != 2 {
        return fails("arith_bad_arity");
    }
    match operand(eval(&args[1])) {
        // `is` unifies arg0 with the embedding of the result; the atom is ground, so
        // unification is structural equality against the canonical embedding OF THE
        // RESULT'S SORT ([`Num::to_term`]). A decimal result lowers to `decimal(…)`, so
        // `5 is 2 + 3.0` fails (decimal(5,0) ≠ int(5)) and `5.0 is 2 + 3.0` holds.
        Ok(value) => holds_if(args[0] == value.to_term()),
        Err(settled) => settled,
    }
}

/// Decide one of the six comparisons: evaluate both operands and accept iff
/// `accept(cmp(a, b))`. A non-2 arity has no relation (`arith_bad_arity`).
///
/// The operands are evaluated left to right and the first that does not give a value settles the
/// comparison, as a stop inside one expression does: a [`DomainError`] makes it false (its code),
/// a work cap leaves it not decided (#3126). Mirrors the search-side `arith_compare`.
fn decide_compare(
    args: &[Term],
    accept: impl Fn(Ordering) -> bool,
) -> Completion<TheoryDecision, NoCallerLimit> {
    if args.len() != 2 {
        return fails("arith_bad_arity");
    }
    let left = match operand(eval(&args[0])) {
        Ok(num) => num,
        Err(settled) => return settled,
    };
    let right = match operand(eval(&args[1])) {
        Ok(num) => num,
        Err(settled) => return settled,
    };
    // Compare by VALUE across sorts ([`Num::cmp_value`]), so `2 =:= 2.0` holds.
    holds_if(accept(left.cmp_value(&right)))
}

/// Evaluate a GROUND arithmetic-expression term to an exact [`Num`] (integer or decimal,
/// #331). The grammar:
/// * an `int` embedding `int(Atom(payload))` → [`Num::Int`];
/// * a `decimal` embedding `decimal(int(m), int(e))` → [`Num::Dec`];
/// * an operator compound `Tuple([Atom(op), arg…])` for a known `op/arity` → combine;
/// * anything else (a bare/number-shaped atom, an unknown operator, the wrong arity for
///   an operator) → a [`DomainError`];
/// * a variable (which a ground atom never carries) → not completed, an instantiation stop.
///
/// A [`DomainError`] (division/mod by zero, a non-terminating decimal `/`, …) is the language's
/// answer, and the caller's goal over it is false. An exceeded decimal scale alignment is
/// `NotCompleted(work_cap)` (#3126), and the caller's goal is not decided. Never a panic. There
/// is no depth at which it stops (#3123): the walk is [`eval_resolving`]'s, which keeps its
/// place on the heap. This is the ground specialization of `logos_core::builtins`'
/// variable-resolving evaluator, which runs the SAME walk, so check and search cannot drift.
pub fn eval(term: &Term) -> Evaluation {
    eval_resolving(term, |node| node)
}

/// One step of [`eval_resolving`]'s walk. The walk's control lives HERE, in the variant, and
/// never in the value stack (research 0030: no input value can be read as a control marker).
enum Step<'t> {
    /// Evaluate this operand and push its value onto the value stack.
    Eval(&'t Term),
    /// Every operand of one operator compound is evaluated: the `arity` values from `base` up
    /// are its operands, in order. Pop them and push `op` applied to them.
    Apply {
        op: &'t [u8],
        base: usize,
        arity: usize,
    },
}

/// **The arithmetic walk**, shared by check ([`eval`], over a ground term) and search
/// (`logos_core::builtins`, which passes its substitution's walk as `resolve`, so a bound
/// variable is read through its binding). `resolve` is applied to every node before it is
/// read. The grammar and the outcomes are [`eval`]'s.
///
/// **Iterative (#3123).** A recursive evaluator needs one native frame per level, so it had a
/// depth cap, and the cap's stop was read as `Fails`: a capacity turned into a decided false
/// that a negation or a closure read as knowledge. This walk keeps its place on an explicit
/// heap stack of [`Step`]s, so an expression of any depth evaluates, and the only depth limit
/// is the caller's `max_term_depth`. Operands are evaluated left to right and each compound is
/// applied after its operands, the order the recursion used, so the first error met is the
/// recursion's. The first operand that gives no value ends the walk, whether it is a
/// [`DomainError`] or a stop: every core walks in this order, so they report the same one.
pub fn eval_resolving<'t>(
    root: &'t Term,
    mut resolve: impl FnMut(&'t Term) -> &'t Term,
) -> Evaluation {
    let mut work: Vec<Step<'t>> = vec![Step::Eval(root)];
    let mut vals: Vec<Num> = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            Step::Eval(node) => {
                let term = resolve(node);
                // A number leaf: the exact `int` embedding, then the exact `decimal` embedding.
                if let Some(value) = BigInt::from_int_term(term) {
                    vals.push(Num::Int(value));
                    continue;
                }
                if let Some(value) = BigDecimal::from_decimal_term(term) {
                    vals.push(Num::Dec(value));
                    continue;
                }
                match term {
                    // Not decided: the value is not known yet. `logos_core::builtins` refuses an
                    // unbound operand before it evaluates (#3131), so this is defensive.
                    Term::Var(_) => {
                        return Completion::NotCompleted(NonCompletion::instantiation(
                            CauseScope::Literal,
                        ))
                    }
                    Term::Atom(_) => return no_value(DomainError::NotANumber),
                    Term::Tuple(children) => {
                        // Operator compound: head atom is the operator, the rest are operands.
                        let Some((Term::Atom(op), operands)) = children.split_first() else {
                            return no_value(DomainError::NotANumber);
                        };
                        // The apply runs after every operand: it is pushed first (LIFO), and
                        // the operands in reverse, so the leftmost is evaluated first.
                        work.push(Step::Apply {
                            op,
                            base: vals.len(),
                            arity: operands.len(),
                        });
                        work.extend(operands.iter().rev().map(Step::Eval));
                    }
                }
            }
            Step::Apply { op, base, arity } => {
                let operands = vals.split_off(base);
                assert_eq!(
                    operands.len(),
                    arity,
                    "arithmetic walk: an apply step found {} values above its base, want its arity",
                    operands.len()
                );
                match apply_operator(op, &operands) {
                    Completion::Completed(Ok(num)) => vals.push(num),
                    // No value (the language's answer) or a stop: it settles the whole expression.
                    settled @ (Completion::Completed(Err(_))
                    | Completion::LimitExceeded(_)
                    | Completion::NotCompleted(_)) => return settled,
                }
            }
        }
    }
    // Every compound consumed its operands and pushed one value, so the root's is the only one.
    assert_eq!(
        vals.len(),
        1,
        "arithmetic walk: the root left {} values",
        vals.len()
    );
    value(vals.pop().expect("one value, asserted above"))
}

/// Apply an arithmetic operator named `op` to its already-evaluated operands. The
/// single source of operator semantics, shared by `decide` (check) and
/// `logos_core::builtins` (search), so the two cannot drift. An unknown `op/arity` is
/// [`DomainError::UnknownOperator`]; an operator's own failures are its [`DomainError`]s, and
/// a decimal alignment past the cap is not completed (#3126).
///
/// **Sort discipline (#331).** An all-integer operand list stays in the integer domain
/// (byte-identical to the pre-decimal path); if ANY operand is a decimal, the integer
/// operands are promoted to decimals and the operator runs in the decimal domain, so the
/// result is a decimal. `/` is EXACT in both domains (integer: even quotient only;
/// decimal: terminating-in-base-10 only — never a float; `1.0/3` fails). `//` (truncating
/// division, toward zero, always result `int`) and `mod` (ISO floored, sign of the
/// divisor; result `int` for two integers, `decimal` when an operand is decimal) follow
/// the SAME convention in both domains, computed exactly via integer division on scaled
/// mantissas — no decimal `/`, so no termination concern (ADR 0022 Amendment). `min`/`max`
/// order by value across sorts and return the chosen operand in its own sort.
pub fn apply_operator(op: &[u8], vals: &[Num]) -> Evaluation {
    match (op, vals) {
        (b"+", [a, b]) => num_add(a, b),
        (b"-", [a, b]) => num_sub(a, b),
        (b"-", [a]) => value(a.negate()), // unary minus
        (b"*", [a, b]) => num_mul(a, b),
        (b"abs", [a]) => value(a.abs()),
        // `min`/`max` keep the chosen operand's own sort; ties keep the left operand.
        (b"min", [a, b]) => value(if a.cmp_value(b) == Ordering::Greater {
            b.clone()
        } else {
            a.clone()
        }),
        (b"max", [a, b]) => value(if a.cmp_value(b) == Ordering::Less {
            b.clone()
        } else {
            a.clone()
        }),
        (b"/", [a, b]) => num_div(a, b),
        (b"//", [a, b]) => num_floor_div(a, b),
        (b"mod", [a, b]) => num_mod(a, b),
        _ => no_value(DomainError::UnknownOperator),
    }
}

/// `a + b`: integer-closed when both are integers (byte-identical to the pre-#331 path),
/// else promoted to the decimal domain.
fn num_add(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => value(Num::Int(x.add(y))),
        _ => decimal_step(a.to_decimal().add(&b.to_decimal()), Num::Dec),
    }
}

/// `a - b` (see [`num_add`]).
fn num_sub(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => value(Num::Int(x.sub(y))),
        _ => decimal_step(a.to_decimal().sub(&b.to_decimal()), Num::Dec),
    }
}

/// `a * b` (see [`num_add`]).
fn num_mul(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => value(Num::Int(x.mul(y))),
        _ => decimal_step(a.to_decimal().mul(&b.to_decimal()), Num::Dec),
    }
}

/// `a / b` — EXACT in both domains. Integer: the even quotient, else
/// [`DomainError::InexactDivision`] (no fractional integer; `7/2` has no value). Decimal: the
/// terminating-in-base-10 quotient, else [`DomainError::NonTerminating`] (`1.0/3`). Never a
/// float, never a silent truncation.
fn num_div(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => match x.div_exact(y) {
            Some(q) => value(Num::Int(q)),
            None if y.is_zero() => no_value(DomainError::DivisionByZero),
            None => no_value(DomainError::InexactDivision),
        },
        _ => decimal_step(a.to_decimal().div_terminating(&b.to_decimal()), Num::Dec),
    }
}

/// `a // b` — **truncating** integer division (toward zero), the single rounding
/// convention shared by the integer and decimal domains (ADR 0022 Amendment). Integer:
/// the truncated quotient ([`BigInt::div_rem_trunc`], byte-identical to the pre-decimal
/// path). Decimal (any operand a decimal, the integers promoted): the exact quotient of
/// the scaled mantissas truncated toward zero ([`BigDecimal::div_trunc_int`]) — e.g.
/// `-7.5 // 2 = -3` (toward zero, NOT floor −4). The result is always an **integer** in
/// BOTH domains (`//` answers a whole-multiple count). [`DomainError::DivisionByZero`] on a
/// zero divisor.
fn num_floor_div(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => match x.div_rem_trunc(y) {
            Some((q, _r)) => value(Num::Int(q)),
            None => no_value(DomainError::DivisionByZero),
        },
        _ => decimal_step(a.to_decimal().div_trunc_int(&b.to_decimal()), Num::Int),
    }
}

/// `a mod b` — ISO **floored** modulo (the result takes the sign of the divisor), the
/// single sign convention shared by the integer and decimal domains (ADR 0022
/// Amendment). Integer: the floored remainder ([`BigInt::modulo_floored`], byte-identical
/// to the pre-decimal path), result **integer**. Decimal (any operand a decimal, the
/// integers promoted): `a − floor(a/b)·b` ([`BigDecimal::modulo_floored`]) — always exact
/// (no division, pure mantissa arithmetic), result **decimal** — e.g. `7.5 mod 0.25 = 0.0`,
/// `-7.5 mod 2 = 0.5` (sign follows the divisor). [`DomainError::DivisionByZero`] on a zero
/// divisor.
fn num_mod(a: &Num, b: &Num) -> Evaluation {
    match (a, b) {
        (Num::Int(x), Num::Int(y)) => match x.modulo_floored(y) {
            Some(r) => value(Num::Int(r)),
            None => no_value(DomainError::DivisionByZero),
        },
        _ => decimal_step(a.to_decimal().modulo_floored(&b.to_decimal()), Num::Dec),
    }
}
