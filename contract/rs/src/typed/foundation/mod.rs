//! Low-level implementation of dependent-fragment-1, edition 1.
//!
//! These mathematical checking primitives support the production typed gate and
//! conformance experiments. They do not enforce receiver policy, preflight host
//! input, or mint the production accepted-statement token. Consumers seeking that
//! boundary use `typed::check`. The rulebook's metatheory remains explicitly
//! assumed; executable checking is not a proof of those metatheorems.

mod machine;
mod transform;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Sort(u32),
    Var(u32),
    Const(String),
    Pi {
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    Lam {
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    App {
        fun: Box<Expr>,
        arg: Box<Expr>,
    },
    Sigma {
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    Pair {
        sigma: Box<Expr>,
        first: Box<Expr>,
        second: Box<Expr>,
    },
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    Nat,
    Zero,
    Succ(Box<Expr>),
    NatElim {
        motive: Box<Expr>,
        zero: Box<Expr>,
        step: Box<Expr>,
        scrutinee: Box<Expr>,
    },
    Bool,
    False,
    True,
    BoolElim {
        motive: Box<Expr>,
        on_false: Box<Expr>,
        on_true: Box<Expr>,
        scrutinee: Box<Expr>,
    },
    Eq {
        ty: Box<Expr>,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Refl {
        ty: Box<Expr>,
        value: Box<Expr>,
    },
    Transport {
        ty: Box<Expr>,
        from: Box<Expr>,
        to: Box<Expr>,
        equality: Box<Expr>,
        motive: Box<Expr>,
        value: Box<Expr>,
    },
}

/// Constructors are merely syntax. Only `infer`/`check` establish typing.
pub fn b(expr: Expr) -> Box<Expr> {
    Box::new(expr)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Limit {
    Work,
    Depth,
    UniverseCapacity,
    IndexCapacity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    EscapedVariable,
    UnknownConstant(String),
    DuplicateConstant,
    MissingAssumptions,
    EmptyConstantName,
    ExpectedUniverse,
    ExpectedFunction,
    ExpectedSigma,
    TypeMismatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Accepted<T> {
    pub value: T,
    /// Syntactically reachable declaration/type/definition closure, not a
    /// purported minimum set of assumptions sufficient for the theorem.
    pub used_constants: BTreeSet<String>,
    pub dependencies: BTreeSet<String>,
    pub steps: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome<T> {
    Accepted(Accepted<T>),
    Invalid(Error),
    Incomplete(Limit),
}

#[derive(Debug)]
pub struct Budget {
    remaining: u64,
    max_depth: usize,
    spent: u64,
}

impl Budget {
    pub fn new(work: u64, depth: usize) -> Self {
        Self {
            remaining: work,
            max_depth: depth,
            spent: 0,
        }
    }

    pub fn spent(&self) -> u64 {
        self.spent
    }

    pub(crate) fn charge(&mut self) -> std::result::Result<(), Limit> {
        self.charge_many(1)
    }

    pub(crate) fn charge_many(&mut self, units: u64) -> std::result::Result<(), Limit> {
        if self.remaining < units {
            return Err(Limit::Work);
        }
        self.remaining -= units;
        self.spent += units;
        Ok(())
    }

    fn tick(&mut self, depth: usize) -> Result<()> {
        if depth > self.max_depth {
            return Err(Failure::Incomplete(Limit::Depth));
        }
        if self.remaining == 0 {
            return Err(Failure::Incomplete(Limit::Work));
        }
        self.remaining -= 1;
        self.spent += 1;
        Ok(())
    }
}

#[derive(Debug)]
enum Failure {
    Invalid(Error),
    Incomplete(Limit),
}

impl From<Error> for Failure {
    fn from(value: Error) -> Self {
        Self::Invalid(value)
    }
}

type Result<T> = std::result::Result<T, Failure>;

#[derive(Debug)]
struct Entry {
    ty: Expr,
    definition: Option<Expr>,
    used_constants: BTreeSet<String>,
    dependencies: BTreeSet<String>,
}

/// A closed signature built in dependency order. Private entries prevent
/// clients from inserting unchecked types, recursive definitions or cycles.
/// Names resolve these checked entries; names themselves establish no theorem.
#[derive(Debug, Default)]
pub struct Signature {
    entries: BTreeMap<String, Entry>,
}

impl Signature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn admit(
        &mut self,
        name: &str,
        ty: Expr,
        dependencies: BTreeSet<String>,
        budget: &mut Budget,
    ) -> Outcome<()> {
        if dependencies.is_empty() || dependencies.iter().any(String::is_empty) {
            return Outcome::Invalid(Error::MissingAssumptions);
        }
        self.declare(name, ty, None, dependencies, budget)
    }

    pub fn define(
        &mut self,
        name: &str,
        ty: Expr,
        value: Expr,
        budget: &mut Budget,
    ) -> Outcome<()> {
        self.declare(name, ty, Some(value), BTreeSet::new(), budget)
    }

    fn declare(
        &mut self,
        name: &str,
        ty: Expr,
        definition: Option<Expr>,
        dependencies: BTreeSet<String>,
        budget: &mut Budget,
    ) -> Outcome<()> {
        if name.is_empty() {
            return Outcome::Invalid(Error::EmptyConstantName);
        }
        if self.entries.contains_key(name) {
            return Outcome::Invalid(Error::DuplicateConstant);
        }
        let mut machine = Machine::new(self, budget);
        let mut ctx = Vec::new();
        let result = (|| {
            machine.universe(&ty, &mut ctx, 0)?;
            machine.collect(&ty, 0)?;
            if let Some(value) = &definition {
                machine.expect(value, &ty, &mut ctx, 0)?;
                machine.collect(value, 0)?;
            }
            Ok(())
        })();
        machine.dependencies.extend(dependencies);
        let result = result.and_then(|()| {
            machine
                .budget
                .charge_many(name.len() as u64)
                .map_err(Failure::Incomplete)?;
            for copied in machine.used_constants.iter().chain(&machine.dependencies) {
                machine
                    .budget
                    .charge_many(copied.len() as u64)
                    .map_err(Failure::Incomplete)?;
            }
            Ok(())
        });
        let outcome = machine.finish(result);
        if let Outcome::Accepted(accepted) = &outcome {
            self.entries.insert(
                name.to_owned(),
                Entry {
                    ty,
                    definition,
                    used_constants: accepted.used_constants.clone(),
                    dependencies: accepted.dependencies.clone(),
                },
            );
        }
        outcome
    }
}

/// Context types are ordered outermost first; each type is scoped *before* its
/// own binder. Every supplied context and expected type is independently checked.
/// Public inference also validates the synthesized type's formation before it
/// returns. The internal inference routine remains private. This establishes an
/// executable admission check, not repeated type-of-type closure or a metatheorem.
pub fn infer(
    signature: &Signature,
    context: &[Expr],
    term: &Expr,
    budget: &mut Budget,
) -> Outcome<Expr> {
    let mut machine = Machine::new(signature, budget);
    let result = machine.context(context).and_then(|mut ctx| {
        machine.collect(term, 0)?;
        let ty = machine.infer(term, &mut ctx, 0)?;
        machine.universe(&ty, &mut ctx, 0)?;
        Ok(ty)
    });
    machine.finish(result)
}

pub fn check(
    signature: &Signature,
    context: &[Expr],
    term: &Expr,
    expected: &Expr,
    budget: &mut Budget,
) -> Outcome<Expr> {
    check_located(signature, context, term, expected, budget).0
}

#[derive(Clone, Copy)]
pub(crate) enum CheckPhase {
    Context(usize),
    Expected,
    Candidate,
}

pub(crate) fn check_located(
    signature: &Signature,
    context: &[Expr],
    term: &Expr,
    expected: &Expr,
    budget: &mut Budget,
) -> (Outcome<Expr>, CheckPhase) {
    let mut machine = Machine::new(signature, budget);
    let mut phase = CheckPhase::Expected;
    let result = (|| {
        let mut ctx = Vec::new();
        for (index, ty) in context.iter().enumerate() {
            phase = CheckPhase::Context(index);
            machine.context_entry(ty, &mut ctx)?;
        }
        phase = CheckPhase::Expected;
        machine.universe(expected, &mut ctx, 0)?;
        machine.collect(expected, 0)?;
        phase = CheckPhase::Candidate;
        machine.collect(term, 0)?;
        let actual = machine.infer(term, &mut ctx, 0)?;
        machine.convert(&actual, expected, 0)?;
        Ok(actual)
    })();
    (machine.finish(result), phase)
}

pub(crate) fn copy(expression: &Expr, budget: &mut Budget) -> Outcome<Expr> {
    let signature = Signature::new();
    let mut machine = Machine::new(&signature, budget);
    let result = machine.copy(expression, 0);
    machine.finish(result)
}

struct Machine<'a> {
    signature: &'a Signature,
    budget: &'a mut Budget,
    started: u64,
    used_constants: BTreeSet<String>,
    dependencies: BTreeSet<String>,
}

pub(crate) fn children(expr: &Expr) -> Vec<&Expr> {
    use Expr::*;
    match expr {
        Sort(_) | Var(_) | Const(_) | Nat | Zero | Bool | False | True => vec![],
        Pi { domain, body } | Lam { domain, body } | Sigma { domain, body } => vec![domain, body],
        App { fun, arg } => vec![fun, arg],
        Pair {
            sigma,
            first,
            second,
        } => vec![sigma, first, second],
        Fst(p) | Snd(p) | Succ(p) => vec![p],
        NatElim {
            motive,
            zero,
            step,
            scrutinee,
        } => vec![motive, zero, step, scrutinee],
        BoolElim {
            motive,
            on_false,
            on_true,
            scrutinee,
        } => vec![motive, on_false, on_true, scrutinee],
        Eq { ty, lhs, rhs } => vec![ty, lhs, rhs],
        Refl { ty, value } => vec![ty, value],
        Transport {
            ty,
            from,
            to,
            equality,
            motive,
            value,
        } => vec![ty, from, to, equality, motive, value],
    }
}
