use super::*;

impl<'a> Machine<'a> {
    pub(super) fn copy(&mut self, expr: &Expr, depth: usize) -> Result<Expr> {
        self.shift(expr, 0, depth)
    }

    pub(super) fn shift(&mut self, expr: &Expr, amount: u32, depth: usize) -> Result<Expr> {
        self.walk(expr, 0, depth, &mut |machine, index, bound, d| {
            machine.budget.tick(d)?;
            Ok(Expr::Var(if index < bound {
                index
            } else {
                index
                    .checked_add(amount)
                    .ok_or(Failure::Incomplete(Limit::IndexCapacity))?
            }))
        })
    }

    /// Substitute the outermost free slot with `argument` and remove that slot.
    /// At a nested binder, lift the inserted argument so its free variables
    /// cannot be captured. Higher free slots decrease because one binder leaves.
    pub(super) fn instantiate(
        &mut self,
        body: &Expr,
        argument: &Expr,
        depth: usize,
    ) -> Result<Expr> {
        self.walk(body, 0, depth, &mut |machine, index, bound, d| {
            machine.budget.tick(d)?;
            if index == bound {
                machine.shift(argument, bound, d + 1)
            } else {
                Ok(Expr::Var(if index > bound { index - 1 } else { index }))
            }
        })
    }

    pub(super) fn walk<F>(
        &mut self,
        expr: &Expr,
        bound: u32,
        depth: usize,
        variable: &mut F,
    ) -> Result<Expr>
    where
        F: FnMut(&mut Self, u32, u32, usize) -> Result<Expr>,
    {
        self.budget.tick(depth)?;
        use Expr::*;
        let d = depth + 1;
        let next = || {
            bound
                .checked_add(1)
                .ok_or(Failure::Incomplete(Limit::IndexCapacity))
        };
        Ok(match expr {
            Sort(u) => Sort(*u),
            Var(i) => return variable(self, *i, bound, d),
            Const(n) => {
                self.budget
                    .charge_many(n.len() as u64)
                    .map_err(Failure::Incomplete)?;
                Const(n.clone())
            }
            Pi { domain, body } => Pi {
                domain: b(self.walk(domain, bound, d, variable)?),
                body: b(self.walk(body, next()?, d, variable)?),
            },
            Lam { domain, body } => Lam {
                domain: b(self.walk(domain, bound, d, variable)?),
                body: b(self.walk(body, next()?, d, variable)?),
            },
            Sigma { domain, body } => Sigma {
                domain: b(self.walk(domain, bound, d, variable)?),
                body: b(self.walk(body, next()?, d, variable)?),
            },
            App { fun, arg } => App {
                fun: b(self.walk(fun, bound, d, variable)?),
                arg: b(self.walk(arg, bound, d, variable)?),
            },
            Pair {
                sigma,
                first,
                second,
            } => Pair {
                sigma: b(self.walk(sigma, bound, d, variable)?),
                first: b(self.walk(first, bound, d, variable)?),
                second: b(self.walk(second, bound, d, variable)?),
            },
            Fst(p) => Fst(b(self.walk(p, bound, d, variable)?)),
            Snd(p) => Snd(b(self.walk(p, bound, d, variable)?)),
            Nat => Nat,
            Zero => Zero,
            Succ(n) => Succ(b(self.walk(n, bound, d, variable)?)),
            Bool => Bool,
            False => False,
            True => True,
            NatElim {
                motive,
                zero,
                step,
                scrutinee,
            } => NatElim {
                motive: b(self.walk(motive, bound, d, variable)?),
                zero: b(self.walk(zero, bound, d, variable)?),
                step: b(self.walk(step, bound, d, variable)?),
                scrutinee: b(self.walk(scrutinee, bound, d, variable)?),
            },
            BoolElim {
                motive,
                on_false,
                on_true,
                scrutinee,
            } => BoolElim {
                motive: b(self.walk(motive, bound, d, variable)?),
                on_false: b(self.walk(on_false, bound, d, variable)?),
                on_true: b(self.walk(on_true, bound, d, variable)?),
                scrutinee: b(self.walk(scrutinee, bound, d, variable)?),
            },
            Eq { ty, lhs, rhs } => Eq {
                ty: b(self.walk(ty, bound, d, variable)?),
                lhs: b(self.walk(lhs, bound, d, variable)?),
                rhs: b(self.walk(rhs, bound, d, variable)?),
            },
            Refl { ty, value } => Refl {
                ty: b(self.walk(ty, bound, d, variable)?),
                value: b(self.walk(value, bound, d, variable)?),
            },
            Transport {
                ty,
                from,
                to,
                equality,
                motive,
                value,
            } => Transport {
                ty: b(self.walk(ty, bound, d, variable)?),
                from: b(self.walk(from, bound, d, variable)?),
                to: b(self.walk(to, bound, d, variable)?),
                equality: b(self.walk(equality, bound, d, variable)?),
                motive: b(self.walk(motive, bound, d, variable)?),
                value: b(self.walk(value, bound, d, variable)?),
            },
        })
    }

    pub(super) fn convert(&mut self, left: &Expr, right: &Expr, depth: usize) -> Result<()> {
        self.budget.tick(depth)?;
        let left = self.normalize(left, depth + 1)?;
        let right = self.normalize(right, depth + 1)?;
        if self.same(&left, &right, depth + 1)? {
            Ok(())
        } else {
            Err(Error::TypeMismatch.into())
        }
    }

    pub(super) fn same(&mut self, left: &Expr, right: &Expr, depth: usize) -> Result<bool> {
        self.budget.tick(depth)?;
        if std::mem::discriminant(left) != std::mem::discriminant(right) {
            return Ok(false);
        }
        match (left, right) {
            (Expr::Sort(a), Expr::Sort(b)) | (Expr::Var(a), Expr::Var(b)) => return Ok(a == b),
            (Expr::Const(a), Expr::Const(b)) => {
                self.budget
                    .charge_many(a.len().max(b.len()) as u64)
                    .map_err(Failure::Incomplete)?;
                return Ok(a == b);
            }
            _ => {}
        }
        let a = children(left);
        let b = children(right);
        for (a, b) in a.into_iter().zip(b) {
            if !self.same(a, b, depth + 1)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn normalize(&mut self, expr: &Expr, depth: usize) -> Result<Expr> {
        self.budget.tick(depth)?;
        use Expr::*;
        let d = depth + 1;
        Ok(match expr {
            Sort(u) => Sort(*u),
            Var(i) => Var(*i),
            Const(name) => {
                let entry = self.entry(name, d)?;
                match &entry.definition {
                    Some(body) => self.normalize(body, d)?,
                    None => {
                        self.budget
                            .charge_many(name.len() as u64)
                            .map_err(Failure::Incomplete)?;
                        Const(name.clone())
                    }
                }
            }
            Pi { domain, body } => Pi {
                domain: b(self.normalize(domain, d)?),
                body: b(self.normalize(body, d)?),
            },
            Lam { domain, body } => Lam {
                domain: b(self.normalize(domain, d)?),
                body: b(self.normalize(body, d)?),
            },
            Sigma { domain, body } => Sigma {
                domain: b(self.normalize(domain, d)?),
                body: b(self.normalize(body, d)?),
            },
            App { fun, arg } => {
                let fun = self.normalize(fun, d)?;
                let arg = self.normalize(arg, d)?;
                match fun {
                    Lam { body, .. } => {
                        let reduced = self.instantiate(&body, &arg, d)?;
                        self.normalize(&reduced, d)?
                    }
                    neutral @ (Sort(_)
                    | Var(_)
                    | Const(_)
                    | Pi { .. }
                    | App { .. }
                    | Sigma { .. }
                    | Pair { .. }
                    | Fst(_)
                    | Snd(_)
                    | Nat
                    | Zero
                    | Succ(_)
                    | NatElim { .. }
                    | Bool
                    | False
                    | True
                    | BoolElim { .. }
                    | Eq { .. }
                    | Refl { .. }
                    | Transport { .. }) => App {
                        fun: b(neutral),
                        arg: b(arg),
                    },
                }
            }
            Pair {
                sigma,
                first,
                second,
            } => Pair {
                sigma: b(self.normalize(sigma, d)?),
                first: b(self.normalize(first, d)?),
                second: b(self.normalize(second, d)?),
            },
            Fst(pair) => match self.normalize(pair, d)? {
                Pair { first, .. } => *first,
                neutral @ (Sort(_)
                | Var(_)
                | Const(_)
                | Pi { .. }
                | Lam { .. }
                | App { .. }
                | Sigma { .. }
                | Fst(_)
                | Snd(_)
                | Nat
                | Zero
                | Succ(_)
                | NatElim { .. }
                | Bool
                | False
                | True
                | BoolElim { .. }
                | Eq { .. }
                | Refl { .. }
                | Transport { .. }) => Fst(b(neutral)),
            },
            Snd(pair) => match self.normalize(pair, d)? {
                Pair { second, .. } => *second,
                neutral @ (Sort(_)
                | Var(_)
                | Const(_)
                | Pi { .. }
                | Lam { .. }
                | App { .. }
                | Sigma { .. }
                | Fst(_)
                | Snd(_)
                | Nat
                | Zero
                | Succ(_)
                | NatElim { .. }
                | Bool
                | False
                | True
                | BoolElim { .. }
                | Eq { .. }
                | Refl { .. }
                | Transport { .. }) => Snd(b(neutral)),
            },
            Nat => Nat,
            Zero => Zero,
            Succ(n) => Succ(b(self.normalize(n, d)?)),
            Bool => Bool,
            False => False,
            True => True,
            NatElim {
                motive,
                zero,
                step,
                scrutinee,
            } => match self.normalize(scrutinee, d)? {
                Zero => self.normalize(zero, d)?,
                Succ(n) => {
                    let recursion = NatElim {
                        motive: b(self.copy(motive, d)?),
                        zero: b(self.copy(zero, d)?),
                        step: b(self.copy(step, d)?),
                        scrutinee: b(self.copy(&n, d)?),
                    };
                    let reduced = App {
                        fun: b(App {
                            fun: b(self.copy(step, d)?),
                            arg: n,
                        }),
                        arg: b(recursion),
                    };
                    self.normalize(&reduced, d)?
                }
                neutral @ (Sort(_)
                | Var(_)
                | Const(_)
                | Pi { .. }
                | Lam { .. }
                | App { .. }
                | Sigma { .. }
                | Pair { .. }
                | Fst(_)
                | Snd(_)
                | Nat
                | NatElim { .. }
                | Bool
                | False
                | True
                | BoolElim { .. }
                | Eq { .. }
                | Refl { .. }
                | Transport { .. }) => NatElim {
                    motive: b(self.normalize(motive, d)?),
                    zero: b(self.normalize(zero, d)?),
                    step: b(self.normalize(step, d)?),
                    scrutinee: b(neutral),
                },
            },
            BoolElim {
                motive,
                on_false,
                on_true,
                scrutinee,
            } => match self.normalize(scrutinee, d)? {
                False => self.normalize(on_false, d)?,
                True => self.normalize(on_true, d)?,
                neutral @ (Sort(_)
                | Var(_)
                | Const(_)
                | Pi { .. }
                | Lam { .. }
                | App { .. }
                | Sigma { .. }
                | Pair { .. }
                | Fst(_)
                | Snd(_)
                | Nat
                | Zero
                | Succ(_)
                | NatElim { .. }
                | Bool
                | BoolElim { .. }
                | Eq { .. }
                | Refl { .. }
                | Transport { .. }) => BoolElim {
                    motive: b(self.normalize(motive, d)?),
                    on_false: b(self.normalize(on_false, d)?),
                    on_true: b(self.normalize(on_true, d)?),
                    scrutinee: b(neutral),
                },
            },
            Eq { ty, lhs, rhs } => Eq {
                ty: b(self.normalize(ty, d)?),
                lhs: b(self.normalize(lhs, d)?),
                rhs: b(self.normalize(rhs, d)?),
            },
            Refl { ty, value } => Refl {
                ty: b(self.normalize(ty, d)?),
                value: b(self.normalize(value, d)?),
            },
            Transport {
                ty,
                from,
                to,
                equality,
                motive,
                value,
            } => match self.normalize(equality, d)? {
                Refl { .. } => self.normalize(value, d)?,
                neutral @ (Sort(_)
                | Var(_)
                | Const(_)
                | Pi { .. }
                | Lam { .. }
                | App { .. }
                | Sigma { .. }
                | Pair { .. }
                | Fst(_)
                | Snd(_)
                | Nat
                | Zero
                | Succ(_)
                | NatElim { .. }
                | Bool
                | False
                | True
                | BoolElim { .. }
                | Eq { .. }
                | Transport { .. }) => Transport {
                    ty: b(self.normalize(ty, d)?),
                    from: b(self.normalize(from, d)?),
                    to: b(self.normalize(to, d)?),
                    equality: b(neutral),
                    motive: b(self.normalize(motive, d)?),
                    value: b(self.normalize(value, d)?),
                },
            },
        })
    }
}
