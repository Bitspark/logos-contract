use super::*;

impl<'a> Machine<'a> {
    pub(super) fn new(signature: &'a Signature, budget: &'a mut Budget) -> Self {
        Self {
            started: budget.spent,
            signature,
            budget,
            used_constants: BTreeSet::new(),
            dependencies: BTreeSet::new(),
        }
    }

    pub(super) fn finish<T>(self, result: Result<T>) -> Outcome<T> {
        match result {
            Ok(value) => Outcome::Accepted(Accepted {
                value,
                used_constants: self.used_constants,
                dependencies: self.dependencies,
                steps: self.budget.spent - self.started,
            }),
            Err(Failure::Invalid(error)) => Outcome::Invalid(error),
            Err(Failure::Incomplete(limit)) => Outcome::Incomplete(limit),
        }
    }

    pub(super) fn context(&mut self, supplied: &[Expr]) -> Result<Vec<Expr>> {
        let mut ctx = Vec::new();
        for ty in supplied {
            self.context_entry(ty, &mut ctx)?;
        }
        Ok(ctx)
    }

    pub(super) fn context_entry(&mut self, ty: &Expr, ctx: &mut Vec<Expr>) -> Result<()> {
        self.budget.tick(ctx.len())?;
        self.universe(ty, ctx, 0)?;
        self.collect(ty, 0)?;
        ctx.push(self.copy(ty, 0)?);
        Ok(())
    }

    /// Reachability is syntactic, including operands subsequently erased by
    /// conversion. Checked entries already contain their declaration closure.
    pub(super) fn collect(&mut self, expression: &Expr, depth: usize) -> Result<()> {
        self.budget.tick(depth)?;
        if let Expr::Const(name) = expression {
            self.entry(name, depth)?;
        }
        for child in children(expression) {
            self.collect(child, depth + 1)?;
        }
        Ok(())
    }

    pub(super) fn entry(&mut self, name: &str, depth: usize) -> Result<&'a Entry> {
        self.budget.tick(depth)?;
        self.budget
            .charge_many(name.len() as u64)
            .map_err(Failure::Incomplete)?;
        let entry = self
            .signature
            .entries
            .get(name)
            .ok_or_else(|| Error::UnknownConstant(name.to_owned()))?;
        self.used_constants.insert(name.to_owned());
        for constant in &entry.used_constants {
            self.budget.tick(depth)?;
            self.budget
                .charge_many(constant.len() as u64)
                .map_err(Failure::Incomplete)?;
            self.used_constants.insert(constant.clone());
        }
        for dependency in &entry.dependencies {
            self.budget.tick(depth)?;
            self.budget
                .charge_many(dependency.len() as u64)
                .map_err(Failure::Incomplete)?;
            self.dependencies.insert(dependency.clone());
        }
        Ok(entry)
    }

    pub(super) fn universe(
        &mut self,
        expr: &Expr,
        ctx: &mut Vec<Expr>,
        depth: usize,
    ) -> Result<u32> {
        self.budget.tick(depth)?;
        let inferred = self.infer(expr, ctx, depth + 1)?;
        match self.normalize(&inferred, depth + 1)? {
            Expr::Sort(level) => Ok(level),
            Expr::Var(_)
            | Expr::Const(_)
            | Expr::Pi { .. }
            | Expr::Lam { .. }
            | Expr::App { .. }
            | Expr::Sigma { .. }
            | Expr::Pair { .. }
            | Expr::Fst(_)
            | Expr::Snd(_)
            | Expr::Nat
            | Expr::Zero
            | Expr::Succ(_)
            | Expr::NatElim { .. }
            | Expr::Bool
            | Expr::False
            | Expr::True
            | Expr::BoolElim { .. }
            | Expr::Eq { .. }
            | Expr::Refl { .. }
            | Expr::Transport { .. } => Err(Error::ExpectedUniverse.into()),
        }
    }

    pub(super) fn expect(
        &mut self,
        expr: &Expr,
        expected: &Expr,
        ctx: &mut Vec<Expr>,
        depth: usize,
    ) -> Result<()> {
        self.budget.tick(depth)?;
        let actual = self.infer(expr, ctx, depth + 1)?;
        self.convert(&actual, expected, depth + 1)
    }

    pub(super) fn infer(&mut self, expr: &Expr, ctx: &mut Vec<Expr>, depth: usize) -> Result<Expr> {
        self.budget.tick(depth)?;
        use Expr::*;
        let d = depth + 1;
        match expr {
            Sort(level) => Ok(Sort(
                level
                    .checked_add(1)
                    .ok_or(Failure::Incomplete(Limit::UniverseCapacity))?,
            )),
            Var(index) => {
                // A non-addressable/out-of-scope variable is invalid regardless
                // of host word size. Check scope before computing its distance.
                let i = usize::try_from(*index).map_err(|_| Error::EscapedVariable)?;
                if i >= ctx.len() {
                    return Err(Error::EscapedVariable.into());
                }
                let at = ctx.len() - (i + 1);
                self.shift(
                    &ctx[at],
                    index
                        .checked_add(1)
                        .ok_or(Failure::Incomplete(Limit::IndexCapacity))?,
                    d,
                )
            }
            Const(name) => {
                let entry = self.entry(name, d)?;
                self.copy(&entry.ty, d)
            }
            Pi { domain, body } | Sigma { domain, body } => {
                let a = self.universe(domain, ctx, d)?;
                ctx.push(self.copy(domain, d)?);
                let result = self.universe(body, ctx, d);
                let _ = ctx.pop();
                Ok(Sort(a.max(result?)))
            }
            Lam { domain, body } => {
                self.universe(domain, ctx, d)?;
                ctx.push(self.copy(domain, d)?);
                let result = self.infer(body, ctx, d);
                let _ = ctx.pop();
                Ok(Pi {
                    domain: b(self.copy(domain, d)?),
                    body: b(result?),
                })
            }
            App { fun, arg } => {
                let ty = self.infer(fun, ctx, d)?;
                match self.normalize(&ty, d)? {
                    Pi { domain, body } => {
                        self.expect(arg, &domain, ctx, d)?;
                        self.instantiate(&body, arg, d)
                    }
                    Sort(_)
                    | Var(_)
                    | Const(_)
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
                    | Refl { .. }
                    | Transport { .. } => Err(Error::ExpectedFunction.into()),
                }
            }
            Pair {
                sigma,
                first,
                second,
            } => {
                self.universe(sigma, ctx, d)?;
                match self.normalize(sigma, d)? {
                    Sigma { domain, body } => {
                        self.expect(first, &domain, ctx, d)?;
                        let second_ty = self.instantiate(&body, first, d)?;
                        self.expect(second, &second_ty, ctx, d)?;
                        self.copy(sigma, d)
                    }
                    Sort(_)
                    | Var(_)
                    | Const(_)
                    | Pi { .. }
                    | Lam { .. }
                    | App { .. }
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
                    | Transport { .. } => Err(Error::ExpectedSigma.into()),
                }
            }
            Fst(pair) | Snd(pair) => {
                let ty = self.infer(pair, ctx, d)?;
                match self.normalize(&ty, d)? {
                    Sigma { domain, body } => {
                        if matches!(expr, Fst(_)) {
                            Ok(*domain)
                        } else {
                            let first = Fst(b(self.copy(pair, d)?));
                            self.instantiate(&body, &first, d)
                        }
                    }
                    Sort(_)
                    | Var(_)
                    | Const(_)
                    | Pi { .. }
                    | Lam { .. }
                    | App { .. }
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
                    | Transport { .. } => Err(Error::ExpectedSigma.into()),
                }
            }
            Nat | Bool => Ok(Sort(0)),
            Zero => Ok(Nat),
            Succ(n) => {
                self.expect(n, &Nat, ctx, d)?;
                Ok(Nat)
            }
            False | True => Ok(Bool),
            NatElim {
                motive,
                zero,
                step,
                scrutinee,
            } => {
                self.motive(motive, &Nat, ctx, d)?;
                self.expect(scrutinee, &Nat, ctx, d)?;
                let zero_ty = App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(Zero),
                };
                self.expect(zero, &zero_ty, ctx, d)?;
                let ih_ty = App {
                    fun: b(self.shift(motive, 1, d)?),
                    arg: b(Var(0)),
                };
                let step_result = App {
                    fun: b(self.shift(motive, 2, d)?),
                    arg: b(Succ(b(Var(1)))),
                };
                let step_ty = Pi {
                    domain: b(Nat),
                    body: b(Pi {
                        domain: b(ih_ty),
                        body: b(step_result),
                    }),
                };
                self.expect(step, &step_ty, ctx, d)?;
                Ok(App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(self.copy(scrutinee, d)?),
                })
            }
            BoolElim {
                motive,
                on_false,
                on_true,
                scrutinee,
            } => {
                self.motive(motive, &Bool, ctx, d)?;
                self.expect(scrutinee, &Bool, ctx, d)?;
                let false_ty = App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(False),
                };
                let true_ty = App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(True),
                };
                self.expect(on_false, &false_ty, ctx, d)?;
                self.expect(on_true, &true_ty, ctx, d)?;
                Ok(App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(self.copy(scrutinee, d)?),
                })
            }
            Eq { ty, lhs, rhs } => {
                let level = self.universe(ty, ctx, d)?;
                self.expect(lhs, ty, ctx, d)?;
                self.expect(rhs, ty, ctx, d)?;
                Ok(Sort(level))
            }
            Refl { ty, value } => {
                self.universe(ty, ctx, d)?;
                self.expect(value, ty, ctx, d)?;
                Ok(Eq {
                    ty: b(self.copy(ty, d)?),
                    lhs: b(self.copy(value, d)?),
                    rhs: b(self.copy(value, d)?),
                })
            }
            Transport {
                ty,
                from,
                to,
                equality,
                motive,
                value,
            } => {
                self.universe(ty, ctx, d)?;
                self.expect(from, ty, ctx, d)?;
                self.expect(to, ty, ctx, d)?;
                let equality_ty = Eq {
                    ty: b(self.copy(ty, d)?),
                    lhs: b(self.copy(from, d)?),
                    rhs: b(self.copy(to, d)?),
                };
                self.expect(equality, &equality_ty, ctx, d)?;
                self.motive(motive, ty, ctx, d)?;
                let source_ty = App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(self.copy(from, d)?),
                };
                self.expect(value, &source_ty, ctx, d)?;
                Ok(App {
                    fun: b(self.copy(motive, d)?),
                    arg: b(self.copy(to, d)?),
                })
            }
        }
    }

    pub(super) fn motive(
        &mut self,
        motive: &Expr,
        domain: &Expr,
        ctx: &mut Vec<Expr>,
        depth: usize,
    ) -> Result<()> {
        self.budget.tick(depth)?;
        let ty = self.infer(motive, ctx, depth + 1)?;
        match self.normalize(&ty, depth + 1)? {
            Expr::Pi {
                domain: actual,
                body,
            } => {
                self.convert(&actual, domain, depth + 1)?;
                if matches!(*body, Expr::Sort(_)) {
                    Ok(())
                } else {
                    Err(Error::ExpectedUniverse.into())
                }
            }
            Expr::Sort(_)
            | Expr::Var(_)
            | Expr::Const(_)
            | Expr::Lam { .. }
            | Expr::App { .. }
            | Expr::Sigma { .. }
            | Expr::Pair { .. }
            | Expr::Fst(_)
            | Expr::Snd(_)
            | Expr::Nat
            | Expr::Zero
            | Expr::Succ(_)
            | Expr::NatElim { .. }
            | Expr::Bool
            | Expr::False
            | Expr::True
            | Expr::BoolElim { .. }
            | Expr::Eq { .. }
            | Expr::Refl { .. }
            | Expr::Transport { .. } => Err(Error::ExpectedFunction.into()),
        }
    }
}
