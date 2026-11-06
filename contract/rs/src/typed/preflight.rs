use super::foundation::{self, Budget};
use super::{Declaration, Expr, Incomplete, Invalid, Limits, Outcome, Policy, Statement};

/// Count/copy charges deliberately apply to occurrences, not unique pointers.
/// Rust's owned Expr grammar cannot contain a safe cyclic or malformed node.
pub(super) fn inspect(
    statement: &Statement,
    candidate: &Expr,
    policy: &Policy,
    limits: Limits,
    budget: &mut Budget,
) -> Result<(), Outcome> {
    let mut scan = Scan {
        limits,
        budget,
        nodes: 0,
        entries: 0,
    };
    scan.name(&statement.foundation)?;
    scan.collection(statement.declarations.len())?;
    scan.collection(statement.context.len())?;
    scan.collection(policy.dependencies.len())?;
    for declaration in &statement.declarations {
        match declaration {
            Declaration::Assume {
                name,
                ty,
                dependencies,
            } => {
                scan.name(name)?;
                if name.is_empty() {
                    return Err(Outcome::invalid(Invalid::EmptyConstantName));
                }
                scan.collection(dependencies.len())?;
                if dependencies.is_empty() {
                    return Err(Outcome::invalid(Invalid::MissingAssumptions));
                }
                for dependency in dependencies {
                    scan.name(dependency)?;
                    if dependency.is_empty() {
                        return Err(Outcome::invalid(Invalid::MissingAssumptions));
                    }
                }
                scan.expression(ty)?;
            }
            Declaration::Define { name, ty, value } => {
                scan.name(name)?;
                if name.is_empty() {
                    return Err(Outcome::invalid(Invalid::EmptyConstantName));
                }
                scan.expression(ty)?;
                scan.expression(value)?;
            }
        }
    }
    for ty in &statement.context {
        scan.expression(ty)?;
    }
    scan.expression(&statement.expected)?;
    scan.expression(candidate)?;
    scan.name(&policy.foundation)?;
    scan.name(&policy.checker)?;
    for dependency in &policy.dependencies {
        scan.name(dependency)?;
        if dependency.is_empty() {
            return Err(Outcome::invalid(Invalid::MalformedInput));
        }
    }
    Ok(())
}

struct Scan<'a> {
    limits: Limits,
    budget: &'a mut Budget,
    nodes: u64,
    entries: u64,
}

impl Scan<'_> {
    fn charge(&mut self) -> Result<(), Outcome> {
        self.budget
            .charge()
            .map_err(|limit| Outcome::incomplete(limit.into()))
    }

    fn name(&mut self, name: &str) -> Result<(), Outcome> {
        if name.len() > self.limits.name_bytes as usize {
            return Err(Outcome::incomplete(Incomplete::NameBytes));
        }
        self.charge()?;
        self.budget
            .charge_many(name.len() as u64)
            .map_err(|limit| Outcome::incomplete(limit.into()))?;
        Ok(())
    }

    fn collection(&mut self, count: usize) -> Result<(), Outcome> {
        // Compare before adding: a caller-owned oversized collection does not
        // get traversed or copied, and arithmetic cannot overflow.
        if count as u128 + self.entries as u128 > self.limits.collection_entries as u128 {
            return Err(Outcome::incomplete(Incomplete::CollectionEntries));
        }
        self.entries += count as u64;
        for _ in 0..count {
            self.charge()?;
        }
        Ok(())
    }

    fn expression(&mut self, root: &Expr) -> Result<(), Outcome> {
        let mut pending = vec![(root, 1u32)];
        while let Some((expression, depth)) = pending.pop() {
            self.charge()?;
            if depth > self.limits.input_depth.min(super::MAX_INPUT_DEPTH) {
                return Err(Outcome::incomplete(Incomplete::InputDepth));
            }
            if self.nodes >= self.limits.input_nodes as u64 {
                return Err(Outcome::incomplete(Incomplete::InputNodes));
            }
            self.nodes += 1;
            if let Expr::Const(name) = expression {
                self.name(name)?;
                if name.is_empty() {
                    return Err(Outcome::invalid(Invalid::EmptyConstantName));
                }
            }
            for child in foundation::children(expression).into_iter().rev() {
                pending.push((child, depth + 1));
            }
        }
        Ok(())
    }
}
