use super::foundation::{self, Budget, Signature};
use super::{preflight, Accepted, Declaration, Expr, Limits, Outcome, Policy, Statement};
use super::{Location, Phase, Unsupported, CHECKER, FOUNDATION, MAX_DEPTH};
use std::collections::BTreeSet;

/// Check supplied syntax against a caller-fixed statement and current policy.
/// No result is minted until input, typing, actual dependencies and snapshot
/// construction have all completed within the same work allowance.
pub fn check(statement: &Statement, candidate: &Expr, policy: &Policy, limits: Limits) -> Outcome {
    let mut budget = Budget::new(limits.work as u64, limits.depth.min(MAX_DEPTH) as usize);
    match checked(statement, candidate, policy, limits, &mut budget) {
        Ok(accepted) => Outcome::Accepted(Box::new(accepted)),
        Err(outcome) => outcome,
    }
}

fn checked(
    statement: &Statement,
    candidate: &Expr,
    policy: &Policy,
    limits: Limits,
    budget: &mut Budget,
) -> Result<Accepted, Outcome> {
    preflight::inspect(statement, candidate, policy, limits, budget)?;
    if statement.foundation != FOUNDATION {
        return Err(Outcome::unsupported(Unsupported::Foundation));
    }
    if policy.foundation != FOUNDATION {
        return Err(Outcome::unsupported(Unsupported::UnadmittedFoundation));
    }
    if policy.checker != CHECKER {
        return Err(Outcome::unsupported(Unsupported::UnadmittedChecker));
    }

    // Preflight bounds recursive Clone depth. Its second charged traversal pays
    // for the owned receiver snapshot before any clone/allocation is performed.
    preflight::inspect(statement, candidate, policy, limits, budget)
        .map_err(|outcome| outcome.at(Location::new(Phase::Snapshot)))?;
    let owned_statement = statement.clone();
    let owned_candidate = candidate.clone();
    let owned_policy = policy.clone();
    let signature = admit(&owned_statement.declarations, budget)?;
    let (result, phase) = foundation::check_located(
        &signature,
        &owned_statement.context,
        &owned_candidate,
        &owned_statement.expected,
        budget,
    );
    let location = match phase {
        foundation::CheckPhase::Context(index) => Location::indexed(Phase::Context, index as u32),
        foundation::CheckPhase::Expected => Location::new(Phase::Expected),
        foundation::CheckPhase::Candidate => Location::new(Phase::Candidate),
    };
    let result = checked_value(result).map_err(|outcome| outcome.at(location))?;
    let mut allowed = BTreeSet::new();
    for dependency in &policy.dependencies {
        budget
            .charge()
            .map_err(|limit| Outcome::incomplete(limit.into()).at(Location::new(Phase::Policy)))?;
        allowed.insert(dependency.as_str());
    }
    for dependency in &result.dependencies {
        budget
            .charge()
            .map_err(|limit| Outcome::incomplete(limit.into()).at(Location::new(Phase::Policy)))?;
        budget
            .charge_many(dependency.len() as u64)
            .map_err(|limit| Outcome::incomplete(limit.into()).at(Location::new(Phase::Policy)))?;
        if !allowed.contains(dependency.as_str()) {
            return Err(Outcome::unsupported(Unsupported::UnadmittedDependency(
                dependency.clone(),
            )));
        }
    }
    Ok(Accepted {
        statement: owned_statement,
        candidate: owned_candidate,
        policy: owned_policy,
        used_constants: result.used_constants,
        dependencies: result.dependencies,
        steps: budget.spent(),
    })
}

fn admit(declarations: &[Declaration], budget: &mut Budget) -> Result<Signature, Outcome> {
    let mut signature = Signature::new();
    for (index, declaration) in declarations.iter().enumerate() {
        let location = Location::indexed(Phase::Declaration, index as u32);
        admit_declaration(&mut signature, declaration, budget)
            .map_err(|outcome| outcome.at(location))?;
    }
    Ok(signature)
}

fn admit_declaration(
    signature: &mut Signature,
    declaration: &Declaration,
    budget: &mut Budget,
) -> Result<(), Outcome> {
    match declaration {
        Declaration::Assume {
            name,
            ty,
            dependencies,
        } => {
            let ty = checked_value(foundation::copy(ty, budget))?.value;
            let mut admitted_dependencies = BTreeSet::new();
            for dependency in dependencies {
                budget
                    .charge()
                    .map_err(|limit| Outcome::incomplete(limit.into()))?;
                budget
                    .charge_many(dependency.len() as u64)
                    .map_err(|limit| Outcome::incomplete(limit.into()))?;
                admitted_dependencies.insert(dependency.clone());
            }
            checked_value(signature.admit(name, ty, admitted_dependencies, budget))?;
        }
        Declaration::Define { name, ty, value } => {
            let ty = checked_value(foundation::copy(ty, budget))?.value;
            let value = checked_value(foundation::copy(value, budget))?.value;
            checked_value(signature.define(name, ty, value, budget))?;
        }
    }
    Ok(())
}

fn checked_value<T>(outcome: foundation::Outcome<T>) -> Result<foundation::Accepted<T>, Outcome> {
    match outcome {
        foundation::Outcome::Accepted(value) => Ok(value),
        foundation::Outcome::Invalid(error) => Err(Outcome::invalid(error.into())),
        foundation::Outcome::Incomplete(limit) => Err(Outcome::incomplete(limit.into())),
    }
}
