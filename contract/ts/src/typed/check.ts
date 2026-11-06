import type { Expr } from "./expr.js";
import { Budget, sorted } from "./budget.js";
import * as m from "./model.js";
import { accepted, CheckFailure, type Outcome } from "./outcome.js";
import { Preflight, validateLimits } from "./preflight.js";
import { Machine } from "./machine.js";
import type { Entry } from "./reduction.js";
import { copy } from "./syntax.js";

function snapshot(input: m.Statement, candidate: Expr, policy: m.Policy, budget: Budget): {
  statement: m.Statement; candidate: Expr; policy: m.Policy;
} {
  budget.locate("snapshot");
  const declarations: m.Declaration[] = [];
  for (const declaration of input.declarations) {
    budget.tick(0);
    const type = copy(declaration.type, budget);
    if (declaration.kind === "assume") {
      const dependencies: string[] = [];
      for (const dependency of declaration.dependencies) { budget.tick(0); dependencies.push(dependency); }
      declarations.push(m.assume(declaration.name, type, dependencies));
    } else declarations.push(m.define(declaration.name, type, copy(declaration.value, budget)));
  }
  const context: Expr[] = [];
  for (const type of input.context) { budget.tick(0); context.push(copy(type, budget)); }
  const expected = copy(input.expected, budget);
  const proof = copy(candidate, budget);
  const dependencies: string[] = [];
  for (const dependency of policy.dependencies) { budget.tick(0); dependencies.push(dependency); }
  budget.tick(0);
  return { statement: m.statement({ foundation: input.foundation, declarations, context, expected }),
    candidate: proof, policy: m.policy({ foundation: policy.foundation, checker: policy.checker, dependencies }) };
}

function signature(declarations: readonly m.Declaration[], budget: Budget): ReadonlyMap<string, Entry> {
  const entries = new Map<string, Entry>();
  for (let index = 0; index < declarations.length; index += 1) {
    budget.locate("declaration", index);
    budget.tick(0);
    const declaration = declarations[index]!;
    budget.charge(declaration.name.length);
    if (entries.has(declaration.name)) budget.invalid("duplicate-constant");
    const machine = new Machine(entries, budget);
    machine.collect(declaration.type);
    machine.universe(declaration.type, [], 0);
    if (declaration.kind === "define") {
      machine.collect(declaration.value);
      machine.expect(declaration.value, declaration.type, [], 0);
    } else {
      for (const dependency of declaration.dependencies) {
        budget.tick(0);
        budget.charge(dependency.length);
        machine.dependencies.add(dependency);
      }
    }
    budget.tick(0);
    budget.charge(declaration.name.length);
    entries.set(declaration.name, { type: declaration.type,
      definition: declaration.kind === "define" ? declaration.value : null,
      usedConstants: machine.usedConstants, dependencies: machine.dependencies });
  }
  return entries;
}

/**
 * Check supplied proof syntax against one receiver-fixed statement. This performs
 * no search, artifact extraction, declaration discovery or host callback.
 * Inputs must come from typed syntax-storage constructors; hostile serialized
 * ingress is not a service provided by this in-process API.
 */
export function check(statement: m.Statement, candidate: Expr, policy: m.Policy,
  limits: m.Limits = m.defaultLimits()): Outcome {
  try {
    validateLimits(limits);
    const budget = new Budget(limits);
    new Preflight(limits, budget).inspect(statement, candidate, policy);
    budget.locate("policy");
    if (statement.foundation !== m.FOUNDATION) budget.unsupported("foundation");
    if (policy.foundation !== m.FOUNDATION) budget.unsupported("unadmitted-foundation");
    if (policy.checker !== m.CHECKER) budget.unsupported("unadmitted-checker");
    const owned = snapshot(statement, candidate, policy, budget);
    const machine = new Machine(signature(owned.statement.declarations, budget), budget);
    const context = machine.context(owned.statement.context);
    budget.locate("expected");
    machine.collect(owned.statement.expected);
    machine.universe(owned.statement.expected, context, 0);
    budget.locate("candidate");
    machine.collect(owned.candidate);
    const actual = machine.infer(owned.candidate, context, 0);
    machine.convert(actual, owned.statement.expected, 0);
    budget.locate("policy");
    const allowed = new Set<string>();
    for (const dependency of owned.policy.dependencies) {
      budget.tick(0);
      budget.charge(dependency.length);
      allowed.add(dependency);
    }
    for (const dependency of machine.dependencies) {
      budget.tick(0);
      budget.charge(dependency.length);
      if (!allowed.has(dependency)) budget.unsupported("unadmitted-dependency");
    }
    budget.locate("snapshot");
    const dependencies = sorted(machine.dependencies, budget);
    const usedConstants = sorted(machine.usedConstants, budget);
    budget.tick(0);
    return accepted(owned.statement, owned.candidate, owned.policy,
      dependencies, usedConstants, budget.spent);
  } catch (failure) {
    if (failure instanceof CheckFailure) return failure.outcome;
    throw failure;
  }
}
