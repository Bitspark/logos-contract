import * as e from "./expr.js";
import { Budget, successor } from "./budget.js";
import { MAX_NATURAL } from "./model.js";

/** Rebuild an already admitted constructor from its transformed operands. */
function rebuild(expr: e.Expr, args: readonly e.Expr[]): e.Expr {
  switch (expr.kind) {
    case "sort": return e.sort(expr.level);
    case "var": return e.variable(expr.index);
    case "const": return e.constant(expr.name);
    case "nat": return e.nat();
    case "zero": return e.zero();
    case "bool": return e.bool();
    case "false": return e.falseValue();
    case "true": return e.trueValue();
    case "pi": return e.pi(args[0]!, args[1]!);
    case "lam": return e.lam(args[0]!, args[1]!);
    case "sigma": return e.sigma(args[0]!, args[1]!);
    case "app": return e.app(args[0]!, args[1]!);
    case "pair": return e.pair(args[0]!, args[1]!, args[2]!);
    case "fst": return e.fst(args[0]!);
    case "snd": return e.snd(args[0]!);
    case "succ": return e.succ(args[0]!);
    case "nat-elim": return e.natElim(args[0]!, args[1]!, args[2]!, args[3]!);
    case "bool-elim": return e.boolElim(args[0]!, args[1]!, args[2]!, args[3]!);
    case "id": return e.id(args[0]!, args[1]!, args[2]!);
    case "refl": return e.refl(args[0]!, args[1]!);
    case "transport": return e.transport(args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!);
  }
}

type Variable = (index: number, bound: number, depth: number) => e.Expr;

function walk(expr: e.Expr, bound: number, depth: number,
  budget: Budget, variable: Variable): e.Expr {
  budget.tick(depth);
  const d = depth + 1;
  if (expr.kind === "var") return variable(expr.index, bound, d);
  if (expr.kind === "const") budget.charge(expr.name.length);
  const binds = expr.kind === "pi" || expr.kind === "lam" || expr.kind === "sigma";
  const args = e.children(expr).map((child, index) => walk(child,
    binds && index === 1 ? successor(bound, budget, "index-capacity") : bound,
    d, budget, variable));
  return rebuild(expr, args);
}

export function shift(expr: e.Expr, amount: number, budget: Budget, depth: number): e.Expr {
  return walk(expr, 0, depth, budget, (index, bound, d) => {
    budget.tick(d);
    if (index < bound) return e.variable(index);
    if (amount > MAX_NATURAL - index) budget.incomplete("index-capacity");
    return e.variable(index + amount);
  });
}

export function copy(expr: e.Expr, budget: Budget, depth = 0): e.Expr {
  return shift(expr, 0, budget, depth);
}

/** Remove the outer free slot, lifting the replacement below every inner binder. */
export function instantiate(body: e.Expr, argument: e.Expr, budget: Budget, depth: number): e.Expr {
  return walk(body, 0, depth, budget, (index, bound, d) => {
    budget.tick(d);
    if (index === bound) return shift(argument, bound, budget, d + 1);
    return e.variable(index > bound ? index - 1 : index);
  });
}

export function same(left: e.Expr, right: e.Expr, budget: Budget, depth: number): boolean {
  budget.tick(depth);
  if (left.kind !== right.kind) return false;
  if (left.kind === "sort" && right.kind === "sort") return left.level === right.level;
  if (left.kind === "var" && right.kind === "var") return left.index === right.index;
  if (left.kind === "const" && right.kind === "const") {
    budget.charge(left.name.length + right.name.length);
    return left.name === right.name;
  }
  const a = e.children(left);
  const b = e.children(right);
  for (let i = 0; i < a.length; i += 1) {
    if (!same(a[i]!, b[i]!, budget, depth + 1)) return false;
  }
  return true;
}
