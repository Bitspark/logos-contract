import * as e from "./expr.js";
import { Budget } from "./budget.js";
import { copy, instantiate, same } from "./syntax.js";

export interface Entry {
  readonly type: e.Expr;
  readonly definition: e.Expr | null;
  readonly usedConstants: ReadonlySet<string>;
  readonly dependencies: ReadonlySet<string>;
}

/** Native reduction only. There is no extension evaluator or host callback. */
export class Reduction {
  readonly usedConstants = new Set<string>();
  readonly dependencies = new Set<string>();

  constructor(readonly signature: ReadonlyMap<string, Entry>, readonly budget: Budget) {}

  entry(name: string, depth: number): Entry {
    this.budget.tick(depth);
    this.budget.charge(name.length);
    const entry = this.signature.get(name);
    if (entry === undefined) this.budget.invalid("unknown-constant");
    this.usedConstants.add(name);
    for (const used of entry.usedConstants) {
      this.budget.tick(depth);
      this.budget.charge(used.length);
      this.usedConstants.add(used);
    }
    for (const dependency of entry.dependencies) {
      this.budget.tick(depth);
      this.budget.charge(dependency.length);
      this.dependencies.add(dependency);
    }
    return entry;
  }

  /** Closure follows original syntax, including operands conversion can erase. */
  collect(expr: e.Expr): void {
    const stack = [expr];
    while (stack.length > 0) {
      this.budget.tick(0);
      const current = stack.pop()!;
      if (current.kind === "const") this.entry(current.name, 0);
      const operands = e.children(current);
      for (let i = operands.length - 1; i >= 0; i -= 1) stack.push(operands[i]!);
    }
  }

  convert(left: e.Expr, right: e.Expr, depth: number): void {
    this.budget.tick(depth);
    const a = this.normalize(left, depth + 1);
    const b = this.normalize(right, depth + 1);
    if (!same(a, b, this.budget, depth + 1)) this.budget.invalid("type-mismatch");
  }

  normalize(expr: e.Expr, depth: number): e.Expr {
    this.budget.tick(depth);
    const d = depth + 1;
    switch (expr.kind) {
      case "sort": case "var": case "nat": case "zero":
      case "bool": case "false": case "true": return expr;
      case "const": {
        const entry = this.entry(expr.name, d);
        return entry.definition === null ? expr : this.normalize(entry.definition, d);
      }
      case "pi": return e.pi(this.normalize(expr.domain, d), this.normalize(expr.body, d));
      case "lam": return e.lam(this.normalize(expr.domain, d), this.normalize(expr.body, d));
      case "sigma": return e.sigma(this.normalize(expr.domain, d), this.normalize(expr.body, d));
      case "app": {
        const fun = this.normalize(expr.fun, d);
        const arg = this.normalize(expr.arg, d);
        return fun.kind === "lam"
          ? this.normalize(instantiate(fun.body, arg, this.budget, d), d) : e.app(fun, arg);
      }
      case "pair": return e.pair(this.normalize(expr.sigma, d),
        this.normalize(expr.first, d), this.normalize(expr.second, d));
      case "fst": {
        const pair = this.normalize(expr.pair, d);
        return pair.kind === "pair" ? pair.first : e.fst(pair);
      }
      case "snd": {
        const pair = this.normalize(expr.pair, d);
        return pair.kind === "pair" ? pair.second : e.snd(pair);
      }
      case "succ": return e.succ(this.normalize(expr.value, d));
      case "nat-elim": return this.natElim(expr, d);
      case "bool-elim": {
        const scrutinee = this.normalize(expr.scrutinee, d);
        if (scrutinee.kind === "false") return this.normalize(expr.onFalse, d);
        if (scrutinee.kind === "true") return this.normalize(expr.onTrue, d);
        return e.boolElim(this.normalize(expr.motive, d), this.normalize(expr.onFalse, d),
          this.normalize(expr.onTrue, d), scrutinee);
      }
      case "id": return e.id(this.normalize(expr.type, d),
        this.normalize(expr.lhs, d), this.normalize(expr.rhs, d));
      case "refl": return e.refl(this.normalize(expr.type, d), this.normalize(expr.value, d));
      case "transport": {
        const equality = this.normalize(expr.equality, d);
        if (equality.kind === "refl") return this.normalize(expr.value, d);
        return e.transport(this.normalize(expr.type, d), this.normalize(expr.from, d),
          this.normalize(expr.to, d), equality, this.normalize(expr.motive, d),
          this.normalize(expr.value, d));
      }
    }
  }

  private natElim(expr: Extract<e.Expr, { kind: "nat-elim" }>, depth: number): e.Expr {
    const scrutinee = this.normalize(expr.scrutinee, depth);
    if (scrutinee.kind === "zero") return this.normalize(expr.zero, depth);
    if (scrutinee.kind === "succ") {
      const recursion = e.natElim(copy(expr.motive, this.budget, depth),
        copy(expr.zero, this.budget, depth), copy(expr.step, this.budget, depth),
        copy(scrutinee.value, this.budget, depth));
      const reduced = e.app(e.app(copy(expr.step, this.budget, depth), scrutinee.value), recursion);
      return this.normalize(reduced, depth);
    }
    return e.natElim(this.normalize(expr.motive, depth), this.normalize(expr.zero, depth),
      this.normalize(expr.step, depth), scrutinee);
  }
}
