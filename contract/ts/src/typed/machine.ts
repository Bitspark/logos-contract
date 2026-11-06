import * as e from "./expr.js";
import { successor } from "./budget.js";
import { Reduction } from "./reduction.js";
import { copy, instantiate, shift } from "./syntax.js";

/** The selected rulebook's typing rules over an admitted closed signature. */
export class Machine extends Reduction {
  context(supplied: readonly e.Expr[]): e.Expr[] {
    const context: e.Expr[] = [];
    for (let index = 0; index < supplied.length; index += 1) {
      this.budget.locate("context", index);
      this.budget.tick(context.length);
      const type = supplied[index]!;
      this.collect(type);
      this.universe(type, context, 0);
      context.push(copy(type, this.budget, 0));
    }
    return context;
  }

  universe(expr: e.Expr, context: e.Expr[], depth: number): number {
    this.budget.tick(depth);
    const inferred = this.infer(expr, context, depth + 1);
    const reduced = this.normalize(inferred, depth + 1);
    if (reduced.kind !== "sort") this.budget.invalid("expected-universe");
    return reduced.level;
  }

  expect(expr: e.Expr, expected: e.Expr, context: e.Expr[], depth: number): void {
    this.budget.tick(depth);
    const actual = this.infer(expr, context, depth + 1);
    this.convert(actual, expected, depth + 1);
  }

  infer(expr: e.Expr, context: e.Expr[], depth: number): e.Expr {
    this.budget.tick(depth);
    const d = depth + 1;
    switch (expr.kind) {
      case "sort": return e.sort(successor(expr.level, this.budget, "universe-capacity"));
      case "var": {
        if (expr.index >= context.length) this.budget.invalid("escaped-variable");
        return shift(context[context.length - 1 - expr.index]!,
          successor(expr.index, this.budget, "index-capacity"), this.budget, d);
      }
      case "const": return copy(this.entry(expr.name, d).type, this.budget, d);
      case "pi": case "sigma": {
        const a = this.universe(expr.domain, context, d);
        context.push(copy(expr.domain, this.budget, d));
        let b: number;
        try { b = this.universe(expr.body, context, d); } finally { context.pop(); }
        return e.sort(Math.max(a, b));
      }
      case "lam": {
        this.universe(expr.domain, context, d);
        context.push(copy(expr.domain, this.budget, d));
        let body: e.Expr;
        try { body = this.infer(expr.body, context, d); } finally { context.pop(); }
        return e.pi(copy(expr.domain, this.budget, d), body);
      }
      case "app": {
        const type = this.normalize(this.infer(expr.fun, context, d), d);
        if (type.kind !== "pi") this.budget.invalid("expected-function");
        this.expect(expr.arg, type.domain, context, d);
        return instantiate(type.body, expr.arg, this.budget, d);
      }
      case "pair": {
        this.universe(expr.sigma, context, d);
        const type = this.normalize(expr.sigma, d);
        if (type.kind !== "sigma") this.budget.invalid("expected-sigma");
        this.expect(expr.first, type.domain, context, d);
        this.expect(expr.second, instantiate(type.body, expr.first, this.budget, d), context, d);
        return copy(expr.sigma, this.budget, d);
      }
      case "fst": case "snd": {
        const type = this.normalize(this.infer(expr.pair, context, d), d);
        if (type.kind !== "sigma") this.budget.invalid("expected-sigma");
        return expr.kind === "fst" ? type.domain
          : instantiate(type.body, e.fst(copy(expr.pair, this.budget, d)), this.budget, d);
      }
      case "nat": case "bool": return e.sort(0);
      case "zero": return e.nat();
      case "succ": this.expect(expr.value, e.nat(), context, d); return e.nat();
      case "false": case "true": return e.bool();
      case "nat-elim": return this.inferNatElim(expr, context, d);
      case "bool-elim": {
        this.motive(expr.motive, e.bool(), context, d);
        this.expect(expr.scrutinee, e.bool(), context, d);
        this.expect(expr.onFalse, e.app(copy(expr.motive, this.budget, d), e.falseValue()), context, d);
        this.expect(expr.onTrue, e.app(copy(expr.motive, this.budget, d), e.trueValue()), context, d);
        return e.app(copy(expr.motive, this.budget, d), copy(expr.scrutinee, this.budget, d));
      }
      case "id": {
        const level = this.universe(expr.type, context, d);
        this.expect(expr.lhs, expr.type, context, d);
        this.expect(expr.rhs, expr.type, context, d);
        return e.sort(level);
      }
      case "refl": {
        this.universe(expr.type, context, d);
        this.expect(expr.value, expr.type, context, d);
        return e.id(copy(expr.type, this.budget, d), copy(expr.value, this.budget, d),
          copy(expr.value, this.budget, d));
      }
      case "transport": {
        this.universe(expr.type, context, d);
        this.expect(expr.from, expr.type, context, d);
        this.expect(expr.to, expr.type, context, d);
        this.expect(expr.equality, e.id(copy(expr.type, this.budget, d),
          copy(expr.from, this.budget, d), copy(expr.to, this.budget, d)), context, d);
        this.motive(expr.motive, expr.type, context, d);
        this.expect(expr.value, e.app(copy(expr.motive, this.budget, d),
          copy(expr.from, this.budget, d)), context, d);
        return e.app(copy(expr.motive, this.budget, d), copy(expr.to, this.budget, d));
      }
    }
  }

  private inferNatElim(expr: Extract<e.Expr, { kind: "nat-elim" }>,
    context: e.Expr[], depth: number): e.Expr {
    this.motive(expr.motive, e.nat(), context, depth);
    this.expect(expr.scrutinee, e.nat(), context, depth);
    this.expect(expr.zero, e.app(copy(expr.motive, this.budget, depth), e.zero()), context, depth);
    const ih = e.app(shift(expr.motive, 1, this.budget, depth), e.variable(0));
    const stepResult = e.app(shift(expr.motive, 2, this.budget, depth), e.succ(e.variable(1)));
    this.expect(expr.step, e.pi(e.nat(), e.pi(ih, stepResult)), context, depth);
    return e.app(copy(expr.motive, this.budget, depth), copy(expr.scrutinee, this.budget, depth));
  }

  private motive(motive: e.Expr, domain: e.Expr, context: e.Expr[], depth: number): void {
    this.budget.tick(depth);
    const type = this.normalize(this.infer(motive, context, depth + 1), depth + 1);
    if (type.kind !== "pi") this.budget.invalid("expected-function");
    this.convert(type.domain, domain, depth + 1);
    if (type.body.kind !== "sort") this.budget.invalid("expected-universe");
  }
}
