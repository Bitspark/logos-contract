/** Syntax of dependent-fragment-1. Constructors do not establish typing. */
declare const expressionBrand: unique symbol;

type Form =
  | { readonly kind: "sort"; readonly level: number }
  | { readonly kind: "var"; readonly index: number }
  | { readonly kind: "const"; readonly name: string }
  | { readonly kind: "pi" | "lam" | "sigma"; readonly domain: Expr; readonly body: Expr }
  | { readonly kind: "app"; readonly fun: Expr; readonly arg: Expr }
  | { readonly kind: "pair"; readonly sigma: Expr; readonly first: Expr; readonly second: Expr }
  | { readonly kind: "fst" | "snd"; readonly pair: Expr }
  | { readonly kind: "nat" | "zero" | "bool" | "false" | "true" }
  | { readonly kind: "succ"; readonly value: Expr }
  | { readonly kind: "nat-elim"; readonly motive: Expr; readonly zero: Expr;
      readonly step: Expr; readonly scrutinee: Expr }
  | { readonly kind: "bool-elim"; readonly motive: Expr; readonly onFalse: Expr;
      readonly onTrue: Expr; readonly scrutinee: Expr }
  | { readonly kind: "id"; readonly type: Expr; readonly lhs: Expr; readonly rhs: Expr }
  | { readonly kind: "refl"; readonly type: Expr; readonly value: Expr }
  | { readonly kind: "transport"; readonly type: Expr; readonly from: Expr;
      readonly to: Expr; readonly equality: Expr; readonly motive: Expr; readonly value: Expr };

/** Immutable syntax made by the constructors below, not an arbitrary host object. */
export type Expr = Form & { readonly [expressionBrand]: true };
const expressions = new WeakSet<object>();

function make(form: Form): Expr {
  const value = Object.freeze(form) as Expr;
  expressions.add(value);
  return value;
}

/** Internal shape test does not read properties or execute host getters. */
export function isExpr(value: unknown): value is Expr {
  return typeof value === "object" && value !== null && expressions.has(value);
}

export const sort = (level: number): Expr => make({ kind: "sort", level });
export const variable = (index: number): Expr => make({ kind: "var", index });
export const constant = (name: string): Expr => make({ kind: "const", name });
export const pi = (domain: Expr, body: Expr): Expr => make({ kind: "pi", domain, body });
export const lam = (domain: Expr, body: Expr): Expr => make({ kind: "lam", domain, body });
export const app = (fun: Expr, arg: Expr): Expr => make({ kind: "app", fun, arg });
export const sigma = (domain: Expr, body: Expr): Expr => make({ kind: "sigma", domain, body });
export const pair = (sigma: Expr, first: Expr, second: Expr): Expr =>
  make({ kind: "pair", sigma, first, second });
export const fst = (pair: Expr): Expr => make({ kind: "fst", pair });
export const snd = (pair: Expr): Expr => make({ kind: "snd", pair });
export const nat = (): Expr => make({ kind: "nat" });
export const zero = (): Expr => make({ kind: "zero" });
export const succ = (value: Expr): Expr => make({ kind: "succ", value });
export const natElim = (motive: Expr, zero: Expr, step: Expr, scrutinee: Expr): Expr =>
  make({ kind: "nat-elim", motive, zero, step, scrutinee });
export const bool = (): Expr => make({ kind: "bool" });
export const falseValue = (): Expr => make({ kind: "false" });
export const trueValue = (): Expr => make({ kind: "true" });
export const boolElim = (motive: Expr, onFalse: Expr, onTrue: Expr, scrutinee: Expr): Expr =>
  make({ kind: "bool-elim", motive, onFalse, onTrue, scrutinee });
export const id = (type: Expr, lhs: Expr, rhs: Expr): Expr => make({ kind: "id", type, lhs, rhs });
export const refl = (type: Expr, value: Expr): Expr => make({ kind: "refl", type, value });
export const transport = (type: Expr, from: Expr, to: Expr, equality: Expr,
  motive: Expr, value: Expr): Expr => make({ kind: "transport", type, from, to, equality, motive, value });

/** Children in the exact mathematical constructor order. Input must be admitted syntax. */
export function children(expr: Expr): readonly Expr[] {
  switch (expr.kind) {
    case "sort": case "var": case "const": case "nat": case "zero":
    case "bool": case "false": case "true": return [];
    case "pi": case "lam": case "sigma": return [expr.domain, expr.body];
    case "app": return [expr.fun, expr.arg];
    case "pair": return [expr.sigma, expr.first, expr.second];
    case "fst": case "snd": return [expr.pair];
    case "succ": return [expr.value];
    case "nat-elim": return [expr.motive, expr.zero, expr.step, expr.scrutinee];
    case "bool-elim": return [expr.motive, expr.onFalse, expr.onTrue, expr.scrutinee];
    case "id": return [expr.type, expr.lhs, expr.rhs];
    case "refl": return [expr.type, expr.value];
    case "transport": return [expr.type, expr.from, expr.to, expr.equality, expr.motive, expr.value];
  }
}
