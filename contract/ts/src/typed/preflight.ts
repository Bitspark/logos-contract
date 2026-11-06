import { children, isExpr, type Expr } from "./expr.js";
import { Budget, expressionNatural, natural } from "./budget.js";
import { isDeclaration, isLimits, isPolicy, isStatement, MAX_INPUT_DEPTH, MAX_NATURAL,
  type Limits, type Policy, type Statement } from "./model.js";
import { CheckFailure, type InvalidCode } from "./outcome.js";

/** Refuse foreign host objects without enumerating their properties. */
export function validateLimits(value: unknown): asserts value is Limits {
  if (!isLimits(value) || ![value.inputNodes, value.inputDepth, value.collectionEntries,
    value.nameBytes, value.work, value.depth].every(natural)) {
    throw new CheckFailure(Object.freeze({ kind: "invalid", code: "malformed-input",
      location: Object.freeze({ phase: "preflight" }) }));
  }
}

export class Preflight {
  #nodes = 0;
  #entries = 0;
  #capacity: "universe-capacity" | "index-capacity" | undefined;

  constructor(readonly limits: Limits, readonly budget: Budget) {}

  private entries(count: number): void {
    this.budget.tick(0);
    if (count > this.limits.collectionEntries - this.#entries) {
      this.budget.incomplete("collection-entries");
    }
    this.#entries += count;
  }

  private identity(value: unknown, empty?: InvalidCode): asserts value is string {
    this.budget.tick(0);
    if (typeof value !== "string") this.budget.invalid("malformed-input");
    if (value.length === 0 && empty !== undefined) this.budget.invalid(empty);
    // UTF-16 length is a lower bound on UTF-8 bytes for well-formed text. Refuse
    // oversized strings before scanning; no unbounded encoding allocation.
    if (value.length > this.limits.nameBytes) this.budget.incomplete("name-bytes");
    let bytes = 0;
    for (let i = 0; i < value.length; i += 1) {
      this.budget.tick(0);
      const unit = value.charCodeAt(i);
      if (unit >= 0xd800 && unit <= 0xdbff) {
        if (i + 1 >= value.length) this.budget.invalid("malformed-input");
        const low = value.charCodeAt(i + 1);
        if (low < 0xdc00 || low > 0xdfff) this.budget.invalid("malformed-input");
        this.budget.tick(0);
        i += 1;
        bytes += 4;
      } else {
        if (unit >= 0xdc00 && unit <= 0xdfff) this.budget.invalid("malformed-input");
        bytes += unit < 0x80 ? 1 : unit < 0x800 ? 2 : 3;
      }
      if (bytes > this.limits.nameBytes) this.budget.incomplete("name-bytes");
    }
  }

  private expressions(roots: readonly Expr[]): void {
    type Frame = { readonly value: unknown; readonly depth: number; readonly leave: boolean };
    const stack: Frame[] = [];
    const active = new Set<object>();
    const maxDepth = Math.min(this.limits.inputDepth, MAX_INPUT_DEPTH);
    for (let i = roots.length - 1; i >= 0; i -= 1) {
      stack.push({ value: roots[i], depth: 1, leave: false });
    }
    while (stack.length > 0) {
      this.budget.tick(0);
      const frame = stack.pop()!;
      if (!isExpr(frame.value)) this.budget.invalid("malformed-input");
      const expr = frame.value;
      if (frame.leave) { active.delete(expr); continue; }
      if (active.has(expr)) this.budget.invalid("malformed-input");
      if (frame.depth > maxDepth) this.budget.incomplete("input-depth");
      if (this.#nodes >= this.limits.inputNodes) this.budget.incomplete("input-nodes");
      this.#nodes += 1;
      if (expr.kind === "sort") {
        if (!expressionNatural(expr.level)) this.budget.invalid("malformed-input");
        if (expr.level > MAX_NATURAL) this.#capacity ??= "universe-capacity";
      }
      if (expr.kind === "var") {
        if (!expressionNatural(expr.index)) this.budget.invalid("malformed-input");
        if (expr.index > MAX_NATURAL) this.#capacity ??= "index-capacity";
      }
      if (expr.kind === "const") this.identity(expr.name, "empty-constant-name");
      active.add(expr);
      stack.push({ value: expr, depth: frame.depth, leave: true });
      const operands = children(expr);
      for (let i = operands.length - 1; i >= 0; i -= 1) {
        stack.push({ value: operands[i], depth: frame.depth + 1, leave: false });
      }
    }
  }

  inspect(statement: Statement, candidate: Expr, policy: Policy): void {
    this.budget.tick(0);
    if (!isStatement(statement) || !isPolicy(policy)) this.budget.invalid("malformed-input");
    this.identity(statement.foundation);
    this.identity(policy.foundation);
    this.identity(policy.checker);
    this.entries(statement.declarations.length);
    this.entries(statement.context.length);
    this.entries(policy.dependencies.length);
    for (const dependency of policy.dependencies) this.identity(dependency, "malformed-input");
    const roots: Expr[] = [];
    for (const declaration of statement.declarations) {
      this.budget.tick(0);
      if (!isDeclaration(declaration)) this.budget.invalid("malformed-input");
      this.identity(declaration.name, "empty-constant-name");
      roots.push(declaration.type);
      if (declaration.kind === "assume") {
        this.entries(declaration.dependencies.length);
        if (declaration.dependencies.length === 0) this.budget.invalid("missing-assumptions");
        for (const dependency of declaration.dependencies) this.identity(dependency, "missing-assumptions");
      } else roots.push(declaration.value);
    }
    for (const type of statement.context) { this.budget.tick(0); roots.push(type); }
    roots.push(statement.expected, candidate);
    this.expressions(roots);
    // Capacity classifies an otherwise well-formed mathematical expression.
    // A large natural must not hide a malformed later root or sibling. Input
    // and work limits may still interrupt this bounded validation pass.
    if (this.#capacity !== undefined) this.budget.incomplete(this.#capacity);
  }
}
