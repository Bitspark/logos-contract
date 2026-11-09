import type { Expr } from "./expr.js";

export const FOUNDATION = "logos/dependent-fragment-1/edition-1";
export const CHECKER = "logos/typed-check-only-v1/typescript";
export const MAX_INPUT_DEPTH = 128;
export const MAX_DEPTH = 512;
export const MAX_NATURAL = 0xffff_ffff;

declare const declarationBrand: unique symbol;
type DeclarationForm =
  | { readonly kind: "assume"; readonly name: string; readonly type: Expr;
      readonly dependencies: readonly string[] }
  | { readonly kind: "define"; readonly name: string; readonly type: Expr; readonly value: Expr };
export type Declaration = DeclarationForm & { readonly [declarationBrand]: true };
const declarations = new WeakSet<object>();

/** These factories store caller-owned syntax; they do not admit a declaration. */
export function assume(name: string, type: Expr, dependencies: readonly string[]): Declaration {
  const value = Object.freeze({ kind: "assume", name, type,
    dependencies: Object.freeze([...dependencies]) }) as Declaration;
  declarations.add(value);
  return value;
}

export function define(name: string, type: Expr, value: Expr): Declaration {
  const declaration = Object.freeze({ kind: "define", name, type, value }) as Declaration;
  declarations.add(declaration);
  return declaration;
}

export function isDeclaration(value: unknown): value is Declaration {
  return typeof value === "object" && value !== null && declarations.has(value);
}

export interface StatementInput {
  readonly foundation: string;
  readonly declarations: readonly Declaration[];
  readonly context: readonly Expr[];
  readonly expected: Expr;
}
declare const statementBrand: unique symbol;
export type Statement = StatementInput & { readonly [statementBrand]: true };
const statements = new WeakSet<object>();

/** Syntax storage only. Checking, policy admission and budget accounting start at check(). */
export function statement(input: StatementInput): Statement {
  const value = Object.freeze({ foundation: input.foundation,
    declarations: Object.freeze([...input.declarations]),
    context: Object.freeze([...input.context]), expected: input.expected }) as Statement;
  statements.add(value);
  return value;
}

export function isStatement(value: unknown): value is Statement {
  return typeof value === "object" && value !== null && statements.has(value);
}

export interface PolicyInput {
  readonly foundation: string;
  readonly checker: string;
  readonly dependencies: readonly string[];
}
declare const policyBrand: unique symbol;
export type Policy = PolicyInput & { readonly [policyBrand]: true };
const policies = new WeakSet<object>();

/** Explicit receiver permission. This does not authenticate any assumed fact. */
export function policy(input: PolicyInput): Policy {
  const value = Object.freeze({ foundation: input.foundation, checker: input.checker,
    dependencies: Object.freeze([...input.dependencies]) }) as Policy;
  policies.add(value);
  return value;
}

export function isPolicy(value: unknown): value is Policy {
  return typeof value === "object" && value !== null && policies.has(value);
}

export interface LimitsInput {
  readonly inputNodes: number;
  readonly inputDepth: number;
  readonly collectionEntries: number;
  readonly nameBytes: number;
  readonly work: number;
  readonly depth: number;
}
declare const limitsBrand: unique symbol;
export type Limits = LimitsInput & { readonly [limitsBrand]: true };
const limitValues = new WeakSet<object>();

/** Stores numeric limits. check() rejects non-u32 fields before using them. */
export function limits(input: LimitsInput): Limits {
  const value = Object.freeze({ inputNodes: input.inputNodes, inputDepth: input.inputDepth,
    collectionEntries: input.collectionEntries, nameBytes: input.nameBytes,
    work: input.work, depth: input.depth }) as Limits;
  limitValues.add(value);
  return value;
}

export function defaultLimits(): Limits {
  return limits({ inputNodes: 100_000, inputDepth: MAX_INPUT_DEPTH, collectionEntries: 4_096,
    nameBytes: 256, work: 1_000_000, depth: MAX_DEPTH });
}

export function isLimits(value: unknown): value is Limits {
  return typeof value === "object" && value !== null && limitValues.has(value);
}
