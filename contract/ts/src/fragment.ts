// #2759 (seat:caa's design gate; research 0028 row A15): the CONSTRUCTOR-ACYCLIC fragment's
// cycle test, in the checker's tier so there is ONE computation. `check` runs it over a
// certificate's sealed scope (cert_check.ts's constructor-acyclic gate), and the kernel's resolver
// runs it over the certifying producer's seal plan (kernel/ts runtime/sealed_compound.ts) to derive
// the function-symbol level at admission. The ts twin of rs `logos_contract::fragment::ScopeGraph`.
//
// A CONSTRUCTING rule's head carries an OPEN compound (`Term.isOpenCompound`): it wraps a variable
// in a function symbol. It lies on a dependency cycle when its head predicate is reachable from one
// of its own body predicates through the scope's clauses. What acyclicity discharges is FINITENESS
// of the relevant model (row A9), nothing else: matching completeness, domain coverage, support,
// stratification, aggregates and the budget are each still checked by their own gate.

import type { Goal, Symbol } from "./literal.js";
import type { Clause, CountLit } from "./program.js";
import { Term, type VarId } from "./term.js";

/**
 * The dependency graph of a scope, built one clause at a time: an edge from each in-scope clause's
 * head to every body literal predicate (positive or negated) that is in scope. A count reads a
 * relation a strictly lower certificate seals, never one of its own scope, so it adds no edge.
 * Keyed by name bytes, as a certificate's scope is.
 */
export class ScopeGraph {
  readonly #edges = new Map<string, Set<string>>();

  /** Add one clause of the program. A clause whose head is out of scope adds nothing. */
  add(clause: Clause, inScope: (pred: Symbol) => boolean): void {
    if (!inScope(clause.head.pred)) return;
    const head = hexOf(clause.head.pred);
    let out = this.#edges.get(head);
    if (out === undefined) {
      out = new Set<string>();
      this.#edges.set(head, out);
    }
    for (const bl of clause.body) {
      const goal = bl.asInner();
      if (goal !== null && inScope(goal.pred)) out.add(hexOf(goal.pred));
    }
  }

  /** Whether `clause` CONSTRUCTS: its head carries an open compound. */
  static constructs(clause: Clause): boolean {
    return clause.head.args.some(Term.isOpenCompound);
  }

  /**
   * The first body predicate of `clause`, in body order, from which the clause's own head
   * predicate is reachable in this graph (itself included): the clause lies on a dependency cycle
   * through it. `undefined` when the clause is on no cycle.
   */
  cycleThrough(clause: Clause): Symbol | undefined {
    const head = hexOf(clause.head.pred);
    for (const bl of clause.body) {
      const goal = bl.asInner();
      if (goal !== null && this.#reaches(hexOf(goal.pred), head)) return goal.pred;
    }
    return undefined;
  }

  /** Whether `to` is reachable from `from` along the edges, `from` itself included. */
  #reaches(from: string, to: string): boolean {
    const seen = new Set<string>();
    const work = [from];
    while (work.length > 0) {
      const pred = work.pop()!;
      if (pred === to) return true;
      if (seen.has(pred)) continue;
      seen.add(pred);
      for (const next of this.#edges.get(pred) ?? []) work.push(next);
    }
    return false;
  }
}

/** Lowercase hex of a predicate name's bytes: the graph's key. */
function hexOf(pred: Symbol): string {
  let out = "";
  for (const b of pred.bytes()) out += b.toString(16).padStart(2, "0");
  return out;
}

/**
 * The context a sealed clause is classified in (#3067, research 0028 row A15; seat:caa's ruling
 * Q2): the relations its certificate seals, and the relations it reads from a strictly lower
 * certificate. ONE type: `check` builds it from a certificate and the lower certificates it
 * resolves. Keyed by name bytes, as a certificate's scope is. The ts twin of rs
 * `logos_contract::fragment::SealContext`.
 */
export class SealContext {
  readonly #seals: Set<string>;
  readonly #readsLower: Set<string>;

  constructor(seals: Iterable<Symbol>, readsLower: Iterable<Symbol>) {
    this.#seals = new Set(Array.from(seals, hexOf));
    this.#readsLower = new Set(Array.from(readsLower, hexOf));
  }

  /** Whether the clause's own certificate seals `pred`. */
  seals(pred: Symbol): boolean {
    return this.#seals.has(hexOf(pred));
  }

  /** Whether the clause reads `pred` from a strictly lower certificate. */
  readsLower(pred: Symbol): boolean {
    return this.#readsLower.has(hexOf(pred));
  }
}

/**
 * Why a sealed clause is outside the certifiable fragment: the FIRST gate it fails, in the one order
 * `classifySealedClause` declares, with that gate's subject. The ts twin of rs
 * `logos_contract::fragment::Outside`; `kind` is the gate's name in `vectors/fragment.json`.
 */
export type Outside =
  | { readonly kind: "count_not_lower"; readonly pred: Symbol; readonly sameScope: boolean }
  | { readonly kind: "count_open_compound"; readonly pred: Symbol }
  | { readonly kind: "constructor_cycle"; readonly through: Symbol }
  | { readonly kind: "unserved"; readonly pred: Symbol }
  | { readonly kind: "intra_scope_negation"; readonly pred: Symbol }
  | { readonly kind: "unbound_count_filter"; readonly pred: Symbol; readonly var: VarId }
  | { readonly kind: "unbound_variable"; readonly var: VarId };

/** Whether a count's filter or result carries an OPEN compound (the function-free count gate, #2294). */
export function countHasOpenCompound(count: CountLit): boolean {
  return Term.isOpenCompound(count.count) || count.filter.some((e) => Term.isOpenCompound(e.term));
}

/**
 * THE classification of one sealed clause (#3067; seat:caa's rulings Q1 to Q3): `undefined` inside
 * the certifiable fragment, else the first gate it fails. `graph` is the scope's dependency graph
 * (built over the program with the context's sealed relations as its scope).
 *
 * The theory is read in TWO directions (seat:caa's ruling on #3067 increment 2, Q1): `servedBy` says
 * which relations a theory decides live, for the read gate, and `bindsNothing` which relations bind no
 * variable, for range restriction. check and a producer pass the bound theory's ownership for both;
 * a caller that sees only part of the theory passes what it knows for each reading (the kernel's
 * resolver reads the theories the kernel ships, and the certifying provider decides, #3211).
 *
 * The gates run in ONE order, the checker's, declared here and never restated by a caller:
 *
 * 1. the count gate, per count literal in body order: it reads a strictly lower certificate, and
 *    its terms carry no open compound;
 * 2. the constructor-cycle gate (`ScopeGraph`);
 * 3. the read gate, per body literal in body order: the relation is sealed, served by a theory
 *    (`servedBy`) or read lower, and a `\+` never reads this certificate's own table;
 * 4. range restriction: every count filter variable, count by count in body order, then every
 *    variable of the clause, is bound by a positive literal over a relation the certificate seals
 *    or reads lower and that binds (not `bindsNothing`); a count then binds its result. Where
 *    several variables are unbound it names the first in name order.
 *
 * The ts twin of rs `logos_contract::fragment::classify_sealed_clause`, whose comments carry each
 * gate's reason.
 */
export function classifySealedClause(
  clause: Clause,
  ctx: SealContext,
  graph: ScopeGraph,
  servedBy: (pred: Symbol) => boolean,
  bindsNothing: (pred: Symbol) => boolean,
): Outside | undefined {
  for (const bl of clause.body) {
    const count = bl.asInner() === null ? bl.countLit : undefined;
    if (count === undefined) continue;
    const pred = count.pred.pred;
    if (!ctx.readsLower(pred)) return { kind: "count_not_lower", pred, sameScope: ctx.seals(pred) };
    if (countHasOpenCompound(count)) return { kind: "count_open_compound", pred };
  }
  if (ScopeGraph.constructs(clause)) {
    const through = graph.cycleThrough(clause);
    if (through !== undefined) return { kind: "constructor_cycle", through };
  }
  for (const bl of clause.body) {
    const goal = bl.asInner();
    if (goal === null) continue;
    const sealed = ctx.seals(goal.pred);
    if (!sealed && !servedBy(goal.pred) && !ctx.readsLower(goal.pred)) return { kind: "unserved", pred: goal.pred };
    if (bl.isNeg() && sealed) return { kind: "intra_scope_negation", pred: goal.pred };
  }
  const bound = new Map<string, VarId>();
  for (const bl of clause.body) {
    const goal = bl.asInner();
    if (bl.isNeg() || goal === null) continue;
    if ((ctx.seals(goal.pred) || ctx.readsLower(goal.pred)) && !bindsNothing(goal.pred)) goalVars(goal, bound);
  }
  for (const bl of clause.body) {
    const count = bl.asInner() === null ? bl.countLit : undefined;
    if (count === undefined) continue;
    const filter = new Map<string, VarId>();
    for (const e of count.filter) termVars(e.term, filter);
    const unbound = firstUnbound(filter, bound);
    if (unbound !== undefined) return { kind: "unbound_count_filter", pred: count.pred.pred, var: unbound };
  }
  for (const bl of clause.body) {
    const count = bl.asInner() === null ? bl.countLit : undefined;
    if (count !== undefined) termVars(count.count, bound);
  }
  const all = new Map<string, VarId>();
  goalVars(clause.head, all);
  for (const bl of clause.body) {
    const goal = bl.asInner();
    if (goal !== null) {
      goalVars(goal, all);
    } else if (bl.countLit !== undefined) {
      for (const e of bl.countLit.filter) termVars(e.term, all);
      termVars(bl.countLit.count, all);
    }
  }
  const unbound = firstUnbound(all, bound);
  return unbound === undefined ? undefined : { kind: "unbound_variable", var: unbound };
}

/** The first variable of `vars`, in name order, that `bound` does not hold. */
function firstUnbound(vars: ReadonlyMap<string, VarId>, bound: ReadonlyMap<string, VarId>): VarId | undefined {
  for (const name of Array.from(vars.keys()).sort()) {
    if (!bound.has(name)) return vars.get(name);
  }
  return undefined;
}

function goalVars(goal: Goal, out: Map<string, VarId>): void {
  for (const t of goal.args) termVars(t, out);
}

function termVars(term: Term, out: Map<string, VarId>): void {
  const work: Term[] = [term];
  while (work.length > 0) {
    const t = work.pop()!;
    if (t.kind === "var") out.set(t.id().asStr(), t.id());
    else if (t.kind === "tuple") work.push(...t.children());
  }
}
