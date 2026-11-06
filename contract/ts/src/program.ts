// §2 Program — clauses as data, not engine. [FIRM]
// TS sibling of contract/rs/src/program.rs.

import { Goal, Symbol } from "./literal.js";
import { Term, type Subst } from "./term.js";

/**
 * An opaque clause handle. For v1 its only contract is stable + lookup-able (§2);
 * deliberately NOT yet a canonical hash (§9).
 */
export class ClauseId {
  readonly #handle: string;

  constructor(handle: string) {
    this.#handle = handle;
    Object.freeze(this);
  }

  static of(handle: string): ClauseId {
    return new ClauseId(handle);
  }

  asStr(): string {
    return this.#handle;
  }
}

/** Polarity of a body literal (ADR 0007 / ADR 0023): positive, negated, or a count. */
export type Polarity = "pos" | "neg" | "count";

/**
 * An ARITY-SENSITIVE reference to the sealed relation a certifiable aggregate counts
 * over (ADR 0023, #581). A counted relation is matched by name AND arity — `obs/3` and
 * `obs/2` are different relations — so a wrong-arity count cannot slip past name agreement
 * alone (a mismatch is `count_attr_out_of_range`). TS sibling of Rust's `PredicateRef`.
 */
export class PredicateRef {
  readonly pred: Symbol;
  readonly arity: number;

  constructor(pred: Symbol, arity: number) {
    this.pred = pred;
    this.arity = arity;
    Object.freeze(this);
  }

  /** Structural identity: same predicate bytes AND same arity. */
  equals(other: PredicateRef): boolean {
    return this.pred.equals(other.pred) && this.arity === other.arity;
  }
}

/**
 * What a certifiable aggregate folds over a sealed relation's matching rows (ADR 0023
 * Phase 0 + the `min`/`max`/`sum` follow-on, #587). `"rows"` ⇒ `count`; `"distinct"` with a
 * 0-based `attr` ⇒ `count_distinct` of one projected column (deduped by canonical codec key,
 * EXCLUDING `null()`); `"sum"`/`"min"`/`"max"` with a 0-based `attr` ⇒ the exact INTEGER fold
 * of column `attr` over matching rows. v1 is integer-only over a sealed numeric (int) column;
 * a non-int column is `count_attr_out_of_range`. Set semantics over the proven-exact deduped
 * rows; an empty `sum` is `0`, an empty `min`/`max` is undefined (`agg_empty_undefined`). TS
 * sibling of Rust's `ProjectSpec`.
 */
export type ProjectSpec =
  | { readonly kind: "rows" }
  | { readonly kind: "distinct"; readonly attr: number }
  | { readonly kind: "sum"; readonly attr: number }
  | { readonly kind: "min"; readonly attr: number }
  | { readonly kind: "max"; readonly attr: number };

export const ProjectSpec = {
  /** `count`: count rows matching the filter (no projection). */
  rows(): ProjectSpec {
    return { kind: "rows" };
  },
  /** `count_distinct`: count distinct values of attribute `attr` over matching rows. */
  distinct(attr: number): ProjectSpec {
    return { kind: "distinct", attr };
  },
  /** `sum`: the exact integer sum of column `attr` over matching rows (empty ⇒ `0`). */
  sum(attr: number): ProjectSpec {
    return { kind: "sum", attr };
  },
  /** `min`: the exact integer minimum of column `attr` over matching rows (empty ⇒ REJECT). */
  min(attr: number): ProjectSpec {
    return { kind: "min", attr };
  },
  /** `max`: the exact integer maximum of column `attr` over matching rows (empty ⇒ REJECT). */
  max(attr: number): ProjectSpec {
    return { kind: "max", attr };
  },
  /**
   * The 0-based projected/folded column index for a column-bearing spec
   * (`distinct`/`sum`/`min`/`max`), or `undefined` for `rows`. Mirrors Rust's
   * `ProjectSpec::attr`.
   */
  attr(p: ProjectSpec): number | undefined {
    return p.kind === "rows" ? undefined : p.attr;
  },
  /** Structural identity of two projection specs (kind, and `attr` for all column kinds). */
  equals(a: ProjectSpec, b: ProjectSpec): boolean {
    if (a.kind !== b.kind) return false;
    if (a.kind === "rows" || b.kind === "rows") return true;
    return a.attr === b.attr;
  },
};

/** One `(position, term)` of a count filter: the row's argument at `pos` must equal `term`. */
export interface CountFilterEntry {
  readonly pos: number;
  readonly term: Term;
}

/**
 * A certifiable `count` / `count_distinct` body literal (ADR 0023). It is NOT a derivation
 * node: like a negated literal, it is discharged as a checked side-condition against a
 * sealed `ClosedModelCert` by `verifyCountPremise` — the searcher proposes the cardinality,
 * the gate re-derives it over a relation it has independently proven exact. TS sibling of
 * Rust's `CountLit<Term>`.
 */
export class CountLit {
  /** The sealed relation whose rows are counted — matched by name AND arity. */
  readonly pred: PredicateRef;
  /** The ground/bound-position filter (caller order preserved; treated positionally). */
  readonly filter: readonly CountFilterEntry[];
  /** `rows` ⇒ count rows; `distinct{attr}` ⇒ count-distinct of column `attr`. */
  readonly project: ProjectSpec;
  /** The result slot — the claimed cardinality `k`, as a term that binds a head var. */
  readonly count: Term;

  constructor(pred: PredicateRef, filter: readonly CountFilterEntry[], project: ProjectSpec, count: Term) {
    this.pred = pred;
    this.filter = Object.freeze(Array.from(filter));
    this.project = project;
    this.count = count;
    Object.freeze(this);
  }

  /** Apply a grounding substitution to the filter terms and the count slot. */
  substitute(subst: Subst): CountLit {
    return new CountLit(
      this.pred,
      this.filter.map((e) => ({ pos: e.pos, term: Term.substitute(e.term, subst) })),
      this.project,
      Term.substitute(this.count, subst),
    );
  }
}

/**
 * A clause body literal carrying polarity (ADR 0007 / ADR 0023) — `"pos"` for a positive
 * subgoal `p(t…)`, `"neg"` for a negated subgoal `\+ p(t…)`, `"count"` for a certifiable
 * aggregate. TS sibling of Rust's `BodyLit<Term>` enum.
 *
 * Additive (ADR 0007 / ADR 0023): today's account is exactly an all-positive body. The
 * account codec (`account.ts`) reads a positive literal byte-identically to the bare
 * `goalAsTerm(goal)` (no wrapper), so existing positive clause ids are unchanged; a negated
 * literal and a count literal each get a distinct tagged reading, so a body with no count
 * literal encodes byte-identically to the pre-amendment account. A count literal's payload
 * lives in `countLit` (`lit` is a placeholder).
 */
export class BodyLit {
  readonly polarity: Polarity;
  readonly lit: Goal;
  readonly countLit: CountLit | undefined;

  constructor(polarity: Polarity, lit: Goal, countLit?: CountLit) {
    this.polarity = polarity;
    this.lit = lit;
    this.countLit = countLit;
    Object.freeze(this);
  }

  /** Lift a goal to a positive body literal. */
  static pos(lit: Goal): BodyLit {
    return new BodyLit("pos", lit);
  }

  /** Lift a goal to a negated body literal. */
  static neg(lit: Goal): BodyLit {
    return new BodyLit("neg", lit);
  }

  /**
   * Lift a `CountLit` to a count body literal (ADR 0023).
   *
   * `lit` IS THE EMPTY GOAL, DELIBERATELY — matching go (whose `CountLitBody` leaves `Lit`
   * unset) and rust (whose `Count` variant carries no such field at all). A Count has no
   * single underlying goal; its payload is `countLit`. Do not populate this, and do not
   * "align" the cores by populating go's field instead — see logos#723.
   *
   * WHY IT IS EMPTY RATHER THAN THE COUNTED PREDICATE'S NAME, which is what this core used to
   * carry: the field was read through `inner()`, the documented-partial accessor (deleted in
   * #2733; the field itself stays public), and a consumer that reads it without branching on
   * polarity then gets a DIFFERENT ANSWER PER CORE. That is not theoretical — it is thesmos#409, and measurement found it in two more
   * consumers:
   *
   *   - thesmos: a count-bearing rule-fact was ADMITTED by this core and REJECTED by go, an
   *     authorization split on attacker-supplied bytes (measured by assay@lab, controls held).
   *   - stele read-gate: `matchLiteral` gates on the pred, so the same rule over the same store
   *     produced DIFFERENT DERIVED ROWS across cores (measured by abb0fe02@stele, stele#579).
   *   - logos-db read path: a rule-fact whose body is a count over `p`, plus a readable
   *     zero-arity fact `p`, DERIVED ITS HEAD here while go refused identical bytes — from a
   *     count literal never evaluated as a count (measured by 39ebeb21@logos-db, logos-db#153).
   *
   * The empty goal is the fail-closed choice: a consumer gating on the pred degrades to
   * "matches nothing" instead of silently matching real facts under a name the rule author
   * never wrote. Both affected consumers independently reported the same failure direction
   * (measurement, not mandate — fail-closed is right here regardless of any consumer's
   * position, per ADR 0025 D2).
   *
   * Consumers gating on positive-Horn bodies should use `isPos()` (#722) rather than reading
   * any field off a Count — and never `pred()`, which returns the COUNTED relation's name and
   * would make every core agree on ADMIT.
   */
  static count(c: CountLit): BodyLit {
    return new BodyLit("count", new Goal(Symbol.of(""), []), c);
  }

  /**
   * The underlying goal of a positive/negated body literal, or `null` for a count. It is
   * TOTAL (#728, the same additive shape as `isPos` in #722; the partial `inner()` was
   * deleted in #2733), the ts
   * face of rust's `as_inner() -> Option<&Literal>` and go's `AsInner() (Goal, bool)`. A
   * WHITELIST over the polarity (the `isPos` doctrine): a future non-pos/neg polarity
   * yields `null`, never a sentinel. Prefer this wherever the body may carry a count —
   * any clause decoded from bytes (#727 established a count round-trips the clause codec):
   * the absent case lands in the caller's control flow identically in every core, instead
   * of hitting a per-core failure mode.
   */
  asInner(): Goal | null {
    return this.polarity === "pos" || this.polarity === "neg" ? this.lit : null;
  }

  /**
   * True iff this is a plain positive body literal.
   *
   * Prefer this over `!isNeg() && !isCount()` when gating on positive-only bodies. A
   * consumer that admits by ruling out the known non-positive variants is writing a
   * BLACKLIST: every polarity added here later is admitted by default, silently, in every
   * consumer that has not been updated. `isPos` is total over the polarity — it stays
   * correct for variants that do not exist yet — so a positive-Horn gate (arche PROTOCOL
   * 3.10a) can be expressed as the whitelist it actually is. That matters most where the
   * clause is attacker-supplied, since the default must be deny.
   */
  isPos(): boolean {
    return this.polarity === "pos";
  }

  /**
   * True iff this is a negated body literal.
   *
   * ⚠ NOT a building block for a positive-Horn gate. `!isNeg() && !isCount()` is a
   * BLACKLIST: it admits every polarity added later, silently, in every consumer that has
   * not been updated. Use `isPos()`, which is total over the polarity and stays correct for
   * variants that do not exist yet — the reasoning is on `isPos`.
   */
  isNeg(): boolean {
    return this.polarity === "neg";
  }

  /**
   * True iff this is a certifiable count body literal.
   *
   * ⚠ NOT a building block for a positive-Horn gate — see `isNeg()`, and use `isPos()`.
   */
  isCount(): boolean {
    return this.polarity === "count";
  }

  /**
   * The predicate symbol this body literal is over — the underlying goal's predicate for
   * pos/neg, or the counted relation's predicate for count. Total over all variants.
   */
  pred(): Symbol {
    return this.polarity === "count" ? this.countLit!.pred.pred : this.lit.pred;
  }

  // ── first-class binding & dependency modes (research-doc 0009) ──────────────────
  // The analyzer's safety + dependency passes ask the form, per body literal, WHICH variables it
  // binds, WHICH must already be bound, and WHAT dependency edge it contributes — instead of
  // switching on the polarity and reaching for the literal's goal (a count has none). Mirrors rs/go
  // bindingTerms / requiredTerms / dependency.

  /** The argument terms whose variables this literal BINDS (range-restriction outputs): a positive
   * atom binds all its arguments; a negation binds nothing; a count binds only its result term. */
  bindingTerms(): readonly Term[] {
    switch (this.polarity) {
      case "pos":
        return this.lit.args;
      case "count":
        return [this.countLit!.count];
      case "neg":
        return [];
      default:
        // UNKNOWN polarity (#996) — fail closed: assume it binds NOTHING. Until this arm
        // existed, `default` WAS the pos case, so a polarity this core had never seen was
        // answered as the most permissive one we have.
        return [];
    }
  }

  /** The argument terms whose variables must ALREADY be positively bound for this literal to be
   * safe (range-restriction inputs): a positive atom requires nothing (it binds); a negation
   * requires all its arguments bound; a count requires its filter/group variables bound (its
   * result is exempt — that is what it binds). */
  requiredTerms(): readonly Term[] {
    switch (this.polarity) {
      case "pos":
        return [];
      case "count":
        return this.countLit!.filter.map((e) => e.term);
      case "neg":
        return this.lit.args;
      default:
        // UNKNOWN polarity (#996) — fail closed: assume it can evaluate NOTHING on its own,
        // so every argument term must already be positively bound. The permissive answer
        // ([], the old `default: // pos`) told range restriction this literal was safe
        // unconditionally.
        return this.lit.args;
    }
  }

  /** The predicate this literal reads and whether its dependency edge is NON-MONOTONE: a negation
   * or an aggregate both read a sealed, strictly-lower stratum, tagged identically. hasNegation (a
   * per-stratum closed-world obligation) stays a Neg-only query via isNeg(). */
  dependency(): { readonly pred: Symbol; readonly nonMonotone: boolean } {
    switch (this.polarity) {
      case "pos":
        return { pred: this.lit.pred, nonMonotone: false };
      case "count":
        return { pred: this.countLit!.pred.pred, nonMonotone: true };
      case "neg":
        return { pred: this.lit.pred, nonMonotone: true };
      default:
        // UNKNOWN polarity (#996) — fail closed: assume it BREAKS monotonicity and force the
        // stratum barrier. The old `default: // pos` returned false here, so an unseen
        // polarity reached the stratifier claiming to need no barrier at all.
        return { pred: this.lit.pred, nonMonotone: true };
    }
  }

  /** Apply a grounding substitution to the underlying literal, preserving polarity. */
  substitute(subst: Subst): BodyLit {
    if (this.polarity === "count") {
      return BodyLit.count(this.countLit!.substitute(subst));
    }
    return new BodyLit(this.polarity, this.lit.substitute(subst));
  }
}

/**
 * `head :- body₀, …, bodyₙ`. The head is a `Goal`; each body literal is a
 * polarity-tagged `BodyLit`. An empty `body` is a rule-fact.
 *
 * The constructor accepts either bare `Goal`s (each read as a positive body literal,
 * so every existing positive-body call site is unchanged) or explicit `BodyLit`s.
 */
export class Clause {
  readonly head: Goal;
  readonly body: readonly BodyLit[];

  constructor(head: Goal, body: readonly (Goal | BodyLit)[]) {
    this.head = head;
    this.body = Object.freeze(body.map((b) => (b instanceof BodyLit ? b : BodyLit.pos(b))));
    Object.freeze(this);
  }

  /** A rule-fact: a clause with an empty body. */
  static fact(head: Goal): Clause {
    return new Clause(head, []);
  }

  /**
   * `head :- pos₀, …, \+ neg₀, …` — a clause with explicit positive and negated body
   * literals (ADR 0007). Positive literals come first, then the negated ones, so the
   * body order is `[pos…, neg…]`. Mirrors Rust's `Clause::with_neg`.
   */
  static withNeg(head: Goal, pos: readonly Goal[], neg: readonly Goal[]): Clause {
    const body: BodyLit[] = [
      ...pos.map((g) => BodyLit.pos(g)),
      ...neg.map((g) => BodyLit.neg(g)),
    ];
    return new Clause(head, body);
  }
}

/**
 * The capabilities `check` requires of a program: look a cited clause up by id, and —
 * for the ADR-0007 closed-model cert verification (scope downward-closure, the program
 * digest, and the trusted whole-program closure self-enumeration) — enumerate the
 * COMPLETE clause set.
 *
 * `forEachClause` is OPTIONAL for backward compat: a positive (`closedWorld`-empty)
 * `check` never enumerates, so a `Program` that only implements `clause` keeps working
 * exactly as before. A program cited by a `Neg`-bearing derivation MUST implement it
 * (else the cert's whole-program obligations cannot be discharged → `cert_scope_incomplete`).
 * `MapProgram` implements it in canonical clause-id order. Mirrors Rust's
 * `Program::for_each_clause`.
 */
export interface Program {
  clause(id: ClauseId): Clause | undefined;
  /** Visit every `[id, clause]` of the COMPLETE clause set (canonical order on `MapProgram`). */
  forEachClause?(visit: (id: ClauseId, clause: Clause) => void): void;
}

/** A straightforward in-memory `Program` (a `ClauseId → Clause` map). */
export class MapProgram implements Program {
  readonly #clauses = new Map<string, Clause>();

  with(id: ClauseId | string, clause: Clause): this {
    this.insert(id, clause);
    return this;
  }

  insert(id: ClauseId | string, clause: Clause): void {
    const key = typeof id === "string" ? id : id.asStr();
    this.#clauses.set(key, clause);
  }

  clause(id: ClauseId): Clause | undefined {
    return this.#clauses.get(id.asStr());
  }

  /** The number of clauses in the program. */
  size(): number {
    return this.#clauses.size;
  }

  /** Whether the program has no clauses. */
  isEmpty(): boolean {
    return this.#clauses.size === 0;
  }

  /**
   * The `[id, clause]` pairs of the program (insertion order — the program
   * (de)serialization sorts by id, so the iteration order here is not relied upon for
   * canonical output). Used by `programToValue` (program_serde.ts).
   */
  entries(): Array<[string, Clause]> {
    return Array.from(this.#clauses.entries());
  }

  /**
   * The program's `[ClauseId, Clause]` pairs in CANONICAL ORDER — ascending by the
   * clause-id's UTF-8 bytes (lexicographic). This is the same total order the program
   * (de)serialization (`programToValue` in program_serde.ts) sorts entries by, Rust's
   * `BTreeMap<ClauseId>`-backed `MapProgram::iter` yields, and Go's `MapProgram.Iter`
   * yields — so the enumeration is DETERMINISTIC and BYTE-IDENTICAL across `{rs,go,ts}`.
   * A raw `Map` iteration would be insertion order (not canonical), so the sort is
   * load-bearing: a consumer assembling a request straight from the program gets
   * identical bytes tri-core. Clause ids are unique (map keys), so the order is total and
   * unambiguous.
   */
  iter(): Array<[ClauseId, Clause]> {
    const enc = new TextEncoder();
    const entries = Array.from(this.#clauses.entries());
    entries.sort(([a], [b]) => compareIdBytes(enc.encode(a), enc.encode(b)));
    return entries.map(([id, clause]) => [ClauseId.of(id), clause]);
  }

  /**
   * Visit every `[id, clause]` of the COMPLETE clause set in canonical clause-id order
   * (the `iter()` order). The whole-program enumeration the ADR-0007 cert verifier needs
   * for scope downward-closure, the recomputed program digest, and the trusted closure
   * self-enumeration. Deterministic + byte-identical tri-core.
   */
  forEachClause(visit: (id: ClauseId, clause: Clause) => void): void {
    for (const [id, clause] of this.iter()) {
      visit(id, clause);
    }
  }
}

/** Lexicographic byte ordering — the total order Rust's slice `Ord` / Go's `bytes.Compare` uses. */
function compareIdBytes(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i += 1) {
    const ai = a[i]!;
    const bi = b[i]!;
    if (ai !== bi) return ai < bi ? -1 : 1;
  }
  return a.length - b.length;
}
