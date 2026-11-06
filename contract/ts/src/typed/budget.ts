import { MAX_DEPTH, MAX_NATURAL, type Limits } from "./model.js";
import { CheckFailure, type IncompleteCause, type InvalidCode, type Location,
  type Phase, type UnsupportedCause } from "./outcome.js";

/** The same object meters preflight, admission, conversion and owned result construction. */
export class Budget {
  #spent = 0;
  #location: Location = Object.freeze({ phase: "preflight" });
  readonly #work: number;
  readonly #depth: number;

  constructor(limits: Limits) {
    this.#work = limits.work;
    this.#depth = Math.min(limits.depth, MAX_DEPTH);
  }

  get spent(): number { return this.#spent; }

  locate(phase: Phase, index?: number): void {
    this.#location = index === undefined ? Object.freeze({ phase }) : Object.freeze({ phase, index });
  }

  tick(depth: number): void {
    if (depth > this.#depth) this.incomplete("depth");
    this.charge(1);
  }

  charge(units: number): void {
    if (units > this.#work - this.#spent) this.incomplete("work");
    this.#spent += units;
  }

  invalid(code: InvalidCode): never {
    throw new CheckFailure(Object.freeze({ kind: "invalid", code, location: this.#location }));
  }

  incomplete(code: IncompleteCause): never {
    throw new CheckFailure(Object.freeze({ kind: "incomplete", code, location: this.#location }));
  }

  unsupported(code: UnsupportedCause): never {
    throw new CheckFailure(Object.freeze({ kind: "unsupported", code, location: this.#location }));
  }
}

export function natural(value: unknown): value is number {
  return typeof value === "number" && Number.isInteger(value) && value >= 0
    && value <= MAX_NATURAL;
}

export function expressionNatural(value: unknown): value is number {
  return typeof value === "number" && Number.isSafeInteger(value) && value >= 0;
}

export function successor(value: number, budget: Budget, cause: "index-capacity" | "universe-capacity"): number {
  if (value === MAX_NATURAL) budget.incomplete(cause);
  return value + 1;
}

export function sorted(values: ReadonlySet<string>, budget: Budget): readonly string[] {
  const copy: string[] = [];
  for (const value of values) { budget.tick(0); copy.push(value); }
  return copy.sort((a, b) => {
    budget.tick(0);
    budget.charge(a.length + b.length);
    // For valid Unicode, scalar order is UTF-8 byte order. JavaScript's default
    // UTF-16 ordering differs when an astral scalar meets a BMP scalar.
    let ai = 0;
    let bi = 0;
    while (ai < a.length && bi < b.length) {
      const ac = a.codePointAt(ai)!;
      const bc = b.codePointAt(bi)!;
      if (ac !== bc) return ac < bc ? -1 : 1;
      ai += ac > 0xffff ? 2 : 1;
      bi += bc > 0xffff ? 2 : 1;
    }
    return ai < a.length ? 1 : bi < b.length ? -1 : 0;
  });
}
