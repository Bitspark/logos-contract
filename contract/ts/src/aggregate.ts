// ADR 0023's one aggregate fold, the TS twin of rs `logos_contract::aggregate::evaluate_aggregate`
// and go `evaluateAggregate`. `verifyCountPremise` recomputes a claimed aggregate with it, and
// (#2258 L3.3b) a closure count stage and a `count_lower` support ref evaluate the same one.

import { encode } from "@bitspark/ontos-codec";
import { equals as valueEquals, type Value } from "@bitspark/ontos-core";
import { readInt } from "@bitspark/ontos-data";

import { type RejectionCode } from "./check.js";
import { type GroundFilterEntry } from "./derivation.js";
import { type GroundLiteral } from "./literal.js";
import { type ProjectSpec } from "./program.js";

/** A folded aggregate, or the checker code that refuses it. */
export type AggregateResult = { readonly value: bigint } | { readonly err: readonly [RejectionCode, string] };

/**
 * `true` iff `v` is the canonical `null()` marker (ADR 0023 Phase 0). With ontos's
 * nullary-compound convention, `null()` is `Tuple[Atom("null")]` — the same shape a nullary
 * goal `p()` reads as. `count_distinct` EXCLUDES a projected value equal to this marker
 * (SQL-style). Recognized structurally so the ts mirror does not depend on a newer ontos
 * `null()` constructor — the same shape the rs oracle's `is_null_value` recognizes.
 */
export function isNullValue(v: Value): boolean {
  const items = (v as { items?: () => readonly Value[] }).items?.();
  if (items === undefined || items.length !== 1) return false;
  const only = items[0]!;
  const bytes = (only as { bytes?: () => Uint8Array }).bytes?.();
  if (bytes === undefined || bytes.length !== 4) return false;
  return bytes[0] === 0x6e && bytes[1] === 0x75 && bytes[2] === 0x6c && bytes[3] === 0x6c; // "null"
}

/**
 * Fold the rows that match `filter` under `project`, in ONE linear scan:
 *
 *  - `rows`: the number of matching rows;
 *  - `distinct{attr}`: the number of distinct values of column `attr`, by canonical encoding,
 *    EXCLUDING `null()`;
 *  - `sum{attr}`: the integer sum of column `attr`; empty sums to `0`;
 *  - `min`/`max{attr}`: the integer extreme of column `attr`; empty is UNDEFINED.
 *
 * `rows` are read as a SET (a sealed table is sorted and deduplicated). A filter position or a
 * projection column outside a row's arity simply does not match; checking both against the
 * relation's arity is the caller's. The errors are the checker's own codes:
 * `count_attr_out_of_range` for a non-int column under sum/min/max (v1 folds are integer-only),
 * `agg_empty_undefined` for min/max over no matching row.
 */
export function evaluateAggregate(
  rows: readonly GroundLiteral[],
  filter: readonly GroundFilterEntry[],
  project: ProjectSpec,
): AggregateResult {
  const matches = (row: GroundLiteral): boolean =>
    filter.every((e) => e.pos < row.args.length && valueEquals(row.args[e.pos]!, e.value));
  switch (project.kind) {
    case "rows":
      return { value: BigInt(rows.filter(matches).length) };
    case "distinct": {
      const seen = new Set<string>();
      for (const row of rows) {
        if (!matches(row) || project.attr >= row.args.length) continue;
        const projected = row.args[project.attr]!;
        if (isNullValue(projected)) continue; // count_distinct EXCLUDES null() (ADR 0023 Phase 0).
        seen.add(hex(encode(projected)));
      }
      return { value: BigInt(seen.size) };
    }
    case "sum":
    case "min":
    case "max": {
      let sum = 0n;
      let extremum: bigint | undefined; // min/max; undefined until the first matching row
      for (const row of rows) {
        if (!matches(row) || project.attr >= row.args.length) continue;
        // v1 sum/min/max are integer-only: a non-int column value (including null()) is
        // count_attr_out_of_range, as rs's fold, which does not special-case null.
        let v: bigint;
        try {
          v = readInt(row.args[project.attr]!);
        } catch {
          return {
            err: [
              "count_attr_out_of_range",
              `aggregate column ${project.attr} is not a sealed numeric (int) value — v1 sum/min/max are integer-only`,
            ],
          };
        }
        if (project.kind === "sum") sum += v;
        else if (extremum === undefined || (project.kind === "min" ? v < extremum : v > extremum)) extremum = v;
      }
      if (project.kind === "sum") return { value: sum }; // empty sum ⇒ 0
      if (extremum === undefined) return { err: ["agg_empty_undefined", `${project.kind} of an empty set is undefined`] };
      return { value: extremum };
    }
  }
}

function hex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}
