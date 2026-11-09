// R3's generated domain and its raise value for contract/ts's replays (#2733; seat:caa's ruling (B) on
// 3b-ii). kernel/ts/test_helpers/r3_domain.ts's twin: the two packages compile apart, so each carries
// its reader. The domain's computation is rs's replay_manifest::relational_cases, drift-guarded there;
// ts reads the list and never re-derives it.
import assert from "node:assert/strict";
import { CHECK_BUDGETS, captureCheckLimits, proofBudgetError, type CheckLimits } from "../../src/index.js";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

function vectorsFile(name: string): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const file = path.join(dir, "vectors", name);
    if (fs.existsSync(file)) return file;
    const up = path.dirname(dir);
    if (up === dir) throw new Error(`r3_domain: no vectors/${name} above ${dir}`);
    dir = up;
  }
}

/**
 * `file`'s R3 case ids, joined both ways against `cases`, the ids the replay has (seat:caa's condition
 * 3): an id no case carries, or that two cases carry, fails. The count is printed.
 */
export function r3Domain(file: string, cases: readonly string[]): Set<string> {
  const doc = JSON.parse(fs.readFileSync(vectorsFile("r3_domain.json"), "utf8")) as { files: { file: string; cases: string[] }[] };
  // One record per runs file, its name a value (#2733 3b-ii): exactly one must name `file`.
  const records = doc.files.filter((r) => r.file === file);
  assert.equal(records.length, 1, `vectors/r3_domain.json holds ${records.length} records for ${file}, not exactly one`);
  const ids = records[0]!.cases;
  for (const id of ids) {
    const n = cases.filter((c) => c === id).length;
    assert.equal(n, 1, `${file}'s domain id ${JSON.stringify(id)} resolves to ${n} of the replay's cases, not exactly one`);
  }
  console.error(`r3 ${file}: ${ids.length} domain case(s) of ${cases.length}`);
  return new Set(ids);
}

/** The value R3 raises an allowance to, from the declared carrier table (vectors/allowances.json). */
export function r3Raised(): number {
  const table = JSON.parse(fs.readFileSync(vectorsFile("allowances.json"), "utf8")) as { raised: number };
  assert.ok(table.raised > 0, "vectors/allowances.json has no raised value");
  return table.raised;
}

/**
 * R3's variants at the checker (#2733; seat:caa's C2 on 3b): each budget raised to at least `to`
 * alone, labelled by its name, then every budget together (`every`). A budget already at or above `to`
 * is left alone, and a variant equal to `limits` is dropped, so a raise is never a no-op and never a
 * lowering.
 */
export function eachBudgetRaised(limits: CheckLimits, to: number): { name: string; limits: CheckLimits }[] {
  const error = proofBudgetError("raised", to);
  if (error !== undefined) throw error;
  const captured = captureCheckLimits(limits);
  if (!captured.ok) throw captured.error;
  limits = captured.value;
  const out: { name: string; limits: CheckLimits }[] = [];
  let every: CheckLimits = limits;
  for (const [name, key] of CHECK_BUDGETS) {
    if (limits[key] >= to) continue;
    out.push({ name, limits: { ...limits, [key]: to } });
    every = { ...every, [key]: to };
  }
  if (out.length > 1) out.push({ name: "every", limits: every });
  return out;
}
