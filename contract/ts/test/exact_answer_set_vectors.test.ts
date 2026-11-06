/**
 * TS replay of vectors/exact_answer_set.json (#3022, research 0028 rows 1, 3, 4, 5 and 6): G4
 * compares the emitted answers with the sealed rows STRUCTURALLY. #3023 (research 0028 A16): G4 is
 * `checkAnswerSet`, so the replay runs it here, through the contract entry point, and asserts its
 * structured result: the kind of mismatch, and the literal the normative precedence names. Replayed
 * identically by rs (contract/rs/tests/exact_answer_set_vectors.rs) and go
 * (contract/go/exact_answer_set_vectors_test.go).
 *
 * Denominator first: the file must carry exactly the named cases, so a case added to the file and
 * not replayed, or dropped from it, reds here rather than silently thinning the replay.
 */
import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { type AnswerSetMismatch, checkAnswerSet, Goal, GroundLiteral, Symbol, Term } from "../src/index.js";

interface VTerm {
  readonly var?: string;
  readonly atom_str?: string;
  readonly tuple?: readonly VTerm[];
}
interface VLiteral {
  readonly pred: string;
  readonly args: readonly VTerm[];
}
interface VCase {
  readonly name: string;
  readonly goal: VLiteral;
  readonly sealed: readonly VLiteral[];
  readonly emitted: readonly VLiteral[];
  readonly outcome:
    | "accept"
    | { readonly reject: string; readonly mismatch: { readonly extra?: VLiteral; readonly missing?: VLiteral } };
}

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "exact_answer_set.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/exact_answer_set.json");
    dir = parent;
  }
}

const VECTOR = JSON.parse(
  fs.readFileSync(path.join(repoRoot(), "vectors", "exact_answer_set.json"), "utf8"),
) as { readonly cases: readonly VCase[] };

const CASE_NAMES = [
  "control_the_sealed_set_emitted_accepts",
  "row1_one_spelling_emitted_of_two_sealed_rows_is_refused",
  "row1_both_sealed_rows_emitted_accepts",
  "row3_a_flat_ground_goal_has_no_cons_instance_accepts_the_empty_set",
  "row3_the_cons_row_emitted_for_a_flat_ground_goal_is_refused",
  "row4_an_open_cons_pattern_matches_its_cons_row_accepts",
  "row5_an_open_flat_pattern_has_no_cons_instance_accepts_the_empty_set",
  "row6_a_repeated_variable_does_not_join_two_spellings_accepts_the_empty_set",
  "precedence_an_extra_is_reported_before_a_missing_row",
  "precedence_the_first_extra_is_in_claim_order",
  "precedence_the_first_missing_row_is_in_key_order",
];

function term(j: VTerm): Term {
  if (typeof j.var === "string") return Term.var(j.var);
  if (typeof j.atom_str === "string") return Term.atom(new TextEncoder().encode(j.atom_str));
  if (Array.isArray(j.tuple)) return Term.tuple(j.tuple.map(term));
  throw new Error(`term must be atom_str/var/tuple: ${JSON.stringify(j)}`);
}

function goal(j: VLiteral): Goal {
  return new Goal(Symbol.of(j.pred), j.args.map(term));
}

function ground(j: VLiteral): GroundLiteral {
  const g = goal(j).asGround();
  if (g === undefined) throw new Error(`a sealed row or an emitted claim is ground: ${JSON.stringify(j)}`);
  return g;
}

test("every exact_answer_set case replays through checkAnswerSet (#3022, #3023)", () => {
  assert.deepEqual(
    VECTOR.cases.map((c) => c.name),
    CASE_NAMES,
    "the file's cases are exactly the replayed ones",
  );
  for (const c of VECTOR.cases) {
    const got = checkAnswerSet(goal(c.goal), c.sealed.map(ground), c.emitted.map(ground));
    if (c.outcome === "accept") {
      assert.equal(got, undefined, `${c.name}: expected accept, got ${JSON.stringify(got)}`);
      continue;
    }
    assert.equal(c.outcome.reject, "completeness_set_mismatch", `${c.name}: the only G4 refusal`);
    const { extra, missing } = c.outcome.mismatch;
    let want: AnswerSetMismatch;
    if (extra !== undefined && missing === undefined) want = { kind: "extra", literal: ground(extra) };
    else if (missing !== undefined && extra === undefined) want = { kind: "missing", literal: ground(missing) };
    else throw new Error(`${c.name}: a mismatch names exactly one of extra or missing`);
    assert.ok(got !== undefined, `${c.name}: expected a ${want.kind} mismatch, got accept`);
    assert.equal(got.kind, want.kind, `${c.name}: the mismatch's kind`);
    assert.ok(got.literal.equals(want.literal), `${c.name}: the named literal`);
  }
});
