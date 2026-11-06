/*
 * TS replay of vectors/decider_completion.json's declarations (#3142, research 0031 row 13): what
 * each standard decider declares about completing, per theory as seat:caa ruled, a compound
 * routing to the owning member, and a theory that declares nothing reading undeclared (fail
 * closed). The rs (contract/rs/tests/decider_completion_3142.rs) and go
 * (contract/go/decider_completion_3142_test.go) bindings replay the same rows.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
  completionOf,
  ComponentIdentity,
  DecisionCompletion,
  type GroundLiteral,
  newArithmeticTheory,
  newListTheory,
  newStandardTheory,
  newTermTheory,
  newTextTheory,
  Symbol,
  type Theory,
  TheoryOutcome,
} from "../src/index.js";

interface CompletionRow {
  readonly name: string;
  readonly theory: string;
  readonly pred: string;
  readonly completion: string;
  readonly decider?: string;
}

function loadVector(): { readonly declarations: readonly CompletionRow[] } {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "decider_completion.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8"));
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/decider_completion.json above ${dir}`);
    dir = parent;
  }
}

/** A consumer theory that owns `p` and declares nothing: no completion, no identity. */
// test-double: consumer(a domain theory that declares nothing about completing)
class DeclaresNothing implements Theory {
  owns(pred: Symbol): boolean {
    return pred.equals(Symbol.of("p"));
  }
  decide(_atom: GroundLiteral): TheoryOutcome {
    return TheoryOutcome.Holds;
  }
}

/**
 * A consumer theory that owns `q` and declares that a decision may stop and still answer `Fails`:
 * the population the guard still refuses (host builtins until #3506, v1-only deciders). No standard
 * theory declares it after #3313, so the replay carries its own to exercise the kind.
 */
// test-double: consumer(a domain theory whose stops still surface as Fails)
class StopsUntyped implements Theory {
  owns(pred: Symbol): boolean {
    return pred.equals(Symbol.of("q"));
  }
  decide(_atom: GroundLiteral): TheoryOutcome {
    return TheoryOutcome.Holds;
  }
  completion(_pred: Symbol): DecisionCompletion {
    const utf8 = new TextEncoder();
    return DecisionCompletion.mayNotComplete(
      ComponentIdentity.of(utf8.encode("demo/stops-untyped-theory"), utf8.encode("1"), new Uint8Array(32)),
      "a stop surfaces as Fails",
    );
  }
}

function theory(name: string): Theory {
  switch (name) {
    case "arithmetic":
      return newArithmeticTheory();
    case "text":
      return newTextTheory();
    case "term":
      return newTermTheory();
    case "list":
      return newListTheory();
    case "standard":
      return newStandardTheory();
    case "undeclared":
      return new DeclaresNothing();
    case "stops_untyped":
      return new StopsUntyped();
    default:
      throw new Error(`unknown theory ${name}`);
  }
}

test("every core declares the same completion (#3142)", () => {
  const rows = loadVector().declarations;
  assert.ok(rows.length > 0, "the declarations section is empty");
  const kinds = new Set<string>();
  const utf8 = new TextDecoder();
  for (const row of rows) {
    const got = completionOf(theory(row.theory), Symbol.of(row.pred));
    assert.equal(got.kind, row.completion, `${row.name}: the declaration`);
    assert.equal(DecisionCompletion.stopsAreTyped(got), row.completion === "stops_are_typed", `${row.name}: stopsAreTyped()`);
    const decider = got.kind === "stops_are_typed" ? undefined : utf8.decode(got.decider.id);
    assert.equal(decider, row.decider, `${row.name}: the decider it names`);
    kinds.add(row.completion);
  }
  assert.deepEqual([...kinds].sort(), ["may_not_complete", "stops_are_typed", "undeclared"], "every declaration kind is exercised");
});
