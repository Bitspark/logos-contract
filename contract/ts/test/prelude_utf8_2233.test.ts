/*
 * #2233: loadPrelude refuses a lone UTF-16 surrogate, whether a `\u` escape produces it or the
 * text carries it raw. Once a name is encoded it would become U+FFFD, so `p(X,Y) :- q(X), r(Y)`
 * would load as `p(V,V) :- q(V), r(V)`. The same witnesses are pinned in contract/rs and
 * contract/go.
 */

import test from "node:test";
import assert from "node:assert/strict";

import { loadPrelude, PreludeError, type PreludeBundle, TermVar } from "../src/index.js";

/** `p(X,Y) :- q(X), r(Y)` with the two variable names spliced in as raw JSON string contents. */
function clause(x: string, y: string): string {
  return (
    `{"head":{"pred":"p","args":[{"var":"${x}"},{"var":"${y}"}]},` +
    `"body":[{"pred":"q","args":[{"var":"${x}"}]},{"pred":"r","args":[{"var":"${y}"}]}]}`
  );
}

/** Load a one-clause bundle, pinning the digest the loader recomputes. */
function load(clauseJson: string): PreludeBundle {
  const doc = `{"name":"t","version":"0.0.0","program_digest":"DIGEST","clauses":[{"clause":${clauseJson}}]}`;
  try {
    return loadPrelude(doc);
  } catch (e) {
    if (e instanceof PreludeError && e.kind === "digest_mismatch" && e.recomputed !== undefined) {
      return loadPrelude(doc.replace("DIGEST", e.recomputed));
    }
    throw e;
  }
}

test("#2233: a lone UTF-16 surrogate is refused as malformed", () => {
  const refused: [string, string, string][] = [
    ["PJ1 lone surrogate escapes", "\\ud800", "\\udc00"],
    ["a high surrogate followed by a non-surrogate escape", "\\ud800\\u0041", "Y"],
    ["a lone low surrogate", "X", "\\udfff"],
    ["a lone surrogate carried RAW in the text", "\ud800", "\udc00"],
  ];
  for (const [name, x, y] of refused) {
    assert.throws(
      () => load(clause(x, y)),
      (e: unknown) => e instanceof PreludeError && e.kind === "malformed",
      name,
    );
  }
});

test("#2233: well-formed names still load, and stay distinct", () => {
  const loaded: [string, string, string][] = [
    ["PJ0 control", "X", "Y"],
    ["a surrogate PAIR each (U+1F600, U+1F601)", "\\ud83d\\ude00", "\\ud83d\\ude01"],
  ];
  for (const [name, x, y] of loaded) {
    const head = load(clause(x, y)).clauses[0]!.clause.head;
    const [a, b] = head.args;
    assert.ok(a instanceof TermVar && b instanceof TermVar, `${name}: two variable arguments`);
    assert.ok(!a.equals(b), `${name}: the head variables merged`);
  }
});
