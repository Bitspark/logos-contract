import assert from "node:assert/strict";
import { test } from "node:test";
import {
  Clause, Goal, PreludeError, Term, bundleDigest, canonicalClauseId, loadPrelude,
} from "@bitspark/logos-contract";

const clause = Clause.fact(Goal.of("p", [Term.atom(Uint8Array.of(15))]));
const expectedId = canonicalClauseId(clause).asStr();
const expectedDigest = bundleDigest([clause]);

function manifest(hex, pinned = clause) {
  return JSON.stringify({
    name: "hex", version: "1.0.0", program_digest: bundleDigest([pinned]),
    clauses: [{ id: canonicalClauseId(pinned).asStr(), clause: { head: { pred: "p", args: [{ atom: hex }] } } }],
  });
}

test("the pinned native fact loads with either case of hex digits", () => {
  for (const spelling of ["0f", "0F"]) {
    const result = loadPrelude(manifest(spelling));
    assert.equal(result.programDigest, expectedDigest);
    assert.equal(result.clauses[0].id.asStr(), expectedId);
  }
});

test("empty and multibyte prelude atoms keep their exact native bytes", () => {
  for (const [spelling, bytes] of [["", []], ["00aFFe", [0, 0xaf, 0xfe]]]) {
    const pinned = Clause.fact(Goal.of("p", [Term.atom(Uint8Array.from(bytes))]));
    const bundle = loadPrelude(manifest(spelling, pinned));
    assert.equal(bundle.programDigest, bundleDigest([pinned]));
    assert.equal(bundle.clauses[0].id.asStr(), canonicalClauseId(pinned).asStr());
  }
});

for (const spelling of ["fg", "gf", "+f", " f", "f ", "f", "0f\n\n", "０Ｆ"]) {
  test(`malformed atom ${JSON.stringify(spelling)} is a bad clause even under a matching pin`, () => {
    assert.throws(() => loadPrelude(manifest(spelling)),
      e => e instanceof PreludeError && e.kind === "bad_clause" && e.index === 0);
  });
}
