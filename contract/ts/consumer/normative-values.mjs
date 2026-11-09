import assert from "node:assert/strict";
import { test } from "node:test";
import * as contract from "@bitspark/logos-contract";

const goal = contract.Goal.of("p", []);
const fact = contract.Clause.fact(goal);
const id = contract.ClauseId.of("key");
const program = new contract.MapProgram().with(id, fact);

function afterChangingFirstByte(bytes, inspect) {
  const first = bytes[0];
  try {
    bytes[0] ^= 0xff;
    return inspect();
  } finally {
    bytes[0] = first;
  }
}

test("a program reader retains its wire version after another importer edits the exported bytes", () => {
  const wire = contract.programToValue(program);
  const expected = contract.programBytes(program);
  assert.ok(contract.programFromValue(wire).clause(id));
  const observed = afterChangingFirstByte(contract.programFormatTag(), () => {
    assert.ok(contract.programFromValue(wire).clause(id));
    return contract.programBytes(program);
  });
  assert.deepEqual(observed, expected);
});

for (const tag of [0, 1]) {
  test(`the public program codec keeps the reserved byte ${tag} outside the predicate vocabulary`, () => {
    const clause = contract.Clause.fact(contract.Goal.of(contract.Symbol.of(Uint8Array.of(tag)), []));
    const forbidden = new contract.MapProgram().with(id, clause);
    const read = () => {
      assert.deepEqual(contract.reservedPredicateOf(clause), Uint8Array.of(tag));
      assert.throws(() => contract.programBytes(forbidden), contract.ProgramSerdeEncodeError);
    };
    read();
    afterChangingFirstByte(contract.reservedProgramPredicateSymbols()[tag], read);
  });
}

for (const [name, inspectPrefix, read] of [
  ["clause", "clauseHashPrefix", () => contract.canonicalClauseId(fact).asStr()],
  ["program", "programHashPrefix", () => contract.bundleDigest([fact])],
  ["EDB snapshot", "edbSnapshotHashPrefix", () => Buffer.from(contract.edbTableHash(goal.pred, [goal.asGround()])).toString("hex")],
]) {
  test(`a new ${name} hash keeps its normative domain after inspection`, () => {
    const expected = read();
    assert.equal(afterChangingFirstByte(contract[inspectPrefix](), read), expected);
  });
}

test("a caller's pending UTF-8 stream cannot invalidate a genuine program identifier", () => {
  const wire = contract.programToValue(program);
  const read = () => contract.programFromValue(wire).clause(id);
  assert.ok(read());
  const partial = Uint8Array.of(0xe2);
  const caller = new TextDecoder("utf-8", { fatal: true });
  assert.equal(caller.decode(partial, { stream: true }), "");
  assert.throws(() => contract.decodeUtf8(partial, { stream: true }), TypeError);
  assert.ok(read());
  assert.equal(caller.decode(Uint8Array.of(0x82, 0xac)), "€");
});

test("a caller's pending replacement stream cannot change an aggregate account", () => {
  const counted = new contract.CountLit(new contract.PredicateRef(contract.Symbol.of("p"), 1),
    [], contract.ProjectSpec.rows(), contract.Term.var("N"));
  const clause = new contract.Clause(goal, [contract.BodyLit.count(counted)]);
  const wire = contract.clauseValue(clause);
  const read = () => contract.clauseFromValue(wire);
  assert.ok(read());
  const partial = Uint8Array.of(0xe2);
  const caller = new TextDecoder();
  assert.equal(caller.decode(partial, { stream: true }), "");
  assert.equal(contract.decodeUtf8Lossy(partial, { stream: true }), "�");
  assert.ok(read());
  assert.equal(caller.decode(Uint8Array.of(0x82, 0xac)), "€");
});
