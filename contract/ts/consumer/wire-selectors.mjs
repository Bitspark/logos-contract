import assert from "node:assert/strict";
import { test } from "node:test";
import {
  CertWireError, PATH_EACH, certWireSpans, certWireSpansAt, certWireTag, certWireWalk, pathIndex,
} from "@bitspark/logos-contract";

// A consumer-authored layout with certificates at two independent list entries.
// The tiny values use single-byte canonical lengths; the public walker receives
// only the encoded bytes and the caller's structural selector declaration.
const atom = text => {
  const bytes = new TextEncoder().encode(text);
  return [0, bytes.length, ...bytes];
};
const tuple = (...items) => [1, items.length, ...items.flat()];
const frame = Uint8Array.from(tuple(
  atom("tag"),
  tuple(tuple(tuple(), tuple(atom("a"), atom("bc"))), tuple(tuple(), tuple(atom("def")))),
));
const expected = [[1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 1, 0]];

function selected(steps, input = frame) {
  const spans = certWireSpansAt(input, steps);
  assert.deepEqual(spans.map(span => span.path), expected);
  assert.deepEqual(
    spans.map(span => Array.from(frame.subarray(span.start, span.start + span.span))),
    [atom("a"), atom("bc"), atom("def")],
  );
  return spans;
}

function invalidPath(error) {
  return error instanceof CertWireError && error.wireName === "invalid_path";
}

test("generic selector composition reports the selected bytes and nonzero coordinates", () => {
  selected([pathIndex(1), PATH_EACH, pathIndex(1)]);
  const spans = certWireSpansAt(frame, [pathIndex(1), pathIndex(0), pathIndex(1)]);
  assert.deepEqual(certWireSpans(frame, [1, 0, 1]), spans.map(span => span.span));
});

test("generic traversal reads the native frame extent at its actual offset", () => {
  const storage = new Uint8Array(frame.length + 7).fill(255);
  storage.set(frame, 3);
  const input = storage.subarray(3, 3 + frame.length);
  for (const field of ["length", "buffer", "byteOffset", "byteLength", "subarray"]) {
    Object.defineProperty(input, field, { get() { throw Error(`input getter was read: ${field}`); } });
  }
  selected([pathIndex(1), PATH_EACH, pathIndex(1)], input);
  assert.doesNotThrow(() => certWireWalk(input));
  assert.deepEqual(certWireTag(input), Uint8Array.from([116, 97, 103]));
  assert.throws(() => certWireSpans(input, [-1]), invalidPath);
});

for (const index of [-1, 0.5, NaN, Infinity, -Infinity, 2 ** 53, "1", undefined]) {
  test(`invalid selector index ${String(index)} is refused before any frame traversal`, () => {
    for (const bytes of [frame, Uint8Array.from(tuple()), new Uint8Array()]) {
      assert.throws(() => certWireSpans(bytes, [index]), invalidPath);
      assert.throws(() => certWireSpansAt(bytes, [{ kind: "index", index }]), invalidPath);
      assert.throws(() => certWireSpansAt(bytes, [PATH_EACH, { kind: "index", index }]), invalidPath);
    }
  });
}

test("a valid absent selector retains its portable count without truncation", () => {
  for (const index of [2, 2 ** 31 - 1, 2 ** 31, 2 ** 32 - 1, 2 ** 32, Number.MAX_SAFE_INTEGER]) {
    assert.deepEqual(certWireSpans(frame, [index]), []);
    assert.deepEqual(certWireSpansAt(frame, [pathIndex(index)]), []);
  }
});

test("either JavaScript spelling of zero reports the same coordinate", () => {
  const bytes = Uint8Array.from(tuple(tuple(atom("zero"))));
  for (const index of [0, -0]) {
    assert.deepEqual(certWireSpansAt(bytes, [pathIndex(index)]).map(span => span.path), [[0, 0]]);
  }
});

test("the complete selector is validated even when an earlier step reaches no values", () => {
  for (const step of [{ kind: "unknown" }, {}, null, undefined]) {
    for (const steps of [[step], [PATH_EACH, step], [pathIndex(99), step]]) {
      assert.throws(() => certWireSpansAt(Uint8Array.from(tuple()), steps), invalidPath);
    }
  }
  assert.throws(() => certWireSpansAt(frame, Array(1)), invalidPath);
  assert.throws(() => certWireSpans(frame, Array(1)), invalidPath);
});

test("a structural index is captured once for all branches and reported coordinates", () => {
  let reads = 0;
  const index = Object.create(null, {
    kind: { value: "index" },
    index: { get() { return ++reads === 1 ? 1 : 99; } },
  });
  selected([pathIndex(1), PATH_EACH, index]);
  assert.equal(reads, 1);
});

test("each structural step and its kind are captured once", () => {
  let stepReads = 0;
  let kindReads = 0;
  const index = Object.create({ index: 1 }, {
    kind: { get() { return ++kindReads === 1 ? "index" : "each"; } },
  });
  const steps = [pathIndex(1), PATH_EACH, index];
  Object.defineProperty(steps, 2, {
    get() { stepReads += 1; return stepReads === 1 ? index : pathIndex(99); },
  });
  selected(steps);
  assert.equal(stepReads, 1);
  assert.equal(kindReads, 1);
});

test("a selector is an indexed declaration without application-owned collection methods", () => {
  const paths = [1, 0, 1];
  for (const method of ["map", Symbol.iterator]) {
    Object.defineProperty(paths, method, { get() { throw Error("collection method was read"); } });
  }
  assert.deepEqual(certWireSpans(frame, paths), [atom("a").length, atom("bc").length]);
  const each = Object.create(null, {
    kind: { value: "each" },
    index: { get() { throw Error("irrelevant index was read"); } },
  });
  selected([pathIndex(1), each, pathIndex(1)]);
});
