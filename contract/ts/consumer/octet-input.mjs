import assert from "node:assert/strict";
import { test } from "node:test";
import { runInNewContext } from "node:vm";
import {
  CertContext, Clause, ClauseId, ClosedModelCert, ComponentIdentity, Derivation, Goal, GroundLiteral,
  LeafNode, MapProgram, ProgramSerdeEncodeError, StratumPrefix, Symbol as Predicate,
  Term, TermAtom, captureDerivation, copyOctets, defaultLimits, encodeUtf8, hashEquals, hashFromBytes, programBytes,
} from "@bitspark/logos-contract";

const constructors = [
  ["Symbol", source => new Predicate(source)],
  ["Symbol.of", source => Predicate.of(source)],
  ["TermAtom", source => new TermAtom(source)],
  ["Term.atom", source => Term.atom(source)],
];

for (const [name, construct] of constructors) {
  test(`${name} admits exact octets and rejects numeric values that would alias them`, () => {
    const invalid = [[-1], [256], [0.5], [NaN], [Infinity], [-Infinity], ["0"], [true], [undefined], Array(1)];
    for (const source of invalid) {
      assert.throws(() => construct(source), undefined, `invalid octet in ${name}`);
    }
    assert.deepEqual(construct([]).bytes(), new Uint8Array());
    assert.deepEqual(construct([0, -0, 127, 255]).bytes(), Uint8Array.of(0, 0, 127, 255));
  });

  test(`${name} reads each numeric position once and never dispatches to a sequence's iterator`, () => {
    const array = [0, 255];
    let reads = 0;
    Object.defineProperty(array, 0, { get() { return ++reads === 1 ? 127 : 256; } });
    Object.defineProperty(array, Symbol.iterator, { get() { throw Error("iterator was inspected"); } });
    let sizes = 0;
    const sequence = new Proxy(array, {
      get(target, key, receiver) {
        if (key === "length") sizes++;
        return Reflect.get(target, key, receiver);
      },
    });
    const value = construct(sequence);
    assert.deepEqual(value.bytes(), Uint8Array.of(127, 255));
    assert.equal(reads, 1);
    assert.equal(sizes, 1);
    array[1] = 1;
    value.bytes().fill(2);
    assert.deepEqual(value.bytes(), Uint8Array.of(127, 255));
  });

  test(`${name} stores the same indexed value it validated`, () => {
    const source = [0];
    let reads = 0;
    Object.defineProperty(source, 0, { get() { return ++reads === 1 ? 17 : 256; } });
    assert.deepEqual(construct(source).bytes(), Uint8Array.of(17));
    assert.equal(reads, 1);
  });

  test(`${name} reads genuine view bytes across realms and refuses other element types`, () => {
    const view = runInNewContext("Uint8Array.of(73, 0, 255, 51).subarray(1, 3)");
    Object.defineProperties(view, {
      length: { get() { throw Error("overridden length was inspected"); } },
      [Symbol.iterator]: { get() { throw Error("typed array iterator was inspected"); } },
    });
    assert.deepEqual(construct(view).bytes(), Uint8Array.of(0, 255));
    for (const source of [new Uint16Array([256]), new Uint8ClampedArray([1]), new DataView(new ArrayBuffer(2)), { length: 1, 0: 1 }]) {
      assert.throws(() => construct(source));
    }
    const detached = Uint8Array.of(1);
    structuredClone(detached.buffer, { transfer: [detached.buffer] });
    assert.throws(() => construct(detached));
  });
}

test("text predicate names distinguish an intentionally authored replacement character from invalid UTF-16", () => {
  for (const invalid of ["\uD800", "\uDFFF", "a\uD800b"]) {
    assert.throws(() => Predicate.of(invalid));
  }
  for (const valid of ["", "\uFEFFa", "\uFFFD", "\u{1F600}"]) {
    assert.deepEqual(Predicate.of(valid).bytes(), new TextEncoder().encode(valid));
  }
});

test("the program codec sees the reserved byte only when the author actually supplied it", () => {
  assert.throws(() => Predicate.of([256]));
  const forbidden = Clause.fact(Goal.of(Predicate.of([0]), []));
  assert.throws(() => programBytes(new MapProgram().with(ClauseId.of("reserved"), forbidden)), ProgramSerdeEncodeError);
  const allowed = Clause.fact(Goal.of(Predicate.of([255]), []));
  assert.ok(programBytes(new MapProgram().with(ClauseId.of("octet"), allowed)).length > 0);
});

test("component identities retain their three original byte fields", () => {
  const id = Uint8Array.of(17);
  const version = Uint8Array.of(29);
  const pin = new Uint8Array(32).fill(71);
  const identity = ComponentIdentity.of(id, version, pin);
  id[0] = version[0] = pin[0] = 0;
  assert.deepEqual(Object.keys(identity), ["id", "version", "configDigest"]);
  assert.deepEqual([identity.id[0], identity.version[0], identity.configDigest[0]], [17, 29, 71]);
  identity.id.fill(0);
  identity.version.fill(0);
  identity.configDigest.fill(0);
  assert.deepEqual([identity.id[0], identity.version[0], identity.configDigest[0]], [17, 29, 71]);
  assert.throws(() => ComponentIdentity.of([256], version, pin));
  assert.throws(() => ComponentIdentity.of(id, new Uint16Array(1), pin));
  for (const width of [0, 31, 33]) {
    assert.throws(() => ComponentIdentity.of(id, version, new Uint8Array(width)));
  }
});

test("independent callers use the same binary and text constructors as the checker", () => {
  const source = Buffer.alloc(34, 0xff).subarray(1, 33);
  const hash = hashFromBytes(source);
  const context = CertContext.of(source, source, source, source);
  const sliceContext = CertContext.withDecomposition(context, source);
  source.fill(0);
  context.profileHash[0] = 1;
  assert.equal(hash[0], 255);
  assert.equal(sliceContext.profileHash[0], 255);
  assert.equal(sliceContext.decompositionWitness[0], 255);
  assert.ok(hashEquals(hash, sliceContext.programHash));
  assert.equal(hashEquals(new Uint8Array(31), new Uint8Array(31)), false);
  assert.deepEqual(copyOctets([0, 127, 255]), Uint8Array.of(0, 127, 255));
  assert.throws(() => copyOctets(new Uint16Array(2)));
  assert.throws(() => hashFromBytes(new Array(32).fill(256)), TypeError);
  assert.throws(() => hashFromBytes(new Array(31).fill(255)), RangeError);
  assert.throws(() => CertContext.of(source, source, source, new Uint8Array(31)), RangeError);
  assert.throws(() => encodeUtf8("\uDC00"));
  assert.deepEqual(encodeUtf8("\uFEFF\uFFFD"), Uint8Array.of(0xef, 0xbb, 0xbf, 0xef, 0xbf, 0xbd));
});

test("detached, out-of-bounds and empty native views have distinct admissions", () => {
  const storage = new ArrayBuffer(4, { maxByteLength: 8 });
  const moving = new Uint8Array(storage, 2, 2);
  storage.resize(1);
  assert.throws(() => copyOctets(moving));
  assert.deepEqual(copyOctets(new Uint8Array(storage, 0, 0)), new Uint8Array());
  storage.resize(4);
  assert.deepEqual(copyOctets(moving), Uint8Array.of(0, 0));
});

test("a malformed fixed-width pin in a native proof is a checker refusal", () => {
  const pin = new Uint8Array(32);
  const cert = new ClosedModelCert({
    scope: StratumPrefix.of(0, []), programHash: new Uint8Array(31), profileHash: pin, ctxHash: pin,
    theoryConfigHash: pin, edbSnapshotHashes: [], domains: [], extensions: [], supports: [],
    limitsDecl: { certFacts: 0, domainValues: 0, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 0 },
  });
  const proposal = new Derivation([new LeafNode(GroundLiteral.of("p", []))], 0, [cert]);
  const result = captureDerivation(proposal, defaultLimits());
  assert.equal(result.kind, "reject");
  assert.equal(result.code, "unknown_node_kind");
});
