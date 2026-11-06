import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { atom as valueAtom } from "@bitspark/ontos-core";
import { encodeInt } from "@bitspark/ontos-data";

import {
  BuiltinNode,
  ClauseId,
  ClosedModelCert,
  CountPremise,
  Derivation,
  Evidence,
  FiniteDomain,
  GroundLiteral,
  LeafNode,
  NodeMeta,
  PredicateRef,
  ProjectSpec,
  RelationTable,
  RuleNode,
  StratumPrefix,
  Symbol,
  decodeDerivationWireV1,
  encodeDerivationWireV1,
} from "../src/index.js";

interface Case {
  name: string;
  wire_hex: string;
}

interface MalformedCase extends Case {
  refusal: string;
}

interface DecodesCase extends Case {
  root: number;
  nodes: number;
}

interface DerivationWireFile {
  positive: Case[];
  malformed: MalformedCase[];
  decodes: DecodesCase[];
}

const enc = new TextEncoder();

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "derivation_wire.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/derivation_wire.json above ${dir}`);
    dir = parent;
  }
}

function vectors(): DerivationWireFile {
  return JSON.parse(fs.readFileSync(path.join(repoRoot(), "vectors", "derivation_wire.json"), "utf8")) as DerivationWireFile;
}

function toHex(bytes: Uint8Array): string {
  return Buffer.from(bytes).toString("hex");
}

function hexToBytes(hex: string): Uint8Array {
  return new Uint8Array(Buffer.from(hex, "hex"));
}

function atom(s: string) {
  return valueAtom(enc.encode(s));
}

function lit(pred: string, ...args: string[]): GroundLiteral {
  return GroundLiteral.of(pred, args.map(atom));
}

function zeroHash(): Uint8Array {
  return new Uint8Array(32);
}

function closedCert(): ClosedModelCert {
  const pred = Symbol.of("sealed");
  return new ClosedModelCert({
    scope: StratumPrefix.of(0, [pred]),
    programHash: zeroHash(),
    profileHash: zeroHash(),
    ctxHash: zeroHash(),
    theoryConfigHash: zeroHash(),
    edbSnapshotHashes: [],
    domains: [FiniteDomain.of(Symbol.of("entity"), [atom("a")])],
    extensions: [RelationTable.of(pred, 1, [lit("sealed", "a")])],
    supports: [],
    limitsDecl: { certFacts: 1, domainValues: 1, supportEdges: 0, ruleGroundings: 0, joinSteps: 0, certBytes: 0 },
  });
}

function fixture(name: string): Derivation {
  switch (name) {
    case "leaf":
      return new Derivation([new LeafNode(lit("edge", "a", "b"), Evidence.none())], 0);
    case "builtin":
      return new Derivation([new BuiltinNode(lit("=", "a", "a"))], 0);
    case "rule":
      return new Derivation(
        [
          new LeafNode(lit("edge", "a", "b"), Evidence.none()),
          new RuleNode(lit("path", "a", "b"), ClauseId.of("path#edge"), new Map(), [0], NodeMeta.none()),
        ],
        1,
      );
    case "closed_world_count":
      return new Derivation(
        [
          new RuleNode(
            lit("has_count", "a"),
            ClauseId.of("count#sealed"),
            new Map(),
            [
              new CountPremise(
                new PredicateRef(Symbol.of("sealed"), 1),
                [{ pos: 0, value: atom("a") }],
                ProjectSpec.rows(),
                encodeInt(1n),
                0,
              ),
            ],
            NodeMeta.none(),
          ),
        ],
        0,
        [closedCert()],
      );
    case "closed_world_count_partial": {
      // ADR 0030 D4: the twelve-element cert — the D10 witness at slot 11 AND a partial
      // sub-scope at slot 12. Byte-identical to the RED-first malformed entry of b1d3d5a7; a
      // WIRE fixture only (the level-1 partial scope over a level-0 seal is not checkable).
      const base = closedCert();
      const cert = new ClosedModelCert({
        scope: base.scope,
        programHash: base.programHash,
        profileHash: base.profileHash,
        ctxHash: base.ctxHash,
        theoryConfigHash: base.theoryConfigHash,
        edbSnapshotHashes: base.edbSnapshotHashes,
        domains: base.domains,
        extensions: base.extensions,
        supports: base.supports,
        limitsDecl: base.limitsDecl,
        decompositionWitness: new Uint8Array(32).fill(0xd1),
        partialScope: StratumPrefix.of(1, [Symbol.of("sealed")]),
      });
      return new Derivation(
        [
          new RuleNode(
            lit("has_count", "a"),
            ClauseId.of("count#sealed"),
            new Map(),
            [
              new CountPremise(
                new PredicateRef(Symbol.of("sealed"), 1),
                [{ pos: 0, value: atom("a") }],
                ProjectSpec.rows(),
                encodeInt(1n),
                0,
              ),
            ],
            NodeMeta.none(),
          ),
        ],
        0,
        [cert],
      );
    }
    default:
      throw new Error(`unknown derivation_wire fixture ${name}`);
  }
}

test("DerivationWireV1 positive vectors match and round-trip", () => {
  for (const c of vectors().positive) {
    const deriv = fixture(c.name);
    assert.equal(toHex(encodeDerivationWireV1(deriv)), c.wire_hex, `${c.name} wire bytes`);
    assert.equal(toHex(encodeDerivationWireV1(decodeDerivationWireV1(encodeDerivationWireV1(deriv)))), c.wire_hex, `${c.name} round-trip`);
  }
});

test("DerivationWireV1 malformed vectors reject", () => {
  const malformed = vectors().malformed;
  assert.ok(malformed.length > 0, "the vector has malformed rows");
  for (const c of malformed) {
    // #2630: the one decoder's refusal text, byte-identical in all three cores.
    assert.ok(typeof c.refusal === "string" && c.refusal !== "", `${c.name} states no refusal`);
    assert.throws(
      () => decodeDerivationWireV1(hexToBytes(c.wire_hex)),
      (e: unknown) => e instanceof Error && e.message === c.refusal,
      `${c.name} must reject with ${JSON.stringify(c.refusal)}`,
    );
  }
});

// #2630 (seat:caa's ruling on #2645): wires the decoder must ACCEPT. A root that indexes no node
// passes through (check refuses it as root_out_of_range), and a subst in canonical order decodes;
// each re-encodes byte for byte.
test("DerivationWireV1 decodes vectors are accepted and round-trip", () => {
  const decodes = vectors().decodes;
  assert.ok(decodes.length > 0, "the vector has decodes rows");
  for (const c of decodes) {
    const d = decodeDerivationWireV1(hexToBytes(c.wire_hex));
    assert.equal(d.root, c.root, `${c.name} root`);
    assert.equal(d.nodes.length, c.nodes, `${c.name} node count`);
    assert.equal(toHex(encodeDerivationWireV1(d)), c.wire_hex, `${c.name} re-encodes byte for byte`);
  }
});
