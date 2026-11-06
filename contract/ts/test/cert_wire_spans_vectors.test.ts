// TS replay of vectors/cert_wire_spans.json (#2528, #2561): certWireSpansAt walks each guest-to-host
// frame's tags and uvarints WITHOUT decoding it, and must report the rs walk's certificates (their
// concrete paths and spans), tag, walk verdict, budget verdict and refusal names; an all-index path
// must give certWireSpans the same spans.

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import { decode, encode } from "@bitspark/ontos-codec";
import { encodeInt } from "@bitspark/ontos-data";

import {
  certBytesSlack,
  certSpanOverBudget,
  CertWireError,
  certWireSpans,
  certWireSpansAt,
  certWireTag,
  certWireWalk,
  PATH_EACH,
  pathIndex,
  type PathStep,
} from "../src/index.js";

interface Case {
  readonly name: string;
  readonly path: readonly (number | "*")[];
  readonly tag?: string;
  readonly at?: readonly (readonly number[])[];
  readonly spans?: readonly number[];
  readonly starts?: readonly number[];
  readonly measures?: readonly number[];
  readonly refused?: string;
  readonly max_cert_bytes?: number;
  readonly over_budget?: readonly (readonly number[])[];
  readonly walk: string;
  readonly frame: string;
}

/** A case's path as steps, and as indices when every step is one (the index-only walker's input). */
function stepsOf(c: Case): { steps: PathStep[]; indices: number[] | undefined } {
  const steps = c.path.map((s) => (s === "*" ? PATH_EACH : pathIndex(s)));
  const indices = c.path.every((s) => s !== "*") ? (c.path as number[]) : undefined;
  return { steps, indices };
}

function load(): { readonly cert_bytes_slack: number; readonly cases: readonly Case[] } {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const candidate = path.join(dir, "vectors", "cert_wire_spans.json");
    if (fs.existsSync(candidate)) return JSON.parse(fs.readFileSync(candidate, "utf8"));
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("could not locate vectors/cert_wire_spans.json");
    dir = parent;
  }
}

function fromHex(hex: string): Uint8Array {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.slice(2 * i, 2 * i + 2), 16);
  return out;
}

function refusal(f: () => unknown): string | undefined {
  try {
    f();
    return undefined;
  } catch (e) {
    if (e instanceof CertWireError) return e.wireName;
    throw e;
  }
}

test("#2528: every core walks the vector's frames to the same spans, tags and refusals", () => {
  const v = load();
  assert.equal(certBytesSlack(), v.cert_bytes_slack, "the slack");
  assert.ok(v.cases.length >= 10, `the vector's cases: ${v.cases.length}`);
  let measured = 0;
  let each = 0;
  let budgeted = 0;
  for (const c of v.cases) {
    const frame = fromHex(c.frame);
    // A malformed frame has no readable tag (the go and rs replays read it the same way).
    let tag: Uint8Array | undefined;
    try {
      tag = certWireTag(frame);
    } catch {
      tag = undefined;
    }
    assert.equal(tag === undefined ? undefined : new TextDecoder().decode(tag), c.tag, `${c.name}: tag`);
    assert.equal(refusal(() => certWireWalk(frame)) ?? "ok", c.walk, `${c.name}: the walk alone`);
    const { steps, indices } = stepsOf(c);
    if (indices === undefined) each += 1;
    if (c.refused !== undefined) {
      assert.equal(refusal(() => certWireSpansAt(frame, steps)), c.refused, `${c.name}: refused`);
      if (indices !== undefined) {
        assert.equal(refusal(() => certWireSpans(frame, indices)), c.refused, `${c.name}: the index-only walker`);
      }
      continue;
    }
    const certs = certWireSpansAt(frame, steps);
    const spans = certs.map((cert) => cert.span);
    assert.deepEqual(
      certs.map((cert) => cert.path),
      c.at,
      `${c.name}: at`,
    );
    assert.deepEqual(spans, c.spans, `${c.name}: spans`);
    assert.deepEqual(
      certs.map((cert) => cert.start),
      c.starts,
      `${c.name}: starts`,
    );
    if (indices !== undefined) assert.deepEqual(certWireSpans(frame, indices), spans, `${c.name}: the index-only walker`);
    if (c.max_cert_bytes !== undefined) {
      const over = certs.filter((cert) => certSpanOverBudget(cert.span, c.max_cert_bytes!)).map((cert) => cert.path);
      assert.deepEqual(over, c.over_budget, `${c.name}: over budget`);
      budgeted += 1;
    }
    (c.measures ?? []).forEach((m, i) => {
      assert.ok(spans[i]! >= m && spans[i]! - m <= certBytesSlack(), `${c.name}: certificate ${i} within the slack`);
      measured += 1;
    });
  }
  assert.ok(measured >= 4, `the vector measures real certificates: ${measured}`);
  assert.ok(each >= 3 && budgeted >= 1, `the vector walks * paths (${each}) and holds a case to a budget (${budgeted})`);
});

test("#2561: the walk alone reads any value, and refuses what the codec refuses", () => {
  certWireWalk(Uint8Array.from([0x00, 0x01, 0x78]));
  assert.equal(refusal(() => certWireWalk(Uint8Array.from([0x00, 0x01, 0x78, 0x00]))), "trailing_bytes");
  assert.equal(refusal(() => certWireWalk(Uint8Array.from([0x01, 0x02, 0x00, 0x00]))), "truncated");
});

test("#2528: the walk refuses what the codec refuses", () => {
  const padded = Uint8Array.from([0x01, 0x81, 0x00, 0x00, 0x01, 0x61]);
  assert.throws(() => decode(padded), "CONTROL: the codec refuses the padded uvarint");
  assert.equal(refusal(() => certWireSpans(padded, [])), "non_canonical_uvarint");
  const frame = Uint8Array.from([0x01, 0x01, 0x00, 0x01, 0x61]);
  for (let cut = 0; cut < frame.length; cut++) {
    assert.equal(refusal(() => certWireSpans(frame.subarray(0, cut), [])), "truncated", `cut ${cut}`);
  }
  assert.deepEqual(certWireSpans(frame, [3]), [], "an absent slot has no certificates");
});

test("#2528: the slack bounds every declaration's growth over 0", () => {
  const slack = certBytesSlack();
  const zero = encode(encodeInt(0n)).length;
  for (const n of [0n, 1n, 255n, 256n, 1n << 20n, 1n << 40n, (1n << 64n) - 1n]) {
    assert.ok(encode(encodeInt(n)).length - zero <= slack, `${n}`);
  }
  assert.ok(certSpanOverBudget(100 + slack + 1, 100) && !certSpanOverBudget(100 + slack, 100));
});
