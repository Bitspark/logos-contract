/*
 * TS replay of the cross-core Shelf-B prelude-loader vector vectors/prelude.json (ADR
 * 0016 Shelf-B Horn-clause prelude), plus a load of the shipped on-disk bundles
 * prelude/sample@1.0.0.json + lists@1.0.0/1.1.0/1.2.0.json, plus the cross-core
 * program_digest pin.
 *
 * Each vector case is a complete prelude manifest plus the PINNED loadPrelude outcome.
 * This replay drives the REAL loadPrelude over each manifest (the committed file is
 * checked against the loader, not trusted blind) and asserts the {ok | err} outcome. The
 * SAME vectors/prelude.json is replayed in Rust (contract/rs/tests/prelude_vectors.rs)
 * and Go (contract/go/prelude_vectors_test.go) — the recomputed program_digest is
 * byte-identical across {rs,go,ts} (frozen ontos-codec + syntactic VarId), so
 * search/check/loader cannot silently diverge.
 *
 * The trust anchor is DIGEST RE-DERIVATION, not the JSON parser: the digest_mismatch and
 * tampered_clause_rejected_by_digest cases pin that a wrong clause set (or a wrong pinned
 * digest) is REFUSED, never silently admitted.
 */

import test from "node:test";
import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

import {
  bundleDigest,
  canonicalClauseId,
  Clause,
  Goal,
  loadPrelude,
  PROGRAM_PREFIX,
  CLAUSE_PREFIX,
  PreludeError,
  type PreludeBundle,
  Term,
} from "../src/index.js";

// ----- the on-disk vector shape -----

interface PreludeVectorFile {
  readonly program_prefix_hex: string;
  readonly clause_prefix_hex: string;
  readonly cases: readonly PreludeVecCase[];
}

interface PreludeVecCase {
  readonly name: string;
  readonly manifest: unknown;
  readonly outcome: { readonly ok?: PreludeOk; readonly err?: string };
}

interface PreludeOk {
  readonly name: string;
  readonly version: string;
  readonly program_digest: string;
  readonly clause_ids: readonly string[];
}

function repoRoot(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    if (fs.existsSync(path.join(dir, "vectors", "prelude.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error(`could not locate vectors/prelude.json above ${dir}`);
    dir = parent;
  }
}

function loadVectors(): PreludeVectorFile {
  const file = path.join(repoRoot(), "vectors", "prelude.json");
  return JSON.parse(fs.readFileSync(file, "utf8")) as PreludeVectorFile;
}

function toHex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}

function assertOk(name: string, want: PreludeOk, got: PreludeBundle): void {
  assert.equal(got.name, want.name, `${name}: bundle name`);
  assert.equal(got.version, want.version, `${name}: bundle version`);
  assert.equal(got.programDigest, want.program_digest, `${name}: recomputed program_digest`);
  const gotIds = got.clauses.map((c) => c.id.asStr());
  assert.deepEqual(gotIds, want.clause_ids, `${name}: clause ids (in manifest order)`);
}

// ----- the replay -----

test("loadPrelude reproduces every pinned vector outcome byte-for-byte", () => {
  const vf = loadVectors();
  assert.equal(vf.cases.length > 0, true, "no loader vectors loaded");
  let sawOk = false;
  let sawErr = false;
  for (const c of vf.cases) {
    // Re-serialize the embedded manifest to the JSON string loadPrelude consumes.
    const manifest = JSON.stringify(c.manifest);
    if (c.outcome.ok !== undefined) {
      sawOk = true;
      const bundle = loadPrelude(manifest);
      assertOk(c.name, c.outcome.ok, bundle);
    } else if (c.outcome.err !== undefined) {
      sawErr = true;
      try {
        const bundle = loadPrelude(manifest);
        assert.fail(`${c.name}: expected err ${c.outcome.err}, got ok ${JSON.stringify(bundle)}`);
      } catch (e) {
        assert.equal(e instanceof PreludeError, true, `${c.name}: expected PreludeError, got ${String(e)}`);
        assert.equal((e as PreludeError).kind, c.outcome.err, `${c.name}: error variant`);
      }
    } else {
      assert.fail(`${c.name}: outcome is neither ok nor err`);
    }
  }
  assert.equal(sawOk && sawErr, true, `vectors must cover both ok and err (sawOk=${sawOk} sawErr=${sawErr})`);
});

test("the vector's program/clause prefix bytes equal the hashing constants", () => {
  const vf = loadVectors();
  assert.equal(toHex(PROGRAM_PREFIX), vf.program_prefix_hex, "PROGRAM_PREFIX hex");
  assert.equal(toHex(CLAUSE_PREFIX), vf.clause_prefix_hex, "CLAUSE_PREFIX hex");
});

test("programDigest reproduces the Rust-pinned digest for the sample clause set", () => {
  // nat(z).  and  nat(s(X)) :- nat(X).  — built in TS so the test is independent of the
  // on-disk manifest.
  const natZ = Clause.fact(Goal.of("nat", [Term.tuple([Term.atom(new TextEncoder().encode("z"))])]));
  const natS = new Clause(
    Goal.of("nat", [Term.tuple([Term.atom(new TextEncoder().encode("s")), Term.var("X")])]),
    [Goal.of("nat", [Term.var("X")])],
  );
  const wantDigest = "cb22fbb4f7fcaf55de33742c2ad0328cc9f964bbb97b62ab508fced396fbb5a7";
  assert.equal(bundleDigest([natZ, natS]), wantDigest, "program_digest matches the Rust/Go pin");
  // Order-independence: the digest sorts the per-clause bytes, so a reversed slice agrees.
  assert.equal(bundleDigest([natS, natZ]), wantDigest, "program_digest is order-independent");
  // The per-clause canonical ids match the manifest pins.
  assert.equal(
    canonicalClauseId(natZ).asStr(),
    "8c245a7a0ea73dab49ff899cc27254953f7cb321e15a803bf832c174ab2d757c",
    "nat(z) clause id",
  );
  assert.equal(
    canonicalClauseId(natS).asStr(),
    "d02e98ca7fe546344c88c2bc5afdfea44779e90195c9432de6858d5055d46e84",
    "nat(s(X)):-nat(X) clause id",
  );
});

test("every shipped on-disk prelude bundle loads through the real loader", () => {
  const root = repoRoot();
  const cases = [
    { file: "sample@1.0.0.json", name: "sample", version: "1.0.0", digest: "cb22fbb4f7fcaf55de33742c2ad0328cc9f964bbb97b62ab508fced396fbb5a7" },
    { file: "lists@1.0.0.json", name: "lists", version: "1.0.0", digest: "59d7f32b8a3a7d936ce098d15b05d87d03b0727d920cedd2e24891a857176e25" },
    { file: "lists@1.1.0.json", name: "lists", version: "1.1.0", digest: "9451f99428fd18a60eb19c9ef26a72b94b4db5b5a8f755ed851fe159ffcf0e35" },
    { file: "lists@1.2.0.json", name: "lists", version: "1.2.0", digest: "c2cb5164002b89db421463d3d98e057646545a6b25c3b3145ae170443bd1b056" },
  ];
  for (const tc of cases) {
    const raw = fs.readFileSync(path.join(root, "prelude", tc.file), "utf8");
    const bundle = loadPrelude(raw);
    assert.equal(bundle.name, tc.name, `${tc.file}: name`);
    assert.equal(bundle.version, tc.version, `${tc.file}: version`);
    if (tc.digest !== undefined) {
      assert.equal(bundle.programDigest, tc.digest, `${tc.file}: program_digest`);
    }
    assert.equal(bundle.clauses.length > 0, true, `${tc.file}: loaded with clauses`);
  }
});
