// Research 0030 row 6: the package compiles with `noImplicitReturns`, and the setting is live.
//
// `strict` already refuses (TS2366) a function whose return type excludes `undefined` and which can
// fall off its end. It says nothing when the return type admits `undefined`, whether declared or
// inferred: a missing arm then returns `undefined` silently, and a caller reads it as an answer.
// `noImplicitReturns` makes that path a compile error (TS7030). It is NOT runtime validation
// (research 0030's advice): a function that returns on every path it knows about still returns
// whatever a forged value leads it to, which is why the executable `never` arms (row 5) exist
// separately.
//
// This test reads THIS package's tsconfig.json (the production configuration, not a copy) and
// compiles a planted function under it. The plant must be refused with TS7030, and the control,
// which returns on every path, must compile clean. Remove the flag and the plant compiles, so this
// test turns red.

import { strict as assert } from "node:assert";
import { test } from "node:test";
import path from "node:path";
import { fileURLToPath } from "node:url";
import ts from "typescript";

const here = path.dirname(fileURLToPath(import.meta.url));
// dist/test/<file>.js -> the package root holds tsconfig.json
const packageRoot = path.resolve(here, "..", "..");

function compilerOptions(): ts.CompilerOptions {
  const configPath = path.join(packageRoot, "tsconfig.json");
  const read = ts.readConfigFile(configPath, (p) => ts.sys.readFile(p));
  assert.equal(read.error, undefined, "tsconfig.json must parse");
  const parsed = ts.parseJsonConfigFileContent(read.config, ts.sys, packageRoot);
  return { ...parsed.options, noEmit: true };
}

function diagnosticsFor(source: string): readonly ts.Diagnostic[] {
  const options = compilerOptions();
  const fileName = path.join(packageRoot, "__planted_0030__.ts");
  const host = ts.createCompilerHost(options);
  const same = (name: string) => path.resolve(name) === fileName;
  const original = host.getSourceFile.bind(host);
  host.getSourceFile = (name, languageVersion, onError, shouldCreate) =>
    same(name)
      ? ts.createSourceFile(name, source, languageVersion, true)
      : original(name, languageVersion, onError, shouldCreate);
  const fileExists = host.fileExists.bind(host);
  host.fileExists = (name) => same(name) || fileExists(name);
  const readFile = host.readFile.bind(host);
  host.readFile = (name) => (same(name) ? source : readFile(name));
  const program = ts.createProgram([fileName], options, host);
  return ts.getPreEmitDiagnostics(program, program.getSourceFile(fileName));
}

// The return type admits `undefined`, so `strict` alone accepts the missing "c" path.
const PLANT = `
export function pick(kind: "a" | "b" | "c"): number | undefined {
  if (kind === "a") return 1;
  if (kind === "b") return 2;
}
`;

const CONTROL = `
export function pick(kind: "a" | "b" | "c"): number | undefined {
  if (kind === "a") return 1;
  if (kind === "b") return 2;
  return 3;
}
`;

test("0030 row 6: tsconfig.json enables noImplicitReturns", () => {
  assert.equal(compilerOptions().noImplicitReturns, true);
});

test("0030 row 6: a function that can fall off its end is refused with TS7030", () => {
  const codes = diagnosticsFor(PLANT).map((d) => d.code);
  assert.ok(codes.includes(7030), `expected TS7030 (not all code paths return a value), got [${codes.join(", ")}]`);
});

test("0030 row 6: the control, returning on every path, compiles clean", () => {
  const codes = diagnosticsFor(CONTROL).map((d) => d.code);
  assert.deepEqual(codes, []);
});
