#!/usr/bin/env node
// Refuse any `*.test.ts` under `src/` (#1432, a form-33 instance).
//
// WHY THIS EXISTS. `tsconfig.json` sets `rootDir: "."` and includes both `src/**` and
// `test/**`, so a test authored beside its subject compiles to `dist/src/…` — while the
// test runner's glob is `dist/test/*.test.js`. The file therefore:
//
//   * type-checks,
//   * passes when a human runs it by hand,
//   * and is NEVER EXECUTED BY CI.
//
// That is the form-33 shape exactly: a gate whose PASS is compatible with the thing not
// existing. `npm test` goes green having run one fewer file than anyone believes, and
// nothing anywhere says so — the count is not printed and the absence has no error to grep.
//
// The convention ("tests live in test/") was previously enforced by remembering it. This
// makes it enforced by construction. Dependency-free on purpose: a guard that needs an
// install is a guard that gets skipped in the environment that most needs it.
//
// ⚠ It answers PLACEMENT, not coverage — a test in `test/` that no glob matches is a
// different defect and this does not reach it.

import { readdirSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const pkgRoot = fileURLToPath(new URL('..', import.meta.url));
const srcRoot = join(pkgRoot, 'src');

/** Every `*.test.ts` at any depth under `src/`, or [] when `src/` does not exist. */
function offenders(dir) {
  let found = [];
  let entries;
  try {
    entries = readdirSync(dir, { withFileTypes: true });
  } catch {
    return found; // no src/ — nothing to police, not an error
  }
  for (const e of entries) {
    const p = join(dir, e.name);
    // Follow the dirent, but fall back to stat for symlinks so a linked dir is still walked.
    const isDir = e.isDirectory() || (e.isSymbolicLink() && safeIsDir(p));
    if (isDir) {
      if (e.name === 'node_modules' || e.name === 'dist') continue;
      found = found.concat(offenders(p));
    } else if (/\.test\.ts$/.test(e.name)) {
      found.push(p);
    }
  }
  return found;
}

function safeIsDir(p) {
  try {
    return statSync(p).isDirectory();
  } catch {
    return false;
  }
}

const bad = offenders(srcRoot);
if (bad.length > 0) {
  const list = bad.map((p) => `  ${relative(pkgRoot, p).replace(/\\/g, '/')}`).join('\n');
  process.stderr.write(
    `test-placement: ${bad.length} test file(s) under src/ — these NEVER RUN in CI.\n` +
      `${list}\n\n` +
      `  tsconfig rootDir is "." and includes src/** , so these compile to dist/src/… ,\n` +
      `  while the test glob is dist/test/*.test.js — which never looks there. They\n` +
      `  type-check and pass by hand, and CI silently runs one fewer file (#1432).\n\n` +
      `  Move them to test/ , which is where this package's tests live.\n`,
  );
  process.exit(1);
}
