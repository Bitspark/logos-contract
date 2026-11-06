/*
 * contract/ts's replay adapter for the per-assertion replay accounting (#2732 increment 2;
 * vectors/REPLAY-ACCOUNTING.md section 4). A vector replay calls observe() AFTER its assertion held,
 * so an observation means the assertion ran; a skipped or deleted assertion leaves a missing line,
 * which the central check reads.
 *
 * observe() appends one JSON line to the file LOGOS_REPLAY_LEDGER names, and does nothing when the
 * variable is unset, so a local run is unaffected. The target is this package's, never the caller's.
 * The line carries the vector file's sha256, so a receipt written against an older corpus cannot
 * satisfy the check (research 0025 row A20). What a valid line is, is decided once, by the central
 * check's schema (conformance/rs/src/replay_manifest.rs): this adapter only writes it.
 */

import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

/** The deployment contract/ts's replays run in (the manifest's `targets`). */
export const TARGET = "ts";

/** The statuses a line may carry. A skip satisfies no obligation unless the manifest authorizes it. */
export type Status = "passed" | "refused_as_expected";

const hashes = new Map<string, string>();

/** The repository's vectors/ directory: the first ancestor that holds vectors/replay_obligations.json. */
function vectorsDir(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const v = path.join(dir, "vectors");
    if (fs.existsSync(path.join(v, "replay_obligations.json"))) return v;
    const up = path.dirname(dir);
    if (up === dir) throw new Error(`replay_ledger: no vectors/replay_obligations.json above ${dir}`);
    dir = up;
  }
}

/** Record that the replay of vectors/<file>'s case `kase` held assertion `assertion`. */
export function observe(file: string, kase: string, assertion: string, status: Status): void {
  const ledger = process.env.LOGOS_REPLAY_LEDGER;
  if (ledger === undefined || ledger === "") return;
  let sum = hashes.get(file);
  if (sum === undefined) {
    sum = createHash("sha256").update(fs.readFileSync(path.join(vectorsDir(), file))).digest("hex");
    hashes.set(file, sum);
  }
  // One write per line: concurrent test processes append whole lines.
  const line = JSON.stringify({ file, case: kase, assertion, target: TARGET, status, file_sha256: sum });
  fs.appendFileSync(ledger, `${line}\n`);
}
