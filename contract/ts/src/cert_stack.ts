/**
 * #2258 (a): STACKED certificates. A sealed clause may read a predicate its own certificate does
 * not seal when a certificate at a STRICTLY LOWER scope level seals it: uniquely, exactly (not in
 * that certificate's `partialScope`, ADR 0030 D2), and Valid. The citing certificate then reads
 * that lower table: a negated literal is true iff the atom is absent from it, a positive literal
 * binds over its rows.
 *
 * Soundness rests on the order `verificationOrder` fixes: a certificate is verified only after
 * every certificate at a lower level, so a lower table is read only once its own support,
 * closure and EDB obligations have made it the exact least model of its predicate. References go
 * strictly down in level, so the citation graph is acyclic by construction, and an invalid
 * certificate nothing resolves against stays inert (seat:caa's C3 amendment). Mirrors rs
 * `check/cert_stack.rs`.
 */

import { decodeUtf8Lossy } from "./utf8.js";
import { type ClosedModelCert, type RelationTable } from "./cert.js";
import { type CertStatus } from "./cert_check.js";
import { type RejectionCode } from "./check.js";
import { SealContext } from "./fragment.js";
import { Symbol } from "./literal.js";
import { type Clause } from "./program.js";
import { type Theory } from "./spi.js";

/**
 * The order the certificates of a `closedWorld` are verified in: ascending scope level, ties by
 * index. Every certificate a cert at level `L` can resolve against sits at a level below `L`, so
 * its status is final before that cert is verified.
 */
export function verificationOrder(world: readonly ClosedModelCert[]): number[] {
  return world
    .map((_, i) => i)
    .sort((a, b) => world[a]!.scope.level - world[b]!.scope.level || a - b);
}

/** A certificate's world: the `closedWorld`, and the statuses computed so far (in level order). */
export interface CertWorld {
  readonly certs: readonly ClosedModelCert[];
  readonly status: readonly (CertStatus | undefined)[];
}

function symKey(pred: Symbol): string {
  return Array.from(pred.bytes(), (b) => b.toString(16).padStart(2, "0")).join("");
}

/**
 * One certificate's view of the tables its sealed clauses read: its OWN sealed tables, and each
 * predicate it reads from a strictly lower certificate, resolved to that certificate. The
 * closure join, the body-literal evaluation and the support gate all read tables through it.
 * Mirrors rs `CertView`.
 */
export class CertView {
  readonly cert: ClosedModelCert;
  readonly #lower: Map<string, { readonly index: number; readonly cert: ClosedModelCert }>;

  constructor(
    cert: ClosedModelCert,
    lower: Map<string, { readonly index: number; readonly cert: ClosedModelCert }> = new Map(),
  ) {
    this.cert = cert;
    this.#lower = lower;
  }

  /** The table a sealed clause reads for `pred`: the cert's own if it seals `pred`, else the resolved lower cert's. */
  table(pred: Symbol): RelationTable | undefined {
    if (this.cert.scope.seals(pred)) return this.cert.table(pred);
    return this.#lower.get(symKey(pred))?.cert.table(pred);
  }

  /**
   * The context this certificate's sealed clauses are classified in (#3067, research 0028 row A15):
   * the relations it seals, and the relations it reads from a strictly lower certificate. Mirrors rs
   * `CertView::seal_context`.
   */
  sealContext(): SealContext {
    const lower = Array.from(this.#lower.keys(), (hex) =>
      Symbol.of(Uint8Array.from(hex.match(/../g) ?? [], (byte) => parseInt(byte, 16))),
    );
    return new SealContext(this.cert.scope.predicates, lower);
  }

  /** True iff `pred` is read from a strictly lower certificate. */
  readsLower(pred: Symbol): boolean {
    return this.#lower.has(symKey(pred));
  }

  /** The `closedWorld` index of the lower certificate `pred` resolved to, if any. */
  lowerIndex(pred: Symbol): number | undefined {
    return this.#lower.get(symKey(pred))?.index;
  }
}

/**
 * Resolve every predicate the certificate at `own` reads without sealing it: a body literal of a
 * defining clause of one of its sealed predicates (a counted literal's relation included, #2258
 * L3.3b), on a predicate it does not seal and no theory owns. For each, the certificates at a strictly lower level that seal it: none leaves it
 * unresolved (the scope gate refuses the literal, as it always has); more than one is
 * `cert_scope_incomplete`, ambiguous (decided on structure alone); one sealing it partially is
 * `cert_scope_incomplete` (a lower bound read by a sealed clause makes that clause's closure, or
 * its negation, vacuous); one Invalid invalidates this cert with that certificate's own code, the
 * detail naming the chain; one exact and Valid resolves. Mirrors rs `resolve_lower_seals`.
 */
export function resolveLowerSeals(
  cert: ClosedModelCert,
  own: number,
  world: CertWorld,
  clauses: readonly Clause[],
  theory: Theory,
): { readonly view: CertView } | { readonly err: readonly [RejectionCode, string] } {
  const lower = new Map<string, { readonly index: number; readonly cert: ClosedModelCert }>();
  const name = (pred: Symbol): string => JSON.stringify(decodeUtf8Lossy(pred.bytes()));
  for (const clause of clauses) {
    if (!cert.scope.seals(clause.head.pred)) continue;
    for (const bl of clause.body) {
      // #2258 L3.3b: a count's counted predicate resolves like any other literal's, so a count
      // over a strictly lower seal is readable and the scope gate can admit it.
      const pred = bl.pred();
      if (cert.scope.seals(pred) || theory.owns(pred) || lower.has(symKey(pred))) continue;
      const sealers: number[] = [];
      world.certs.forEach((c, j) => {
        if (c.scope.level < cert.scope.level && c.scope.seals(pred)) sealers.push(j);
      });
      if (sealers.length === 0) continue;
      if (sealers.length > 1) {
        return {
          err: [
            "cert_scope_incomplete",
            `predicate ${name(pred)} is sealed by more than one strictly lower certificate (${sealers.join(", ")}); a stacked read needs a unique lower seal`,
          ],
        };
      }
      const j = sealers[0]!;
      const lowerCert = world.certs[j]!;
      if (lowerCert.isPartial(pred)) {
        return {
          err: [
            "cert_scope_incomplete",
            `certificate ${own} reads predicate ${name(pred)}, which certificate ${j} seals PARTIAL (a lower bound cannot be read by a sealed clause, ADR 0030 D2)`,
          ],
        };
      }
      const status = world.status[j];
      if (status === undefined) {
        // The verification order makes every lower status final first; a missing one is a
        // checker defect, refused rather than read as Valid.
        return {
          err: [
            "cert_scope_incomplete",
            `certificate ${own} would read predicate ${name(pred)} from certificate ${j} before it is verified`,
          ],
        };
      }
      if (status.kind === "invalid") {
        return {
          err: [
            status.code,
            `certificate ${own} rests on certificate ${j} for predicate ${name(pred)}, which is invalid: ${status.detail}`,
          ],
        };
      }
      lower.set(symKey(pred), { index: j, cert: lowerCert });
    }
  }
  return { view: new CertView(cert, lower) };
}
