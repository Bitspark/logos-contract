/*
 * logos-contract (TypeScript binding) — module barrel.
 *
 * A faithful, idiomatic-TS mirror of the Rust crate `contract/rs`, split
 * module-for-module to match the rs and go bindings (term · literal · program ·
 * reify · derivation · spi · check). It is the shared artifact between SEARCH and
 * CHECK:
 *
 *         SEARCH                         CHECK
 *   Program × Goal  ──evaluator──▶  Derivation  ──checker──▶  Accept | Reject
 *        (logos)                    (shared DTO)              (arche, logos, …)
 *
 * This binding depends only on ontos's frozen `Atom | Tuple` value model
 * (@bitspark/ontos-core); it contains NO engine. The modules:
 *   - §1   term.ts        — Term (Atom | Tuple | Var), Subst, VarId, ground/eraseGround/fromValue
 *   - §1.1 literal.ts     — Symbol, Goal, GroundLiteral
 *   - §2   program.ts     — Program, Clause, ClauseId, MapProgram
 *   - §2a  reify.ts       — quote, reify
 *   - §3   derivation.ts  — Derivation, Node {Rule, Builtin, Leaf}, NodeMeta, Evidence (opaque)
 *   - §5/§5a/§6 spi.ts    — Theory, RuleAdmissibility, LeafVerifier, PredicateSet
 *   - §4   check.ts       — check(), Outcome, RejectionCode (the 15 stable code strings)
 *
 * The rejection-code STRINGS and every vector outcome are byte-identical to Rust
 * — this is trust-critical parity code (it is what arche's BROWSER checker binds).
 *
 * Depends on the ontos value model by PACKAGE NAME (`@bitspark/ontos-core`), never
 * a repo-escaping source path — so a logos-only checkout (and CI) resolves it
 * through the package boundary, exactly as the Rust binding depends on ontos via a
 * git dependency. The dependency is declared once in package.json (see ADR 0004 D4
 * / the validation record for the {rs,ts,go} dependency story).
 */

// Re-export the ontos value model so consumers of logos-contract get one Value.
export { Atom, Tuple, type Value } from "@bitspark/ontos-core";

export * from "./term.js";
export * from "./utf8.js";
export * from "./literal.js";
export * from "./program.js";
export * from "./program_serde.js";
export * from "./reify.js";
export * from "./account.js";
export * from "./cert.js";
export * from "./answer_set.js";
export * from "./derivation.js";
export * from "./derivation_wire.js";
export * from "./cert_wire.js";
export * from "./spi.js";
export * from "./decval.js";
export * from "./arithmetic.js";
export * from "./text.js";
export * from "./term_theory.js";
export * from "./list_theory.js";
export * from "./compound.js";
export * from "./cert_check.js";
export * from "./fragment.js";
export * from "./check.js";
export * from "./prelude.js";
// The completion algebra (research 0031 row 15), PROPOSED: a namespace, since its not/and/or are
// generic names that would collide at the top level.
export * as completion from "./completion.js";
// Search-free checking for receiver-fixed typed statements (typed-check-only v1).
export * as typed from "./typed/index.js";
