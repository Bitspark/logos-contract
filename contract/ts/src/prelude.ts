/*
 * Shelf-B prelude loader — the hash-pinned Horn-clause standard library. [STABLE v1]
 * TS sibling of contract/rs/src/prelude.rs and contract/go/prelude.go.
 *
 * ADR 0016 sorts every predefined predicate onto one of three shelves by the question
 * "what must be trusted to admit its result?". Shelf B is the answer "nothing new": a
 * relation derivable as ordinary Rule | Builtin | Leaf derivations over the Shelf-A
 * primitives lives here as CURATED DATA, not a package — an array of clauses with a
 * pinned program_digest, re-checked everywhere by the existing check as plain Rule
 * nodes. Zero new trusted code: this module adds no checker logic and no account node
 * kind; it only LOADS clauses the engine and checker already understand.
 *
 * The trust anchor is DIGEST RE-DERIVATION, not the JSON parser. loadPrelude
 * deserializes a manifest, then RECOMPUTES the program_digest over the deserialized
 * clauses using the frozen account codec (clauseBytes -> programDigest) and REJECTS any
 * mismatch. A bundle whose pinned digest does not equal the digest of its own clauses
 * is refused, so a corrupted or tampered manifest can never load. The frozen ontos-codec
 * + syntactic VarId make the digest BYTE-IDENTICAL across {rs,go,ts}, so this TS loader
 * recomputes the same hex and refuses the same mismatched bundles as the Rust loader
 * (replayed against the shared vectors/prelude.json).
 *
 * Manifest shape (prelude/<name>@<version>.json):
 *
 *   {
 *     "name": "sample",
 *     "version": "1.0.0",
 *     "program_digest": "<64-hex sha-256>",
 *     "clauses": [
 *       { "id": "<ClauseId>", "clause": { "head": <goal>, "body": [<body-lit>, ...] } }
 *     ]
 *   }
 *
 * where a term is {"atom":"<hex>"} | {"atom_str":"<utf8>"} | {"tuple":[term…]} |
 * {"var":"<id>"}, a goal is {"pred":"<utf8>", "args":[term…]}, and a body literal is a
 * positive goal or a negated {"neg":<goal>} (ADR 0007) — exactly the notation of
 * vectors/account.json. id is optional; when present it must equal the recomputed
 * canonicalClauseId of the clause.
 */

import { bundleDigest, canonicalClauseId } from "./account.js";
import { decodeHexPairs } from "./hex.js";
import { Goal, Symbol } from "./literal.js";
import { BodyLit, Clause, ClauseId, MapProgram } from "./program.js";
import { reservedPredicateOf } from "./program_serde.js";
import { Term } from "./term.js";
import { wellFormedUtf16 } from "./utf8.js";

/**
 * A loaded, DIGEST-VERIFIED Shelf-B prelude bundle. Its clauses are ordinary account
 * Rule nodes; merge them into a program (`program` / `mergeInto`) and the existing
 * `check` verifies them with no new trusted code. TS sibling of Rust's `PreludeBundle`.
 */
export interface PreludeBundle {
  /** The bundle name (e.g. "lists"), the name of prelude/<name>@<version>.json. */
  readonly name: string;
  /** The bundle version (e.g. "1.0.0") — Shelf B is byte-frozen per (name@version). */
  readonly version: string;
  /** The pinned, recomputed-and-verified canonical program digest (64-char lowercase hex). */
  readonly programDigest: string;
  /** The bundle's clauses, in manifest order, each with its (verified) canonical id. */
  readonly clauses: readonly PreludeClause[];
}

/** A clause paired with its verified canonical id (manifest order). */
export interface PreludeClause {
  readonly id: ClauseId;
  readonly clause: Clause;
}

/**
 * The bundle as a standalone `MapProgram` — the prelude clauses keyed by id, ready to
 * hand to an engine or `check`. (`MapProgram` is order-independent; the DIGEST is what
 * commits to the exact clause set.)
 */
export function preludeProgram(bundle: PreludeBundle): MapProgram {
  const program = new MapProgram();
  for (const { id, clause } of bundle.clauses) {
    program.insert(id, clause);
  }
  return program;
}

/**
 * ADR-0016 PROGRAM-PREPEND: return a new `MapProgram` containing the bundle's clauses
 * PLUS every clause in `extra` (keyed by id), so a consumer program is checked together
 * with the standard library. A consumer clause sharing a prelude id (the canonical hash
 * collides ⇒ the clauses are identical) is a harmless overwrite. The engine and checker
 * see one clause set; the prelude relations resolve as ordinary Rule nodes. (TS's
 * `Program` interface exposes only `clause(id)` lookup, so the caller passes the consumer
 * clauses explicitly — mirroring Rust's `merge_into` over a `Program`'s `for_each_clause`.)
 */
export function preludeMergeInto(bundle: PreludeBundle, extra: readonly PreludeClause[]): MapProgram {
  const merged = preludeProgram(bundle);
  for (const { id, clause } of extra) {
    merged.insert(id, clause);
  }
  return merged;
}

/**
 * The cross-core error variant tag — byte-identical to the Rust `PreludeError` variant
 * strings and the `{"err": "<variant>"}` field of vectors/prelude.json.
 */
export type PreludeErrorKind =
  | "malformed"
  | "bad_clause"
  | "clause_id_mismatch"
  | "duplicate_clause_id"
  | "digest_mismatch"
  | "empty";

/**
 * A refusal to trust — a bundle that does not load is never silently accepted. TS
 * sibling of Rust's `PreludeError` enum. `kind` is the only normative (vector-pinned)
 * field; `index`/`declared`/`recomputed`/`detail` are diagnostic.
 */
export class PreludeError extends Error {
  readonly kind: PreludeErrorKind;
  readonly index: number | undefined;
  readonly declared: string | undefined;
  readonly recomputed: string | undefined;

  constructor(
    kind: PreludeErrorKind,
    message: string,
    extra?: { index?: number; declared?: string; recomputed?: string },
  ) {
    super(message);
    this.name = "PreludeError";
    this.kind = kind;
    this.index = extra?.index;
    this.declared = extra?.declared;
    this.recomputed = extra?.recomputed;
  }
}

function malformed(detail: string): PreludeError {
  return new PreludeError("malformed", `malformed prelude manifest: ${detail}`);
}

/** Whether every string in a parsed JSON value, keys included, is well-formed UTF-16 (#2233). */
function everyStringWellFormed(value: unknown): boolean {
  if (typeof value === "string") return wellFormedUtf16(value);
  if (Array.isArray(value)) return value.every(everyStringWellFormed);
  if (value !== null && typeof value === "object") {
    return Object.entries(value).every(([key, item]) => wellFormedUtf16(key) && everyStringWellFormed(item));
  }
  return true;
}

function badClause(index: number, reason: string): PreludeError {
  return new PreludeError("bad_clause", `clause[${index}] is malformed: ${reason}`, { index });
}

type Json = Record<string, unknown>;

function isObject(v: unknown): v is Json {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

/**
 * Load a Shelf-B prelude manifest, VERIFYING its pinned `program_digest` against the
 * digest recomputed over the deserialized clauses.
 *
 * On success the returned `PreludeBundle` is guaranteed: non-empty; free of duplicate
 * canonical clause ids; every present per-clause `id` equals the recomputed
 * `canonicalClauseId`; and `programDigest` equals `bundleDigest` over the bundle's
 * clauses (the tamper anchor).
 *
 * The JSON parser is NOT the trust boundary, but the digest is recomputed over the DECODED
 * clauses, so it cannot see a parse that silently decodes the wrong ones (#2233). A lone UTF-16
 * surrogate, in the text or produced by a `\u` escape, becomes U+FFFD once a name is encoded, so
 * two distinct authored names would load as one. Rust's loader rejects it, and a parse may only
 * ever REJECT a bundle, so it is refused here.
 * Throws a `PreludeError` on any refusal. Mirrors Rust's `load_prelude`.
 */
export function loadPrelude(json: string): PreludeBundle {
  if (!wellFormedUtf16(json)) {
    throw malformed("the document contains a lone UTF-16 surrogate");
  }
  let root: unknown;
  try {
    root = JSON.parse(json);
  } catch (e) {
    throw malformed(e instanceof Error ? e.message : String(e));
  }
  if (!everyStringWellFormed(root)) {
    throw malformed("a string decodes to a lone UTF-16 surrogate (a \\u escape)");
  }
  if (!isObject(root)) {
    throw malformed("top level is not a JSON object");
  }

  const name = stringField(root, "name");
  const version = stringField(root, "version");
  const declaredDigest = stringField(root, "program_digest");

  const clausesRaw = root["clauses"];
  if (clausesRaw === undefined) {
    throw malformed("missing field `clauses`");
  }
  if (!Array.isArray(clausesRaw)) {
    throw malformed("field `clauses` is not an array");
  }
  if (clausesRaw.length === 0) {
    throw new PreludeError("empty", "prelude bundle has no clauses");
  }

  const clauses: PreludeClause[] = [];
  const seen = new Set<string>();
  for (let index = 0; index < clausesRaw.length; index += 1) {
    const entry = clausesRaw[index];
    const { clause, declaredId } = parseClauseEntry(index, entry);
    // #2247: a reserved predicate reads exactly like a tagged literal, so it would share that
    // literal's id and the bundle's digest. Refused here, BEFORE the digest check, since a digest
    // match is exactly what such a clause would pass.
    const reserved = reservedPredicateOf(clause);
    if (reserved !== undefined) {
      throw badClause(
        index,
        `reserved predicate symbol 0x${[...reserved].map((b) => b.toString(16).padStart(2, "0")).join("")} (an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)`,
      );
    }
    const id = canonicalClauseId(clause);
    // If the manifest pins a per-clause id, it must equal the recomputed canonical id.
    if (declaredId !== undefined && declaredId !== id.asStr()) {
      throw new PreludeError(
        "clause_id_mismatch",
        `clause[${index}] id mismatch: declared ${declaredId}, recomputed ${id.asStr()}`,
        { index, declared: declaredId, recomputed: id.asStr() },
      );
    }
    if (seen.has(id.asStr())) {
      throw new PreludeError("duplicate_clause_id", `duplicate clause id ${id.asStr()}`, {
        declared: id.asStr(),
      });
    }
    seen.add(id.asStr());
    clauses.push({ id, clause });
  }

  // Recompute the canonical program digest over the deserialized clauses (the tamper
  // anchor) and refuse a mismatch. The SAME digest definition the checker uses (ADR 0007
  // §3.1) hashes the bundle — one digest definition, no drift.
  const recomputed = bundleDigest(clauses.map((c) => c.clause));
  if (recomputed !== declaredDigest) {
    throw new PreludeError(
      "digest_mismatch",
      `program_digest mismatch: declared ${declaredDigest}, recomputed ${recomputed}`,
      { declared: declaredDigest, recomputed },
    );
  }

  return { name, version, programDigest: recomputed, clauses };
}

function stringField(obj: Json, key: string): string {
  const v = obj[key];
  if (v === undefined) {
    throw malformed(`missing field \`${key}\``);
  }
  if (typeof v !== "string") {
    throw malformed(`field \`${key}\` is not a string`);
  }
  return v;
}

/**
 * Parse one `{ "id"?, "clause": { head, body } }` wrapper (or a bare `{ head, body }`
 * object) into a `Clause`, returning the clause + the declared id (if present).
 */
function parseClauseEntry(index: number, entry: unknown): { clause: Clause; declaredId: string | undefined } {
  if (!isObject(entry)) {
    throw badClause(index, "clause entry is not an object");
  }
  // The clause object is either the nested `clause` field or the bare entry itself.
  const clauseObj = "clause" in entry ? entry["clause"] : entry;
  const clause = parseClause(index, clauseObj);

  let declaredId: string | undefined;
  if ("id" in entry && entry["id"] !== undefined) {
    if (typeof entry["id"] !== "string") {
      throw badClause(index, "`id` is not a string");
    }
    declaredId = entry["id"];
  }
  return { clause, declaredId };
}

/** Parse a `{ "head": <goal>, "body": [<body-lit>…] }` into a `Clause`. */
function parseClause(index: number, raw: unknown): Clause {
  if (!isObject(raw)) {
    throw badClause(index, "clause is not an object");
  }
  if (!("head" in raw)) {
    throw badClause(index, "missing `head`");
  }
  const head = parseGoal(index, raw["head"]);
  const bodyRaw = raw["body"];
  const body: BodyLit[] = [];
  if (bodyRaw !== undefined) {
    if (!Array.isArray(bodyRaw)) {
      throw badClause(index, "`body` is not an array");
    }
    for (const lit of bodyRaw) {
      body.push(parseBodyLit(index, lit));
    }
  }
  return new Clause(head, body);
}

/** Parse a `{ "pred": "<utf8>", "args": [term…] }` goal. */
function parseGoal(index: number, raw: unknown): Goal {
  if (!isObject(raw)) {
    throw badClause(index, "goal is not an object");
  }
  if (typeof raw["pred"] !== "string") {
    throw badClause(index, "goal missing string `pred`");
  }
  const argsRaw = raw["args"];
  const args: Term[] = [];
  if (argsRaw !== undefined) {
    if (!Array.isArray(argsRaw)) {
      throw badClause(index, "goal `args` is not an array");
    }
    for (const a of argsRaw) {
      args.push(parseTerm(index, a));
    }
  }
  return Goal.of(Symbol.of(raw["pred"]), args);
}

/** Parse a positive goal or a negated `{ "neg": <goal> }` body literal (ADR 0007). */
function parseBodyLit(index: number, raw: unknown): BodyLit {
  if (isObject(raw) && "neg" in raw) {
    return BodyLit.neg(parseGoal(index, raw["neg"]));
  }
  return BodyLit.pos(parseGoal(index, raw));
}

/**
 * Parse a term: `{"atom":"<hex>"} | {"atom_str":"<utf8>"} | {"tuple":[term…]} |
 * {"var":"<id>"}` — the vectors/account.json notation.
 */
function parseTerm(index: number, raw: unknown): Term {
  if (!isObject(raw)) {
    throw badClause(index, `term is not an object: ${JSON.stringify(raw)}`);
  }
  if ("atom" in raw) {
    if (typeof raw["atom"] !== "string") {
      throw badClause(index, "`atom` is not a string");
    }
    return Term.atom(decodeAtomHex(index, raw["atom"]));
  }
  if ("atom_str" in raw) {
    if (typeof raw["atom_str"] !== "string") {
      throw badClause(index, "`atom_str` is not a string");
    }
    return Term.atom(new TextEncoder().encode(raw["atom_str"]));
  }
  if ("var" in raw) {
    if (typeof raw["var"] !== "string") {
      throw badClause(index, "`var` is not a string");
    }
    return Term.var(raw["var"]);
  }
  if ("tuple" in raw) {
    if (!Array.isArray(raw["tuple"])) {
      throw badClause(index, "`tuple` is not an array");
    }
    return Term.tuple(raw["tuple"].map((c) => parseTerm(index, c)));
  }
  throw badClause(index, `unrecognized term shape: ${JSON.stringify(raw)}`);
}

function decodeAtomHex(index: number, hex: string): Uint8Array {
  if (hex.length % 2 !== 0) {
    throw badClause(index, `odd-length hex string: ${JSON.stringify(hex)}`);
  }
  const bytes = decodeHexPairs(hex, "mixed");
  if (bytes === undefined) {
    throw badClause(index, `non-hex characters in ${JSON.stringify(hex)}`);
  }
  return bytes;
}
