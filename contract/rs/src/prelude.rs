//! Shelf-B prelude loader — the hash-pinned Horn-clause standard library. **[STABLE v1]**
//!
//! ADR 0016 sorts every predefined predicate onto one of three shelves by the question
//! *"what must be trusted to admit its result?"*. **Shelf B** is the answer *"nothing new"*:
//! a relation that is derivable as ordinary `Rule | Builtin | Leaf` derivations over the
//! Shelf-A primitives goes here as **curated data, not a crate** — an array of clauses with
//! a pinned `program_digest`, re-checked everywhere by the *existing* [`check`](crate::check)
//! as plain `Rule` nodes. **Zero new trusted code**: this module adds no checker logic and no
//! account node kind; it only *loads* clauses the engine and checker already understand.
//!
//! ## What this module is (and is not)
//!
//! The trust anchor is **digest re-derivation**, not the JSON parser. [`load_prelude`]
//! deserializes a manifest, then **recomputes** the `program_digest` over the deserialized
//! clauses using the frozen account codec ([`crate::account::clause_bytes`] →
//! [`crate::program_digest`]) and **rejects any mismatch**. A bundle whose pinned digest does
//! not equal the digest of its own clauses is refused, so a corrupted or tampered manifest
//! can never load — exactly the Coq-stdlib / proof-carrying-code discipline ADR 0016 names
//! (the kernel re-checks untrusted library material). The frozen `ontos-codec` + syntactic
//! `VarId` make the digest **byte-identical across {rs,go,ts}**, so a Go/TS loader mirror
//! recomputes the same hex and refuses the same mismatched bundles.
//!
//! ## Wiring — program-prepend, not a `CheckProfile` field
//!
//! A loaded bundle's clauses are simply **merged into the program** the engine and checker
//! see ([`PreludeBundle::program`] / [`PreludeBundle::merge_into`]). They are then verified as
//! ordinary `Rule` nodes by the unchanged [`check`](crate::check::check) — **no new field on
//! the tri-core [`CheckProfile`](crate::check::CheckProfile) and no new check logic**. The
//! frozen account grammar (ADR 0001) is untouched: Shelf B = `Rule` nodes, period.
//!
//! ## Manifest shape (`prelude/<name>@<version>.json`)
//!
//! ```json
//! {
//!   "name": "sample",
//!   "version": "1.0.0",
//!   "program_digest": "<64-hex sha-256>",
//!   "clauses": [
//!     { "id": "<ClauseId>", "clause": { "head": <goal>, "body": [<body-lit>, ...] } }
//!   ]
//! }
//! ```
//!
//! where a `term` is `{ "atom": "<hex>" } | { "atom_str": "<utf8>" } | { "tuple": [term…] }
//! | { "var": "<id>" }`, a `goal` is `{ "pred": "<utf8>", "args": [term…] }`, and a body
//! literal is a positive `goal` or a negated `{ "neg": <goal> }` (ADR 0007) — exactly the
//! notation of `vectors/account.json`. `id` is optional; when present it must equal the
//! recomputed [`ClauseId::canonical`](crate::ClauseId::canonical) of the clause.

use crate::account::clause_bytes;
use crate::check::program_digest;
use crate::literal::{Goal, Symbol};
use crate::program::{BodyLit, Clause, ClauseId, CompleteProgram, MapProgram};
use crate::term::Term;
use serde_json::Value as Json;
use std::collections::BTreeSet;

/// A loaded, **digest-verified** Shelf-B prelude bundle. Its clauses are ordinary account
/// `Rule` nodes; merge them into a program ([`Self::program`] / [`Self::merge_into`]) and the
/// existing [`check`](crate::check::check) verifies them with no new trusted code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreludeBundle {
    /// The bundle name (e.g. `"lists"`), the `name` of `prelude/<name>@<version>.json`.
    pub name: String,
    /// The bundle version (e.g. `"1.0.0"`) — Shelf B is byte-frozen per `(name@version)`.
    pub version: String,
    /// The pinned, recomputed-and-verified canonical program digest (64-char lowercase hex).
    pub program_digest: String,
    /// The bundle's clauses, in manifest order, each with its (verified) canonical id.
    pub clauses: Vec<(ClauseId, Clause)>,
}

impl PreludeBundle {
    /// The bundle as a standalone [`MapProgram`] — the prelude clauses keyed by id, ready to
    /// hand to an engine or `check`. (`MapProgram` is order-independent; the *digest* is what
    /// commits to the exact clause set.)
    pub fn program(&self) -> MapProgram {
        let mut program = MapProgram::new();
        for (id, clause) in &self.clauses {
            program.insert(id.clone(), clause.clone());
        }
        program
    }

    /// **Program-prepend** (ADR 0016): return a new [`MapProgram`] containing this bundle's
    /// clauses *plus* every clause of `target`, so a consumer program is checked together
    /// with the standard library. The bundle's clauses are inserted first; a `target` clause
    /// sharing a prelude id (the canonical hash collides ⇒ the clauses are identical) is a
    /// harmless no-op. Returns the merged program — the engine and checker see one clause set,
    /// and the prelude relations resolve as ordinary `Rule` nodes.
    pub fn merge_into(&self, target: &MapProgram) -> MapProgram {
        let mut merged = self.program();
        target.for_each_clause(&mut |id, clause| {
            merged.insert(id.clone(), clause.clone());
        });
        merged
    }
}

/// Why a manifest failed to load. Every variant is a *refusal to trust* — a bundle that does
/// not load is never silently accepted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreludeError {
    /// The manifest is not valid JSON, or a required field is missing / mistyped.
    Malformed(String),
    /// A clause could not be deserialized from the account-codec term form.
    BadClause { index: usize, reason: String },
    /// A per-clause `id` was present but did not equal the recomputed `ClauseId::canonical`.
    ClauseIdMismatch {
        index: usize,
        declared: String,
        recomputed: String,
    },
    /// Two clauses share the same canonical id (a duplicate clause in the bundle).
    DuplicateClauseId(String),
    /// The recomputed `program_digest` did not match the manifest's pinned `program_digest`
    /// — the load-bearing tamper check.
    DigestMismatch {
        declared: String,
        recomputed: String,
    },
    /// The bundle declared no clauses (an empty prelude is rejected — a prelude with nothing
    /// in it is almost certainly an authoring error, and its digest is degenerate).
    Empty,
}

impl std::fmt::Display for PreludeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreludeError::Malformed(m) => write!(f, "malformed prelude manifest: {m}"),
            PreludeError::BadClause { index, reason } => {
                write!(f, "clause[{index}] is malformed: {reason}")
            }
            PreludeError::ClauseIdMismatch {
                index,
                declared,
                recomputed,
            } => write!(
                f,
                "clause[{index}] id mismatch: declared {declared}, recomputed {recomputed}"
            ),
            PreludeError::DuplicateClauseId(id) => write!(f, "duplicate clause id {id}"),
            PreludeError::DigestMismatch {
                declared,
                recomputed,
            } => write!(
                f,
                "program_digest mismatch: declared {declared}, recomputed {recomputed}"
            ),
            PreludeError::Empty => write!(f, "prelude bundle has no clauses"),
        }
    }
}

impl std::error::Error for PreludeError {}

/// Load a Shelf-B prelude manifest, **verifying its pinned `program_digest`** against the
/// digest recomputed over the deserialized clauses.
///
/// On success the returned [`PreludeBundle`] is guaranteed:
/// * non-empty;
/// * free of duplicate canonical clause ids;
/// * every present per-clause `id` equals the recomputed [`ClauseId::canonical`];
/// * `program_digest` equals [`program_digest`](crate::program_digest) over the bundle's
///   clauses (the tamper anchor).
///
/// The JSON parser is *not* the trust boundary: even a buggy parse that produced the wrong
/// clauses would change the recomputed digest and be rejected by [`PreludeError::DigestMismatch`].
pub fn load_prelude(json: &str) -> Result<PreludeBundle, PreludeError> {
    let root: Json =
        serde_json::from_str(json).map_err(|e| PreludeError::Malformed(e.to_string()))?;
    let obj = root
        .as_object()
        .ok_or_else(|| PreludeError::Malformed("top level is not a JSON object".into()))?;

    let name = string_field(obj, "name")?;
    let version = string_field(obj, "version")?;
    let declared_digest = string_field(obj, "program_digest")?;

    let clauses_json = obj
        .get("clauses")
        .ok_or_else(|| PreludeError::Malformed("missing field `clauses`".into()))?
        .as_array()
        .ok_or_else(|| PreludeError::Malformed("field `clauses` is not an array".into()))?;

    if clauses_json.is_empty() {
        return Err(PreludeError::Empty);
    }

    let mut clauses: Vec<(ClauseId, Clause)> = Vec::with_capacity(clauses_json.len());
    let mut seen: BTreeSet<ClauseId> = BTreeSet::new();
    for (index, entry) in clauses_json.iter().enumerate() {
        let clause = parse_clause(index, entry)?;
        // #2247: a reserved predicate reads exactly like a tagged literal, so it would share that
        // literal's id and the bundle's digest. Refused here, BEFORE the digest check, since a
        // digest match is exactly what such a clause would pass.
        if let Some(pred) = crate::program_serde::reserved_predicate(&clause) {
            return Err(PreludeError::BadClause {
                index,
                reason: format!(
                    "reserved predicate symbol 0x{} (an account tag byte, 0x00 negation or 0x01 count, is not a valid predicate name)",
                    to_hex(pred)
                ),
            });
        }
        let id = ClauseId::canonical(&clause);
        // If the manifest pins a per-clause id, it must equal the recomputed canonical id.
        if let Some(declared_id) = entry.get("id") {
            let declared_id = declared_id
                .as_str()
                .ok_or_else(|| PreludeError::BadClause {
                    index,
                    reason: "`id` is not a string".into(),
                })?;
            if declared_id != id.as_str() {
                return Err(PreludeError::ClauseIdMismatch {
                    index,
                    declared: declared_id.to_string(),
                    recomputed: id.as_str().to_string(),
                });
            }
        }
        if !seen.insert(id.clone()) {
            return Err(PreludeError::DuplicateClauseId(id.as_str().to_string()));
        }
        clauses.push((id, clause));
    }

    // Recompute the canonical program digest over the deserialized clauses (the tamper
    // anchor) and refuse a mismatch. Build a MapProgram so the SAME `program_digest` the
    // checker uses (ADR 0007 §3.1) hashes the bundle — one digest definition, no drift.
    let mut program = MapProgram::new();
    for (id, clause) in &clauses {
        program.insert(id.clone(), clause.clone());
    }
    let recomputed = to_hex(&program_digest(&program));
    if recomputed != declared_digest {
        return Err(PreludeError::DigestMismatch {
            declared: declared_digest,
            recomputed,
        });
    }

    Ok(PreludeBundle {
        name,
        version,
        program_digest: recomputed,
        clauses,
    })
}

fn string_field(obj: &serde_json::Map<String, Json>, key: &str) -> Result<String, PreludeError> {
    obj.get(key)
        .ok_or_else(|| PreludeError::Malformed(format!("missing field `{key}`")))?
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| PreludeError::Malformed(format!("field `{key}` is not a string")))
}

/// Parse one `{ "head": <goal>, "body": [<body-lit>…] }` (or a bare `{ "id", "clause" }`
/// wrapper) into a [`Clause`].
fn parse_clause(index: usize, entry: &Json) -> Result<Clause, PreludeError> {
    let bad = |reason: String| PreludeError::BadClause { index, reason };
    // Accept either the wrapped form `{ "id"?, "clause": { head, body } }` or the bare
    // `{ "head", "body" }` form (the wrapper is the manifest schema; the bare form keeps the
    // loader usable on a raw clause object).
    let clause_obj = match entry.get("clause") {
        Some(c) => c,
        None => entry,
    };
    let head_json = clause_obj
        .get("head")
        .ok_or_else(|| bad("missing `head`".into()))?;
    let head = parse_goal(index, head_json)?;
    let body_json = clause_obj
        .get("body")
        .map(|b| {
            b.as_array()
                .ok_or_else(|| bad("`body` is not an array".into()))
        })
        .transpose()?
        .map(|v| v.as_slice())
        .unwrap_or(&[]);
    let mut body: Vec<BodyLit<Term>> = Vec::with_capacity(body_json.len());
    for lit in body_json {
        body.push(parse_body_lit(index, lit)?);
    }
    Ok(Clause { head, body })
}

/// Parse a `{ "pred": "<utf8>", "args": [term…] }` goal.
fn parse_goal(index: usize, goal: &Json) -> Result<Goal, PreludeError> {
    let bad = |reason: String| PreludeError::BadClause { index, reason };
    let pred = goal
        .get("pred")
        .and_then(Json::as_str)
        .ok_or_else(|| bad("goal missing string `pred`".into()))?;
    let args_json = goal
        .get("args")
        .map(|a| {
            a.as_array()
                .ok_or_else(|| bad("goal `args` is not an array".into()))
        })
        .transpose()?
        .map(|v| v.as_slice())
        .unwrap_or(&[]);
    let mut args = Vec::with_capacity(args_json.len());
    for a in args_json {
        args.push(parse_term(index, a)?);
    }
    Ok(Goal {
        pred: Symbol::new(pred.as_bytes().to_vec()),
        args,
    })
}

/// Parse a positive `goal` or a negated `{ "neg": <goal> }` body literal (ADR 0007).
fn parse_body_lit(index: usize, lit: &Json) -> Result<BodyLit<Term>, PreludeError> {
    if let Some(neg) = lit.get("neg") {
        Ok(BodyLit::Neg(parse_goal(index, neg)?))
    } else {
        Ok(BodyLit::Pos(parse_goal(index, lit)?))
    }
}

/// Parse a term: `{ "atom": "<hex>" } | { "atom_str": "<utf8>" } | { "tuple": [term…] }
/// | { "var": "<id>" }` — the `vectors/account.json` notation.
fn parse_term(index: usize, term: &Json) -> Result<Term, PreludeError> {
    let bad = |reason: String| PreludeError::BadClause { index, reason };
    let obj = term
        .as_object()
        .ok_or_else(|| bad(format!("term is not an object: {term}")))?;
    if let Some(hex) = obj.get("atom") {
        let hex = hex
            .as_str()
            .ok_or_else(|| bad("`atom` is not a string".into()))?;
        return Ok(Term::Atom(decode_hex(hex).map_err(bad)?));
    }
    if let Some(s) = obj.get("atom_str") {
        let s = s
            .as_str()
            .ok_or_else(|| bad("`atom_str` is not a string".into()))?;
        return Ok(Term::Atom(s.as_bytes().to_vec()));
    }
    if let Some(var) = obj.get("var") {
        let var = var
            .as_str()
            .ok_or_else(|| bad("`var` is not a string".into()))?;
        return Ok(Term::var(var));
    }
    if let Some(children) = obj.get("tuple") {
        let children = children
            .as_array()
            .ok_or_else(|| bad("`tuple` is not an array".into()))?;
        let mut out = Vec::with_capacity(children.len());
        for c in children {
            out.push(parse_term(index, c)?);
        }
        return Ok(Term::Tuple(out));
    }
    Err(bad(format!("unrecognized term shape: {term}")))
}

fn decode_hex(hex: &str) -> Result<Vec<u8>, String> {
    if !hex.len().is_multiple_of(2) {
        return Err(format!("odd-length hex string: {hex:?}"));
    }
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    let nibble = |c: u8| -> Result<u8, String> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            b'A'..=b'F' => Ok(c - b'A' + 10),
            _ => Err(format!("non-hex character {:?}", c as char)),
        }
    };
    for pair in bytes.chunks(2) {
        out.push((nibble(pair[0])? << 4) | nibble(pair[1])?);
    }
    Ok(out)
}

/// Lowercase-hex of a 32-byte digest (mirrors the account codec's private `to_hex`).
fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

/// The canonical `program_digest` (lowercase hex) of a set of clauses — the value a manifest
/// pins. Exposed so a prelude *generator* can author the `program_digest` field from the same
/// computation the loader verifies against (one digest definition, no drift).
pub fn bundle_digest(clauses: &[(ClauseId, Clause)]) -> String {
    let mut program = MapProgram::new();
    for (id, clause) in clauses {
        program.insert(id.clone(), clause.clone());
    }
    to_hex(&program_digest(&program))
}

/// The canonical bytes of a single clause (re-export of the frozen account codec) — used by a
/// generator that builds a manifest's per-clause `id` from the same encoding the loader hashes.
pub fn canonical_clause_bytes(clause: &Clause) -> Vec<u8> {
    clause_bytes(clause)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    /// `nat(z).` and `nat(s(X)) :- nat(X).` — the sample bundle, built in Rust so the test is
    /// independent of the on-disk manifest.
    fn sample_clauses() -> Vec<Clause> {
        let nat_z = Clause::fact(Goal::new("nat", [Term::tuple([Term::atom(*b"z")])]));
        let nat_s = Clause::new(
            Goal::new("nat", [Term::tuple([Term::atom(*b"s"), Term::var("X")])]),
            [Goal::new("nat", [Term::var("X")])],
        );
        vec![nat_z, nat_s]
    }

    fn sample_manifest(digest: &str) -> String {
        format!(
            r#"{{
              "name": "sample",
              "version": "1.0.0",
              "program_digest": "{digest}",
              "clauses": [
                {{ "clause": {{ "head": {{ "pred": "nat", "args": [{{ "tuple": [{{ "atom_str": "z" }}] }}] }}, "body": [] }} }},
                {{ "clause": {{ "head": {{ "pred": "nat", "args": [{{ "tuple": [{{ "atom_str": "s" }}, {{ "var": "X" }}] }}] }}, "body": [{{ "pred": "nat", "args": [{{ "var": "X" }}] }}] }} }}
              ]
            }}"#
        )
    }

    fn sample_digest() -> String {
        let clauses: Vec<(ClauseId, Clause)> = sample_clauses()
            .into_iter()
            .map(|c| (ClauseId::canonical(&c), c))
            .collect();
        bundle_digest(&clauses)
    }

    #[test]
    fn loads_a_valid_bundle() {
        let digest = sample_digest();
        let bundle = load_prelude(&sample_manifest(&digest)).expect("valid bundle loads");
        assert_eq!(bundle.name, "sample");
        assert_eq!(bundle.version, "1.0.0");
        assert_eq!(bundle.program_digest, digest);
        assert_eq!(bundle.clauses.len(), 2);
        // The deserialized clauses round-trip to the Rust-built clauses.
        let want = sample_clauses();
        for (got, want) in bundle.clauses.iter().map(|(_, c)| c).zip(&want) {
            assert_eq!(got, want);
        }
    }

    #[test]
    fn rejects_digest_mismatch() {
        let bad = "0".repeat(64);
        match load_prelude(&sample_manifest(&bad)) {
            Err(PreludeError::DigestMismatch {
                declared,
                recomputed,
            }) => {
                assert_eq!(declared, bad);
                assert_eq!(recomputed, sample_digest());
            }
            other => panic!("expected DigestMismatch, got {other:?}"),
        }
    }

    #[test]
    fn rejects_empty_bundle() {
        let manifest =
            r#"{ "name": "e", "version": "1.0.0", "program_digest": "x", "clauses": [] }"#;
        assert_eq!(load_prelude(manifest), Err(PreludeError::Empty));
    }

    #[test]
    fn rejects_duplicate_clause_ids() {
        // The same clause twice — identical canonical ids.
        let manifest = r#"{
          "name": "dup", "version": "1.0.0", "program_digest": "x",
          "clauses": [
            { "clause": { "head": { "pred": "nat", "args": [{ "tuple": [{ "atom_str": "z" }] }] }, "body": [] } },
            { "clause": { "head": { "pred": "nat", "args": [{ "tuple": [{ "atom_str": "z" }] }] }, "body": [] } }
          ]
        }"#;
        match load_prelude(manifest) {
            Err(PreludeError::DuplicateClauseId(_)) => {}
            other => panic!("expected DuplicateClauseId, got {other:?}"),
        }
    }

    #[test]
    fn rejects_malformed_clause() {
        let manifest = r#"{
          "name": "m", "version": "1.0.0", "program_digest": "x",
          "clauses": [ { "clause": { "body": [] } } ]
        }"#;
        match load_prelude(manifest) {
            Err(PreludeError::BadClause { index: 0, .. }) => {}
            other => panic!("expected BadClause, got {other:?}"),
        }
    }

    #[test]
    fn rejects_clause_id_mismatch() {
        let manifest = format!(
            r#"{{
              "name": "s", "version": "1.0.0", "program_digest": "{}",
              "clauses": [
                {{ "id": "deadbeef", "clause": {{ "head": {{ "pred": "nat", "args": [{{ "tuple": [{{ "atom_str": "z" }}] }}] }}, "body": [] }} }}
              ]
            }}"#,
            // digest is irrelevant — the id check fires first.
            "0".repeat(64)
        );
        match load_prelude(&manifest) {
            Err(PreludeError::ClauseIdMismatch { index: 0, .. }) => {}
            other => panic!("expected ClauseIdMismatch, got {other:?}"),
        }
    }

    #[test]
    fn merge_into_prepends_prelude_clauses() {
        let bundle = load_prelude(&sample_manifest(&sample_digest())).unwrap();
        // A consumer program with one extra clause, keyed by its canonical id.
        let extra = Clause::fact(Goal::new("extra", [Term::atom(*b"x")]));
        let consumer = MapProgram::new().with(ClauseId::canonical(&extra), extra.clone());
        let merged = bundle.merge_into(&consumer);
        // Both prelude clauses are present in the merged program.
        for (id, clause) in &bundle.clauses {
            assert_eq!(
                merged.clause(id),
                Some(clause),
                "prelude clause {id:?} missing from merged program"
            );
        }
        // And the merged program's digest commits to the union.
        let mut all = bundle.clauses.clone();
        all.push((ClauseId::canonical(&extra), extra));
        assert_eq!(to_hex(&program_digest(&merged)), bundle_digest(&all));
    }

    #[test]
    fn program_clauses_check_as_ordinary_rule_nodes() {
        // The bundle's program looks the clauses up by id — the exact capability `check`
        // requires of a `Program` (the prelude adds Rule nodes, nothing else).
        let bundle = load_prelude(&sample_manifest(&sample_digest())).unwrap();
        let program = bundle.program();
        for (id, clause) in &bundle.clauses {
            assert_eq!(program.clause(id), Some(clause));
        }
    }
}
