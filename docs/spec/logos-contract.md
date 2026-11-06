# logos-contract — Term · Derivation · Checker SPI

**Scope.** This is the contract for Logos's shared terms, core accounts, and
independent checking. Logos as a whole also includes a generalizing logical model,
a kernel that plans and orchestrates reasoning, and packaged native engines. See
the [model overview](../../model/README.md) for that architecture and the
[consumer specification](../references/logos-api-design-v2.md) for query, planning,
and evidence policies. The limits of a certified fragment in this document are
obligations for that fragment, not a statement that it exhausts Logos's ambition.
This orientation changes none of the firmness or verification requirements below.

**Status:** shipped and stable. The **account layer is FIRM**
([ADR 0001](../architecture/decisions/0001-account-grammar-invariant.md), *accepted*)
and the **checker-facing SPI is STABLE v1, additive-only**
([ADR 0003](../architecture/decisions/0003-checker-spi-v1-stable.md), *accepted*);
the FIRM account ships **certified stratified negation**
([ADR 0007](../architecture/decisions/0007-certifiable-stratified-negation.md)) as a
backward-compatible additive amendment — the node set `Rule | Builtin | Leaf` is
unchanged, and a negated body literal is a *checked side-condition*, not a node (§3,
§3.1). This is the *interface* a consumer (arche first, others later) compiles
against so it can adopt logos's model **without depending on any logos engine**, and
swap the engine in later with no further refactor.

**Three firmness layers, split by direction (read this first).** Not every part
of this document has the same epistemic status. The surface divides into three
layers — the account it shares, the seams a *checker* consumer binds, and the
seams a *producer/engine* binds — each with its own stability promise. (This
supersedes the earlier two-tier framing; the old "RECOMMENDED" tier is split into
the now-**stable** checker-facing SPI and the still-**proposed** engine-facing SPI,
per [ADR 0003](../architecture/decisions/0003-checker-spi-v1-stable.md), the
consumer's request on [logos#2], and the expert consultation in
[research-docs/0002](../../research-docs/0002-how-firm-a-stability-promise-for-the-logos-checker-spi-contract-surface-given-arche-consumer-plexis-engine-migration.advice.md).)

- **[FIRM] — A. the account layer** ([ADR 0001](../architecture/decisions/0001-account-grammar-invariant.md),
  *accepted*): the **account grammar** — the `Derivation` node set `Rule |
  Builtin(Theory) | Leaf` (closed, positive) and the **structural** rejection
  taxonomy — is **invariant**, forced by arche's "check, never search." §1 (Term),
  §2 (Program/Clause shape), §3 (Derivation), and the *structural* obligations and
  codes of §4 are firm. This is the **trust artifact**: stronger than API
  stability, because checkability depends on finite, local, positive derivations.

- **[STABLE v1] — B. the checker-facing SPI** (`logos-checker-spi v1`,
  [ADR 0003](../architecture/decisions/0003-checker-spi-v1-stable.md), *accepted*):
  the surface a **check-only** consumer (arche first) compiles against — `check`
  (§4), `Theory` (§5), `LeafVerifier` (§6), `RuleAdmissibility` (§5a), `Context`
  (§4.1), `CheckLimits` (§4.3), `Outcome`. **Promise:** no breaking signature or
  semantic change *within v1*; additive changes (new optional config, helper
  adapters, new delegated sub-codes) allowed; any breaking redesign requires a
  named **v2** with a migration path. **Genericity is validated by a second,
  non-arche consumer (logos#461, was provisional).** v1 was first validated *for
  production use by arche*; the one open obligation — *"a second, non-arche
  **checker** consumer is still wanted"* — is now **discharged** by **netreach**, a
  self-contained reachability/parity consumer that binds the public surface (`check`
  / `Theory` / `LeafVerifier` / `RuleAdmissibility` / `Context` / `CheckLimits` /
  `Outcome`) over its own domain, independent of arche's usage pattern: a
  DB-snapshot `Context` (no signatures), a custom `link` leaf namespace, a custom
  `same_parity` theory relation (not `is_root`), and a custom `NodeMeta` tag policy —
  every seam exercised with a shape arche does not use. It compiles+runs in the
  existing tri-core CI as `contract/go`'s `netreach_consumer_test.go` and
  `contract/ts`'s `netreach_consumer.test.ts`. **Outcome:** the v1 generic shape held
  with **no contract change** — every seam was bindable against the public surface
  with non-arche-shaped types, `check` accepting every well-formed netreach
  derivation and rejecting every malformed one with the documented FIRM structural /
  host-extension codes. A consumer may compile production code against v1 today.

- **[PROPOSED] — C. the engine-facing SPI** ([ADR 0002](../architecture/decisions/0002-chosen-architecture-recommendation.md),
  *proposed*, pending non-arche validation): the producer side — `Evaluator` /
  searcher (§7), and the engine architecture (theory registry, rings,
  store/server) ADR 0002 governs. **Revisable**; the migrated plexis/logos engine
  is the non-arche exerciser that will validate this layer.

Each section below is tagged **[FIRM]**, **[STABLE v1]**, or **[PROPOSED]**. A
**[FIRM]** change reopens ADR 0001 (breaks SDKs + arche replay + vectors at once);
a **[STABLE v1]** change is additive-only until a named v2 (breaking it breaks
arche's compiled code); a **[PROPOSED]** change is cheap until an implementer
commits to it.

> **The deadlock this resolves.** "arche can't proceed until ADR 0002 ratifies" was
> a scope error: arche binds layer **B** (check-only), not the layer-**C** engine
> architecture 0002 governs. Promoting B to a stable versioned contract unblocks
> arche now; arche compiling its real engine's seams against B *is* the first
> validation event. ADR 0002 stays unratified and unhurried — it gates the engine,
> not the checker contract.

**Byte-level vectors land with the implementation, not before.** The two
prerequisites are now closed — `ontos/codec` is blessed (`ontos-codec-v1`, frozen)
and — as of 2026-06-01 — `ClauseId`'s canonical-hash form is **also frozen** (the
account codec, §2a/§9: `SHA-256(CLAUSE_PREFIX ‖ ontos-codec(quote(clause)))`, with
`VarId` **syntactic**); the §2 "opaque stable+lookup-able" contract still holds as a
generalization — so byte-level conformance vectors are produced by the FIRM-layer
implementation
([logos#7](https://github.com/Bitspark/logos/issues/7)), which pins `check`
accept/reject over arche-vocabulary-free programs. Until that code lands the
surface is pinned at the *shape* level; this is sequencing (codec → impl →
byte-frozen vectors), not an open design question.

**Design rule.** The core of this contract contains **zero** consumer-specific
concepts. Precisely: **no arche vocabulary** (`is_root`, `signed_fact`, `grant`,
`projection`, `space`, `Arche/…`) may appear in **normative type names, node tags,
structural rejection codes, canonical bytes, package names, or cross-core
vectors**. Those terms may appear *only* in non-normative examples explaining one
consumer's binding (as they do throughout this document). The discipline the
project's review (logos#3) names is **lift the concept, not the name**: every seam
below carries a generic concept, and a non-arche fixture must exercise it so
genericity is *demonstrated*, not asserted. Everything consumer-specific enters
through the **extension points** (Theory, Leaf, RuleAdmissibility, Context —
STABLE v1 checker-facing seams, §4.1/§5/§5a/§6). The proof that the surface is
right is dual:

- **Implementable by the incumbent:** arche-core's existing checker
  ([`core/ts/src/proof.ts`](https://github.com/Bitspark/arche-core/blob/main/core/ts/src/proof.ts)) must
  be expressible as one implementation of the Checker SPI, with its
  arche-specific parts living entirely in the extension points. (Adapter-first:
  if the incumbent can't implement it, the interface is wrong.)
- **Producible by the engine:** plexis logos's evaluator
  (`Term = Atom|Number|Variable|Compound`, SLD/least-model search) must be able to
  emit a `Derivation` this contract's `check` accepts.

Built on [ontos](https://github.com/Bitspark/ontos): see
[ontos/core (L0)](https://github.com/Bitspark/ontos/blob/main/docs/spec/ontos-core.md) and
[ontos/compound (L1)](https://github.com/Bitspark/ontos/blob/main/docs/design/0003-layered-architecture.md).
**This document is the normative *semantic* contract.** The committed language
bindings live in the single **`logos-contract`** crate (the FIRM account *and* the
checker SPI together — [ADR 0004](../architecture/decisions/0004-repo-layout.md)
D2), realized in full tri-core **`{rs,ts,go}`** (Rust now; TS for arche's browser
checker + Go for its native checker — ADR 0004 D4, matching ontos and arche-core).
Within that crate the checker-facing surface carries the **`logos-checker-spi
v1`** *stability label* (a versioned promise on the B-tier items per ADR 0003, not
a separate package). A consumer compiles against a binding once it lands; until
then this document is the source of truth. The Rust-ish pseudocode here fixes the
*shape* the bindings realize, not a specific language's syntax.

> **Cross-host produce-then-verify is an intended, supported consumer pattern** (#1366):
> an account produced by one binding (say Rust) is re-checked standalone by another (Go or
> TS) — tri-core parity plus the shared vector oracle are what make the result mean the
> same thing on every host. One scope rule travels with it: **theory-owned `Builtin` nodes
> verify only on hosts that bind the theory** — theory implementations do not ship with the
> account, so a verifier either binds the same theory (per-host implementations) or the
> producer pushes theory results into the sealed relation, where any host can re-check them
> as `Leaf`/`Rule` facts. Whether an account needs a theory the verifier lacks is answerable
> *before* `check()` runs: `unowned_builtin_predicates` / `UnownedBuiltinPredicates` /
> `unownedBuiltinPredicates` (tri-core) names exactly the unverifiable predicates.

---

## 0. The duality this contract encodes

```text
        SEARCH                         CHECK
  Program × Goal  ──evaluator──▶  Derivation  ──checker──▶  Accept | Reject
       (logos)                    (shared DTO)              (arche, logos, …)
```

One artifact — the **Derivation** — flows between two directions. The engine
*produces* it by searching; a checker *consumes* it by verifying, with no search.
arche only needs the **check** direction at P0; the search direction is logos's
job and is specified here only enough to pin the shared DTO.

---

<a id="term"></a>

## 1. Term  (an ontos value, with holes)  [FIRM]

A term is an ontos value *with holes*. The hole — the **variable** — is the one
thing reasoning adds that being does not need. The grammar mirrors ontos's
`Atom(bytes) | Tuple(children)` exactly, but a tuple child **may be a `Var`** — so
holes can appear at *any depth*, not only at the top:

```rust
enum Term {
    Atom(Bytes),          // the same bytes as an ontos Atom
    Tuple(Vec<Term>),     // the same ordered shape as an ontos Tuple, but children MAY contain Var
    Var(VarId),           // the unknown — logos's sole addition
}
```

This is **full term algebra with holes** — e.g. `pair(X, "a")` ≅
`Tuple[Atom("pair"), Var(X), Atom("a")]` — *not* Datalog's variables-as-whole-
arguments (which a `Value | Var` grammar would have accidentally specified, since
an `ontos::Value` tuple's children are ground).

Precise relations (normative):

```text
ground(t)        ⟺  t contains no Var
ground Term      ≅  ontos Value          (a bijection on ground terms)
erase_ground(t)  =  the corresponding ontos::Value   (defined iff ground(t))
```

- A **ground** term corresponds exactly to an `ontos::Value` (same `Atom`/`Tuple`
  shape, no `Var`), comparable by ontos structural identity. An implementation MAY
  store ground terms directly as `ontos::Value` as an optimization, but the
  normative grammar is the recursive one above — so a non-ground term like
  `pair(X, "a")` is representable.
- `Var` is a genuine term constructor, **not** an ontos value under a reserved
  label. (Encoding it as `Tuple(Atom("var"), …)` would force logos to reserve the
  label `"var"`, colliding with consumer data — the leak the model refuses.)
  Reifying a term-with-holes as ground data (e.g. to *store* a rule) is the
  explicit `quote` operation (§2a), producing an ordinary ontos value.
- Identity on terms extends ontos identity with `Var(a) = Var(b) ⟺ a = b`. No
  numeric/quotient equality (that stays a consumer/theory concern).

`VarId` is an opaque variable identity (name or index); its only contract is
equality and freshness (renaming apart).

**The anonymous variable `_` (source syntax, #2149).** In source text each bare `_` is
its OWN fresh variable, as in Prolog and Datalog: `attr(X, _, _)` matches `attr(a, x, y)`.
The parser gives the n-th bare `_` of a clause or query a distinct `VarId` that no source
can spell (`_@<n>`, numbered by source position within that clause or query), so the same
source yields the same bytes in every core. `_Name` is an ordinary named variable. Human-facing
text renders an anonymous variable as `_`; machine forms (a derivation's substitution, a wire
clause) carry its `VarId` verbatim. A query's `_` is never an answer binding. A bare `_`
under `\+` is refused, because a negated premise must be ground (§3.1): project it through a
named predicate first, `has_p(A) :- p(A, _).` then `\+ has_p(A)`. A `_` in a clause HEAD is,
at the range-restricted (Datalog) tier, an unbound head variable, refused exactly as a named
one is, in a rule (`p(X, _) :- q(X).`) and in a fact (`p(a, _).`) alike (#2153): name the
position and bind it in the body, or drop it from the head. The term tier, which admits
non-ground heads (ADR 0027 D2), admits it too; that is where the prelude's
`member(X, [X|_])` lives.

### 1.1 Literal — a predicate application (the `ontos/compound` reading)

A **`Literal`** is a predicate applied to argument terms — `p(args…)`. It is the
logic-level "atom" of Horn logic, and is *deliberately a different type from an
ontos `Atom(bytes)`*: the two senses of "atom" are load-bearing here, so the
logic-level one is named `Literal`. It is the labeled-compound reading from
`ontos/compound`: `p(args…)` ≅ `Tuple[Atom("p"), args…]`.

```rust
struct Literal<T> { pred: Symbol, args: Vec<T> }   // Symbol = an ontos Atom(bytes), by convention a name

type Goal         = Literal<Term>;          // may contain Vars — clause heads/bodies, the claim
type GroundLiteral = Literal<ontos::Value>;  // ground — every derivation-node conclusion
```

Making the ground-ness a *type* (not just prose) is the point: a clause's
head/body are `Goal`s (variables allowed); every `Derivation` node concludes a
`GroundLiteral` (§3). (This is the role arche-core's `Atom { pred, args }` plays;
the changes are the `Literal` rename, the `Vec<Term>` recursive args, and the
`Goal`/`GroundLiteral` split.)

## 2. Program  (clauses — data, not engine)  [FIRM]

```rust
struct Clause { head: Goal, body: Vec<Goal> }    // head :- body₀, …, bodyₙ ;  body empty = a rule-fact
trait Program { fn clause(&self, id: &ClauseId) -> Option<&Clause>; }
```

- A `Clause`'s head and body are `Goal`s (`Literal<Term>`) — they contain
  variables; that is what makes a clause a *rule* rather than a ground fact.
- **`ClauseId`'s only required contract is *stable + lookup-able*** (§2), and a
  consumer may use any such id. Its **canonical-hash** form is now also defined and
  frozen (§2a/§9, the account codec `account.rs`): `ClauseId::canonical(clause) =
  SHA-256(CLAUSE_PREFIX ‖ ontos-codec(quote(clause)))`, with `VarId` **syntactic**
  (variable names encoded; no alpha-normalization). (The `ontos/codec` freeze is
  necessary but not sufficient on its own: a clause contains variables,
  so it is not itself an ontos value.)
- A consumer's whole policy is a `Program`. **arche's authorization theory
  (`authorized`, `grant`, `covers_*`, sealing helpers) is a `Program` — data, not
  code** — so swapping the engine never touches the policy.
- **Local checking.** `check` validates only the clauses a derivation *cites*
  (via `program.clause(id)`); whole-program predicate-partition hygiene (§4.4) is a
  consumer/program-loading responsibility, not a per-`check` obligation. So
  `clause(id)` is the only method the checker requires of `Program`.

## 2a. Reification: `quote` / `reify`  [STABLE v1 shape · byte form FROZEN v1]

Storing or transmitting a *rule* (a clause with variables) as ordinary data
requires turning a term-with-holes into a ground ontos value and back. This is
**not** an engine concern — it is needed for storing rules, exchanging policies,
and (later) canonical clause hashing — so it lives here, beside the model, not in
the proposed engine section.

```rust
fn quote(t: &Term) -> ontos::Value;          // total: maps Atom/Tuple/Var → a ground ontos value
fn reify(v: &ontos::Value) -> Option<Term>;  // partial inverse of quote
```

- A `Var(id)` quotes to a reserved *quoted-variable* shape (a tagged ontos value),
  distinct from the live `Var` constructor (which is **not** an ontos value, §1).
  This is how a variable becomes a *being* without logos reserving a label in the
  consumer's data namespace.
- **Both tiers now frozen (§9 settled, 2026-06-01):** the *semantic shape* (that
  `quote` exists, is total, and round-trips via `reify`) is **[STABLE v1]**, and the
  *exact canonical bytes* (the 1-byte tags `0x00` Atom / `0x01` Tuple / `0x02` Var,
  with a `Var` carrying its **name verbatim — syntactic**) are now **FROZEN v1**.
  This is the account codec (`logos-contract` `account.rs`): `quote → ontos-codec`
  is the canonical clause encoding, and **`ClauseId::canonical(clause) =
  SHA-256(CLAUSE_PREFIX ‖ ontos-codec(quote(clause)))`** (§9). Changing a tag is a
  breaking change shipped as a new version, never an edit.
- **A quoted variable's name is UTF-8 text** ([#3102](https://github.com/Bitspark/logos/issues/3102)).
  A `VarId`'s name is text in every core (Rust holds it as a `String`), the rule the
  derivation wire already applies to a subst key (`decode subst.var: not valid UTF-8`). So a
  quoted variable whose name bytes are not valid UTF-8 is outside the image of `quote`, and
  `reify` refuses it (go since `CHECKER_VERSION` 19, a narrowing ruled by `seat:caa` on #3114;
  rs and ts always did). An atom's bytes are opaque data and are never UTF-8-checked.
  `vectors/reify.json` pins the `reify` decision in all three cores, and
  `vectors/derivation_wire.json`'s `subst_term_quoted_var_not_utf8` pins its refusal on the
  wire (`decode subst.term: value is not a quoted ground term`).
- **Constructing a `VarId` holds to the same domain** ([#3115](https://github.com/Bitspark/logos/issues/3115),
  `CHECKER_VERSION` 21, a narrowing ruled by `seat:caa`). A name no Rust `String` can hold is
  refused where the variable is made, not only where it is decoded: in go a string that is not
  valid UTF-8, in TypeScript a string with a lone UTF-16 surrogate (which `quote` would otherwise
  write as U+FFFD, merging distinct variables into one account and one `ClauseId`). Go's
  `ParseVarId` refuses by name (`VarIdError`), and `NewVarId`/`Var` are its Must forms, which
  panic by name; TypeScript's `VarId`, `VarId.of` and `Term.var` throw a named `VarIdError`.
  Each core has ONE test of the domain, called by every construction, by `reify` and by the
  decoders. `vectors/reify.json`'s `var_names` pins it tri-core, with the rows a core cannot
  express marked as such.

<a id="derivation"></a>

## 3. Derivation  (the shared DTO — the heart)  [FIRM]

A finite DAG of nodes; each node concludes a **ground** atom; positive premises
reference earlier nodes (acyclic). This is arche-core's `Proof { nodes, root }`,
generalized so the two non-structural node kinds delegate to extension points and a
*negated* premise discharges against a sealed certificate (§3.1). The node set
`Rule | Builtin | Leaf` is **unchanged** — negation adds no node kind.

<!-- design:figure id=account-anatomy -->
<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../img/account-anatomy-dark.svg">
    <img alt="The anatomy of an account — the proof DAG a checker walks. At the top a Rule node concludes the ground literal permit(s1, a1) by instantiating a clause with a substitution; it carries two premises. A positive premise (Premise::Pos) resolves to a Leaf node, the admitted fact grant(s1, a1). A negated premise (Premise::Neg) carries the atom \+ denied(s1, a1) and is discharged not by a node but by absence from a sealed ClosedModelCert — a closed model in which that atom is genuinely absent. Every node concludes one positive ground literal; the three node kinds are Rule, Builtin, and Leaf." src="../img/account-anatomy-light.svg" width="820">
  </picture>
</p>
<!-- /design:figure -->

```rust
struct Derivation {
    nodes: Vec<Node>,
    root: usize,
    closed_world: Vec<ClosedModelCert>,  // the certs this derivation CARRIES, indexed by CertId:
                                         // every cert its Neg/Count premises cite (§3.1); EMPTY
                                         // for every derivation that cites none (see below).
                                         // rs holds it as a `CertStack`: the same sequence, whose
                                         // storage clones SHARE (#2565); no byte moves
}

enum Node {
    /// Intensional step: instantiate a cited clause.
    Rule {
        conclusion: GroundLiteral,
        clause: ClauseId,
        subst: Subst,              // grounding substitution applied to the clause
        premises: Vec<Premise>,    // one per body literal, in body order (§3.1)
        meta: NodeMeta,            // opaque to core (provenance, projection binding, …)
    },
    /// A theory/builtin atom, decided by the Theory SPI (§5), not by clauses.
    Builtin { conclusion: GroundLiteral },
    /// An extensional leaf, admitted by the Leaf SPI (§6), not derived.
    Leaf { conclusion: GroundLiteral, evidence: Evidence },
}

/// One premise per body literal, carrying the body literal's POLARITY (ADR 0007).
enum Premise {
    /// A positive body literal, discharged by an earlier node (the backward edge the
    /// account formerly carried as a bare `usize` — `From<usize>` still lifts to this,
    /// so an all-positive `premises: vec![0, 2]` list constructs unchanged).
    Pos { node: usize },                  // node < this node's index (acyclic DAG)
    /// A NEGATED body literal `\+ atom`, discharged as a CHECKED SIDE-CONDITION (not a
    /// node): `atom` must be ABSENT from the cited, already-verified ClosedModelCert.
    Neg { atom: GroundLiteral, cert: CertId, nonmember: NonMemberProof },
}
```

- Every node concludes a **`GroundLiteral`** — ground-ness is in the type, not
  only in prose (§1.1). (`non_ground_conclusion` remains a structural code for an
  implementation/decoder that constructs a node from untrusted input whose args
  aren't actually ground.)
- `Subst = Map<VarId, Term>` — applying it to the cited clause's head/body must
  yield ground literals (`subst` covers every `Var` in the clause).
- **`Builtin` carries no `TheoryId`.** Dispatch is by predicate ownership:
  `check` routes a `Builtin` node to the unique `Theory` that `owns(conclusion.pred)`
  (§5), and the predicate-partition invariant (§4.4) guarantees exactly one owner.
  (Dropping the explicit `TheoryId` removes a class of "tag disagrees with owner"
  errors.)
- `NodeMeta` and `Evidence` are **opaque to the core** (see §4/§6) — this is the
  hatch that carries arche's `RuleProvenance`, `signer/signature/admission/space`
  without the core knowing them.
- **`premises` is a `Vec<Premise>`, and `closed_world` defaults to empty (ADR 0007 —
  additive, backward compatible).** A `Rule` node's premises carry the polarity of the
  body literal they discharge: a `Pos { node }` is the backward edge to an earlier
  node (the bare `usize` the account formerly carried — `From<usize>` still lifts to
  it), and a `Neg { atom, cert, nonmember }` is a *checked side-condition* against one
  of the derivation's `closed_world` certificates (§3.1), **not** a node. An
  all-`Pos`, empty-`closed_world` derivation is **exactly today's account**, and
  `check` over it behaves byte-identically — the certificate machinery is consulted
  only when a `Neg` premise is present. The FIRM node set `Rule | Builtin | Leaf` is
  **unchanged**: negation adds no node kind.
- **`closed_world` is what the derivation CARRIES, not what it relies on (#2533).** A premise
  cites a certificate by its index (`CertId`), and so does each certificate's own support, always
  downward to a strictly lower certificate of a stack. So a derivation must carry every
  certificate it cites, at the index it cites it by. The in-tree producer carries exactly the
  **downward-closed prefix up to the highest certificate the derivation cites**, and nothing when
  it cites none: an answer whose premises are all positive carries no certificate, even in a
  program that negates elsewhere. That prefix can hold a lower certificate nothing in the
  derivation relies on. `check` computes a status for every carried certificate, but a status
  reaches the verdict only through a premise that cites it, so an uncited carried certificate can
  neither satisfy nor sink the check (it is still subject to the eager term-depth gate, like any
  carried data). **Do not read a carried certificate as a dependency; read the citations.**

### 3.0 Proof-interchange wire for `Derivation`  [FIRM]

`Derivation` is the proof-interchange artifact that lets a producer emit once and a
consumer re-check without trusting the producer. Its public interchange bytes are
therefore part of `logos-contract`, not a kernel-private seam.

Two layers are frozen:

1. **`DerivationWirePayloadV1`** is the byte-compatible payload. It is an
   `ontos-core` `Value`, encoded with `ontos-codec-v1`, with this exact shape:

   ```text
   Tuple[
     Tuple[node0, node1, ...],
     int(root)
     (, Tuple[closed_model_cert0, closed_model_cert1, ...])
   ]
   ```

   The third field is trailing-optional and is emitted only when `closed_world` is
   non-empty. An all-positive derivation with empty `closed_world` therefore remains
   exactly the two-field `Tuple[nodes, root]` payload used by the incumbent kernel
   seam. Node order is identity-bearing DAG order and MUST NOT be sorted.

   A `closed_model_cert` reading is a **ten**-element tuple (scope, the four pins, the
   EDB snapshot hashes, domains, extensions, supports, `limits_decl`) with **two
   trailing-optional elements**, in this order: the eleventh is ADR 0029 D10's
   decomposition-witness digest (a slice seal), the twelfth is ADR 0030 D4's
   `partial_scope` (§3.1). A cert with neither is the ten-element tuple it always was,
   byte for byte. When only the twelfth is present, the eleventh slot carries the `opt`
   none marker `Tuple[Atom("none")]` (§0.3.4) so the twelfth keeps its position; an
   eleven-element cert is therefore always a digest at slot eleven, and a decoder MUST
   accept exactly ten, eleven or twelve elements and refuse any other arity.

2. **`DerivationWireV1`** is the public proof-interchange wrapper:

   ```text
   Tuple[
     Atom("proof-interchange/derivation/v1"),
     DerivationWirePayloadV1
   ]
   ```

   Consumers MUST reject any unknown public wrapper tag rather than treating it as
   v1. Decoders MAY expose an explicit payload-only helper for internal compatibility,
   but the public interchange API MUST traffic in `DerivationWireV1`.

The payload reuses the FIRM account readings already used by this contract:

- `Rule` node: `Tuple[Atom("rule"), conclusion, Atom(clause_handle), subst,
  Tuple[premise0, ...], node_meta]`
- `Builtin` node: `Tuple[Atom("builtin"), conclusion]`
- `Leaf` node: `Tuple[Atom("leaf"), conclusion, evidence]`
- positive premise: bare `int(node_index)` (byte-compatible with the pre-ADR-0007
  positive account)
- `Neg` premise: `Tuple[Atom("neg"), atom, int(cert_index)]`
- `Count` premise: `Tuple[Atom("count"), Tuple[Atom(pred), int(arity)], filter,
  project, k, int(cert_index)]`

`conclusion`, `atom`, `subst`, `node_meta`, `evidence`, `project`, `k`, and
`closed_model_cert` are the contract readings defined in this document; no
consumer-specific vocabulary is introduced by the wire. Clause coordinates are the
clause handle string (`Atom(clause_handle)`), not a hash substitution.

The contract bindings MUST provide these operations, with idiomatic casing per
language but equivalent semantics:

- `derivation_wire_payload_v1_to_value(Derivation) -> Value`
- `derivation_wire_payload_v1_from_value(Value) -> Result<Derivation>`
- `derivation_wire_v1_to_value(Derivation) -> Value`
- `derivation_wire_v1_from_value(Value) -> Result<Derivation>`
- `encode_derivation_wire_v1(Derivation) -> bytes`
- `decode_derivation_wire_v1(bytes) -> Result<Derivation>`
- `ground_literal_as_value(GroundLiteral) -> Value` and its strict inverse
  `ground_literal_from_value_v1(Value) -> Result<GroundLiteral>` (#1914) — the standalone
  pair for ONE ground literal, the same reading every node `conclusion` uses:
  `Tuple[Atom(predicate), quote(argument)…]`. ⚠ This is the **account representation**, not
  the raw Ontos labeled compound `Tuple[Atom(predicate), argument…]`: the arguments are
  `quote`d, and that is what lets the inverse check they are ground. The inverse refuses a
  missing or non-atom predicate, an argument outside the image of `quote` (an unquoted
  compound is refused, by design), and a quoted variable or any non-ground argument; an atom
  whose bytes merely spell a variable name is data and round-trips unchanged. Example:
  `p(a, (b, c))` encodes as `Tuple[Atom("p"), quote(Atom "a"), quote(Tuple[Atom "b", Atom "c"])]`
  and decodes back to the same literal; `Tuple[Atom("p"), Atom("a")]` (unquoted) does not.

The payload helpers preserve the incumbent two-field positive bytes. The public
helpers add the `proof-interchange/derivation/v1` domain boundary and are the only
helpers consumers should use for durable proof exchange. A future change to the
payload shape requires `DerivationWireV2` unless an additive v1 extension rule is
first specified here.

**The decoder's value domains and refusal texts (#2630, #2682).** A decoder refuses a
malformed wire with the text `decode <path>: <defect>`, byte-identical in Rust, Go and
TypeScript. The contract, not any platform, defines each field's value domain:

- **`u32` fields**: a count premise's predicate arity, a filter position and a project
  attribute; a certificate's scope level, extension arity and support ranks. Domain
  `0..=2^32 - 1`.
- **index and count fields**: the root, a premise's node index, every certificate index
  and the six `limits_decl` fields. Domain `0..=INDEX_MAX`, `INDEX_MAX = 2^53 - 1`, the
  exact-integer range every core holds.
- Outside its domain an integer is refused `not a canonical int embedding`, never
  narrowed or truncated. A value in the domain always decodes, so a root in
  `(len, INDEX_MAX]` reaches `check`, which refuses it as `root_out_of_range`.
- **An index is a protocol INTEGER, not a host offset (#2735).** Every core holds an
  in-domain index or declared size as a 64-bit integer, whatever its pointer width. It
  becomes an offset into a collection only after a range check against that collection's
  length. So an index past its collection is never a decode refusal on any platform; it
  reaches `check`, which refuses it by name (`root_out_of_range`, `cert_out_of_range`,
  `bad_dependency_order`).
- A core that cannot BUILD an in-domain value refuses it by name as its own capability
  limit, never as `BadInt`. Rust's `TooDeep` term-depth bound is that family (#2630
  (3′)). An integer is not such a value: holding one is not allocating an object of that
  size.
- **Text is its exact bytes.** A leading UTF-8 byte-order mark is data, never stripped.
  So `EF BB BF` then `leaf` is not the tag `leaf`, and subst variables `X` and BOM+`X`
  are two variables.
- **An unknown tag renders byte by byte** as a double-quoted string. Each ASCII byte
  renders as Rust's `{:?}` renders that character: `\"`, `\\`, `\t`, `\r`, `\n`, `\0`,
  another control as `\u{hex}`, a printable byte as itself. Each byte `>= 0x80` renders
  as `\x{hh}`. Nothing is UTF-8-decoded, so the text is identical in every core.

**Every decoded integer names a contract domain (#3238, research 0021).** The two domains above
are not the derivation wire's alone. Every integer a core decodes from any wire (the derivation,
a certificate, and the kernel seam's request, negotiation, plan and event records) has exactly one
of the domains below, decided the same way by every core that decodes it. Outside it the value is
refused by name, never narrowed and never bounded by a platform's integer width (ADR 0012's
2026-09-26 amendment: a platform may inform a domain, and never sets one).

- **`u32` fields**, `0..=2^32 - 1`: the fields above, and the kernel seam's arities (a host
  builtin's arity, §5), stratum ids, stack-reference ordinals, variants and ranks.
- **index and count fields**, `0..=INDEX_MAX`: the fields above, and the seam's indices.
- **`u64` fields**, `0..=2^64 - 1`: a duration in nanoseconds, a search budget (`RunLimits`), an
  epoch, a counter.
- **`int` values**: every integer. A term's integer VALUE (an argument a theory evaluates, an
  aggregate's column, a count premise's claimed result) is unbounded (ADR 0022 §5: an integer is
  unbounded, like `BigInt`), so its size is never a decode refusal; the theory decides what it
  means.

[`scripts/decoded_integer_domains.json`](../../scripts/decoded_integer_domains.json) names the
domain of every decoded integer field in every core, and the census over it
(`scripts/decoded_integer_census.py` for rs and ts, `scripts/ci/lossyrune` for go) reds on a
field that names none. A field whose cores do not yet decide one domain is listed there as a gap,
with the issue that tracks it.

`vectors/derivation_wire.json`'s malformed rows pin each refusal class, both sides of
each domain boundary, and the tag renderings. The rows are authored by
`scripts/vectors/derivation_wire_refusal_oracle.py`.

Shared hand-authored vectors MUST land with the codec implementation and be replayed
by the Rust, Go, and TypeScript contract tests. The minimum vector set is:

- positive leaf/rule derivation with empty `closed_world`;
- builtin node derivation, proving builtins are first-class nodes rather than leaves;
- derivation with non-empty `closed_world` through a `Neg` or `Count` premise;
- malformed/unknown public wrapper tag rejection;
- malformed payload rejection for an invalid node or premise tag.

### 3.1 The node set is CLOSED and POSITIVE (the negation boundary)

The three node kinds above are the **whole** set, and every node concludes a
**positive** ground literal: `Rule | Builtin(Theory) | Leaf`. There is deliberately
no `Neg`/`Failure`/`ClosedWorldLeaf` node, no cut node, no `findall`/aggregation node.

> ⚠ **"No aggregation NODE" is not "no certifiable aggregation" — and a consumer read it that way
> (#1364).** A certifiable `count` / `count_distinct` adds no node kind because it is a checked
> **premise** (`Premise::Count`), exactly as negation is `Premise::Neg`: the checker recomputes the
> cardinality over a sealed `ClosedModelCert` and accepts only if it equals the claimed `k`. The
> sentence above is true **of nodes** and stays as written; this pointer exists because the reader
> who needs "k such things" arrives *here*, while the carve-out sits far below in §3 — under the
> heading ***Certifiable `count` / `count_distinct` adds no node kind either***. (Deliberately named
> rather than counted: a line-distance rots on the next insert, a heading does not.) See also §4's
> `count_*` rejection codes.

This closed-positive node set is the single decision that makes the contract
genuinely agnostic to *both* a solver and a verifier rather than "arche with holes."
See [`../design/0001-agnostic-shared-contract.md`](../design/0001-agnostic-shared-contract.md).

**Negation is a checked side-condition, not a node** ([ADR 0007](../architecture/decisions/0007-certifiable-stratified-negation.md),
*certifiable stratified negation*). The naive worry was that `\+ p` asserts *p is not
derivable* — a closed-world property of the whole program — so checking it would force
the verifier to **re-run the search**, destroying "check, never search." ADR 0007
resolves this **without** adding a node and **without** any search: a negated body
literal `\+ r(a)` is carried as a `Premise::Neg { atom, cert, nonmember }` on the
`Rule` node (§3), and it is discharged by showing `r(a)` is **absent** from a sealed
[`ClosedModelCert`](../architecture/decisions/0007-certifiable-stratified-negation.md)
the derivation cites in its `closed_world` — a *finite, exact* model of a stratum
prefix that the checker verifies **totally**:

- The certificate seals a **stratum prefix** and pins itself to the program / profile
  / context / theory-config hashes and the EDB snapshot. It carries the finite typed
  **domains**, the exact **relation tables** of the sealed predicates, and a **support**
  witness. The theorem is stated stratum by stratum ([#3022](https://github.com/Bitspark/logos/issues/3022),
  research 0028 A4). Let `L` be the already-verified lower strata and `T_s^L` the stratum's
  immediate-consequence operator, with negation and counts read against `L`. **Support** gives
  `E_s ⊆ lfp(T_s^L)` (no junk: every row has a support edge, and a same-stratum dependency has a
  strictly smaller rank). **Closure** gives `T_s^L(E_s) ⊆ E_s`, hence `lfp(T_s^L) ⊆ E_s` (no
  missing heads): the checker meets every satisfied grounding by a complete relational join over
  the sealed tables, never by enumerating the domains, and an undecidable or inconsistent literal
  refuses rather than reading as false. Together they make the sealed relation `E_s` *exact*, so
  `a ∉ E` proves `a` is genuinely not in the least model — absence is sound, **not**
  merely an unproven upper bound (the `p :- p` trap a bare closure check would accept).
  Neither obligation needs the program to be constructor-acyclic: a finiteness guarantee is an
  admission promise that evaluation ends, and closure is the evidence that this table is complete.
- **A sealed table may be a LOWER BOUND, and the certificate says so** ([ADR 0030](../architecture/decisions/0030-partial-table-certification.md),
  checker version 3). `partial_scope` is an optional sub-scope of `scope` naming the sealed
  predicates whose tables hold *only* rows of the least model but not necessarily all of
  them — the tripping stratum of a truncated evaluation, sealed for its positive rows.
  Absent for every exact seal. The checker verifies its shape **before any table is
  consulted** (`cert_partial_scope_invalid`: it must be canonical, non-empty, a subset of
  `scope` at the prefix's own level, never an extensional table, and *upward-closed*
  within the sealed prefix — a sealed clause whose head is complete may not read a partial
  table positively or under a count, or its closure proof would be vacuous). For a partial
  table **support is verified and closure is not**: its rows are proven `⊆ least model`,
  and nothing is claimed about the rows it lacks — so a `Neg` premise over it is refused
  `neg_atom_partial` and a `Count` premise over it `count_over_partial`. What a partial
  table buys is the sealed prefix *below* it: a negation over a complete table in the
  same certificate is discharged exactly as before, where the certificate as a whole was
  previously refused `cert_not_closed`.
- The `\+` checker verifies each `Neg` premise **totally and without searching**: the
  cert's pins equal the bound check context, `r` is sealed by the cert and sits in a
  *strictly lower* stratum than the rule head, `a` is ground and within the sealed
  finite domain, `a` is absent from the table, and the table has already passed support
  + closure. Every loop ranges over a *supplied* finite table/domain, each pre-bounded
  by a `CheckLimits` cert budget validated before any scan — **verification, not
  search.** The `\+` verifier is **TRI-CORE**: realized identically in all three contract
  cores — [`contract/rs/src/cert.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/cert.rs)
  + [`check.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/check.rs),
  [`contract/go/cert.go`](https://github.com/Bitspark/logos/blob/main/contract/go/cert.go)
  + [`check_negation.go`](https://github.com/Bitspark/logos/blob/main/contract/go/check_negation.go),
  and [`contract/ts/src/cert.ts`](https://github.com/Bitspark/logos/blob/main/contract/ts/src/cert.ts)
  + [`cert_check.ts`](https://github.com/Bitspark/logos/blob/main/contract/ts/src/cert_check.ts)
  ([ADR 0007](../architecture/decisions/0007-certifiable-stratified-negation.md) §4 obligations,
  PRs #427/#428; an `interface`, not a capability — [ADR 0012](../architecture/decisions/0012-interface-parity-not-capability-parity.md)).
  See also [docs/architecture/kernel.md](../architecture/kernel.md) "Certifiable
  negation."

The **admissible certifiable fragment** is *safe, range-restricted, stratified
Datalog¬ over a finite, explicitly sealed domain, with complete EDB snapshots and
total deterministic builtins.* That is the boundary the cert's gates enforce
(constructor-acyclic, range-restriction, downward-closed scope, finite domain
coverage). **A GROUND term is a constant of the fragment** (#2294, ruled `seat:caa`;
CHECKER_VERSION 12): a string (`utf8-text(..)`), an int, a ground list and `f(a)` all are, and §3.4
forces each into ∪domains whole, like an atom. **An OPEN compound (a `Tuple` that contains a
variable) is admitted inside the CONSTRUCTOR-ACYCLIC fragment** (#2759, `seat:caa`'s design gate;
CHECKER_VERSION 18): in a sealed-scope clause's BODY freely, since a destructuring pattern such as
`item(tag(X))` only yields sub-terms of values already sealed and the closure join binds `X` by
unifying the pattern with a sealed row; and in its HEAD (a CONSTRUCTING rule, `ok(tag(X)) :- ...`)
only when the clause lies on no dependency cycle of its scope. Every sealed rule, whether or not
it carries a compound, also passes the strong safety gate: each variable is bound by a positive,
sealed, non-builtin body literal (research 0028 row A7), so `p(a) :- \+ q(X)` is outside. Every
value of the sealed model is then a ground program value, an input sub-term, or built by a
constructing rule on no cycle, so the relevant model is FINITE; no depth or size cutoff is ever
evidence. **Finiteness is all acyclicity discharges** (row A9): matching completeness, domain
coverage, support, stratification, aggregates and the budget are each still checked by their own
gate. A constructing rule ON a cycle (`nat(s(X)) :- nat(X)`) is `cert_scope_incomplete`, and
`check` re-derives that from the bound program rather than trusting the producer. A count's filter
and result terms stay function-free. The checker and the producer read one classification,
`Term::is_open_compound` (go `IsOpenCompound`, ts `Term.isOpenCompound`), and one cycle test, the
checker tier's `fragment::ScopeGraph` (go and ts `ScopeGraph`, row A15). The producer's seal plan
(`SealPlan::sealed_compounds`) is the one computation the resolver derives the
`sealed_acyclic`/`all` function-symbol level from, so a producer declines
`compound_in_sealed_clause` exactly where the fragment ends, and the resolver refuses such a program
at admission. **Until #3022 lands, a certified COMPLETE SET over a sealed compound (`sealed_acyclic`)
is admitted under the `exact` term identity only** (`seat:caa`'s ruling on #2759): under the default
`reify_lists` the resolver refuses it at admission, by name, since research 0028 measured that
identity's label-tolerant comparisons disagreeing with the closed world. #3022's change removes the
condition. Outside it — **unrestricted operational NAF / SLDNF** and programs with
function symbols whose intended model can be non-r.e. — stays an **untrusted engine
strategy** (§7): the engine may run it, but its answers must arrive with a positive
derivation **plus** the closed-model certificates; *failure-as-evidence is never
trusted.* Cut (`!`), `findall`, `bagof`, `setof`, and `aggregate` remain purely
search-side (§7, ADR 0016 Shelf C): they decide *which* positive derivation is
produced and add **no** account node.

> ⚠ `aggregate` in that list is the **search-side** operator, and it is genuinely untrusted. It is
> **not** the same mechanism as a certifiable `count` / `count_distinct`, which *is* checked — see
> the paragraph below and §4. Read as a flat "counts are search-side", this line sends a consumer
> with a counted claim to restructure work they did not need to restructure (#1364).


#### What `check` ACCEPTS, and what that acceptance does *not* claim ([#811](https://github.com/Bitspark/logos/issues/811))

The paragraph above states an **obligation on the producer** — an operational-NAF
answer must arrive with the positive derivation *plus* the closed-model certificates.
It is worth saying plainly what follows when only the first half arrives, because the
verdict alone does not distinguish the two cases and a reader may take it to.

**`check` accepts a derivation, not an answer.** Its verdict ranges over exactly the
obligations of §4 — every cited node locally valid, premises 1:1 with body literals,
the root concluding the claim, and every `Premise::Neg` / `Premise::Count` discharged
against a sealed `ClosedModelCert`. A derivation carrying **no** `Neg` premise has no
negation obligation to discharge, so `check` accepts it on its positive content alone.

That is sound and intended. The consequence to state is this:

> **Where a search used operational NAF (`\+`), cut, `findall`/`bagof`/`setof`, or an
> uncertified aggregate to decide *which* derivation to emit, those steps add no
> account node and therefore no obligation — so `ACCEPTED` is a claim about the
> positive skeleton that was emitted, and is silent about the search-side reasoning
> that selected it.** An `ACCEPTED` verdict on such an answer says *this derivation is
> valid*, never *this is the right answer* or *the negated goal genuinely fails*.

The distinction is not cosmetic. A closed-world conclusion is exactly the case where a
consumer most wants an account, and it is exactly the case where an unaccompanied
`ACCEPTED` carries least. The FIRM account **already** provides the certified route —
`Premise::Neg` discharged against a sealed cert, verified totally and tri-core (above,
ADR 0007) — so the gap is never a missing capability. It is that an answer produced by
the untrusted strategy and an answer carrying the certificates are, at the verdict,
**indistinguishable**.

Two obligations therefore fall on any surface that reports a verdict:

1. **A derivation whose production used the untrusted strategy MUST be distinguishable
   from one whose negation obligations were discharged against a cert.** A bare
   `accepted` for both is a true statement that reliably misleads — the reading a
   consumer takes is stronger than the claim made, and this specification's whole
   premise is that an account justifies itself rather than being taken on faith.
2. **A `certifiable`-tier request over a negation-bearing program MUST NOT be silently
   served by the untrusted strategy.** Satisfy it, refuse it, or downgrade it with a
   stated reason — but silence about which of the three occurred is the one option the
   tier's promise does not permit.

These bind the reporting surfaces (the engine verdict, the tier negotiation, and the
CLI rendering), **not** `check` itself: `check`'s own contract is unchanged by this
section and its verdict remains exactly the §4 obligations. Nothing here narrows what
`check` accepts, and no derivation valid before this paragraph becomes invalid after it.

Of the three bound surfaces, the **tier negotiation** lives in the host resolver in
every core. The wasm guest executes only already-negotiated work — its request wire
deliberately carries no tier, because negotiation completes before dispatch — so a
surface *below* the negotiation boundary cannot be the silent server obligation 2
names: that obligation's enforcement locus is the resolver that holds both the tier
and the program analysis. Dispatching un-negotiated requests to the guest, should any
path ever do so, reopens this placement (ruled on #1292).

**On closing the disjointness.** That a `certifiable` request over a negation-bearing
program has no producer today is a **missing producer, not a missing design**: ADR 0007
is Accepted and shipped — `Premise::Neg`, `Derivation.closed_world`, `ClosedModelCert`
with its support and closure witnesses all exist in the account, and the `\+` verifier
is realized in all three cores. The bottom-up engines that could mint such a
certificate advertise `SearchOnly` and are refused by the tier. Making that path
reachable is provider registration and is tracked separately
([#821](https://github.com/Bitspark/logos/issues/821)); it is **not** a change to this
contract, and obligation 2 above stands whether or not it lands — an unsatisfiable
request must still be refused truthfully rather than served quietly by a strategy that
cannot meet it.

**Certifiable `count` / `count_distinct` adds no node kind either — it is a checked
`Premise::Count`, exactly as negation is a checked `Premise::Neg`**
([ADR 0023](../architecture/decisions/0023-certifiable-aggregation.md), *certifiable
aggregation*). The node set `Rule | Builtin | Leaf` is **unchanged**: a count is
discharged as a derivation-level side-condition against the *same* sealed
[`ClosedModelCert`](../architecture/decisions/0007-certifiable-stratified-negation.md)
the negation amendment defines — the checker recomputes the cardinality `n` over the
proven-exact sealed relation (support + closure) and accepts only if `n` equals the
claimed `k`. A count reads a **strictly lower** sealed stratum (it is non-monotone, like
negation), so it inherits the negation fragment's admissible boundary and certificate
wholesale. This is *certifiable* aggregation — distinct from the search-side
`findall`/`bagof`/`setof`/`aggregate` above, which stay untrusted and mint no node. See
§4 for the `Premise::Count` verifier and its `count_*` rejection codes, and §7 for the
dual-conformance obligation.

<a id="checker-spi"></a>

## 4. Checker SPI  (the P0 deliverable arche depends on)  [FIRM core obligations · STABLE v1 seam params]

```rust
fn check<C>(
    program: &dyn Program,
    claim:   &GroundLiteral,     // the ground goal the derivation must establish
    deriv:   &Derivation,
    ctx:     &C,                 // immutable verification snapshot (§4.1) — threaded, not inspected by core
    profile: &CheckProfile<C>,   // the bound extension points + config + limits
) -> Outcome;

struct CheckProfile<C> {
    theory: Box<dyn Theory>,             // §5  — config-pinned, NOT generic over C
    leaves: Box<dyn LeafVerifier<C>>,    // §6
    admit:  Box<dyn RuleAdmissibility<C>>, // §5a — may be the no-op
    limits: CheckLimits,                 // §4.3 — resource cap on the supplied derivation
}

enum Outcome { Accept, Reject { code: RejectionCode, detail: String } }
```

`check` is **total** and performs **no search**. It verifies, in one pass over the
DAG, that every node is locally valid and that the root concludes `claim`. The
bound `profile` (theory + leaves + admit + limits, with the theory carrying its own
config) is what makes the *signature* stable while the *bindings* are
consumer-supplied. (Bundling them into `CheckProfile` also fixes the first draft's
API mismatch, where a `TheoryConfig` appeared in the prose but not the signature.)

**Core obligations (consumer-agnostic, the frozen part):**

1. `nodes` non-empty; `root` in range; every node's `conclusion` is a
   `GroundLiteral` (the type enforces ground-ness; a decoder building from
   untrusted input that smuggles a `Var` rejects with `non_ground_conclusion`).
2. **Rule** node: cited clause exists (`program.clause(id)`); `subst` applied to
   the clause head equals `conclusion` and is ground; `premises.len()` = body
   length; each premise index `< node index` (acyclic DAG); premise `i`'s
   conclusion equals the clause's `i`-th body literal under `subst`. **Then**
   delegate `meta` to `profile.admit.admissible(clause, meta, ctx)` (§5a) — where a
   consumer validates rule-node metadata (arche's projection binding + rule-fact
   admissibility).

   **Which equality every site uses: structural** ([#3022](https://github.com/Bitspark/logos/issues/3022);
   research 0028; ruled by `seat:caa`, 2026-09-26; `CHECKER_VERSION` 17). Every comparison `check`
   makes is EXACT. `subst` applied to the head is structurally the conclusion. Every positive
   premise's cited conclusion is structurally the grounded body literal, whatever kind of node it
   cites. A `Neg` premise's `atom` is structurally the grounded negated literal, before its exact
   lookup in the sealed table. A count's grounded `pred`, `filter`, `project` and `k` are
   structurally the premise's. And the root's conclusion is structurally the claim (obligation 5).
   A mismatch is `instantiation_mismatch`, or `root_conclusion_mismatch` at the root.

   The history, because each step narrowed a label-tolerant site. #277 compared the head, a
   `Rule`- or `Leaf`-cited premise, a count's `k` and the root under reify-aware **account
   equality**, which treats a proper list's cons and `list(…)` spellings as one term. #2232 and
   #2227 made a `Builtin`-cited premise and a `Neg` atom exact (`CHECKER_VERSION` 5): the term
   theory decides on its own spelling, and a sealed table answers membership exactly. #2256's
   **exact cone** made every premise of a spelling-sensitive rule instance (one with a `Neg`,
   count or builtin literal) exact, transitively through derived facts (`CHECKER_VERSION` 6).
   #2226 made the remaining sites exact under an opt-in `exact` term identity (`CHECKER_VERSION`
   8). #3022 makes them exact under every identity, because the tolerance was unsound in positive
   proofs too. Account equality is not a congruence: the list normal form never rewrites a cons
   TAIL. So `p([b]). r([a|X]) :- p(X).`, with `X = list(b)`, certified `r([a|list(b)])` by citing
   the leaf `p([b])` for `p(list(b))`, and that claim is true in neither the exact model nor the
   list quotient. With every node's conclusion its own exact fact, the exact cone now holds for
   every rule instance by construction. `vectors/exact_claims.json` pins the refused cases and
   their controls tri-core.

   **What the default certifies.** **Every certified literal claim is EXACT**, and list
   respelling is PRESENTATION. A claim `check` accepts is true in the EXACT model: the least model
   under structural equality, where `[a]` (that is, `.(a,[])`) and `list(a)` are distinct terms.
   A producer may show an answer in the flat `list(…)` spelling
   (`DerivationBuilder::with_list_reification`, whose `present` returns a `PresentedFact`), but
   the display spelling travels BESIDE the exact certified fact and is never certified in its
   place. So a consumer whose EDB holds both spellings gets exact-model negation
   (`\+ member(.(a,[]))` holds against `{member(list(a))}`), counts over structurally distinct rows,
   and a completeness gate (G4) that compares answers with sealed rows structurally
   (§4.5, `vectors/exact_answer_set.json`). The honest engines unify structurally, so every node they
   emit is exact, and nothing they certify moves. A semantics in which the two spellings are one
   term is not a comparison mode. It needs one canonical representation, with patterns, matching
   and builtins defined over it and bound to the certificate, and it would enter as a new
   certification-semantics element, deferred until a consumer requests closed-world claims under
   a non-structural identity (research 0028 A3).

   **The term identity is INERT** (added by [#2226](https://github.com/Bitspark/logos/issues/2226);
   made inert by [#3022](https://github.com/Bitspark/logos/issues/3022)).
   `CheckLimits.term_identity`, `reify_lists` (the default) or `exact`, changes nothing `check`
   decides: `check` ignores it, and the check-profile digest does not fold it (§5), so two
   profiles that differ only there give identical verdicts and share one digest. The contracts'
   `exact_identity_2226` tests check under each identity, and each core's completeness gate replays
   `vectors/exact_answer_set.json` under each, to pin that. #3022's step 5 removed it from every
   layer outside the checker SPI ([ADR 0036](../architecture/decisions/0036-certified-claims-are-exact.md)
   D2): no negotiated spec, request or offer carries it (§4.1). The contract field itself is deleted
   by checker SPI v2 ([#3111](https://github.com/Bitspark/logos/issues/3111)). It does not move to
   the representation axis: how a list is spelled on display is the consumer's rendering choice,
   not a property of what is certified.
3. **Builtin** node: route by ownership — the unique theory with
   `profile.theory.owns(conclusion.pred)` decides it via `decide(conclusion, cfg)`
   (§5), where `cfg` is the **theory's own config, not the live `ctx`** (a theory
   verdict is config-pinned and pure). If no theory owns the predicate →
   `predicate_partition_violation`.
4. **Leaf** node: enforce **sealing** (§4.2), then delegate *all* leaf admission —
   evidence, signatures, placement — to `profile.leaves.verify(conclusion,
   evidence, ctx)` (§6). The kernel itself verifies no signatures (v1 choice, §6).
5. Root node's `conclusion` equals `claim`.
6. **No reachability requirement (frozen; downstream-load-bearing).** `check` verifies
   obligations 1–5 — each cited node locally valid, the root concluding `claim` — and
   **nothing about node connectivity beyond the per-`Rule` premise edges**. It does
   **not** require every node be reachable from `root`: a locally-valid node the root
   does not transitively cite is neither rejected nor required. This *absence* is a
   frozen behavior a downstream consumer's shipped law rests on (thesmos **CD-015**,
   "reach-as-non-op / enforcement-by-absence"), so it is named here rather than left
   implicit — **adding** a reachability requirement is a breaking change under the
   consumer change gate below.

> **Load-bearing for downstream consumers (change gate).** Two *surfaces* of this
> spec are consumed as FIRM law by other boards, and a register of *consumer
> bindings* records who freezes what against them. The surfaces — named here because
> they are provider law and may not silently drift — are: **(i)** the checker
> node-accounting of obligations 1–6 above — *every cited node locally verified ·
> premises 1:1 with body literals · `NodeMeta` opaque-threaded · unknown clause →
> `unknown_clause` · **no reachability requirement*** — a shipped downstream law
> (thesmos CD-015, "reach-as-non-op") is valid *only* under exactly these behaviors,
> so **adding** a reachability requirement is a breaking change under this gate; and
> **(ii)** `ClauseId::canonical` (§2a/§9), the frozen tri-core rule/program
> identity. Both already rest on FIRM floors (ADR 0001 account grammar; §2a/§9
> frozen codec) — a break there reopens those — so this gate adds the
> consumer-notification leg, not a new constraint.
>
> **Change gate:** any PR touching surface (i) or (ii), or any provider surface an
> exposure-register row names, MUST notify the owners of the affected register
> bindings *before* merge, under the discharge and delivery rules below.
>
> **The register of consumer bindings lives in
> [`consumer-exposure-register.md`](consumer-exposure-register.md) — this pointer is
> normative; the rows are a finding.** One row per *binding* — `(consumer, binding,
> consumes-as-law, exposed-to, evidence, state)` — never one bit per consumer:
> exposure is a property of a binding, not of a board (a consumer can pin a digest
> in one artifact and re-derive it in another; #764). Rows are seeded by the
> provider from shipped code and recorded commitments, refutable by their owners in
> one read, and **churn by design** — which is why they live outside this document:
> the history of this file answers "what happened to the law", and a churning
> roster inside it would destroy that signal. The register renders each row's age
> and whether its determination is provider-measured or consumer-confirmed; its
> evidence cells quote consumer facts and never adopt consumer semantics (ADR 0025
> D2 — both requirements are #764 ruling conditions).
>
> **Referred work accepted from horos's frozen §5/§8.** horos's frozen v1 spec routes
> **cross-field relational refinement** (`start < end`, `a ≈ b + k` — any invariant
> over *two fields of a record* rather than over a value) and **int-range /
> unbounded arithmetic refinement** (`index >= 1`) **to logos**, because a horos
> refinement predicates over a value and never over a relation between fields.
> **logos accepts the referral**: this is `ArithmeticTheory` (`<`, `>`, `=<`, `>=`,
> `=:=`, `=\=`) and `TermTheory` (`==`, `\==`) as body literals over variables bound
> by preceding subgoals, and the referral is recorded here so the assignment exists
> on *both* sides rather than only in the referring document. Recorded because a
> **frozen** document can create an obligation for a party that never accepted it,
> and freezing makes that irreversible from the referring side — an unratified
> referral reads to a consumer as a guarantee while binding no one.
>
> **What discharges a notification (applies to every entry above).** A notice is
> discharged only by an **acknowledgement from the notified party**, recorded on the
> PR together with the time the notice was sent. Each notified consumer is recorded
> in exactly one of three states: **acknowledged** (a reply came); **unacknowledged**
> (delivered, no reply); **undeliverable** (the send itself was refused). Silence is
> recorded as *unacknowledged* and **never inferred as absent** — a roster's liveness
> is derived state and has been observed wrong in both directions, so a status read is
> not evidence of reach. Recording the send time is what makes *unacknowledged* a claim
> about a real window rather than a formality; the gate deliberately fixes no minimum
> wait, because a visible timestamp a reviewer can judge beats a number that invites
> being satisfied to the letter.
>
> **Unacknowledged and undeliverable do NOT block the merge.** A dark consumer is not
> a gate failure: making logos's release cadence a function of other repos' uptime
> would be a worse defect than the one this closes. The obligation is *honest
> reporting* — "notified 3 of 4, 1 unacknowledged" — never an unqualified green over an
> empty room. Only *acknowledged* is evidence the gate did its job.
>
> **Each entry names a notification coordinate, and where that coordinate is a seat it
> also names a handle.** Delivery has **four** states, not two, and the coordinate that
> works differs in each:
>
> | recipient state | handle | seat |
> |---|---|---|
> | live | delivers | delivers (prefer: survives handle rotation) |
> | handle dead, **seat vacant** | **refused**; durable write available | **refuses — message destroyed** |
> | handle dead, **seat still held by them** | refused; durable write available | **resolves to the same dead handle — no live route either way** |
> | seat held by a **live successor** | reaches the corpse | **reaches the successor** |
>
> **A dead handle behaves the same way in every row — refused, with a durable write available
> as a deliberate second act.** It is a property of the handle, not of the seat beside it; the
> transport declines rather than let a message strand unread, and `--anyway` is what writes the
> record for whoever revives. (This is the point [#755](https://github.com/Bitspark/logos/issues/755)
> established against source: *"queues"* describes a fire-and-forget the transport does not do,
> and believing it is what produced this week's stranded mail.)
>
> **Use the seat for a record that must outlive its holder; the handle for a message that
> must survive the recipient being down.** The two fail in different *kinds*, not degrees:
> a refused handle costs **a second deliberate act**, a vacant seat costs **the message**. Note the third row —
> a seat held by a dead session is neither vacant nor reachable, so *both* coordinates
> refuse and only a deliberate durable write reaches the record at all.
>
> A refused send is the one failure the sender can observe immediately, and it belongs in
> *undeliverable*, never in *unacknowledged* — the distinction matters precisely because a
> durable write looks, in the sender's log, exactly like a delivery.

**Rejection codes — three bands (logos#3; ADR 0007 added the closed-model cert
band).** The verdict taxonomy is split, and the split is itself part of the firm
account contract:

- **[FIRM] Structural band** — the codes the *kernel itself* emits, frozen
  tri-core (branch on these, not on `detail`):

  ```text
  empty_derivation · too_many_nodes · too_deep · term_too_deep ·
  root_out_of_range · non_ground_conclusion · unknown_clause ·
  instantiation_mismatch · bad_dependency_order · root_conclusion_mismatch ·
  sealed_violation · predicate_partition_violation · unknown_node_kind
  ```

  Two of these are new vs. the first draft: **`too_deep`** (the depth cap of §4.3,
  distinct from `too_many_nodes`) and **`predicate_partition_violation`** (§4.4 — a
  predicate is owned by zero or more-than-one of Theory/extensional/intensional, or
  a node kind doesn't match its predicate's partition; e.g. a `Builtin` whose
  predicate no theory owns). `sealed_violation` is reserved for the *proof-shape*
  error specifically — a `Leaf` concluding an intensional predicate, or a `Rule`
  concluding an extensional one — while *partition* conflicts use
  `predicate_partition_violation`.

  **`unknown_node_kind`** is a derivation component of unknown or absent kind: a node, premise,
  term, value or support ref, in a node or a certificate (#3088, ruled by `seat:caa`). A binding
  whose interfaces can be satisfied by a type the checker does not know, or be null (Go), refuses
  such a component at its boundary, before any gate reads it, and names the component in `detail`.
  The verifier never panics on an untrusted derivation. It checks what it reads: a Leaf's
  evidence and a Rule's metadata are opaque to it (only the consumer's verifiers read them), so
  they are the consumer's to judge.
  A nil or foreign component is outside the account grammar (ADR 0035 D2): no decoder produces
  one and the encoder refuses every one, so it has no digest, and refusing it is not a narrowing
  under ADR 0035 D1 (no `CHECKER_VERSION` bump; `seat:caa`'s ruling on #3088, checked by a test).

- **[FIRM] Closed-model certificate band** — the codes the `\+` verifier emits
  (ADR 0007, §3.1's negation boundary), frozen **tri-core** like the structural band
  (a closed, kernel-emitted set; branch on these, not on `detail`):

  ```text
  cert_out_of_range · cert_budget_exceeded · cert_size_exceeded ·
  cert_decl_mismatch · cert_context_mismatch ·
  cert_context_unbound · cert_scope_incomplete · cert_out_of_domain ·
  cert_unsupported · cert_not_closed · cert_edb_mismatch ·
  cert_partial_scope_invalid ·
  neg_atom_not_sealed · neg_stratum_not_lower · neg_atom_ill_typed ·
  neg_atom_present · neg_atom_partial ·
  count_stratum_not_lower · count_attr_out_of_range · count_mismatch ·
  agg_empty_undefined · count_over_partial
  ```

  These are byte-identical lower_snake_case strings across `{rs,go,ts}` — see
  [`check.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/check.rs)
  `RejectionCode`, [`check.go`](https://github.com/Bitspark/logos/blob/main/contract/go/check.go)
  `RejectionCode.Code()`, and [`check.ts`](https://github.com/Bitspark/logos/blob/main/contract/ts/src/check.ts)
  `RejectionCode`. They split into the **per-certificate gates** (`cert_*`, raised once
  per cited `ClosedModelCert` while verifying its exactness) and the **per-`Neg`-premise
  gates** (`neg_*`, raised against an already-verified cert when discharging a single
  `\+ r(a)`):

  - `cert_out_of_range` — a `Neg` premise cites a `closed_world` index out of range, or a
    `LowerStratum` / `NegLower` support ref inside a cert does (#2258 C3; `CHECKER_VERSION` 7).
  - **The certificate-budget codes (#2335, `CHECKER_VERSION` 10).** Three codes, one per
    party, so a caller's own verify budget is never read as an engine fault:
    - `cert_budget_exceeded` — the **closure** budget, the CALLER's: a cert's *declared*
      `rule_groundings` / `join_steps` exceed `max_rule_groundings` / `max_join_steps`, or
      the closure join's count exceeds them while it runs. The kernel maps it to
      `CheckLimitExceeded { ClosureGroundings }`.
    - `cert_size_exceeded` — the **size** budget, the CALLER's: a cert's *declared*
      `cert_bytes` / `cert_facts` / `domain_values` / `support_edges` exceed the matching
      `max_*`. The kernel maps it to `CheckLimitExceeded { CertSize }`. It has no CLI flag:
      the embedding host raises it through its `CheckLimits`.
    - `cert_decl_mismatch` — a **lying declaration**, the ENGINE's fault: a cert's
      *actual* `cert_bytes` / `cert_facts` / `domain_values` / `support_edges`, or the closure
      join's count of groundings or join steps, exceeds the cert's OWN declaration. The kernel
      classifies it as malformed (engine inconformance), never as a budget.

    **`cert_bytes` is MEASURED since #2524 (`CHECKER_VERSION` 13).** A cert's actual size is
    the length of its canonical wire encoding (`closed_model_cert_as_value` through the ontos
    codec) **with `limits_decl.cert_bytes` set to 0**: the encoding contains the declaration,
    so a cert declaring its own literal size would be circular. One definition in all three
    cores (`cert_encoded_bytes` / `CertEncodedBytes` / `certEncodedBytes`), pinned by the
    generated `vectors/cert_encoded_bytes.json`. Before 13 `cert_bytes` was a declaration only,
    so `max_cert_bytes` bounded what a cert declared, not what it was. Bounding the bytes a host
    reads BEFORE decoding is the transport's (#2528).

    ⚠ **Until `CHECKER_VERSION` 10, `cert_budget_exceeded` covered all three**, so a
    verdict stored under an older version meant something wider than the closure budget.

    **Order, and why.** The declared-size gate runs **first, before any scan**: it reads
    six declared numbers against the budget, which is O(1), and the budget it enforces
    bounds every later scan. Then the actual sizes are compared with the declaration.
    `cert_facts`, `domain_values`, `support_edges` and `cert_bytes` are compared with the
    artifact there.
    The two closure counters, `rule_groundings` and `join_steps`, are compared with the
    budget **and with the declaration** as the scan runs (#1829, #1852), budget first,
    tripping the moment the count exceeds either. So the scan cost of a checked cert is
    bounded by `min(declared, budget)`, never by the budget alone.

    The consequence for a cert that both lies AND exceeds the budget (pinned in
    `negation.json`):
    - if its **declaration** is already over the budget, the caller's code wins
      (`cert_size_exceeded` / `cert_budget_exceeded`). Nothing is excused: raising the
      budget re-checks, and the lie then surfaces as `cert_decl_mismatch`.
    - if its declaration is **within** the budget while its actual size is over it,
      `cert_decl_mismatch` wins. The lie is what moved it past the budget gate, so the lie
      is what is reported.

    A *grounding* is one body-true tuple the closure join emits. A *join step* is one
    candidate examined at one body literal: a sealed-table row offered to a binding
    literal, the current tuple offered to a filter literal, or a lower-table row a count
    stage scans (#2258 L3.3b: one join step per row of the counted relation, each time the
    count is evaluated).
  - `cert_context_mismatch` — a cert's four pinned hashes (program / profile / ctx /
    theory-config) — `program_hash` *recomputed* from the live program — do not match
    the bound check context.
  - `cert_context_unbound` — a `Neg`-bearing derivation was checked under an all-zero
    (unbound) `CertContext`; the plain `check()` wrapper supplies a zero context, so a
    cert is verifiable only via `check_with_cert_context` (a zero context must never
    *satisfy* a cert's pins).
  - `cert_scope_incomplete` — the sealed stratum prefix is not self-contained: a
    scope-defining clause references a predicate neither sealed, theory-owned, nor sealed by
    a certificate at a strictly lower level, seals a theory-owned builtin, carries a
    non-flat (tuple/compound) argument, has an unsafe / non-range-restricted variable,
    negates a predicate sealed by the same prefix (intra-scope negation), or leaves a
    closure body literal undecidable. With **stacked certificates** (#2258 (a)) a sealed
    clause may read, positively or under `\+`, a predicate that the UNIQUE, EXACT, Valid
    certificate at a strictly lower level seals: certificates are verified in ascending
    level, so a lower one is known Valid before it is read. A predicate sealed by more than
    one strictly lower certificate (ambiguous), or by one that marks it partial, is refused
    with this code; a lower certificate that is invalid makes the one reading it invalid
    with the lower certificate's own code. Since #2258 L3.3b (`CHECKER_VERSION` 14) a sealed
    clause may also carry a count (`count` / `count_distinct` / `sum` / `min` / `max`) over
    such a relation. Its filter variables must be bound by positive sealed literals, and it
    binds its result variable. The closure evaluates it as a **count stage**: due at the first
    point its filter is bound, counts before filters at each point, both in declared order. A
    count over a relation the certificate itself seals, a theory-owned relation or an unsealed
    one is refused with this code. A `min`/`max` over no matching row has no value, so the
    count is false and the grounding does not fire.
  - `cert_out_of_domain` — a value reachable through the cert (an extension row, a
    support-edge image, or a satisfied closure grounding's head) lies outside the
    sealed finite domains.
  - `cert_unsupported` — a sealed IDB fact lacks a valid support edge, so `E ⊄ least
    model` (junk / unfounded — including the `p :- p` self-justification the strict
    semi-naive rank descent rejects). It also covers a `LowerStratum` / `NegLower`
    support ref citing an in-range cert that is neither its OWN nor the strictly lower
    certificate the ref's predicate resolved to (#2258 C3, (a)): a cross-certificate ref
    must cite exactly the seal the scope gate reads, and is decided against that
    certificate's exact table. A count body literal is supported by a `CountLower { cert }`
    ref (#2258 L3.3b). It carries no atom: its filter and result are the edge's grounded
    `subst`. It must cite the strictly lower certificate the counted predicate resolved to
    (citing its own certificate is refused), and the aggregate recomputed over that table
    must equal the result. A count with no value supports nothing. Any failure here is
    reported with this code.
  - `cert_not_closed` — a satisfied grounding of a scope rule has a head absent from
    `E`, so `least model ⊄ E` (a missing head — the relation is not closed).
  - `cert_edb_mismatch` — a sealed *extensional* table does not equal the live EDB
    snapshot the bound `LeafVerifier` attests (or no snapshot is attested — the
    fail-closed default).
  - `neg_atom_not_sealed` — the negated predicate is not sealed by the cited cert.
  - `neg_stratum_not_lower` — the negated predicate is not in a *strictly lower*
    stratum than the rule head (the rule head is itself in the cert's sealed scope).
  - `neg_atom_ill_typed` — the negated atom is not ground / not within the cert's
    finite domain.
  - `neg_atom_present` — the negated atom **is** present in the sealed relation, so
    `\+` does not hold.
  - `cert_partial_scope_invalid` — the cert's `partial_scope` (ADR 0030 D1) is ill-formed:
    not canonical, empty, not a subset of `scope` at the prefix's own level, naming an
    extensional table, or not upward-closed within the sealed prefix (a complete sealed
    head reads a partial table). Verified before any table is consulted.
  - `neg_atom_partial` — the negated predicate is sealed as a **lower bound**
    (`partial_scope`); absence from a partial table is not a proof of absence
    (ADR 0030 D2).

  The **per-`Count`-premise gates** (`count_*`, ADR 0023 — a `Premise::Count { pred,
  filter, project, k, cert }` discharging a `count`/`count_distinct` body literal against
  an already-verified cert, the negation gates' structural twin) join the same
  **structural / FIRM** band, byte-identical `lower_snake_case` tri-core:

  - `count_stratum_not_lower` — the counted predicate is not in a *strictly lower*
    stratum than the rule head (a count is non-monotone, so it must read a sealed lower
    stratum — the negation discipline applies unchanged).
  - `count_attr_out_of_range` — a `filter` position, or the `project` attribute index, is
    outside the counted relation's arity (matched by name **and** arity, #581).
  - `count_mismatch` — the claimed cardinality `k` does not equal the count `n` the
    checker **recomputes** over the proven-exact sealed relation (the core dual-conformance
    guarantee — the searcher proposes `k`, the gate re-derives it and rejects a wrong one).
  - `agg_empty_undefined` — a `min`/`max` fold (`ProjectSpec::Min`/`Max`, the ADR 0023
    `min`/`max`/`sum` amendment, #587) over an **empty** matching set is undefined and
    rejected — v1 mints no infinity or sentinel; an empty `sum` is `0`, never this code.
  - `count_over_partial` — the counted predicate is sealed as a **lower bound**
    (`partial_scope`); a count over a partial table is not the count (ADR 0030 D2).

  The verifier that emits these is **TOTAL** (every cited cert and every `Neg` premise
  reaches a definite accept/reject — an undecidable in-scope literal is a *hard*
  `cert_scope_incomplete`, never a silent pass), **non-searching** (every loop ranges
  over a *supplied* finite table / domain, each pre-bounded by the budget gate validated
  before any scan — no fixpoint, no Herbrand enumeration beyond the supplied domain, no
  engine call), and **TRI-CORE** (`{rs,go,ts}` verify the closed-model certificate / `\+`
  premise identically; PRs #427/#428 brought go + ts to parity with the Rust account).
  This band is **structural / FIRM** — closed and kernel-emitted, *not* a host-extension
  seam — so unlike the host-extension band below it carries no consumer sub-codes.

- **[STABLE v1, open set] Host-extension band** — verdicts a delegated extension
  point raises. The *mechanism* (codes are namespaced to their seam; delegated
  sub-codes are additive) is part of the stable v1 contract; the *set itself stays
  open* — a consumer registers its own (arche's projection/leaf/attestation
  verdicts live here, pinned only in arche's own suite, never in the cross-core
  kernel set). "Open set" and "stable mechanism" are compatible: adding a sub-code
  is the additive change v1 explicitly permits.

  ```text
  builtin_failed     (Theory, §5)            leaf_rejected   (LeafVerifier, §6)
  rule_inadmissible  (RuleAdmissibility, §5a)
  ```

> **Why a band, not a flat enum (the open/closed fix, logos#3).** You cannot both
> byte-freeze `RejectionCode` as a *closed* tri-core enum *and* let a consumer add
> its own verdicts (`not_visible_in_projection`, `projection_mismatch`, etc.). The
> first draft tried "one code may be emitted by two extension points" — that was a
> patch on the wrong model. The band split is the real fix: the **structural band
> is closed and frozen**; the **host-extension band is open**, and a consumer's
> codes are pinned only in *that consumer's* suite. arche's
> `not_visible_in_projection` then needs no "shared across buckets" special case —
> it is simply an arche host-band code that arche's LeafVerifier *and* its
> RuleAdmissibility may both raise, with no claim on the frozen kernel set.
>
> **Mapping onto arche-core's 17 codes** (verified against `proof.ts`): the
> structural-band codes above map to arche-core's `empty_proof`, `too_many_nodes`,
> `root_out_of_range`, `non_ground_conclusion`, `unknown_rule`(→`unknown_clause`),
> `instantiation_mismatch`, `bad_dependency_order`, `root_conclusion_mismatch`,
> `unknown_node_kind`, `sealed_leaf`(→`sealed_violation`). The remaining
> arche codes — `malformed_signed_fact`, `bad_leaf_signature`, `admission_failed`,
> `not_visible_in_projection`, `projection_mismatch` — are all arche **host-band**
> verdicts (LeafVerifier / RuleAdmissibility), pinned in arche's suite only.
> Nothing is lost; each relocates to the right band. (Both `too_many_nodes` and the
> RuleAdmissibility hook were gaps found by mapping all 17 codes.)

<a id="context"></a>

### 4.1 Context — and the placement-predicate the checker MUST enforce  [STABLE v1 · pin hardest]

`Context` is a consumer-defined value the core **threads**. It carries whatever
the Theory, LeafVerifier, and RuleAdmissibility need beyond the node itself.

- arche binds `Context = { targetSpace, factIndex, root_pubkey }`.
- logos-as-plain-engine binds `Context = ()` (nothing).

**Projection is a trusted-CHECK guarantee, not a search-time filter (logos#5 — the
one to tattoo on the wall).** The tempting "mechanical" move — *let logos be
space-blind; the consumer's leaf source only yields visible facts* — is
**unsound**: it demotes a trusted-path property to a trusted-*search* assumption.
A derivation citing an out-of-projection leaf would then pass a space-blind
checker, because the thing that used to reject it (a visibility check *inside*
`check`) is gone and only the *untrusted* search's choice of leaves enforces it.

So the contract keeps logos space-blind **without** losing the guarantee via a
generic, **checker-validated placement predicate**: a host-supplied relation over
`(leaf/clause metadata, Context)` that the **trusted `check` calls and enforces**,
rejecting a node whose metadata is not admissible in `ctx` (a host-band verdict).
arche plugs in its `visibleFrom`; logos itself defines **no** space, `targetSpace`,
or `factIndex` — the generic concept logos owns is "the host may supply a
placement/context predicate the checker enforces," *not* projection. (If a
consumer instead chooses the leaf-prefilter route, that is a **conscious reduction
of the trusted guarantee** and must be documented as such — never shipped as
"preserves exact behavior.") This is the `RuleAdmissibility` (§5a) + a leaf-side
placement hook in the `LeafVerifier` (§6); both run *inside* `check`.

**Node-invisibility & the per-space dense index (fleet law of record, 2026-07-25).**
Because logos defines **no** space, `factIndex`, cursor, head, or receipt — the
space and the fact-index live entirely in the consumer's `Context`, opaque to the
kernel — logos is **node-invisible by construction** and imposes **no cross-space
order.** Two facts in different spaces are *incomparable* to `check`; there is no
global index domain and no cross-space happened-before anywhere in the account or
the checker. (Every "total order" in this codebase is a canonical *byte* ordering —
clause-id / term / program-serde sorting — not a fact-sequence order.) The per-space
**dense index** (contiguous, gap-free, 1-origin; head index = the space's fact
count) and its completeness / anti-hidden-retraction guarantee are **store/law**
properties owned by logos-db (the op-log cursor), stele (the signed head), and
thesmos (the verifier obligation) — logos consumes an index only as an opaque
per-space coordinate the consumer's placement predicate enforces, never as a
cross-space ordering. This makes node-invisibility an instance of the
blindness-partition logos already lives by: no derivation may reveal, and none rests
on, whether two spaces share a node. Any future consumer clause that leaned on a
node-global cursor's incidental total order would be a violation and must be
re-founded on explicit per-space reasoning (none exists in the account today).

### 4.3 CheckLimits (resource cap on the supplied derivation)

`check` consumes an **untrusted** derivation, so it MUST be bounded independently
of the search side. `CheckLimits` caps total node count (→ `too_many_nodes`),
DAG depth (→ `too_deep`), and **single-term nesting depth** (→ `term_too_deep`).
This reproduces arche-core's `MAX_NODES` guard and adds the two depth bounds.
Distinct from §7 `Limits`, which bounds *search effort*; this bounds *proof size on
verify*.

The cap is a **hard, deterministic rejection** (G9): the bound is checked **before
any node delegation** to a Theory/Leaf/RuleAdmissibility, and exceeding it rejects
with `too_many_nodes` (a strict `>` over the configured maximum). No node is
inspected once the cap is exceeded — so an oversized untrusted proof cannot cause
work proportional to its size before being refused.

**Term-nesting depth (`max_term_depth` → `term_too_deep`, the DoS-hardening bound).**
A single *term* can nest arbitrarily deep within one node (`f(f(f(…)))` tens of
thousands deep, or a deep cons-chain), which neither the node cap nor the DAG-depth
cap bounds. The trusted path traverses terms **recursively** — term decode /
`from_value`, substitution, structural equality, the canonical account-codec/`quote`
bytes, and `Drop` — so a pathologically deep term would overflow the native stack and
**abort the trusted checker** (a liveness/DoS failure, not just a wrong answer).
`check` therefore measures the nesting depth of every term it will traverse (each node
conclusion, the claim, and every cited clause's head/body/subst terms — plus, for a
`Neg`-bearing derivation, the cited certificates' deep data) **before** any recursive
operation runs on it, and rejects `term_too_deep` if any exceeds `max_term_depth`.

Two properties make the bound itself safe and faithful:

- **The measurement is non-recursive** (an explicit work-stack walk with an early
  cutoff), so checking a pathologically deep term's depth does not *itself* overflow —
  a recursive depth-measure would defeat the purpose. The work the gate performs before
  refusing an over-deep term is bounded by `max_term_depth`, not by the (unbounded)
  term.
- **`from_value` and the wire decoder's term readers (`reify`, `erase_ground`) are
  non-recursive too** past the recursion budget (#2275 layer 3), so a deep value is lifted
  into a term, and a deep quoted term decoded, without the construction step crashing. **The
  decoder imposes no depth policy** ([#2731](https://github.com/Bitspark/logos/issues/2731)):
  it never refuses a well-formed derivation for its depth; `check` does, below.

The default (`256`) is chosen empirically: the worst-case single recursive term op
overflows at a nesting depth of ~670 on the ~1 MiB Windows main-thread stack in an
unoptimized debug build, so `256` sits at a ~2.6× margin below that boundary while
giving ~50× headroom over any realistic ground term (real data nests a handful of
levels). The bound is **tri-core-consistent** (`{rs,go,ts}` use the same default and
emit the same `term_too_deep`), so a derivation accepted by one core is accepted by all
three, and a pathological one is refused by all three. It only *refuses* pathological
inputs — the admissible fragment and every accept path are unchanged. A consumer that
genuinely needs deeper terms raises `max_term_depth` *and* the host stack together.

**Two depth bounds, and only one is a policy** ([#2731](https://github.com/Bitspark/logos/issues/2731),
`seat:caa`'s ruling):

- **POLICY: `max_term_depth`.** `check` alone applies it, with the same default (`256`) and the
  same refusal (`term_too_deep`) in every core. It is the only depth at which a well-formed
  derivation is refused, and the promise above is about it.
- **CAPACITY: how deep a value a core's representation can hold.** Each core declares its own
  and refuses past it by name: rs's `VALUE_STACK_DEPTH_LIMIT` (6,144 term levels) as
  `value_too_deep`, and each host's measured reply bound as `reply_decode_limit`. The codec's
  decode depth (1,024 value levels by default, in all three cores) bounds a wire. No capacity
  sits below the policy default: a derivation carrying a ground argument 256 term levels deep
  is a wire about 520 value levels deep.

The promise is pinned at the boundary: `derivation_wire.json`'s
`ground_arg_256_term_levels_decodes` and `ground_arg_257_term_levels_decodes` decode in every
core, and `check.json`'s `term_depth_256_at_the_default_accept` and
`term_depth_257_past_the_default_term_too_deep` give the same verdicts tri-core at the default
policy. Until #2731, rs's decoder refused any quoted value past 256 VALUE levels (about 128
term levels), so a derivation between about 129 and 256 term levels deep was accepted by go and
ts and refused by rs, and this promise was false at the defaults.

**Term identity (`term_identity`; INERT, [#2226](https://github.com/Bitspark/logos/issues/2226), [#3022](https://github.com/Bitspark/logos/issues/3022)).**
`CheckLimits` also carries the term identity, so the type holds more than budgets; it keeps its
name. Since #3022 the identity is inert: `check` ignores it, since every site is structural (§4
obligation 2), and the check-profile digest does not fold it (§5). Checker SPI v2 deletes it
([#3111](https://github.com/Bitspark/logos/issues/3111)). No negotiation wire carries it since
#3022's step 5 ([ADR 0036](../architecture/decisions/0036-certified-claims-are-exact.md) D2):
`CheckLimitsSpec` is `record[max_nodes, max_depth]`, a pinned offer's `OfferPins` is
`record[theories, feature_set, limits_floor]`, and a request's host-gate `CheckLimits` record
carries the nine budgets. Each decoder refuses any other arity, so the forms that carried the
identity (a third `CheckLimitsSpec` element, a served-identity set second in `OfferPins`, a tenth
element in the request's record) are refused rather than mis-read. A kernel that builds a
contract `CheckLimits` from a decoded record leaves the field at its default.

### 4.2 Sealing (generic soundness invariant, consumer-parameterized)

A leaf may conclude **only** an *extensional* predicate (one the LeafVerifier
owns); a clause head defines an *intensional* predicate. The core rejects
(`sealed_violation`) any `Leaf` whose `conclusion.pred` is intensional, and any
clause head that collides with an extensional predicate. The *set* of extensional
predicates is declared by the LeafVerifier — so sealing is generic machinery, and
"which predicates are sealed" is the consumer's data. (This reproduces
arche-core's `sealed_leaf` + the `signed_fact`-only leaf rule, without hardcoding
`signed_fact`.)

### 4.4 Predicate partition (disjointness invariant — G3)

Over the predicates that appear in a `Derivation`, the three node kinds partition
the predicate space and the partition MUST be **disjoint and exhaustive**:

- **builtin** predicates — those a `Theory.owns` (§5);
- **extensional** predicates — those a `LeafVerifier.extensional()` declares (§6);
- **intensional** predicates — those that appear as a clause head in the `Program` (§2).

A predicate is exactly one of these. The core relies on the partition: a `Builtin`
node's predicate MUST be owned by a Theory, a `Leaf` node's predicate MUST be
extensional, a `Rule` node's conclusion predicate MUST be intensional. Overlap is a
program-construction error the consumer must avoid (e.g. an extensional predicate
that is also a clause head). arche depends on this (its sealing is exactly the
extensional∩intensional = ∅ case, §4.2).

> **Where the kernel refuses an overlap (#2253, #2277).** The kernel's front door refuses a
> request whose program overlaps the partition with `predicate_partition_violation`, before any
> engine runs. Where the host binds the gate's declared set `D` (the leaves'
> `extensional()`), the overlap it refuses is **`D ∩ idb`**: a declared predicate that heads a
> rule, whether or not the program also carries rows for it. `idb` is every predicate heading a
> clause other than a ground body-less row (rs, #993; the go and ts native kernels, which admit no
> non-ground clause natively, #1004, read every body-less clause as a row), so a declared
> predicate carried by ground rows alone is extensional data, not an overlap, and a ground row
> beside rules of an UNDECLARED predicate is an intensional rule-fact (§2). Refusing at the front door names the request. Left to the
> checker, a `Rule` proof concluding a declared predicate is `sealed_violation`, which blames
> whichever engine proved the rule honestly, while a leaf-proving engine passes the same
> request. Without a declared set, the front door sees only the syntactic overlap: a predicate
> with both a ground row and a rule. (Rulings:
> [#2253](https://github.com/Bitspark/logos/issues/2253#issuecomment-5815110464),
> [#2277 (a)](https://github.com/Bitspark/logos/issues/2277#issuecomment-5816453792).)

> **Standard-library predicates and the account (ADR 0016).** The placement of a
> standard/predefined predicate follows from whether it produces an account node a
> checker sees. **Shelf A** (a trusted `Theory` primitive — e.g. arithmetic) produces a
> checkable **`Builtin`** node; **Shelf B** (a hash-pinned Horn-clause prelude) produces
> checkable **`Rule`** nodes; both are inside this contract's account and carry stdlib
> pinning. **Shelf C** — engine-only search/meta/control (`\+` NAF, `!` cut,
> `findall`/`bagof`/`setof`/`aggregate`, and the meta-introspection builtins
> `var`/`nonvar`/`copy_term`/`functor`-construction) — is owned by **no `Theory`**, so it
> adds **no account node** and carries **no stdlib pinning**: it is search-side only
> (§3.1, §7). The falsifiable rule is "does it add an account node?" — see
> [ADR 0016](../architecture/decisions/0016-standard-library-placement.md).

> **EDB predicates and stratum membership (ADR 0007).** This partition also fixes
> *stratification* membership for stratified negation: strata partition the
> **intensional** predicates only. An **extensional** (EDB-only) predicate is a
> dependency-edge target, **never a stratum member** — it sits below stratum 0 — and the
> closed-world proof obligations are counted **one per rule stratum**, not one per
> predicate. A reimplementer who counts every dependency SCC (EDB nodes included) as a
> stratum diverges (the #464 two-core regression); the normative statement of this
> convention is the cross-core consumer contract in
> [ADR 0007](../architecture/decisions/0007-certifiable-stratified-negation.md).

> **The order of the strata (#2477).** The analysis records its strata in ONE canonical
> order, which is a property of the program's content, not of how the program is written or
> traversed: a **topological order of the SCC dependency DAG over the intensional
> predicates** in which, among the SCCs the dependencies leave free, the one whose **sorted
> member list is bytewise least** comes first (Kahn's algorithm with a min-priority queue on
> that list). Stratum members and dependency edges are name-ordered too, so the whole
> stratification record is content-ordered. The order reaches the analysis digest and the
> request digest and nothing else: `check` computes no stratum order, so certificate
> acceptance never depends on it, and an engine may evaluate independent strata in any
> order. A reimplementer who records the order a traversal happens to emit (Tarjan's
> completion order, or rule order) diverges on programs with independent SCCs: for
> `a :- z.`, `z :- e.` and an independent `b :- e.` the record is `[b, z, a]`, not
> `[z, a, b]`.

<a id="answer-set"></a>

### 4.5 G4: the answer-set comparison  [STABLE v1 · #3023]

A delivered closed-world answer is a SET: the emitted answers claim to be every answer to the goal.
The completeness gate (design 0008) checks that claim in four steps. The last, **G4**, is a contract
operation, one normative function per language (research 0028 row A16, `seat:caa`'s ruling on
#3023):

```
check_answer_set(goal: Goal, sealed: [GroundLiteral], claims: [GroundLiteral])
    -> Ok | AnswerSetMismatch { Extra(GroundLiteral) | Missing(GroundLiteral) }
```

rs `check_answer_set`, go `CheckAnswerSet` (nil when it holds), ts `checkAnswerSet` (`undefined`
when it holds).

- **Instance.** A row is an instance of `goal` when it has the goal's predicate and arity and one
  binding of the goal's variables makes the goal STRUCTURALLY equal to it. A repeated variable binds
  one value, and a list's cons and flat spellings are different terms (§1). rs computes it with
  `Term::match_value`, the one matcher. go and ts each have the one instance test in their contract.
- **Set.** Two answers are one answer exactly when they are structurally equal, keyed by
  `ground_key`. Repeats collapse.
- **Verdict.** `Ok` exactly when `claims` equals the set of `sealed` rows that are instances of
  `goal`.
- **Precedence (normative).** The result names the FIRST emitted answer that is not a sealed
  instance, in claim order. Otherwise it names the first sealed instance that was not emitted, in
  `ground_key` order.
- **Closed vocabulary.** `AnswerSetMismatch` is exhaustive: it lists exactly the two ways a set
  comparison fails. Every consumer maps it member by member, and a third member would be a v2 item.
  It is not a `RejectionCode`: this is a separate operation, not a `check` verdict over an account.
  Each kernel renders it as its gate's `completeness_set_mismatch`, and the rendering is not
  normative.

`vectors/exact_answer_set.json` pins every rule above, the precedence included, and is replayed
through this entry point in all three cores.

<a id="theory-spi"></a>

## 5. Theory SPI  (builtins / decidable atoms)  [STABLE v1]

```rust
trait Theory {                                       // NOT generic over Context — see purity below
    fn owns(&self, pred: &Symbol) -> bool;
    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome;  // pure, total, deterministic; config closed over at construction
    fn decide_ground(&self, atom: &GroundLiteral) -> Completion<TheoryDecision, NoCallerLimit> {  // additive (ADR 0003, #3126): can say "not decided"; see §5.2
        ground_from_legacy(self.decide(atom))
    }
    fn identity(&self) -> ComponentIdentity { ComponentIdentity::unidentified() }  // additive (ADR 0003): the (id, version, config_digest) attestation triple
    fn completion(&self, pred: &Symbol) -> DecisionCompletion { DecisionCompletion::Undeclared { decider: self.identity() } }  // additive (ADR 0003, #3142): is every stop on pred typed, so its Fails is a decided false?
}
enum TheoryOutcome { Holds, Fails { code: String }, NotMine }
enum TheoryDecision { Holds, Fails { code: String } }  // completion.rs: a theory's own decision, its code kept as data
enum DecisionCompletion { StopsAreTyped, MayNotComplete { decider: ComponentIdentity, cause: String }, Undeclared { decider: ComponentIdentity } }
```

**`completion` (#3142, research 0031 row 13).** A decision that stops before it decides (a
capacity, a bounded-work cap, a host refusal, an unreadable reply) can surface the stop as `Fails`,
and `check` reads that as a decided false. A sealed closure (§"What the checker verifies", ADR 0007)
then under-fires, and a table that misses a derivable row passes as exhaustive. `decide_ground`
(#3313) is the typed channel on which a stop is `NotCompleted` and never `Fails`. `completion` is
the decider's declaration of whether every stop on an owned predicate reaches readers that way:
`StopsAreTyped`, named for the claim the guard needs (a decider here may still stop). It changes no
verdict of `check`: the certifying kernel reads it at ADMISSION and refuses, by name, a seal whose
clauses reach a decider that does not declare `StopsAreTyped` (the undeclared default fails
closed). The standard theories declare `StopsAreTyped`: arithmetic since #3313 typed its work cap,
and text, term and list, which never stop. Host builtins stay `MayNotComplete` until the host's own
decider declares its completion (#3506): #3374 typed only the guest's side, and the claim belongs to
the decider at check time. The declaration retires at v2: ADR 0036 D8 makes `decide_ground`
required and deletes `decide`, and `completion` goes with them. Go spells it as the optional
`CompletionDeclared` interface and ts as the optional `completion` member, the idioms the seams
below use.

`Theory` is deliberately **not** generic over `Context`: a theory verdict must not
depend on the live verification snapshot (that is the leak the purity rule below
forbids). Its only input beyond the ground atom is its **construction-time
configuration** — closed over at construction, not threaded per call (the object-safe
shape §5.1 pins; the earlier `type Config` / `decide(atom, cfg)` associated-type draft
is reconciled away here, as it is not object-safe against §4's `Box<dyn Theory>`) — a
parameterized fact whose pin is the `config_digest` of the `identity()` triple.

- arche binds the `is_root` theory (`Holds` iff `atom = is_root(k)` and `k` is the
  configured root pubkey). Other consumers bind arithmetic/comparison/time.

**Purity is load-bearing, not a nicety (logos#4 — "authorization is a checkable
query").** A theory verdict MUST be:

- **pure** — a function of the ground arguments alone;
- **total + deterministic** — same args → same verdict, always;
- **reproducible from config** — effectively a *parameterized fact*, so the input
  is `TheoryConfig` (config-derived, e.g. arche's root pubkey), **not** the live
  `Context`. (Passing live `ctx` into `decide` is the leak vector: it lets a
  verdict depend on mutable state, silently degrading "checkable from config" to
  "checkable modulo trusting an oracle." The first draft's `decide(atom, ctx)` is
  corrected here to `decide(atom, cfg)`.)
- **no I/O, no clock, no ledger access.**

This is **not** an opaque `(name, args) → bool` oracle (logos#3): such an oracle is
an arche escape hatch wearing a generic name. The generic concept logos owns is a
**config-pinned axiom/trust-anchor set** — a parameterized relation, re-derivable
by anyone. The operational test (a recommended vector): *same facts + same config
→ byte-identical derivation regardless of host*. If a theory cannot be reduced to a
config-derived pure function, that is a **property regression to surface**, not
something to assert by silence.

#### 5.1 The native-predicate purity invariant (load-bearing for "authorization is a checkable query")  [STABLE v1]

The purity of a native predicate a `Theory` decides is **not a stylistic nicety —
it is the precondition for the FIRM "check() re-derives the same proof" property,
hence for the framing "authorization is a checkable query"** (ADR
[0008](../architecture/decisions/0008-planning-logic-kernel.md),
[0009](../architecture/decisions/0009-certification-gate.md)). State it as an
invariant a `Theory` (and its search-side dual `BuiltinSolver`) MUST satisfy:

> **INVARIANT (native-predicate purity).** A predicate a `Theory` decides MUST be
> reducible to a **config-parameterized pure function** of its ground arguments —
> **pure, total, deterministic, config-reproducible, and free of I/O / clock /
> mutable-state / ledger / network access.** It is a *parameterized fact*, **not a
> live oracle**. Equivalently: `decide(atom)` is a mathematical function of `(atom,
> config)` alone, where `config` is fixed at construction.

This is exactly what the realized seam encodes — and it is enforced *structurally*,
not by convention:

- **`Theory::decide(&self, atom: &GroundLiteral) -> TheoryOutcome`** takes **only**
  the ground atom; it is **not generic over `Context`** and is **never handed the
  live verification `ctx`** (the leak vector §5 / ADR 0003 name). The theory's
  configuration is **closed over at construction** (e.g. `IsRoot::new(pubkey)`,
  `ArithmeticTheory::new()`), so a caller cannot vary it between two `decide` calls
  on the same boxed theory. *Source of truth:*
  [`contract/rs/src/spi.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/spi.rs)
  — the `Theory` trait (`owns` + `decide` + the additive `identity`), whose
  doc-comment states "a verdict MUST be a pure, total, deterministic function of the
  ground arguments alone, reproducible from configuration, with no I/O, clock, or
  ledger access."
- **The `config_digest` of [`ComponentIdentity`]** (the `(id, version,
  config_digest)` triple `Theory::identity()` returns) is what lets the certifying
  kernel *attest* the config a derivation was checked under — so "config-pinned" is
  itself a checkable fact, not an honor-system claim.
- **`CompoundTheory`'s identity byte layout is FROZEN tri-core** (logos#767, pinned by
  [`vectors/identity_audit.json`](https://github.com/Bitspark/logos/blob/main/vectors/identity_audit.json)):
  the prefix `logos-core/compound-theory/v1\n`, then per member `u64-BE len(id) ‖ id ‖
  u64-BE len(version) ‖ version ‖ 32-byte config_digest`, under wrapper identity
  `logos-core/compound-theory@1.0.0`. **Member order is identity-bearing.**
  This is recorded here rather than only in the vector because it is a **constraint, not an
  addition**: it was already load-bearing before it was pinned — a compound's identity folds
  into `CheckProfileDigest`, so any change to the layout moves *every* derived digest for
  *every* consumer binding a compound theory. The vector makes an existing immovability
  checkable; the normative statement is what makes it **discoverable before you break it**
  rather than when replay reds.
- **The search side is held to the same bar by dual-conformance.** The
  `BuiltinSolver` seam
  ([`contract/rs/src/engine.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/engine.rs))
  may *bind* a variable (`?- X is 2+3`), but each substitution it returns, deep-
  applied, MUST ground the goal to an atom the **paired `Theory::decide` also
  accepts** (`Holds`) — the engine re-runs `decide` as a gate before emitting the
  `Builtin` node. So an impure or config-divergent solver cannot smuggle an
  unsound `Builtin` node past `check`; its proposed solution is simply dropped.

**Why it is load-bearing.** `check` is `total` and performs **no search**: for a
`Builtin` node it routes by `owns` and asks `decide(conclusion)` (§4 obligation 3,
[`check.rs`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/check.rs)).
If `decide` consulted a clock, a ledger, or any live state, then **two checkers
re-deriving the same proof from the same program + config could disagree** — the
very property "anyone can re-check, trusting none of the search" (ADR 0001) would
collapse, and an "authorized" verdict would mean only "authorized *at the instant
and on the host that searched*," not "authorized as a checkable consequence of the
config-pinned program." A live oracle turns a *proof* back into a *trust-me*. The
purity invariant is what keeps authorization a **query whose answer a third party
can reproduce byte-for-byte** — the whole point of the check direction.

**The reproducibility test (now a real vector, not just recommended).** The
operational test is realized as a Rust conformance vector that pins the
**byte-identical proof bytes** of the same builtin atom over the same config:
[`conformance/rs/tests/theory_purity.rs`](https://github.com/Bitspark/logos/blob/main/conformance/rs/tests/theory_purity.rs)
encodes a `Builtin`-bearing derivation through the **frozen `ontos-codec`** (the
account codec, §2a/§9) and asserts the digest is stable across repeated decisions
and independently-constructed theories — the concrete witness that `decide` is a
function of `(atom, config)` alone. (`vectors/arithmetic.json` already pins the
`decide` *verdict* tri-core; this adds the *derivation-byte* reproducibility the
invariant names.)

**The search-side counterpart of a Theory, across a wire (#1604; `seat:caa`'s ruling).** A
`Theory` decides a ground atom; a **Solver** binds an open one. They are **one component** —
one `identity()` covers both — and every binding a Solver returns MUST be an atom its Theory
decides `Holds`. Search calls the Solver, check calls the Theory, and the account records the
binding as an ordinary `Builtin` node — which is what makes the two halves checkable against
each other. In-process (rs) the engine re-decides each binding before emitting the node
(dual-conformance, above). **Across a wire** — a go/ts host driving the wasm guest — the Solver
is reached by the guest's `logos_host::builtin_solve` import for the predicates the host
**declared** in its request (`SearchRequest::host_builtins`: `{pred, arity, identity}`, the
identity being the same triple the host's Theory attests), and the Theory by the host's own
`check()`: the guest emits the `Builtin` node on the host's word, the host's `check()` is the
gate, and a host that contradicts itself has its own derivation rejected with `builtin_failed`.
An undeclared predicate never crosses the wire (`NotMine`, unchanged); a host solver may not
call back into the instance (reentrancy is refused, never served). **The declaration's `arity` is
a `u32` field (#3238):** its domain is `0..=2^32 - 1`. Every core that decodes a request refuses
any other value as `decode request.host_builtin.arity: not a canonical int embedding`, and the ts
host refuses to encode one. The reason is the account's own typing: every arity the account
carries is a `u32` (a count premise's predicate arity, a certificate's extension arity, §3.0), so a
host can declare every predicate the account can name, and no other. Before #3238 the field had no
stated domain, and each core's integer width supplied one: rs accepted every arity below `2^64` on a
64-bit build (below `2^32` in the wasm32 guest) and go every arity below `2^63`, so one wire value
had two verdicts. The boundary is pinned tri-core by
[`vectors/integer_domain_refusal.json`](https://github.com/Bitspark/logos/blob/main/vectors/integer_domain_refusal.json). **The host's binding
obligation (#1623):** the goal reaches the solver with its terms *as written* under the request's
substitution — an argument may be a variable, an atom, or a structure whose inner variable is the
one to bind — and the reply substitutions MUST unify the solver's computed values with those
argument terms; a solver that binds only a bare variable and compares only a bare atom fails a
structured argument silently, which produces a complete-looking wrong answer set rather than a
refusal (`kernel/go/wasm` `UnifyHostValues` / `kernel/ts` `unifyHostValues` discharge it). **The negotiation
order (#1621):** a `Certifiable` request that declares host builtins is advertised by the guest under
its base check profile with each declared identity *appended* to the theory list — guest bindings
first, then the declared identities in first-use order, deduplicated — and `CheckProfileSpec`'s theory
list is order-bearing, so the request negotiates only when the host's requested profile is exactly
that fold; the same bindings in another order are refused. Neither the go nor the ts host can compute
the fold from the guest, so each states it (`kernel/go/wasm` `AdvertisedCheckProfileSpecWith` /
`kernel/ts` `advertisedCheckProfileSpecWith`). `Theory::decide` is
untouched — STABLE v1, additive only. Pinned tri-host by
[`vectors/wasm_host_builtins.json`](https://github.com/Bitspark/logos/blob/main/vectors/wasm_host_builtins.json).

> **Realization erratum (STABLE v1; see [ADR 0003](../architecture/decisions/0003-checker-spi-v1-stable.md)
> "seam realization notes").** The `type Config` + `decide(atom, cfg)` pseudocode
> above cannot coexist with §4's mandated `theory: Box<dyn Theory>` — an associated
> type is not object-safe. The canonical, binding-visible shape every `{rs,ts,go}`
> realization pins is therefore **`fn decide(&self, atom: &GroundLiteral) ->
> TheoryOutcome`** with the theory's **config closed over at construction** (e.g.
> `IsRoot::new(pubkey)`), not threaded per call. This *strengthens* purity (the
> live `ctx` cannot reach `decide`, so the leak vector named above is structurally
> impossible) at the cost of per-call config parameterization. A config-fingerprint
> hook, if the byte-identical-derivation vector is ever promoted, is an additive v1
> change.

**The standard `ArithmeticTheory` (normative semantics; ADR [0014](../architecture/decisions/0014-checkable-theories-in-contract.md) · [0022](../architecture/decisions/0022-decimal-arithmetic-semantics.md)).**
The contract tier ships one standard checkable `Theory` whose semantics are normative and
tri-core byte-pinned (the canonical instance of the §5 purity invariant):

- **Owned relations (by name): `is/2` and the six comparisons `=:= =\= < > >= =<`.** The
  expression operators `+ − × / // mod abs min max` are **not** owned predicates — they are
  never goals, only sub-terms a relation evaluates. A non-arithmetic functor in operator
  position is a domain error (the goal fails fail-soft, never panics). **Nesting is not
  bounded by the theory (#3123):** every core evaluates an expression with an iterative walk,
  so a deep operator compound evaluates like a shallow one and never overflows the stack. The
  only depth limit is the caller's `CheckLimits::max_term_depth`, refused as `term_too_deep`
  (a completed policy decision, §4.3); an expression that reaches the theory is decided by its
  value. A depth stop is never a `Fails`: a capacity read as false would be a decided false
  that a negation or a closure consumes as knowledge. (Since `CHECKER_VERSION` 20, a narrowing
  ruled by `seat:caa` on #3144: a negation or a sealed table that rested on the old stop is
  refused.)
- **Two numeric sorts, value-compared (ADR 0022).** `int` and `decimal` are **distinct
  canonical terms** (one spelling per value). `is/2` preserves the **result's sort**, so
  `5 is 2 + 3.0` **fails** (the result is `decimal(5,0)`, not `int(5)`) while `5.0 is 2 + 3.0`
  **holds**; the comparison relations order by **value across sorts**, so `2 =:= 2.0` and
  `2 < 2.5` **hold**. (Term identity `==`/`@<` stays structural; value comparison is
  `=:=`/`<`.) An all-integer expression stays integer and is byte-identical to the
  pre-decimal path; any decimal operand promotes the rest to decimal.
- **Division and mod laws.** `/` succeeds **iff** the quotient is exact — an even integer
  quotient, or a decimal that terminates in base 10 (`1.0/2 = 0.5` holds; `1.0/3` fails:
  no rounding, no float). `//` is truncating-toward-zero with an **integer** result; `mod`
  is ISO-floored (sign of the divisor); both are defined over decimals by lifting the
  integer convention exactly (#416), are always exact (scaled-mantissa integer division),
  and a zero divisor is a domain error (the goal fails, never a panic).
- **Codes are host-extension-band, not FIRM.** The `arith_*` reject codes a binding emits
  (e.g. `arith_does_not_hold`) are **delegated sub-codes** in the open/additive host band
  (the §4 extension band), surfaced under the structural outcome — they are illustrative
  examples here, **not** promoted to the FIRM structural rejection taxonomy.
- **Identity.** `ArithmeticTheory::identity()` is `logos-core/arithmetic-theory@1.0.0` with
  a zero config-digest; the decimal sort was added **additively** (ADR 0003), changing no
  committed integer decision. Source of truth: `contract/rs/src/arithmetic.rs` +
  `contract/rs/src/decval.rs`, replayed byte-for-byte from `vectors/arithmetic.json`.

**The standard gate `Theory` a certifying consumer binds: `standard_theory()` / `NewStandardTheory()` / `newStandardTheory()` (tri-core).**
A consumer that wants to *certify* a search using the wasm guest's builtins (`is`, the
comparisons, the text/term/list relations) must bind a `Theory` into its `CheckProfile`
(§4) that **owns the same predicate set the guest evaluates in search** — otherwise a
perfectly-formed `Builtin` node the guest emits routes to no owner under `check` and
silently fails to certify (issue #574). Rather than hand-assemble a `CompoundTheory`
member-by-member and risk drift, bind the **exported standard helper**: it is a
`CompoundTheory` over the four standard checkable theories **in the same order the guest's
`standard_theory()` binds them** — `[ArithmeticTheory, TextTheory, TermTheory, ListTheory]`
(`app/wasm/rs/src/lib.rs`) — owning exactly `is =:= =\= < > >= =< · contains starts_with
ends_with · atom atomic compound is_list number == \== @< @> @=< @>= =.. = \= true fail false ·
length nth0 last` (the unification relations and control constants since `term-theory@1.1.0`,
#1611: on ground terms `=` is structural equality, `\=` its negation, `true` holds, `fail`/`false`
never hold — the checker's `Builtin` arm needs an OWNER, and the account grammar leaves no
engine-native form). A
tri-core **sync-guard test** pins this helper's owned set EQUAL to the guest's, so the two
cannot silently diverge. Crucially, **the advertised `CheckProfileDigest` must be derived
from the same components** the gate runs — the kernel's `DeriveCheckProfileDigest` over the
live `CheckProfile` (whose `theory` is the standard helper) is the single source of that
digest, so the digest a certificate stamps is, by construction, the digest of the very
verification path that ran. Binding the helper and deriving the digest from the same profile
is the whole gate wiring; doing either by hand is the #574 footgun.

**What a matching `CheckProfileDigest` implies — and what it does not (issue #955).**
The digest folds the theory / leaves / admit component bindings and **two** of the ten
`CheckLimits` fields (`max_nodes`, `max_depth`). #2226's `term_identity` is NOT folded (#3022,
`seat:caa`'s ruling): every certified claim is exact, so the identity cannot change what a check
certifies, and an element that cannot change certification is not in the certification binding.
Since #3022's step 5 the negotiated spec carries no term identity at all (ADR 0036 D2), and
every spec's digest is byte-identical to its digest before, because the wire encoded the default
identity by absence. So:

- **It implies the same PROFILE.** Two hosts at one digest bind the same trusted components
  under the same proof-size caps and accepted-variant set.
- **It does NOT, alone, imply the same ACCEPTANCE SEMANTICS (#2663).** The checker version is
  not folded: a checker-version bump can move `check`'s verdicts, in either direction, under an
  unchanged digest. **The pair `(check_profile_digest, checker_version)` names the verdict
  function.** Two hosts at the same pair **agree on what is true**: no derivation one accepts is
  refuted by the other. Key a stored or reused verdict by the pair, never by the digest alone;
  a plain check returns its checker version with its outcome for exactly this reason.
- **It does NOT imply the same resource ceilings.** The remaining seven fields —
  `max_term_depth` plus the six closed-model certificate budgets (`max_cert_bytes`,
  `max_cert_facts`, `max_domain_values`, `max_support_edges`, `max_rule_groundings`,
  `max_join_steps`) — are **deliberately excluded**, because cert budgets are the
  verifier's **self-protection** and are **host-sovereign**: folding them would let a
  remote artifact dictate the local resource ceilings a host runs under. A host may
  lower its own budgets without becoming un-negotiable with its peers.

The consequence is real and is stated here rather than discovered: **a matching-digest
peer may still refuse a certificate-bearing derivation the first host accepted**, on
affordability. That refusal is never a claim about truth, and it is never
indistinguishable from one — it is reported as the FIRM
[`RejectionCode::CertBudgetExceeded`](https://github.com/Bitspark/logos/blob/main/contract/rs/src/check/mod.rs)
(`cert_budget_exceeded`, the closure budget) or `cert_size_exceeded` (the size budget,
#2335), so a strict host **cannot** masquerade a resource refusal as
a refutation, and a consumer can always tell the two apart. Budget refusals are host
policy; the pair `(check_profile_digest, checker_version)` pins semantics.

> *Errata.* The tri-kernel `CheckProfileSpec::digest` doc previously asserted "same
> digest ⇒ same trusted verification path". That is false for certificate-bearing
> derivations: measured on the `negation.json` budget vectors, **seven** byte-identical
> derivation payloads (`sha256[..16] = 79bfa2f9cf295563` — one accept and six budget
> rejects) sit at a single digest. The sentence was corrected at all three kernel sites
> to the acceptance-semantics form above. This is **errata, not a semantic narrowing**:
> the strong reading was never delivered by any released implementation, so no sound
> consumer reliance is withdrawn (ADR 0003 additive-only protects *delivered* behaviour).
>
> *Errata (#2663, ruled `seat:caa` 2026-09-25, option B).* This section then said a matching
> digest implies the same ACCEPTANCE SEMANTICS. That is false across checker versions, which the
> digest does not fold: one fully identified profile derives the same digest (`3d884aaa…`) at
> `CHECKER_VERSION` 4 (v0.17.0), 8 (v0.18.0) and 14, and one false account is accepted at v0.17.0
> and refused `instantiation_mismatch` at v0.18.0. The digest names the PROFILE, which is what a
> certificate binds (`CertContext`), and the pair names the verdict function; the pair is the rule
> ADR 0028 and every verdict-moving `CheckerVersionV*` constant already state. The version is
> deliberately NOT folded into the digest: that would fail every stored certificate's context
> check at every checker bump, exactly when the newer checker should re-check it.

**The digest folds the checker's accepted-variant surface (#708 leg b).** The profile
record is `[theories, leaves, admit, limits, feature_set]`, where `feature_set` is
`[premise, project_spec, non_member_proof]` — three order-preserving lists of the
`Premise` / `ProjectSpec` / `NonMemberProof` variant names the checker admits. So the same
pair `(check_profile_digest, checker_version)` covers what the checker REFUSES as unknown
evidence, not only what it accepts: an additive checker that admits a new evidence variant derives a
different digest for every profile, and a consumer that froze law against a digest refuses
the wider checker instead of silently inheriting it. A decoded profile carries the surface
it was pinned under; only a freshly derived one carries the current checker's. The three
lists are pinned to `CHECKER_VERSION` (4 since the fold) by a tri-core drift guard, so a
variant cannot be added without both moving. Every profile digest moved once when the fold
landed; a pre-fold pin re-derives once and is otherwise unchanged.

**The determinants, as data (#2727).** The rules above, restated as the one table the tri-core
identity-sensitivity tests read (`kernel/rs/tests/identity_sensitivity_2727.rs`,
`kernel/go/certify/identity_sensitivity_2727_test.go`,
`kernel/ts/test/identity_sensitivity_2727.test.ts`). Each test varies every row ONE AT A TIME
through the production path — `DeriveCheckProfileDigest` over a live `CheckProfile`, and the
`VerdictKey` a plain check returns — and requires a `moves` row to change its identity and a
`holds` row to leave it unchanged. Varying `checker_version` moves the key and, by #2663's ruling
B, never the digest; the tests assert both halves of that row. The table, not the digest's own
field list, is the denominator: a determinant the digest forgot to fold is invisible to a walk
over the digest's fields and visible here. So a row a test cannot vary fails it, and so does a
knob a test can turn that no row classifies. Adding, removing or reclassifying a determinant
changes its row in the same change.

<!-- identity-determinants:begin (#2727: read by the tri-core identity-sensitivity tests) -->
| identity | determinant | varying it alone |
| --- | --- | --- |
| `CheckProfileDigest` | `theory` | moves |
| `CheckProfileDigest` | `leaves` | moves |
| `CheckProfileDigest` | `admit` | moves |
| `CheckProfileDigest` | `max_nodes` | moves |
| `CheckProfileDigest` | `max_depth` | moves |
| `CheckProfileDigest` | `term_identity` | holds |
| `CheckProfileDigest` | `feature_set` | moves |
| `CheckProfileDigest` | `max_term_depth` | holds |
| `CheckProfileDigest` | `max_cert_bytes` | holds |
| `CheckProfileDigest` | `max_cert_facts` | holds |
| `CheckProfileDigest` | `max_domain_values` | holds |
| `CheckProfileDigest` | `max_support_edges` | holds |
| `CheckProfileDigest` | `max_rule_groundings` | holds |
| `CheckProfileDigest` | `max_join_steps` | holds |
| `VerdictKey` | `check_profile_digest` | moves |
| `VerdictKey` | `checker_version` | moves |
<!-- identity-determinants:end -->

#### 5.2 `decide_ground`: a theory that did not decide  [STABLE v1, additive · #3126]

A decider that stops before it establishes a fact (a work cap, a capacity) has **not decided** the
atom, and it MUST NOT report that as `Fails`: under a negation or in a certificate's closure a stop
read as false is a false positive (research 0031). v1's `TheoryOutcome` has no "not decided" arm, so
the channel is the additive method `decide_ground` (ADR 0003, the `identity` precedent), which
returns a `Completion<TheoryDecision, NoCallerLimit>`: `Completed(Holds)`, `Completed(Fails { code })`
with the theory's own code, or `NotCompleted(cause)` with a `NonCompletion` from the completion
algebra (`contract/rs/src/completion.rs`). go carries it as the optional interface `GroundDecider`
read through the one helper `DecideGround(theory, atom)`; ts as the optional member `decideGround`
read through the helper `decideGround(theory, atom)`.

- **The default is derived from `decide`:** `Holds` and `Fails { code }` are the decision, and
  `NotMine` is the named `inconsistent_theory` fault (`ground_from_legacy`). A theory that never
  stops needs no change.
- **A theory that can stop overrides it,** and derives its v1 `decide` from it through the one
  legacy adapter (`legacy_outcome`): a not-completed answer is `NotMine` there, never `Fails`, so a
  legacy reader, which refuses an owned atom's `NotMine` by name, fails CLOSED. The standard
  `ArithmeticTheory` does this: the exact alignment of two in-domain decimals past
  `MAX_DECIMAL_SCALE_SHIFT` is `NotCompleted(work_cap)` (ADR 0022).
- **A wrapper FORWARDS it** to the member that owns the atom (`CompoundTheory`, and every theory
  that wraps another), never takes the default, which would read a member's `NotMine` as a fault
  instead of the member's own non-completion.
- **Every logos reader calls `decide_ground`, never `decide`:** `check`'s `Builtin` nodes, a
  support edge's builtin, the closure's literal truth, and the search registry's ground decision.
  A census per core pins it. A fold over theory answers (the closure's body, `\+`) reaches the
  algebra through the one conversion `decision_of`, which keeps a stop a stop; a reader that
  reports the theory's code (`builtin_failed`'s detail) reads the `TheoryDecision` first.
- **`check` refuses a not-decided literal by name**, `builtin_not_decided` (host-extension band,
  the stop's kind tag as its sub-code), in every position: a positive `Builtin` node, a support
  edge's builtin, and a closure rule instance whose body is not decided and whose head is absent.
  A literal-scoped stop is absorbed by a decided false in the same body (`F ∧ U = F`); a stop no
  false absorbs refuses. It never reads as false. Pinned tri-core by
  [`vectors/theory_not_decided.json`](https://github.com/Bitspark/logos/blob/main/vectors/theory_not_decided.json);
  `CHECKER_VERSION` 22.

ADR 0036 D8's checker SPI v2 makes `decide_ground` REQUIRED (so every theory answers the question)
and deletes `decide` with the legacy adapter. Its v2 method returns `Completion<TheoryDecision, _>`:
typing the theory codes is a separate question, not a reason to widen the language's `FalseCode`.

## 5a. RuleAdmissibility SPI  (validates Rule-node metadata)  [STABLE v1]

The core validates a Rule node's *logical* shape (clause cited, head instantiated,
premises matched). Whether the cited clause is *admissible in this context* — e.g.
a projected rule-fact bound to the right projection and visible from the target —
is a consumer concern, so it is delegated:

```rust
trait RuleAdmissibility<C> {
    fn admissible(&self, clause: &Clause, meta: &NodeMeta, ctx: &C) -> RuleOutcome;
    fn identity(&self) -> ComponentIdentity { ComponentIdentity::unidentified() }  // additive (ADR 0003): attestation triple
}
enum RuleOutcome { Admit, Reject { code: String } }   // e.g. "placement_mismatch", "rule_inadmissible"
```

- `NodeMeta` stays **opaque to core**; only this verifier interprets it. arche
  binds the implementation that performs §3.10a admissibility +
  projection-binding + storage-space visibility against `ctx` (its
  `RuleProvenance` checks). 
- **Most consumers bind the no-op** (`Admit` always): a plain logos engine, or any
  consumer whose clauses are all fixed/bootstrap (non-provenance-bound), needs
  nothing here. So this hook costs non-arche consumers nothing.

**Determinism (G14).** `RuleAdmissibility` (like `LeafVerifier`, §6) MUST be
**total and deterministic** over `(clause, meta, ctx)`. `Context` MUST be an
**immutable verification snapshot**, never a live service handle; the admissibility
check MUST NOT perform I/O, read a clock, depend on mutable state, or do unbounded
search. Any data it needs (a fact-index snapshot, projection target, ledger
snapshot) is built into `ctx` *before* `check` runs. This is what keeps `check`
deterministic over its snapshot — the same property that makes a checked derivation
re-checkable by anyone.

**Clause well-formedness belongs here, not in core (G4).** The *logical-shape*
checks the core performs (clause cited, head instantiated, premises matched, §4
obligation 2) are distinct from *clause hygiene*. Note what hygiene does **not**
forbid: a clause **body may contain builtin/theory and extensional predicates** —
e.g. `adult(X) :- age(X, N), geq(N, 18)`, where `geq` is a theory predicate
discharged by a `Builtin` premise node. The body-literal partition is the ordinary
§4.4 rule: each body literal is intensional, extensional, or builtin, and the
matching premise node kind must agree. The genuine hygiene obligations are on
**heads** (a clause head must be intensional — not builtin- or extensional-owned,
unless the profile explicitly allows) plus Horn-positivity. These are **consumer
obligations** — they belong to `RuleAdmissibility` (or, better, a one-time
program-loading precheck the consumer runs before any derivation is checked),
**not** the per-node core. (This is where arche's `checkRuleAdmissible` /
rule-fact head hygiene relocates.)

<a id="leaf-spi"></a>

## 6. Leaf SPI  (attestation / extensional admission)  [STABLE v1]

```rust
trait LeafVerifier<C> {
    fn extensional(&self) -> &PredicateSet;                       // declares sealed/leaf predicates (§4.2)
    fn verify(&self, atom: &GroundLiteral, evidence: &Evidence, ctx: &C) -> LeafOutcome;
    fn edb_snapshot(&self, pred: &Symbol, ctx: &C) -> Option<Hash> { None }  // additive (ADR 0003): sealed-EDB content pin; gates cert_edb_mismatch
    fn identity(&self) -> ComponentIdentity { ComponentIdentity::unidentified() }  // additive (ADR 0003): attestation triple
}
enum LeafOutcome { Admit, Reject { code: String } }
```

- `Evidence` is opaque to core. arche packs `{ signer, signature, admission, space
  }` here and verifies Ed25519 over the canonical fact bytes + ledger admission +
  space visibility (the leaf-side placement check of §4.1).
- A bare/trusted checker binds a LeafVerifier that admits axioms with no evidence.
- logos-as-engine binds one that admits a leaf iff the atom is an extensional fact
  present in its store.

**Determinism (G14), same as §5a.** `verify` MUST be total and deterministic over
`(atom, evidence, ctx)`; `ctx` is an immutable snapshot; no I/O, clock, mutable
state, or unbounded search.

**Every member `check` consults, not only `verify` (#2565).** A leaf verifier, like a
theory's `decide` (§5), MUST be a pure function of its inputs: deterministic, with no side
effect visible to `check`. That holds for `extensional()` and `edb_snapshot(pred, ctx)` as
much as for `verify`. `check`'s verdict, and any memo of it, assumes so.
`check_with_cert_memo` (additive, contract v1) verifies a closed world once per run and
serves the same verdict to every later derivation citing an equal world under the same
program, profile and `ctx` objects, the same `CertContext` and the same `CheckLimits`. It is
exact only because every component it consulted answers the same question the same way.

**The inputs a memo is bound to MUST NOT change while it is in use (#2569).** Go and TS have no
borrow checker, so their `WorldMemo` (`NewWorldMemo` / `new WorldMemo`, used through
`CheckWithWorldMemo` / `checkWithWorldMemo`) binds the program, profile, `ctx` and `CertContext`
at construction and runs every check under them. The caller MUST NOT mutate the program, the
profile's components or `ctx` while the memo is in use: a mutated program leaves the bound
`CertContext` stale, and the memo would then serve a **wrong verdict, not a slow one**. The kernel
gate meets this by construction, because its drive loop holds all three fixed for the run.
`CheckLimits` are the one input checked rather than assumed: they are snapshotted when a world is
verified and compared on every call. In Rust the same holds by construction, because the memo
borrows all three immutably for its lifetime.

**The additive `identity()` / `edb_snapshot` seams (STABLE v1, additive per ADR 0003).**
Three checker components — `Theory` (§5), `RuleAdmissibility` (§5a), and `LeafVerifier`
(§6) — each expose two **additive, defaulted** members a v1 consumer compiles against:

- **`identity() -> ComponentIdentity`** returns the `(id, version, config_digest)` triple
  the certifying kernel folds into the **cert-profile digest**, so the configuration a
  derivation was checked under is itself an attestable, checkable fact (not an honor-system
  claim). The default is `ComponentIdentity::unidentified()` (all-zero `config_digest`), so
  existing impls stay source-compatible.
- **`LeafVerifier::edb_snapshot(pred, ctx) -> Option<Hash>`** returns a content pin for a
  sealed extensional relation; a closed-model certificate's `edb_snapshot_hashes` (§"What
  the checker verifies", ADR 0007) MUST equal it, and a mismatch is rejected with
  **`cert_edb_mismatch`** — the binding that makes a negative premise's "complete EDB
  snapshot" obligation checkable rather than trusted. The default is `None` (not
  EDB-snapshot-bearing). The pin is `edb_table_hash(pred, rows)` over the relation's rows,
  and **the rows are a SET** (#2279): they are sorted by the ground key and a repeated row is
  ignored, by the same key the sealed `RelationTable` dedups by, so order and multiplicity
  never change the pin. A snapshot provider need not deduplicate its rows first.

These are **interface-parity** seams (one tri-core interface, ADR 0012), realized with the
idiomatic per-core shape each language affords — Rust defaulted trait methods, Go split
interfaces (`Identified` / `EdbSnapshotProvider`), TS optional members — a divergence
**blessed** by the parity discipline in
[validation/0001 §rs/ts/go parity discipline](../architecture/validation/0001-consumer-fit-and-parity.md#rstsgo-parity-discipline-adopted-grounded-in-ontos):
the *interface* is the same tri-core, only its host-idiomatic spelling differs.

**Decision — leaf verification is fully delegated to the `LeafVerifier` (v1).** The
kernel `check` verifies **no** signatures itself: a signature is an *arche-style
evidence mechanism*, not a universal property of an extensional leaf (a non-arche
consumer may have trusted local facts, Merkle-included facts, DB-snapshot facts, or
simulation outputs — no signature anywhere). Forcing generic signature machinery
into the kernel would violate the "no consumer-specific concepts in the core" rule.
So the **trusted checker profile = the structural checker + its bound
`LeafVerifier`/`RuleAdmissibility`/`Theory`**: for arche, the `LeafVerifier` is part
of the trusted verification path and is where signature + admission + placement are
checked. (A reusable `logos-leaf-signature` helper package MAY be offered, but it is
*not* part of the FIRM/STABLE kernel.) This resolves the first draft's silent (b)
into an explicit, reasoned (b) — closing logos#6 for v1.

**Naming: no arche domain prefix in the frozen kernel (logos#3).** Any
domain-separation prefix the kernel itself uses for leaf-signing bytes MUST be
neutral (e.g. `logos/v1/leaf`) or host-supplied — never a literal `Arche/…`
string. Cheap to fix now, expensive after a freeze.

## 7. Search side (just enough to pin the DTO)  [PROPOSED — engine-facing, ADR 0002]

```rust
trait Evaluator<C> {
    fn solve(&self, program: &dyn Program, goal: &Goal, ctx: &C,
             profile: &CheckProfile<C>, limits: Limits)
        -> SearchResult;
}
struct SearchResult { solutions: Vec<Solution>, refused: bool }  // refused = budget hit, not failure
struct Solution { answer: Subst, derivation: Derivation }        // derivation MUST pass check(...)
```

When a `Solution.derivation` crosses a process, repository, or language boundary as
a proof artifact, its durable public serialization is `DerivationWireV1` (§3.0).

**The dual-conformance law (normative):** for every `Solution` an `Evaluator`
emits, `check(program, apply(goal, answer) as GroundLiteral, derivation, ctx,
profile)` MUST return `Accept` — where `apply(goal, answer)` grounds the goal (a
solution's answer covers the goal's vars). This single law guarantees the engine is
swap-safe: whatever produces the derivation, the checker re-validates it from
nothing. (Reification of terms/clauses for storage is §2a, not here.)

**The law covers `Count` premises (ADR 0023):** a `Premise::Count { pred, filter,
project, k, cert }` is held to the *same* law — the engine *proposes* the cardinality
`k` (it knows the answer set it enumerated), but the checker **re-derives `k`
independently** by re-counting the proven-exact sealed relation `cert.table(pred)`
under `filter`/`project`, and `check` returns `Accept` only if the recomputed `n`
equals the proposed `k` (else `count_mismatch`). So a count is dual-conformant by the
same mechanism as any other premise: the proposed value never overrides the gate's own
recomputation, and a wrong `k` over an otherwise-valid certificate is rejected
regardless of which engine produced it (the adversarial-tamper conformance vector,
`vectors/aggregation.json`, pins this tri-core).

**What the `solutions` multiset means (normative):** `SearchResult.solutions` is a
**multiset** — one entry per check-accepted derivation, so two distinct proofs of the
same answer (a reconvergent DAG) are two correct, dual-conformant solutions, not a bug;
de-duplication to a set of answers is an opt-in post-pass, never the default. This is
the decision of [ADR 0020](../architecture/decisions/0020-multiset-vs-set-answer-semantics.md).

## 8. What this buys arche (the unblocking)

After this contract is frozen, arche depends only on **ontos** (ready) + **this
surface** (small, engine-free). Concretely:

```text
arche Term   →  Term (ontos value with holes: Atom|Tuple|Var)  [mechanical refactor, parallel, no logos]
arche check  →  Checker SPI, backed FIRST by arche-core via an adapter
arche authz  →  a Program (data)
arche crypto/ledger/space  →  its Theory + LeafVerifier + RuleAdmissibility + Context impls
```

P2 swap is then: replace the Evaluator/Checker implementation behind the SPI with
logos. arche source unchanged. The dual-conformance law (§7) + shared derivation
vectors make the swap verifiable, not hopeful.

## 9. Open questions (flagged, not yet decided)

- **`Subst` representation** on a `Rule` node: explicit map (arche-core style) vs.
  reconstructed by the checker from premises. Explicit is simpler to verify and
  matches the incumbent; keep unless vectors show bloat.
- **`ClauseId`** *(RESOLVED 2026-06-01 — now a canonical hash; the §2 opaque
  contract still holds as a generalization)*: the v1 contract requires only "stable +
  lookup-able" (§2), and that stays true — but the deferred canonical-**hash** form
  is now **defined and frozen** (the account codec, `account.rs`). A clause is not
  an ontos value (it contains variables), so it is canonicalized via (1) the now-
  **frozen** `quote` byte form (§2a) and (2) the settled **`VarId` alpha-normalization
  decision: SYNTACTIC** — `p(X):-q(X)` and `p(Y):-q(Y)` do **not** hash equal
  (variable names are encoded; chosen to match the incumbent and avoid a
  canonical-renaming pass; a future alpha-normalizing id would be a new versioned
  binding). `ClauseId::canonical(clause) = SHA-256(CLAUSE_PREFIX ‖
  ontos-codec(quote(clause)))`, lowercase hex. A consumer may still use any opaque
  stable id; the canonical hash is the additive binding §9 anticipated, and it is
  what arche adopts.
- **Numbers in atoms** *(resolved at the framework level)*: numbers are
  **`ontos/data` embeddings** inside `Term::Value` (now specified —
  [ontos-data.md](https://github.com/Bitspark/ontos/blob/main/docs/spec/ontos-data.md));
  there is **no native float/int term sort**. Exact-number *byte form* is
  codec-gated (ontos-data §6). Not on arche's P0 path (arche's `is_root`/grant use
  byte pubkeys, not ints — confirmed by the call-site inventory). The standard
  `ArithmeticTheory` evaluates **two exact numeric sorts** over these embeddings — the
  `int` embedding (§5.1) and the `decimal` embedding (§5.9, `mantissa × 10^exponent`) —
  with **no float**; `int(n)` and `decimal(n,0)` are distinct terms compared by value, and
  `/` is exact (terminating-in-base-10 for decimals). See
  [ADR 0022](../architecture/decisions/0022-decimal-arithmetic-semantics.md).
- **Leaf-signature location** (logos#6): **RESOLVED for v1 — option (b)**, all leaf
  verification (incl. signatures) is delegated to the `LeafVerifier`; the kernel
  verifies no signatures (§6). The trusted checker profile includes the bound
  `LeafVerifier`. No longer open.
- **List reification (cons ↔ `list`)** *(logos#159 — single emit seam DONE; logos#277
  — reify-aware account-v2 check DONE, tri-core; **superseded for `check` by
  [#3022](https://github.com/Bitspark/logos/issues/3022)**: every certified literal claim is
  exact, `check` compares every site structurally, and the reified spelling is presentation, a
  `PresentedFact` beside the exact fact. What follows is the #277 record)*: the logos surface lowers list syntax
  to Prolog-style **cons cells** (`[H|T]` = `Tuple[Atom("."), H, T]`, `[]` =
  `Atom("[]")`), and that cons byte form is the **FROZEN default identity** every
  derivation conclusion emits (pinned by `vectors/search.json`). The ontos/data L2
  profile instead carries a sequence as the flat `list` embedding
  `Tuple[Atom("list"), e₀, …]`
  ([ontos-data §5.5](https://github.com/Bitspark/ontos/blob/main/docs/spec/ontos-data.md)).
  #159 consolidated the **single account-emit seam** (`DerivationBuilder`, the one
  place both engines funnel conclusions through) and added an **opt-in, additive**
  cons→`list` normalization there (`reify_lists` /
  `DerivationBuilder::with_list_reification`), with its own non-default vector
  `vectors/account-v2-list.json`. It is **off by default — no existing identity byte
  changes.** #277 then closed the previously-deferred half: the reified emission is
  now **dual-conformant** against the trusted `check`. The checker's account-equality —
  the Rule "instantiated head == conclusion" obligation (§3), the premise/body-literal
  match at a premise citing a `Rule` or `Leaf` node, and the root/claim equality — is now a
  **reify-aware account equality** (a premise citing a `Builtin` node, and a `Neg` premise's
  atom, match EXACTLY: §4 obligation 2, #2232 / #2227; and a spelling-sensitive rule instance
  must be exact-grounded: §4 obligation 2, #2256):
  before comparing two ground terms, `check` canonicalizes them through
  `canonicalize_lists` (a thin re-export of which is the producer's `reify_lists`), a
  **total, deterministic BIJECTION on ground proper lists** (cons ↔ `list`) and the
  **identity on every other term**, applied to **both** sides. So a cons-form clause
  head `p([a,b])` matches a reified `p(list(a,b))` conclusion, and a reified leaf
  matches the cons-form EDB (a `LeafVerifier` reuses the public `canonicalize_lists`).
  This is **strictly additive and verdict-preserving**: the default account emission +
  its bytes are unchanged (the canonicalization collapses nothing on a cons / non-list
  term, so every frozen vector replays byte-identically with its original verdict), and
  the bijection **never conflates two distinct terms** (a wrong sequence, the bare `[]`
  atom vs the empty `list()` embedding, and a proper list vs an improper `[a|b]` all
  stay distinct). Realized **tri-core `{rs,go,ts}`** in `check.{rs,go,ts}` over the
  shared `term::canonicalize_lists` primitive; pinned by `vectors/account-v2-list.json`
  (the `check_correspondence` block) and exercised by
  `contract/{rs,go,ts}`'s `account_v2_reify` adversarial suites. This is the
  **account v2** reify-aware checker the rule anticipated — additive within the FIRM
  account, not an edit to the frozen cons identity (§2a). It unblocks a reified Shelf-A
  `ListTheory` (logos#242).
- **Where the contract lives as code** *(RESOLVED — [ADR 0004](../architecture/decisions/0004-repo-layout.md)
  D2/D4)*: a single **`logos-contract`** crate (the FIRM account *and* the checker
  SPI together; it adds `Var` + Derivation + SPIs to ontos, which it depends on),
  realized in full tri-core **`{rs,ts,go}`** (Rust now; TS + Go for arche's
  tri-language checker — arche-core is `core/{go,rs,ts}` and its browser checker is
  `proof.ts`). Not part of `ontos` — ontos stays logic-agnostic. No longer open.

## 10. Out of scope: fact discovery / query (G1)

Fact **discovery / query** (selecting which stored facts feed a search — arche's
`query.Spec` / `FactsSelect` / scope-subtree) is **not** part of this contract. It
is a **separate, parallel transport/discovery SPI**, orthogonal to the checker
surface. It is named here only so it is not a silent gap: a consumer needs it
(arche's CAS/credential paths do), but the logos *checker/account* contract neither
provides nor requires it. Do not pull query into this surface.

## 11. Engine profiling vocabulary  [PROPOSED — engine-facing, ADR 0024]

The kernel MAY emit engine-internal counters/timers behind an **opt-in, default-OFF**
`profiling` cargo feature and an opt-in `--stats` structured field — so the **default
build emits nothing** and its ABI bytes are byte-identical to the pre-feature kernel
([ADR 0024](../architecture/decisions/0024-opt-in-default-off-profiling-channel.md),
honoring [ADR 0003](../architecture/decisions/0003-checker-spi-v1-stable.md) and the
§7 dual-conformance law). This section is the **single source of truth** for the field
names, units, and determinism classes; rs realizes them first, go/ts follow at
**interface parity** ([ADR 0012](../architecture/decisions/0012-interface-parity-not-capability-parity.md)),
and a core **OMITs (never fakes)** a counter it does not compute (an absent field means
*unknown*, never measured `0`). Every field here is firmness-class **PROPOSED** and is a
**diagnostic side-channel** — a profiling counter is never a `Derivation` node, never an
input to `check`, and never part of any trust artifact.

**Determinism classes (normative).** Each field carries exactly one class:

- **`work-count`** — an integer that is a deterministic function of the program + EDB
  under the fixed clause/EDB order; byte-stable run-to-run, independent of wall-clock
  and host, and therefore **cross-core byte-pinnable** (rs ≡ go ≡ ts where computed).
- **`analysis`** — an integer that is a deterministic property of the program's ANALYSIS (a
  partition size, a count of clauses by shape), not a measure of any run: byte-stable,
  host-independent and cross-core byte-pinnable exactly as `work-count`, and never a
  statement about how much work an engine did (#1671).
- **`timer`** — a wall-clock duration; perturbing, host- and load-dependent; **never
  certified**, never cross-core-pinned, diagnostic only.
- **`engine-local`** — an engine-internal quantity (interner size, index byte
  footprint, strategy-specific count) well-defined for the engine that computes it but
  which may legitimately **differ across cores/engines** computing the same least model;
  diagnostic, not cross-core-pinned.

Only **`work-count`** and **`analysis`** fields may feed a cross-core parity vector; `timer` and
`engine-local` fields MUST NOT feed any certified or cross-core-pinned measurement.

### 11.1 D1 — counters

| field | unit | class | meaning |
|---|---|---|---|
| `rounds` | rounds | `work-count` | total seminaive-fixpoint scheduler rounds across every stratum (Σ `StratumSummary::rounds`; `core/rs/src/drive.rs` `WorkCount.rounds`). |
| `tuples_derived` | tuples | `work-count` | total newly-derived tuples across every round (Σ each round's `new_delta_size`; the natural cross-engine comparison unit). |
| `strata` | strata | `analysis` | the stratification's PARTITION size (`SchedulerOutcome.strata` = `engine.stratum_count()`; go/ts: the analyzer's stratum count) — a program property, the one strata number every core computes and the cross-core vector pins unconditionally (#1671). |
| `strata_sealed` | strata | `work-count` | strata the scheduler SEALED — `end_stratum` ran: a stratum truncated mid-round is included, a pre-stratum limit trip is not (`SchedulerOutcome.strata_sealed`; named `strata_completed` until #1671 — NOT "strata that reached a fixpoint"). |
| `strata_at_fixpoint` | strata | `work-count` | strata that reached their fixpoint: `strata_sealed` minus the mid-round-truncated stratum (`SchedulerOutcome::strata_at_fixpoint()`, discriminated by `truncating_stratum_sealed`, #1671). |
| `truncation` | enum/flag | `work-count` | whether the drive truncated and why (`SchedulerOutcome.truncated` reason), vs a clean least fixpoint. |
| `edb_clauses` | clauses | `analysis` | #900's EDB count: extensional empty-body GROUND clauses, each duplicate counted — a program property, emitted by every core (go/ts read it off `ProgramAnalysis.edb_facts`; the rs CLI counts it at load over the source clauses, because it hands the kernel a deduplicated store). Named `edb_facts` until #2219, which split that name: a clause count is not a fact population. NOT comparable to §11.6's `sizes.edb_facts` (the DISTINCT facts in the sealed store); they differ whenever a program repeats a fact. |
| `idb_facts` | facts | `work-count` | intensional (derived) fact population. |
| `total_facts` | facts | `work-count` | total fact population (for bottom-up = `tuples_derived` over the sealed model). |
| `emitted_head_tuples` | tuples | `work-count` | head tuples emitted by rule application (= `tuples_derived` for bottom-up; refined per engine). |
| `variants_scheduled` | variants | `work-count` | rule/clause variants scheduled for evaluation. |
| `operators` | firings (per operator) | `work-count` | firings served per physical operator — a nested map keyed by the operator's stable id (`engine-local` keys, e.g. `cpu-left-deep`, `rel-cpu-join`); answers whether an accelerated operator actually served work rather than the hybrid silently falling back (#1465). Present when the seminaive or relational group is (from the answering run or the `bottom_up_profile` replay); `{}` when a present group dispatched nothing; absent otherwise, never zero-filled (#2216). |
| `skipped_firings` | firings | `work-count` | firings NO operator accepted — skipped, not served — summed across the profiled drives (#1466). `operators` alone cannot express this (a skipped firing has no winner to key on), so a `--operator-policy force:<id>` whose target declined everything is distinguishable from a drive that never ran. Present with `operators`, `0` when a present group skipped nothing; absent otherwise, never zero-filled (#2216). |
| `index_count` | indexes | `engine-local` | number of indexes the relational engine built. |
| `index_rows` | rows | `engine-local` | total rows held across all built indexes. |
| `index_bytes` | bytes | `engine-local` | byte footprint of the built indexes. |
| `indexes_planned` | indexes | `engine-local` | indexes the planner decided to build. |
| `indexes_built` | indexes | `engine-local` | indexes actually materialized. |
| `indexes_used_by_shape` | indexes | `engine-local` | indexes consulted, attributed by access shape. |
| `indexed_lookups` | lookups | `work-count` | lookups served by an index. |
| `full_scan_lookups` | lookups | `work-count` | lookups that fell back to a full scan. |
| `fallback_by_reason` | lookups (per reason) | `work-count` | full-scan fallbacks attributed by reason — a nested map keyed by a stable reason token (`delta_read` = the semi-naive delta read, `no_index` = no `HashExact` index for the access, `non_const_key` = the key is not all-constant). Σ values == `full_scan_lookups`. |
| `candidate_rows_examined` | rows | `work-count` | candidate rows examined during join/match. |
| `match_attempts` | attempts | `work-count` | unification/match attempts. |
| `match_successes` | successes | `work-count` | match attempts that succeeded. |
| `dispatch_firings` | firings | `engine-local` | firings that reached the operator dispatch (design 0006 P13, #1963). The **presence predicate** for the rest of this family: none of them can tell their own absence from a legitimate `0` — `dispatch_rows_in == 0` is a real measurement of a firing that offered no rows — and it is the denominator any per-dispatch average needs. Absent when no firing reached the dispatch this run, and **never `0`**: a run that dispatched anything emits at least 1. |
| `dispatch_rows_in` | rows | `engine-local` | candidate rows the operator dispatch offered the join, summed over the firing's positive sources. A RUN TOTAL; the same id is also stated per firing on that dispatch's `Operator` span (design 0006 P13, #1963). Read by the dispatch before the unit is moved, so it counts every row offered — a backend's own post-filtering count is a different quantity and would need a different name. Absent when no dispatch ran this run, never `0`. |
| `dispatch_rows_out` | rows | `engine-local` | rows the operator dispatch emitted. A RUN TOTAL, and per firing on the `Operator` span. Absent when no dispatch ran this run, never `0`. |
| `dispatch_bytes_uploaded` | bytes | `engine-local` | bytes uploaded to a device for the firings an accelerating operator served. A RUN TOTAL, and per firing on the `Operator` span. **Absent when no device-boundary operator served a dispatch this run** — the honest state of a build without the accelerator — and never `0`: a present `0` means such an operator ran and moved nothing, which is a different fact. |
| `dispatch_bytes_downloaded` | bytes | `engine-local` | bytes copied back from a device for those firings. Bytes MOVED, not bytes of useful result: the readback buffer is sized to every candidate pair, which is the honest transfer cost to set beside the compute. Same run-total/per-span pairing and the same absence as `dispatch_bytes_uploaded`. |
| `dispatch_served_by` | firings (per backend) | `engine-local` | which path actually served each firing — a nested map keyed by a stable backend token (`gpu` = the device path, `cpu-fallback` = the CPU-shaped reference inside an accelerating operator's own `run`). Σ values == the firings an accelerating operator served. The value is the branch that RAN, never inferred from the absence of an error, which is what makes "the accelerator served this" falsifiable (#1466). A RUN TOTAL, and per firing on the `Operator` span. Absent when no dispatch ran this run, never an empty map. |
| `dispatch_timed_firings` | firings | `engine-local` | device-served firings whose adapter reported `TIMESTAMP_QUERY`, so a device clock actually ran (design 0006 P13 (b2), #1963). The **presence predicate** for `dispatch_ns`, in the `dispatch_firings` shape and for the same reason: a summed duration cannot tell its own absence from a real `0`. **STRICTER than the transfer pair's absence** — a device can serve a firing, move bytes, and report no clock, which is the middle of three states this row exists to name (no device-boundary operator · one without the feature · one with it). Absent when nothing was timed, and **never `0`**. |
| `dispatch_ns` | ns | `timer` | device-measured nanoseconds for the **compute pass**, summed over the timed firings (design 0006 P13 (b2), #1963). A RUN TOTAL; the same id is stated per firing on that dispatch's `Operator` span. An **elapsed difference, never an absolute timestamp** — wgpu documents absolute timestamp values as meaningless and only their difference as carrying meaning, so the backend differences the two queries and only the difference is published. Class `timer`, so like every timer it is **never certified and never feeds a cross-core parity vector**. Absent when `dispatch_timed_firings` is absent; a present `0` would be the different fact that a device clock ran and measured a zero-length pass. |

> **Erratum (2026-09-24, #2249; ruled by `seat:caa`):** "extensional" in the `edb_clauses` row means the DATALOG-SENSE EDB: the ground body-less clauses the analysis loads. It is not §4.4's extensional. On a host that lifts every fact into its leaf store (the rs CLI) those clauses are also §4.4-extensional. Where facts stay Program clauses they are §4.4-intensional rule-facts: certification classifies them as intensional (§4 obligation 2's leaf declaration, `ExecutionEnvironment::extensional`), and this counter still counts them. The counter's value is unchanged on every core.

> ⛔ **DECLARED ABSENCE (design/0004 §7) — the `dispatch_*` RUN TOTALS cannot report a device under
> `profiling`, and it is INHERITED from #1521's counting dispatch, not introduced by P13.**
>
> The relational engine has two dispatch paths chosen by `cfg`, and only one of them collects run
> totals:
>
> ```
> cfg(any(test, profiling))       the COUNTED path — can only pick an operator that implements
>                                 counting. The GPU operator does not, so the winner is the CPU
>                                 baseline BY CONSTRUCTION.
> cfg(not(any(test, profiling)))  the REPORTING path — sees the accelerator and states its cost
>                                 on the `Operator` span, but `ProfilingCounters` does not exist
>                                 in this build, so nothing accumulates a run total.
> ```
>
> ⇒ **Under `profiling`/`test`: `dispatch_bytes_uploaded` and `dispatch_bytes_downloaded` are ABSENT,
> and `dispatch_served_by` carries only the `cpu-fallback` key — never `gpu`.** This is the honest
> state, not a defect in the emitter, and it is why the rows above say *absent*, never `0`.
>
> ⭐ **WHAT IS NOT VACUOUS, because one word must not span two carriers:** the **per-dispatch** values
> on the `Operator` span are REAL in the default build — the seam observer is passed on the reporting
> path too, so a traced default-build run does see a device's own numbers. The span and the run total
> are different observables; only the second is limited here.
>
> ✅ **BOTH HALVES OF THE UN-SATISFIER ARE NOW MET (#1963 P13 (b1), 2026-09-13) — this absence is
> DISCHARGED, and the record of it is kept rather than deleted.** It was declared with a two-part
> un-satisfier precisely so it could not silently outlive itself, and both parts landed together, in
> the ruled order:
>
> 1. *the accelerator is reachable from the counted dispatch* — the counted candidate set is now
>    ALIGNED with the reporting one, so an accelerating operator can win a counted firing and hand up
>    a real cost. It reports **no match accounting** (see the `match_*` note below), which is the
>    complement of what the CPU baseline reports, not a gap; **and**
> 2. *a `features` pair building `logos-engine-relational` with `gpu,profiling` together* — a step in
>    the required `gpu` job, mirrored under `scripts/check.sh --gpu`, which is what lets an assertion
>    about these three actually execute.
>
> ⇒ **Under `gpu,profiling` the three are MEASURED.** Under `profiling` WITHOUT `gpu` they remain
> ABSENT — never `0` — because no device-boundary operator is in the catalog at all, which is the
> honest state and is why the rows above say *absent*.
>
> ⚠ **The ORDER was load-bearing and is recorded for the next rung that needs it:** the CI leg lands
> WITH the counting that gives it something to measure, never before, or it spends a gate leg
> asserting an absence — a guard whose pass is compatible with its subject not existing (form 33).
>
> ⭐ **What is pinned, and why it cannot pass vacuously.** Two sibling tests over the **same fixture**,
> differing only in the POLICY, so a divergence cannot be blamed on the programs disagreeing:
> `ForceOperator(rel-cpu-join)` pins the CPU arm's match accounting, and the default `LowestCost`
> policy pins the accelerated arm — backend named for every firing, `match_*` absent, rows still
> emitted. The accelerated one **branches on adapter presence** via `gpu-device` rather than assuming
> a device: the no-adapter arm — the one CI actually builds — asserts a `cpu-fallback` token with a
> MEASURED zero transfer, a determinate claim rather than a disjunction that holds whatever happens.
> *(Declared by `seat:cca` 2026-09-13 with increment (a); discharged by (b1) the same day.)*

> ⛔ **DECLARED ABSENCE (design/0004 §7) — `dispatch_ns` and `dispatch_timed_firings` are ABSENT on
> every host this fleet and its CI have today, and that is a CAPABILITY fact, not a build-mode one.**
>
> ⚠ **A SEPARATE absence from the one above, deliberately not folded into it.** That one was about
> which dispatch path collects run totals and is now DISCHARGED; this one is about what an adapter
> reports, has a different un-satisfier, and is still live. Merging them would make the discharge
> ambiguous — a reader could not tell which half had been met.
>
> Device timing needs `wgpu::Features::TIMESTAMP_QUERY`, negotiated against `adapter.features()` at
> `request_device` and **never requested unconditionally**: an unsupported `required_features` makes
> `request_device` fail outright, which would trade the GPU path itself for an observability field.
>
> ```
> no adapter                        no device dispatch at all   -> transfer rows ABSENT, timer rows ABSENT
> adapter WITHOUT TIMESTAMP_QUERY   bytes move, no clock        -> transfer rows PRESENT, timer rows ABSENT
> adapter WITH TIMESTAMP_QUERY      bytes move and are timed    -> both PRESENT
> ```
>
> ⇒ **The middle row is the whole reason `dispatch_timed_firings` exists as its own predicate.** The
> (a) device predicate — `dispatch_served_by` non-empty — is TRUE there and would publish
> `dispatch_ns: 0`, asserting a measurement nobody took. A `0` here must always mean *the clock ran
> and the interval was zero*.
>
> ⭐ **UN-SATISFIER, phrased as a state HERE rather than an event elsewhere:** a host running this
> suite whose adapter reports `TIMESTAMP_QUERY` — ask `logos_op_gpu::timestamps_supported()`, which
> reads the negotiated capability without running a join. The pin test branches on exactly that, so
> the presence arm executes the moment such a host exists instead of waiting for anyone to notice.
>
> ⛔ **`transfer_ns` IS NOT MINTED, and its absence is a RULING rather than an oversight**
> (`seat:cca`, 2026-09-13). Timing the host↔device copies needs a timestamp between encoder commands
> (`CommandEncoder::write_timestamp`) and therefore `TIMESTAMP_QUERY_INSIDE_ENCODERS` — a *second*,
> native-only feature wgpu documents as "generally not available on tile-based rasterization GPUs".
> `dispatch_ns` needs only `TIMESTAMP_QUERY`, consumed at the pass boundary. **They are two
> capabilities, not one**, so a `transfer_ns` row would have no producer and no predicate: the
> phantom shape this rung has refused throughout — *a row is minted only WITH its producer in the
> tree AND its emitted presence predicate.* Filed as a deferred residue with a state-here trigger.
> *(Declared by `seat:cca` 2026-09-13 with increment (b2).)*
| `duplicate_rejects` | tuples | `work-count` | derived tuples rejected as already-present duplicates. |
| `candidate_clone_bytes` | bytes | `engine-local` | bytes cloned building candidates (the join key for alloc-correlation). |
| `interned_symbols` | symbols | `engine-local` | interner population — symbols (`core/rs/src/symbol.rs`). |
| `interned_relations` | relations | `engine-local` | interner population — relations. |
| `interned_functors` | functors | `engine-local` | interner population — functors. |
| `interned_values` | values | `engine-local` | interner population — values. |
| `sld_goal_resolutions` | resolutions | `work-count` | SLD resolution steps (one per `resolve_goal` entry; `engines/wam/rs/src/machine.rs` `EnumStats.steps`). |
| `sld_unifications_ok` | unifications | `work-count` | SLD unification attempts that **succeeded** (the `+` half of "± successes"; rs splits the success/fail tally into two fields). |
| `sld_unifications_fail` | unifications | `work-count` | SLD unification attempts that **failed** (the `−` half). |
| `sld_clause_lookups` | lookups | `work-count` | SLD clause lookups. |
| `sld_suspensions` | suspensions | `work-count` | SLD goal suspensions. |
| `sld_backtracks` | backtracks | `work-count` | SLD backtracks. |
| `sld_cut_prunes` | prunes | `work-count` | branches pruned by cut. |
| `sld_bindings_made` | bindings | `work-count` | variable bindings made. |
| `sld_trail_rollbacks` | rollbacks | `work-count` | trail entries undone on backtrack. |
| `sld_refused` | flag | `work-count` | whether any branch was pruned by the depth/step budget (`EnumStats.refused`). |
| `sld_normalized_clauses` | clauses | `work-count` | how many clauses the body-literal normalization pass reordered for this query before the top-down search ran (draft 0006, #1435 — `0` when nothing moved; the run report names the clauses). |
| `sld_answers_yielded` | answers | `work-count` | answers yielded by the searcher (distinct from the consumer-collected count). |
| `sld_proof_nodes_cloned` | nodes | `work-count` | `Proof` node handles copied carrying a completed proof up the search: the derivation-building cost of top-down search, linear in derivation depth since #1531 (#2164). |
| `sld_walk_hops` | hops | `work-count` | variable-chain hops the trail's walk followed: the substitution-chain walking cost, constant per yielded answer since #1531 (#2164). |
| `tabled_declared` | tables | `work-count` | tabled subgoals declared ([ADR 0021](../architecture/decisions/0021-tabling-memoization-performance-tier.md)). |
| `tabled_active` | tables | `work-count` | tables active during evaluation. |
| `tabled_pruned` | tables | `work-count` | tabled-coverage prunes. |
| `magic_transformed` | rules | `work-count` | rules rewritten by the magic-set transform. |
| `magic_synthetic` | rules | `work-count` | synthetic magic rules introduced. |
| `magic_facts` | facts | `work-count` | magic (seed) facts produced. |

A core that does not compute a row above **omits** that field (ADR 0012,
omit-not-fake); the field name/unit/class are nonetheless fixed here so a later core or
the bench schema mirror binds the same surface. **rs Tier-2 coverage (#633):** the
seminaive (candidate/dup/clone/`variants_scheduled`/`emitted_head_tuples`), relational
(index footprint/lookups + `fallback_by_reason` + candidate/match work), interner, and the
full SLD counter set are computed and surfaced through the CLI `--stats` channel; the
tabled-coverage counters (`tabled_declared`/`tabled_active`/`tabled_pruned`) and the
`magic_*` counters are computed at the engine seam (the sldnf tabling tier and the
`compile_with_query` demand transform respectively, each with its own counter-pinning test)
but, because the CLI's stats drive uses the full-model `compile` path with no tabling, they
are **omitted** from the CLI emission rather than faked to `0` (omit-not-fake) until a
consumer drives those paths. `sld_suspensions` is emitted as a **structural `0`** — a named
zero-count *theorem* of the current fragment, not a faked measurement (so it is **not** an
omit-not-fake violation): the closed-positive top-down engines (rs `sldnf`/`wam`) have no
SLG/coroutining/cut/`findall` suspension state (#144), so the count is *provably* `0`, and
the counter carries a forward bump site (`SldCounters::bump_suspension`) that becomes a live
work-count the moment a suspension-bearing feature lands. A core that does **not** own this
closed-positive invariant (go/ts, or any future core) keeps omit-not-fake and **omits** the
field rather than emitting a `0` it cannot prove.

**The capture account, and the four `source` tokens (#1935, P6).** A `stats_v2` record carries a
`collectors` group describing the ANSWERING run: `complete`, `dropped`, and `groups`, keyed by
engine group (`seminaive` · `sldnf` · `relational` · `wam`). Each group carries two independent
labels, and the pair is the point: `state` says whether the group's PRODUCER spoke on the
answering run, `source` says which execution the numbers **on this record** were measured on. A
group can be `measured` and still carry replay values — that is exactly the state of a group
whose reader has not been migrated.

- **`selected`** — measured on the execution that produced the caller's answers, read from its sink.
- **`replay`** — measured on a diagnostic replay, which is named beside it as `pass`.
- **`absent`** — the group has registered fields and **neither** source supplied them: a refused read, or a pass that did not run.
- **`unregistered`** — this section registers **no** field the group could supply, so no source could have provided one.

⚠ *Deliberately a list and not a table: the §11 tables are a machine-read surface (a row
`| `name` | … |` here is required to be a registered field), so a documentation table of
token values would be scraped as four phantom fields. It was, once — this note is the reason the
shape is what it is.*

The last two are deliberately distinct, and conflating them is a live hazard rather than a
theoretical one. `unregistered` is the `wam` group's state today: its producer emits counters
(`wam_refused_depth`, `wam_refused_steps`, at the providers tier) and this section surfaces
**none** of them, so *"every measured group shows an actual-path source"* holds there for want of
a domain. That is a **vacuous** satisfaction, and it is recorded as one — with its un-satisfiers:
a §11 row whose producer names `wam`, or an engine group this section has never registered. A
single label covering both arms would make that designed emptiness indistinguishable from a
group whose values were measured and dropped, which is the arm a reader must be able to act on.

⇒ **`unregistered` is DERIVED from this section, not declared per group.** A consumer may
therefore read it as a statement about the registry rather than about any engine: the day a row
here names a group that has none, that group's label moves on its own.

**The record's route: `passes` (#2733 5b-ii).** A `stats_v2` record carries `passes`, the
diagnostic passes that ran on it (`bottom_up_profile`, `sld_replay`), on every record and empty
when none ran. With each group's `source` it is the record's ROUTE, and the CLI's stats registry
states when each key is present as a predicate over those two facts, which its check evaluates on
real records rather than reading prose. A pass is stated rather than inferred from a timer beside
it, which would make the check circular.

**go/ts coverage (#636) — interface parity, not capability parity.** The go and ts cores have
no native bottom-up/relational/SLD engine (all of `engines/{seminaive,relational,sldnf,wam}`
are rs-only, and the wasm search guest they drive returns only candidate frames — never
work-counts over its ABI). Per [ADR 0012](../architecture/decisions/0012-interface-parity-not-capability-parity.md)
(omit-not-fake) they therefore compute and emit ONLY the `work-count` fields they derive
**natively in their analyzer** — `strata` (class `analysis`: the stratum-partition size their
`analyze()` computes — a program property, equal to rs's `strata_sealed` only on a clean run, #1671) and `edb_clauses`
(class `analysis`: #900's extensional empty-body ground clause count, read off `ProgramAnalysis.edb_facts`; emitted as `edb_facts` until #2219) — and **omit** every engine-internal counter above
(`rounds`, `tuples_derived`, `emitted_head_tuples`, `truncation`, `variants_scheduled`, the
relational index/lookup set, the interner population, the full SLD set, `candidate_clone_bytes`,
the tabled/`magic_*` coverage). An omitted counter's key is **absent** (never a faked `0`).
Their emitted fields use these exact names + the frozen ontos-data integer embedding, so the
shared `work-count` fields are **cross-core byte-identical** and pinned by
[`vectors/profiling.json`](../../vectors/profiling.json) (rs ≡ go ≡ ts where computed; timers
D2 + attribution D3 are excluded from the pin by class).

### 11.2 D2 — per-phase timers

The fine per-phase timers, each class **`timer`** (wall-clock, diagnostic, never
certified, never cross-core-pinned), in **microseconds** (`µs`): `compile_lower`,
`demand_pruning`, `planning`, `index_build`, `ingest`, `eval`, `query`, and `size_walk`. (The
coarse `search` / `derivation` / `check` split that exists today is subsumed by these
finer phases when `profiling` is on.) Because timers are perturbing, two runs — and two
cores — legitimately differ; a timer field MUST NOT feed any cross-core or certified
assertion.

They are surfaced (rs, #634) as a **`phases` sub-object** of the `stats` object — one
`u64` microsecond field per named phase, PLUS `other` (the unattributed remainder) and
`total` (the whole diagnostic-channel wall-clock). The named spans are sequential and
**non-overlapping**, so `Σ(named phases) ≤ total` and `other = total − Σ(named)`.

**Presence (#2216).** Each timer is emitted only when its PRODUCER ran: `compile_lower` …
`eval` when the `bottom_up_profile` replay ran, `query` when the `sld_replay` replay ran,
`size_walk` when the record carries a `sizes` group, and `other` / `total` (which bracket the
replays) when any replay ran; the `phases` object is omitted when none did. Within a replay
that ran, a phase it did not exercise (e.g. no `index_build` / `ingest` on a program outside
the function-free fragment) reports **`0`**. Until #2216 the object had a FIXED SHAPE — every
key always present, `0` for an unrun pass — which was honest while `--stats` ran the replays
by default and became a fabricated measurement once it stopped: a `0` under `compile_lower`
would have read as the answering run compiling in no time. The answering run's timing is the
`--trace` span tree. `other` and `total` are class
`timer` like every named phase. **No timer field — including `total` / `other` — ever feeds a
`Derivation`, a certificate, or a cross-core byte-pin** (the timers are display-only; the
default build, with `profiling` off, links no clock at all, so the certified path carries no
timing perturbation by construction).

The `phases` fields, as the registry (§11.5) binds them:

| field | unit | class | meaning |
|---|---|---|---|
| `compile_lower` | µs | `timer` | lowering the clause list into the physical plan (Pass-1 lower + plan, `core/rs/src/compile/`), no query. |
| `demand_pruning` | µs | `timer` | the query-driven demand / magic-set rewrite (`compile_with_query`, Pass-1.5). |
| `planning` | µs | `timer` | building the executable relational plan (query-access planning + index selection over the lowered program). |
| `index_build` | µs | `timer` | materializing the relational indexes across the seed + delta rounds (the engine's `index_build_us`); `0` when no relational drive ran. |
| `ingest` | µs | `timer` | loading the EDB into the relational store (the engine's `ingest_us`); `0` when no relational drive ran. |
| `eval` | µs | `timer` | the bottom-up fixpoint drive (the seminaive round loop). |
| `query` | µs | `timer` | the top-down search replay (`solve_all_reporting` over the same program). |
| `size_walk` | µs | `timer` | the §11.6 SIZE dimension's collection cost — the derivation walks behind `sizes.per_answer[]`, so a reader can subtract what measuring cost. `0` when `--stats` measured no answer. **Named for the walk, not the group**: a `sizes` phase would share an id with the `sizes` group, and one id means one measurement. |
| `other` | µs | `timer` | the unattributed remainder, `total − Σ(named)`, floored at `0`. |
| `total` | µs | `timer` | the whole diagnostic-channel wall-clock — one outer span around every phase, **plus `size_walk`**, which is measured on the answer-rendering path rather than inside that span and is added in when recorded, so `Σ(named) ≤ total` stays exact. |

### 11.3 D3 — attribution

The per-rule / per-variant / per-access **attribution** is a map from an attribution key
to a `work-count` cost (e.g. `candidate_rows_examined`, `match_attempts`,
`tuples_derived`) for that key:

- `per_rule` — keyed by rule (clause) id;
- `per_variant` — keyed by scheduled rule variant;
- `per_access` — keyed by relation-access shape.

The aggregate work counted by attribution is `work-count`; the attribution *keys* are
`engine-local` (a key set is meaningful for the engine that produced it). The
attribution carries a coverage figure — the fraction of total counted work that is
attributable to a named key — for which the build-out sets a **≥ 90 %-attributable**
exit gate (epic [#630](https://github.com/Bitspark/logos/issues/630) / #635); coverage
itself is a `work-count` ratio.

**rs realization (#635, seminaive `per_variant`).** The rs seminaive engine surfaces the
D3 attribution through the `--stats` `stats.attribution` object: a `per_variant` array (one
row per scheduled rule variant, ascending by key), a `top5` view (the five variants with the
largest `elapsed_ns`, descending, ascending-key tie-break; #2163 — ranking by the whole-ms
`elapsed_ms` ordered every sub-millisecond variant by key alone), an `attributable_pct` coverage
summary, and — **warn-only**, set only when coverage `< 90` — an `attribution_warning`. Each
`per_variant` / `top5` row carries:

| field | unit | class | meaning |
|---|---|---|---|
| `rule_id` | id | `engine-local` | the rule's stable global scheduling-order index (`group_rules`), stable across rounds so a rule's cost accumulates rather than fragmenting. |
| `variant_id` | id | `engine-local` | the semi-naive specialization: `0` = the naive/seed firing (every body atom reads the full model); `n + 1` = the delta read of recursive positive body atom `n`. |
| `elapsed_ms` | ms | `timer` | wall-clock accumulated over every firing of this `(rule_id, variant_id)` — one scoped timer per variant firing, never per candidate row. **DISPLAY-ONLY**, never certified, never cross-core-pinned. |
| `elapsed_ns` | ns | `timer` | the same accumulated wall-clock in nanoseconds, saturating at `u64::MAX` — the key `top5` ranks by (#2163). A new key, not a reshaped `elapsed_ms` (§11.5). **DISPLAY-ONLY**, never certified, never cross-core-pinned. |
| `candidate_rows` | rows | `work-count` | candidate rows this variant examined — the SAME per-column counts that feed the engine-wide `candidate_rows_examined` (shared increment; Σ over variants == `candidate_rows_examined`, never a divergent second count). |
| `attribution_pct` | percent | `work-count` | this variant's share of the attributed candidate-row total, in `[0, 100]` — `work-count`-derived (a ratio over `candidate_rows`, never over the perturbing `elapsed_ms`). |

The summary field beside the two arrays:

| field | unit | class | meaning |
|---|---|---|---|
| `attributable_pct` | percent | `work-count` | the attributed candidate-row total over the engine-wide `candidate_rows_examined`, in `[0, 100]` — `work-count`-derived, never over the perturbing `elapsed_ms`. |

`attributable_pct` is `100` on the normal seminaive path (every firing is attributed). When it falls below the `90` self-check the report sets
`attribution_warning` (a human-readable shortfall string) — **warn-only: the run NEVER panics
or fails on low attribution**, because attribution is a diagnostic side-channel and a
low-coverage diagnostic run must still complete. `elapsed_ms` is a `timer` and so MUST NOT
feed any cert, digest, or cross-core-pinned measurement; the `candidate_rows` / pct figures
are determinism-stable work-counts. go/ts may omit the whole D3 group (attribution is rs-first,
#636) — omit-not-fake (ADR 0012).

**Source — the answering run (2026-09-25, #2162, `seat:caa`'s ruling (b)).** A row of this table
is a claim about what the run DID, so the object describes the execution that answered. When a
bottom-up engine answers, it states its per-variant map on the run's profiling sink as two keyed
families, `attribution_candidate_rows` and `attribution_elapsed_ns`, both keyed
`"<rule_id>/<variant_id>"`. A timer entry is stated only for a timed variant. The reader rebuilds
the engine's own report from them. The seminaive object (`attribution`) and the relational one
(`relational_attribution`) are therefore **by-source**, like their groups:
- present from the answering run's sink when that engine answered and the capture dropped nothing;
- else from the `bottom_up_profile` replay when `--stats-replay` requested it;
- never mixed within one record.

An answering engine that emits no §11.3 attribution (sldnf, the WAM) leaves both objects
**ABSENT**, never an empty or zero-filled object and never a row borrowed from a replay, and
`collectors.groups` names the engine that answered. **Origins are by-source too (2026-09-25,
#2493, `seat:caa`'s ruling (b)):** the answering engine states its own lineage on the same sink,
and the origins are resolved from it exactly as from the replay's (below).

**Origins — `attribution_v1` (rs, #1865 increment 1, `--origins`, requires `--stats`).** The
`(rule_id, variant_id)` key names **this artifact's compiled work**: `rule_id` is the
seminaive engine's admission-order index (dense over the rules it schedules; a fact or a
count-bearing clause takes none) and `variant_id` its semi-naive specialization. The numbers
identify nothing across revisions — an unrelated clause inserted above re-numbers every rule
below it — so a consumer MUST NOT equate them between captures. `--origins` annotates each row
with where it came from, read from the engine's own allocation at build time, never
reconstructed from the numbers:

```
origin: { kind: "source", clause: "c<n>", text: "<the clause as pretty-printed>",
          variant: { kind: "naive" } | { kind: "delta", positive_atom: n, delta_atom: "<goal>" } }
      | { kind: "unmapped", reason: "<why>" }
attribution.schema  = "attribution_v1"
attribution.lineage = { rules: [ { rule_id, clause, text, variants: [ { variant_id, kind, … } ] } ],
                        unresolved: [ { rule_id, reason } ] }
```

- **`clause`** is the checker's `ClauseId` (`c<n>`, the source-order index) — the SAME
  coordinate a derivation cites, retrievable at the captured revision without a source span
  (the parser's byte spans do not survive into the contract `Clause`, and carrying them would
  be a contract-tier change, out of scope here).
- **Resolution is by CONTENT (2026-09-25, #2493).** The engine's `source_clause` indexes the
  slice IT compiled. So the holder of that slice names the source by content, as
  `ClauseId::canonical` of the compiled clause, and the consumer matches that value against
  the caller's clauses. It never resolves `source_clause - fact_count` against a list of its
  own, which was right only while two independently built lists agreed. The sink and the
  replay go through ONE resolution. Exactly one matching caller clause gives `source`.
  None (the engine compiled a clause the caller's program does not contain: a rewrite, a
  normalization) and several ("ambiguous: N caller clauses share this content") are both
  `unmapped` by name, never a neighbour and never the lowest `c<n>`.
- **`text`** is the pretty-printer's rendering of that clause, so revisions are compared by
  CONTENT: the same rule after an unrelated insertion above keeps its `text` and moves its
  `clause` — the fixture `stats_golden.rs` pins exactly that.
- **`variant`** is the transformation lineage of a semi-naive variant: `naive` for the seed
  firing (`variant_id 0`), `delta` naming the positive body atom it reads from the round delta
  (`variant_id = positive_atom + 1`) and that atom's text. ⚠ **`delta_atom` is ABSENT when the
  producer cannot render the atom's text** — a physical-plan producer lowers rule bodies to slot
  patterns and the variable names do not survive, so the atom has an index but no text. The kind
  stays `delta` and `positive_atom` is never absent on one: the coordinate is fully placed, and
  declaring the variant `unmapped` would state less than the producer knows. Absent, never `null`
  and never a rendering invented from slots (`seat:caa`, ruling on #1984). ⚠ **An engine's lineage
  lists the variants it FIRES** — every producer fires a seed for each rule it admits, so
  `variant_id 0` is present in every lineage; which delta variants (`n + 1`) exist is the planner's
  and is engine-local, and a consumer resolves a delta variant the lineage lacks as `unmapped`
  rather than assuming one. *(Corrected by `seat:caa` on #1984 increment 2: this read "membership,
  like `variant_id`, is engine-local — a producer whose planner seeds differently may have no
  `variant_id 0` for a recursive rule", which was true of a planner's PLAN VARIANTS and false of
  its FIRINGS. The seed is a property of the evaluation class — a seed round, then delta rounds —
  not of any planner. Narrowed to the delta set rather than flattened to "membership is normative",
  which would void §11.3's reason for forbidding a cross-producer parity test.)*
- **Each producer emits its OWN attribution object; rows are NEVER merged across producers.** A
  `(rule_id, variant_id)` key is `engine-local`, and each producer numbers `rule_id` densely from
  `0` over the rules **it** admits — so a merged table would carry two meanings in one key space,
  and a row would resolve against whichever lineage the reader happened to hold and render a
  confident WRONG origin instead of `unmapped`. Rows in different objects are **not comparable**
  and must not be ranked together; that is the same reason this section forbids a cross-producer
  parity test. ⚠ A producer tag on one shared table is **refused** rather than offered as the
  compromise: it makes two key spaces look like one table, and so invites exactly the comparison
  the rule exists to prevent (`seat:caa`, #1984 increment 2).
- **Unknown is `unmapped`, by name, never a guess** — a `rule_id` the lineage lacks, a
  `variant_id` the rule does not have, or a coordinate outside the rule list. The `lineage`
  list carries every admitted rule (fired or not) and an `unresolved` list of what the map
  could not place, so a partial map says so instead of thinning silently.
- **Not produced by this producer, stated rather than declared as empty arms:** `generated`
  and `merged`. The seminaive engine neither synthesizes nor merges rules; the magic-set
  rewrite lives in the relational planner (`core/rs/src/compile`), whose rule ids do not feed
  these rows. Cross-revision correspondence (ESTABLISHED vs AMBIGUOUS matches) is increment 2.
- Everything here is diagnostic and profiling-only; without `--origins` the attribution object
  is byte-identical to the pre-#1865 one (no `origin`, `schema`, or `lineage` keys), and the
  default build is unchanged.

### 11.4 D4 — the execution trace (`trace_v1`)  [rs, #1864 increments 1, 2a, 2b and 2c]

Every drive the `stats` record describes is a **profiling experiment** — a separate,
read-only replay run for the diagnostic channel (§11.2's phases are timed inside those
replays) — so nothing in §11.1–11.3 says which span was the execution that actually answered
the query. `--trace` (rs CLI; **requires `--stats`**, and inert without the `profiling`
feature exactly as `--stats` is) adds a **`trace` sub-object** to the `stats` record that
names the two apart. Every field is class **`timer`** or a declaration about timers: display
only, never certified, never cross-core-pinned, never compared exactly.

```
trace: {
  schema: "trace_v1",  clock: "monotonic",  unit: "ns",  durations: "inclusive",
  route:  "kernel" | "sldnf-direct",
  engine: <the active plan's provider> | "composed" | "sldnf-direct" | null,
  engine_note?: "no selection",             // only beside engine: null — the run chose no plan
  implementation?: { provider, variant },   plan_revision?: <n>,        // kernel route, #1936
  composition?: "single" | [ { stratum, implementation: { provider, variant } } ... ],
  fallback?: { from: { provider, variant }, to: { provider, variant }, reason } | null,
  coverage: ["prepare", "drive", "stratum", "round", "solve"],
  capture: { outcome: complete | refused | truncated | failed | unsupported, reasons: [..] },
  effective_limits: { sld_max_depth, sld_max_steps },
  spans: [ { id, parent: id | null, kind, name, start_ns, dur_ns, index? } ... ]
}
```

- **Exactly one `selected_execution` pass** (span `0`, parent `null`): the drive that
  produced the answers the caller saw, timed at the app layer. Its children in this
  increment are `prepare` (program load + query parse + search-order analysis) and `drive`
  (the kernel spine stream, or the direct solve + check). **`coverage` names the boundaries
  the trace can observe**; a `drive` with no children means *unobserved below this*,
  never *nothing happened*. The selected pass's `drive` on the kernel spine is still
  unobserved below the app layer.
- **`stratum` and `round` spans (increment 2a)** are the bottom-up profiling drive's OWN
  boundaries: one `stratum` per stratum the scheduler sealed, one `round` per round it ran,
  nested `bottom_up_profile → eval → stratum → round`. They are reported by the scheduler
  itself (`logos_core::drive::DriveObserver`, a read-only witness the default build drives
  with a no-op — the schedule is the same function of the same inputs, observed or not) and
  carry `index` (the stratum's position; the round number from 0). **Their counts equal the
  record's `strata` and `rounds` counters** — two surfaces that cannot disagree.
- **`solve` spans (increment 2b)** are the top-down replay's own boundaries: one per ANSWER
  the replay yielded, nested `sld_replay → solve`, running from the previous answer's yield
  (or the replay's start) to this one's, reported by the searcher itself
  (`logos_sldnf::SolveObserver`, the same read-only-witness shape as the scheduler's). The
  tail after the last answer — the exhausting search that proves there are no more — is
  deliberately not a `solve`: it is the replay's exclusive time. **Their count equals the
  number of answers the replay emitted** (the `solution` records), NOT `sld_answers_yielded`,
  which counts every sub-goal proof the searcher yields on the way and is a different
  number by design. `index` is present only on `stratum`, `round` and `solve`; every
  increment-1 span renders exactly as before.
- **`index` and `operator` span names (design 0006 P5a)** are revision-stable keys a consumer may
  line up between captures: an `index` span's `name` is `<predicate>/<arity>` where the arity is
  the segment after the **last** `/` (a predicate name may itself contain one) and the predicate
  is percent-escaped so that two distinct predicates can never render to one name (`%` renders as
  `%25`, and any byte outside valid UTF-8 as `%XX`), while an `operator` span's `name` is the
  physical operator's catalog id.
- **`diagnostic_pass` spans are top-level siblings, never children of the selected pass**:
  `sld_replay` (the top-down re-run that yields the `sld_*` counters) and
  `bottom_up_profile` (the seminaive profiling drive, with `compile_lower`,
  `demand_pruning`, `planning`, `eval` and `relational_drive` as its `phase` children — the
  same instants §11.2's `phases` read, so the two surfaces cannot disagree). The tree shape
  IS the claim that no diagnostic time sits inside the selected span.
- **Durations are inclusive nanoseconds on the monotonic clock**, `start_ns` relative to the
  trace origin. Exclusive time is derived by the consumer as `dur − Σ(children)` and is never
  emitted. A pass is a tree: children are sequential and nested, so overlap is
  inexpressible, and **no additive production breakdown may be inferred across passes** —
  two passes are two executions of the same program, not two halves of one. The two
  measured span fields, as the registry (§11.5) binds them (`id`, `parent`, `kind`, `name`
  and `index` are metadata):

  | field | unit | class | meaning |
  |---|---|---|---|
  | `start_ns` | ns | `timer` | the span's start, relative to the trace origin (the first instant the app could observe), on the monotonic clock. |
  | `dur_ns` | ns | `timer` | the span's inclusive wall-clock — its children's time included; a span still open when the trace was rendered is closed to that instant and the capture reads `truncated`. |
  | `first_answer_ns` | ns | `timer` | the instant the CLI rendered its first answer, relative to the trace origin, on the same monotonic clock as `start_ns` (design 0006 P16). A **delivery mark**, not a span: it has no duration by nature, so it is carried as an offset rather than as a zero-length span, which would put a non-interval into the interval population. **Absent** when the run rendered no answer — never `0`, which would mean delivered at the origin. |
  | `first_certified_answer_ns` | ns | `timer` | as `first_answer_ns`, for the first answer the gate had CERTIFIED when it was rendered. On a `Certifiable` run every streamed answer is certified and the two coincide; they are stated separately so a reader need not know the tier to read the record. **Absent** when no certified answer was rendered. |
  | `end_of_consumption_ns` | ns | `timer` | the instant the answer stream finished draining, relative to the trace origin — whether it exhausted or an early stop cut it. Distinguishes early-stop delivery from complete enumeration when read against the run's terminal. **Absent** when the stream never drained. |
- **`capture.outcome` is the worst of what the producer noted**, with every reason kept:
  `complete` (every declared pass ran to its end) · `refused` (a pass was cut by its limits —
  the replay's `refused`, the selected drive's limit trip — **or was not run because the
  caller did not select it**, increment 2c) · `truncated` (a declared pass
  could not run — the profiler's evaluator failed to build, or no engine executed the
  request) · `failed` (a pass errored) · `unsupported` (a host that cannot produce this
  record: go/ts have no `--stats` channel, so this state is declared here and produced by
  nobody in increment 1 — stated, not hidden). Partial diagnostics therefore cannot read as
  complete evidence.
- **`engine`** names the execution that produced the answers, read off the kernel's
  `RunReceipt` on the answer path (#1936, design 0006 P3) — never a pin echo, never a second
  `--explain` run: the active plan's provider (`composed` for a composed plan, whose
  per-component assignment is `composition`), with `implementation` (provider + envelope
  variant), `plan_revision` (`0` = the initial plan, `n` = the n-th revision) and `fallback`
  (the `implementation-fallback` revision the drive walked, else `null`). The direct route
  reports `sldnf-direct`. A run that chose no plan (`SelectionRefused`, `Unsupported`,
  `Malformed`, `PlanSearchExhausted`) reports `engine: null` with `engine_note: "no selection"`
  — a refused selection has no fabricated winner (omit-not-fake, ADR 0012).
- **`effective_limits`** records the search budget the SLD replay ran under (the same
  caller-set budget as the answering drive, #802), so a capture says what bounded it.
- **`--stats-replay <LIST>` (#2216; requires `--stats`)** adds DIAGNOSTIC REPLAYS to a run: a
  comma list of `sld_replay`, `bottom_up_profile` or `all`. **Without it `--stats` measures the
  answering run only and executes the program ONCE** (design 0006 P6): the served engine's
  group is read from the answering run's sink (`source: selected`) and every other engine group
  reads `absent`. A replay re-executes the program under a profiling drive, so it is an
  explicit request with a measured price (#1930 A2: `--stats` with both replays cost +84% to
  +111% on recursive programs). A replay that is not run has no span, **no counters and no
  timers on the `stats` record: they are OMITTED, never zeroed** (the fixpoint work-counts, the
  seminaive / relational / interner / magic tier-2 groups, the attribution rows and
  `phases.compile_lower` … `phases.eval` for `bottom_up_profile`; the replay's `sld_*` counters
  and `phases.query` for `sld_replay`), and it is **not** noted on the capture, which describes
  the answering run: a plain `--stats --trace` capture reads `complete`. `--operator-policy`
  binds on the bottom-up profiling drive, so it requires `--stats-replay` naming
  `bottom_up_profile` (or `all`) and is a usage error otherwise. The former `--trace-passes`
  (whose default was `all`, and whose skipped pass noted `refused`) is retired, not aliased.

**Overhead recipe (documented, not promised):** run the same program twice with the same
budget, once with `--stats --trace` and once without either flag, and report the ratio of
the selected pass's `dur_ns` to the plain run's wall-clock — never an absolute. The trace
adds a handful of monotonic-clock reads around boundaries the CLI already crosses; the cost
that dominates is the profiling replays themselves, which since #2216 run only on
`--stats-replay` and which the trace makes visible as the diagnostic passes. Do not assert exact values in a test
(class `timer`); assert structure, as `app/cli/rs/tests/stats_golden.rs` does.

**Byte stability:** a `--stats` run without `--trace` renders exactly the pre-#1864 record
(no `trace` key), and the default build's machine output is byte-identical with or without
`--trace` (the existing ADR 0024 golden ratchet covers both).

### 11.5 Registry columns  [rs, #1931, design 0006 P9]

The root `stats` record carries a **`schema`** version token right after `record` (its value is
the constant `logos_kernel::seam::observe::STATS_SCHEMA`; it went from `stats_v1` to `stats_v2` with
#1935, P6, when the record began to describe the answering run and not only the replays), so a reader
diffing two captures can tell a renamed field from a removed one; the sub-records keep their
own tokens (`trace.schema = "trace_v1"`, `attribution.schema = "attribution_v1"`,
`plan_origin.schema = "plan_origin_v1"`). A changed
unit, scope, aggregation or meaning of an existing key is a new token, never a reshape in
place; adding a key with a new name is not.

Every key the record can emit, at every depth, is registered by path in
`app/cli/rs/src/registry.rs` with §11's unit and determinism class plus the columns
design 0006 §2 adds — the columns a reader needs to interpret a value safely from outside:

| column | values | meaning |
|---|---|---|
| **class** | `work-count` · `analysis` · `timer` · `engine-local` · `metadata` · `outcome` | §11's determinism classes, plus two types §11's tables have no column for: an envelope or identity field (`record`, `schema`, an id, a name, a text) and a verdict or flag (`truncation`, `sld_refused`, `capture.outcome`). An outcome keeps the determinism of its §11 row; the class says it is not a quantity, so it is never read as a counter. |
| **scope** | `selected` · `replay` · `analysis` · `envelope` · `by-span-kind` | which execution the value describes. Every counter and timer today is measured on a diagnostic **replay** (§11.4); only the trace's `selected_execution` span observes the answering run, and a span's scope is decided by its `kind`. A replay figure and the answering run's wall-clock are two executions, never compared as one. |
| **producer** | `seminaive` · `relational` · `sldnf` · `core::compile` · `core::symbol` · `core::analysis` · `cli` · `kernel` | the component that computed the value. |
| **aggregation** | `counter` · `inclusive-duration` · `exclusive-duration` · `gauge` · `peak` · `enum` · `map` · `metadata` | what kind of quantity it is: additive over the execution, a duration with or without its children's time, a level (a footprint, a ratio, an offset), a high-water mark (declared for P7, unused yet), a token, a nested object keyed by **data** (`operators`, `fallback_by_reason`, `effective_limits` — the inner keys are not fields), or structure. |
| **key stability** | `revision-stable` · `artifact-local` · `not-a-key` | whether a value is a key, and whether that key names the same thing in another capture: an operator id, reason token or clause text does; a `rule_id`, `variant_id`, `ClauseId` or span id names this artifact's compiled work only (§11.3 origins). For a `map` the column describes the inner keys. |
| **absence** | prose | what a missing key means — a pass that did not run, a program outside an engine's fragment, a flag not given — and never a measured `0` (ADR 0012). Fields that are always present say so, and say what their zero or `null` means. |
| **section** | `11.1` … `11.5` | the subsection above that defines the key. |

**Conformance.** `app/cli/rs/tests/stats_registry.rs` (profiling build) walks every key at
every depth of a real `--stats --trace --origins` emission and fails on any key the registry
does not carry — **an emitted unregistered field fails conformance** — and checks the registry
against this section's `| field |` rows in both directions: every registered measurement
(every class but `metadata` and `outcome`) has a row here, and every row here is registered.
Rows §11.1 declares that the rs CLI does not compute (the `tabled_*` coverage) are registered with an absence column saying exactly
that, so the vocabulary stays total rather than carving an exception per core.

### 11.6 D6 — sizes  [rs, #1952, design 0006 P8]

The record carried WORK and TIME and no SIZE, so #1531's relationship between a derivation's
SIZE and the time to check it was not expressible from a `--stats` emission alone. Every row
here is class `analysis`: a work count says what this RUN did and moves when the engine changes,
while a size says what this PROGRAM and this PROOF are and is invariant under a change of engine
that delivers the same answers. Aggregation is `gauge` (a size is a level, never a running
total); key stability is `artifact-local` (a node count is meaningful against THIS program at
THIS revision and is not a cross-revision key).

Per run, under `sizes`:

| field | unit | class | meaning |
| `answers` | answers | `analysis` | answers DELIVERED by the answering run (the multiset, unless `--dedup-answers` — then `deduplicated: true` is present and this is the distinct count). |
| `program_clauses` | clauses | `analysis` | clauses in the loaded program (facts + rules), a property of the source and not of the run. |
| `edb_facts` | facts | `work-count` | the DISTINCT extensional facts in the sealed store (rs only; go/ts have no store and omit it). **NOT comparable to §11.1's `edb_clauses`**, which counts source clauses and so counts a repeated fact once per copy (#2219). **ABSENT** unless the `bottom_up_profile` replay ran and sealed a model — the three populations are read off that drive's model, so `--stats` alone (which since #2216 runs no replay) carries none, and `0` would claim nothing was derived. ⚠ The model is the REPLAY's: on a top-down answering route these describe the replay's drive, not the answering run (this row said "the answering route" until #2216, which the code never did). |
| `idb_facts` | facts | `work-count` | intensional (derived) fact population, same absence rule. |
| `total_facts` | facts | `work-count` | total fact population. **ABSENT unless the `bottom_up_profile` replay sealed a model**: §11.1 defines this as `tuples_derived` over the SEALED MODEL, which only that drive produces — so it is engine-scoped, not `edb_facts + idb_facts`. |

Per delivered answer, under `sizes.per_answer[]`, keyed by answer ordinal:

| field | unit | class | meaning |
| `derivation_nodes` | nodes | `analysis` | nodes in the wire arena, each shared sub-proof encoded once (`derivation_wire.rs`: `Tuple[ Tuple[node₀, …], Atom(root) ]` — a flat arena plus a root index). **NOT the checker's visit count** — see #1932. |
| `derivation_depth` | nodes | `analysis` | the longest root-to-leaf path over `Pos` premises, counting the root as 1. A MAX rather than a sum, so it is linear and cannot overflow. |
| `derivation_wire_bytes` | bytes | `analysis` | `len()` of that encoding — taken where the emitter already encodes once, never by a second encode. |
| `closed_world_certs` | certificates | `analysis` | the closed-model certificates the derivation CARRIES (`Derivation::closed_world`); **`Neg` AND `Count` premises cite them** — the field is named after the carried vector, not after what cites it. |
| `closed_world_rows` | rows | `analysis` | rows across every carried certificate's extension tables. |

⚠ **The checker's visit count is deliberately absent, and that is a ruling rather than an
omission** (`seat:cca` on #1952, 2026-09-12). An earlier draft of this rung defined
`derivation_nodes` as *"nodes visited by a pre-order walk … a shared sub-proof counts each time
it is reached"*; that parenthetical is WITHDRAWN, because its premise was that the wire expands
sharing and the encoder above shows a flat arena. Counting reaches is a sum over root-to-node
paths — exponential in depth on a diamond-shared proof, so it can exceed `u64` while the arena
holding it stays linear. That number is a COST of the checker's walk, and checker cost is P1's
`CheckReport` (#1932); a saturating cost in a size row would be the "looks measured and is not"
failure this section exists to prevent. No `sizes` row carries it.

⚠ **A malformed derivation is reported, not hidden.** A `Pos` edge that closes a cycle makes the
proof invalid; the walk refuses to follow the back edge and the entry carries
`derivation_malformed: true`. Both flags are omitted when false, so a well-formed proof stays
quiet.

### 11.7 D7 — the `plan` origin (`plan_origin_v1`)  [rs, #1984 dw2]

§11.3's origins name where a compiled RULE came from. This names which PLAN NODE each executed
segment carried out, so a reader can go from the plan the resolver authorized to the work the
drive did under it. `--origins` (rs CLI, which **requires `--stats`**) adds a **`plan_origin`
sub-object** to the `stats` record on the **kernel route only**. The direct route has no plan
and no segments, so it carries none. Everything here describes the ANSWERING run (scope
`selected`): it is read off that run's `RunReceipt` and its outcome, never off a replay.

```
plan_origin: {
  schema:   "plan_origin_v1",
  origins:  [ { kind: "plan",
                component_path: [ "<component id>" ... ],        // [] is the run root
                authorized: { provider, variant },
                execution: { kind: "same",     segment: <id> }
                         | { kind: "fallback", segment: <id>, executed: "<provider>" }
                         | { kind: "unmapped", reason: "<why>" } } ... ],
  segments: [ { id, component_path?: [ ... ], provider?, <dimension>?: <amount> ... } ... ]
}
```

- **A plan node is keyed by `(component_path, authorized implementation)`**, its own identity.
  A single-engine plan is one node at the run root, `[]`. Each component of a composed plan is
  a node at `[stratum/N]`, the same id the composed executor stamps on that component's segment
  and keys its boundary certificate by. The nodes are the ACTIVE plan's. A single-engine plan
  superseded by an `implementation-fallback` revision never ran a segment, and §11.4's
  `fallback` already reports that walk.
- ⭐ **The join is by `component_path` alone, never by list position, and the provider is a
  CHECK rather than part of the key** (`seat:caa` on #1984, the 2026-09-13 ruling as amended
  2026-09-23). The plan node pins the AUTHORIZED implementation; a segment names the engine
  that RAN. Under a per-component fallback those differ, so a join on the pair would find no
  partner for exactly the component the origin exists to explain. `execution.kind` is the
  outcome of the check:
  - `same`: exactly one segment sits at the path, and it ran the authorized provider;
  - `fallback`: exactly one segment sits at the path, and the outcome's recorded
    `ComponentFallback { stratum, authorized, executed }` for that stratum says it ran
    `executed` instead;
  - `unmapped`, by name: no segment carries the path, more than one does, the segment names no
    provider, or it ran a provider that no recorded fallback reconciles. It is never omitted and
    never guessed. In particular, a segment whose producer carries no path (`none`) joins
    nothing: letting it match would be a join by position.
- **`segments` carries the join partner on the same record**, in run order, so the join can be
  performed on one surface. `id` is the segment's in-run ordinal (`SegmentId`), which
  `execution.segment` names. Each other field is **ABSENT when the segment does not know it**,
  and none is zero-filled:
  - `component_path`: absent when the producer carries no path, which is different from `[]`;
  - `provider`: absent on an unattributed segment;
  - the actuals: one key per budget dimension the segment's actuals METERED, under that
    dimension's wire token. A dimension that was not metered is absent (§18). The rs drive
    meters these two today:

| field | unit | class | meaning |
| `search_nodes` | nodes | `engine-local` | the search work the drive metered for this segment. A composed component's is its draw, the larger of its own nodes and its nested pulls (#1947 2b's E4). |
| `check_nodes` | nodes | `engine-local` | the GATE work spent checking this segment's accepted proofs. It is absent when nothing was accepted, and it is not comparable to `search_nodes`: the two are reported beside each other and never netted. |

- **`plan_origin_v1` is its own token, beside `attribution_v1` and not inside it.** It keys a
  different family (plan nodes joined to segments) from `(rule_id, variant_id)` rows, and growing
  `attribution_v1` would put two key spaces under one version. `component_path`,
  `execution.segment` and `segments[].id` are `artifact-local`: a stratum id and a segment ordinal
  are this run's, and they are not keys across revisions.
- Everything here is diagnostic and profiling-only. Without `--origins` the `stats` record is
  byte-identical to the pre-dw2 one (no `plan_origin` key), and the default build is unchanged.
