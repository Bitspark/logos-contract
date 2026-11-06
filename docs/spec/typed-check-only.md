# Typed check-only contract, version 1

This contract admits an in-process, search-free checking service for the selected
`dependent-fragment-1`, edition 1 [rulebook](foundations/dependent-fragment-1.md).
Implementation and admission are delivered together by the typed check-only change.
It is a scoped service, separate from design 0014's full semantic-package/kernel
promotion. It does not activate that design's registry, wire, planning or family
interfaces. The existing ground account remains its active specialized calculus.

## Ownership and authority

Logos owns the expression language, signature/context checking, substitution,
conversion, exact statement checking, assumption closure, resource behavior and
result construction. There are no solver or consumer callbacks in checking.
Consumers own object-language interpretation, projection from actual artifacts,
source/native judgments and representation laws. They fix the expected statement
and authorize its basis independently of candidate evidence. Bittype does not
provide another proof calculus; Logos does not interpret Page, TextBox, Horos,
Go, mapping configurations or artifact snapshots as built-in meanings.

Names identify declarations in one supplied signature. Their spelling is not an
authenticated artifact reference. A consumer binds actual objects and qualified
declaration identities before constructing that signature, and retains the
association between the checked statement and its invocation. An accepted result
does not prove an extractor, compiler model, imported procedure or assumed law
correct. Those dependencies must be named and permitted. A premise asserting the
entire answer is still an assumption, never an independently derived answer.

## Public operation

The three bindings expose the same operation under a `typed` module/namespace:

```text
check(statement, candidate, policy, limits) -> Outcome

Statement {
  foundation: string,
  declarations: ordered Declaration[],
  context: ordered Expr[],
  expected: Expr
}
Declaration = Assume { name, type: Expr, dependencies: string[] }
            | Define { name, type: Expr, value: Expr }
Policy { foundation: string, checker: string, dependencies: string[] }
Limits { input_nodes, input_depth, collection_entries, name_bytes, work, depth }
Candidate = Expr
```

`foundation` is exactly `logos/dependent-fragment-1/edition-1`.
The checker identities are `logos/typed-check-only-v1/rust`,
`logos/typed-check-only-v1/go` and `logos/typed-check-only-v1/typescript`.
They name the binding's implementation contract; the installed package revision
identifies the actual executable dependency. These identities do not assert
formal implementation correctness. The receiver selects and admits its installed
package revision through application composition; the checker string does not
perform that selection or uniquely identify its binary. Policy must explicitly
admit the current foundation and checker contract as well as every actually used
semantic dependency. A verdict-changing typed release changes the typed checker
identity and documents the change, following ADR 0039's application of ADR 0035
D1/D9. Proof terms can be rechecked; an old result is never restored as authority.

Identities compare by exact UTF-8 bytes without Unicode normalization. Invalid
UTF-8 in Go and unpaired UTF-16 surrogates in TypeScript are malformed input.
Reported identity sets use ascending UTF-8 lexicographic order. Repeated entries
in dependency lists are legal: preflight counts every entry, while admission and
the reported closure treat their identities as a set.

Rust exposes `logos_contract::typed::check`; Go exposes the `typed` subpackage of
`github.com/Bitspark/logos-contract/contract/go`; TypeScript exports namespace `typed` from
`@bitspark/logos-contract`. Their ordinary idiomatic constructors/accessors may
differ; meanings and outcome codes are shared. No kernel, engine, provider
registry, search service or external solver is required.

Expression/declaration constructors store syntax without admitting it. Go and
TypeScript use opaque immutable syntax nodes. Rust exposes algebraic syntax values;
its ownership and borrowing rules protect the checked snapshot from caller mutation.
Zero or forged expression/declaration values reject as malformed input; a zero
outcome is never accepted. Mutable input lists are borrowed for the duration of
the synchronous call and the caller must not concurrently mutate them. Accessors
for immutable nodes return read-only values or defensive operand/dependency lists.

Rust's `typed::foundation` primitives are also available to existing rulebook
experiments. They are low-level typing operations without receiver policy or the
production input boundary. Their result type is distinct from `typed::Accepted`
and cannot be imported as production acceptance. Consumers use `typed::check`.

The candidate contains proof syntax only. It cannot choose a signature, add an
assumption, alter policy or replace the expected statement. Every call checks the
ordered declaration list afresh, then the context and exact expected type.
Assumed declarations require a nonempty list of nonempty dependency identities.
Definitions require checked values and may reference only earlier declarations.
Duplicate declaration identities, unresolved/forward references, recursive
definitions and escaping variables reject. Context entries are ordered outermost
first, each scoped before its own binder. Logical hypotheses in the context are
part of the proposition, distinct from the policy's allowed dependencies.

Expressions are exactly the 21 rulebook constructors, with its operand order:
`sort`, `var`, `const`, `pi`, `lam`, `app`, `sigma`, `pair`, `fst`, `snd`, `nat`,
`zero`, `succ`, `nat-elim`, `bool`, `false`, `true`, `bool-elim`, `id`, `refl`,
`transport`. The existing Rust `Expr::Eq` spells rulebook `id`. Universes and
indices use exact nonnegative values up to the implementation's u32 capacity;
an arithmetic operation exceeding that capacity is incomplete. Scope escape is
invalid. If a binding can represent an exact supplied natural above u32 capacity,
checking returns the corresponding `universe-capacity` or `index-capacity`
noncompletion; it never truncates. Negative, fractional, nonfinite or inexact
numeric inputs are malformed. Rust and Go's u32 constructors cannot express an
oversized natural. TypeScript admits safe integral numbers as syntax, with the
capacity decision made by checking. Limit fields themselves remain u32.
No cumulativity, eta, proof irrelevance, arbitrary inductives, user
rewrite rules, general recursion or equality reflection is added.

Checking validates that the candidate has a type definitionally convertible to
the caller's expected type. It preserves the caller's exact requested expression,
not only its normal form or the inferred type. An accepted result privately owns
an immutable snapshot of the full supplied declaration/context/expected statement,
candidate and acceptance policy. It exposes read-only views or defensive copies, actual used
declaration identities, actual dependencies, checker/foundation identity and work
spent. A caller cannot construct acceptance through a public struct literal,
mutate its stored statement, or recover acceptance by deserializing a report.

The dependency result includes the syntactically reachable closure of declaration
types and values used by the context, expected type and candidate, including
operands later erased by conversion. It is not claimed to be a logically minimal
basis. Unused declarations and unused policy entries do not enlarge this closure.
All declarations must nevertheless be well formed. A fresh policy is enforced on
every call; there is no verdict cache or inherited acceptance under a broader one.

To reuse a closed theorem, retain its defining signature, add a `Define` with the
accepted exact expected type and candidate term, and check an application against
its new independently chosen expected type. This rechecks the definition and its
basis; an earlier accepted report is not imported as a fresh trusted `Assume`.
An open-context result needs explicit abstraction or checked context transport.

## Outcomes and resources

Outcomes are disjoint:

* `Accepted`: this exact statement is established relative to its context and
  admitted foundation, checker implementation and reported assumptions.
* `Invalid`: malformed syntax, scope, declaration or type/evidence mismatch.
* `Incomplete`: work, depth, input size or integer-capacity exhaustion.
* `Unsupported`: an unserved foundation or a basis the receiver has not admitted.

Shared invalid codes are `malformed-input`, `escaped-variable`,
`unknown-constant`, `duplicate-constant`, `missing-assumptions`,
`empty-constant-name`, `expected-universe`, `expected-function`, `expected-sigma`,
and `type-mismatch`. Shared incomplete causes are `input-nodes`, `input-depth`,
`collection-entries`, `name-bytes`, `work`, `depth`, `universe-capacity` and
`index-capacity`. Shared unsupported causes are `foundation`,
`unadmitted-foundation`, `unadmitted-checker` and `unadmitted-dependency`.
Codes are typed variants/constants, not parsed message prefixes.
Failures expose a logical location: phase `preflight`, `declaration`, `context`,
`expected`, `candidate`, `policy` or `snapshot`, with an index where applicable.
An implementation may additionally expose an expression operand path. These are
logical positions, not consumer AST IDs, source spans or artifact locations.
The consumer maps them to its own source and generated-output diagnostics.

A proof of a negative proposition is accepted evidence of that proposition;
invalid evidence and noncompletion do not refute the requested claim. Boolean
data constructors are not checking outcomes. Source-provider `Unproved` cannot
be imported as a proof of nonmembership. This API is synchronous and bounded;
it supplies no asynchronous cancellation or background task. A consumer that
cancels its surrounding operation must report that noncompletion separately.

Defaults are 100,000 aggregate input expression nodes, 128 input depth, 4,096
aggregate collection entries, 256 UTF-8 bytes per identity, 1,000,000 work units
and 512 internal depth. Fixed implementation ceilings are 128 input depth and
512 internal depth; larger requested depth limits do not remove these ceilings.
Limits are unsigned 32-bit integers in every binding. Input expression roots have
depth one; each child increases depth by one. Internal checking depth starts at
zero. Collection entries count declarations, context entries and entries in both
declaration and policy dependency lists; expression operands count as expression
nodes. Zero limits exhaust the corresponding nonempty operation; arithmetic never wraps.
Work counters describe this implementation, not portable computational cost.

Before recursive traversal, copying or signature construction, an iterative
preflight bounds the entire statement and proof, including unused declarations,
contexts, dependency lists and policy identities. It validates constructor kinds,
arity, scalar fields and identity encodings. Cycles and malformed host values
reject; repeated shared subtrees count on each traversed occurrence. Preflight
itself shares the work allowance. The same remaining allowance covers signature
admission, checking and construction of the owned acceptance result. Failure
cannot expose a partial accepted result.

The resource promise covers work performed by Logos on supplied in-memory data.
It does not cover allocation, parsing or destruction performed by the caller
before or after that call. There is no public byte decoder in v1. Test fixture
JSON is not a portable proof protocol. Adding untrusted serialized ingress needs
its own versioned bounded decoder and cross-binding vectors; a caller must not
advertise arbitrary JSON parsing as part of this service's resource boundary.
Host inputs must be inert syntax data. In particular, JavaScript proxies, getters
and host callbacks are outside this API's resource contract; shape validation
cannot bound arbitrary host code invoked while reading an object.

## Consumer acceptance cases

TextBox exercises a concrete counterexample under a fixed source/native
interpretation. Its premises are actual native acceptance of bool, the selected
bool association, and explicit source nonmembership in the resolved Text kind.
Those premises can also feed the existing ground checker. A supplied typed proof
must derive the requested counterexample from those premises; neither absent
membership nor rejected evidence is a counterexample. Field representation is a
separate obligation. Fixtures name their assumed language/procedure basis.

Page fixes source/native proper-type domains, configuration, actual named
families and one resolved kind K. Its statement is:

```text
forall T, N:
  Member(T,K) -> Rep(T,N) ->
    (Member(PageH(T),K) and Rep(PageH(T),PageG(N)))
```

The proof uses real abstraction over T/N, membership and representation premises;
it applies the source constructor guarantee and selected record/list/optional
representation laws. Person application produces both premises for a second
nested application. The theorem establishes the declared static relation. Runtime
value correspondence and native admission over `(S,N,E)` require their own claims.
The representation laws must bind the actual family/fields/helper choices; merely
assuming the final Page theorem is not the acceptance construction.

Shared regression fixtures exercise exact claim and assumption binding, wrong
source/native/mapping identities, changed helpers or field relations, escaped
and captured variables, invalid transport, dependencies hidden in erased terms,
unused declarations, policy narrowing and all resource-outcome partitions.
They establish checking behavior over explicit consumer premises, not delivery of
Bittype's absent native semantic providers or proof of model/compiler adequacy.
The [consumer case explanation](typed-check-only-cases.md) describes the exact
premises, positional field encodings and public theorem-reuse exercise.
