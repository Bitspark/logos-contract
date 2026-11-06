# Typed check-only consumer cases

[`vectors/typed_check.json`](../../vectors/typed_check.json) is an independently
authored checking oracle for the [typed check-only contract](typed-check-only.md).
Its expected outcomes follow the selected rulebook and the explicitly supplied
consumer premises. It does not execute Horos, analyze Go or generate Bittype
artifacts. The source/native models, procedure results and mapping laws are named
assumptions; the resulting composition and exact claim are checked by Logos.

## Fixture notation

The test-only JSON schema is `logos/typed-check-fixtures/v1`. Expressions are
arrays containing a rulebook tag followed by its ordered operands. For example,
`["lam", ["nat"], ["var", 0]]` is the natural identity function. There are no
expression macros or candidate-controlled declarations in this notation.

`declaration_sets` holds ordered lists used by several receiver statements. An
entry is either `{kind:"assume", symbol, type, dependencies}` or
`{kind:"define", symbol, type, value}`. `symbol` is the declared constant's name
in this test notation, distinct from a case label. The latter declaration form
is always typechecked, never treated as an opaque axiom. A case supplies:

```text
id
statement { declarations: set-name, context: Expr[], expected: Expr,
            foundation?: string }
candidate: Expr
policy { dependencies: string[], foundation?: string, checker?: string }
limits?: partial Limits
expect { status, code?: string, dependencies?: sorted string[] }
```

The fixture loader resolves the declaration list, fills omitted statement/policy
foundation with the file's `foundation`, fills omitted policy checker with the
binding's own checker constant, and overlays supplied limits on public defaults.
These are explicit conveniences of the test loader. They do not add default trust
or declaration-set lookup to the production API. JSON decoding is test ingress,
not a supported serialized evidence format or resource guarantee.

Each binding compares status, the typed code when present, and the entire sorted
actual dependency list for every accepted case. Core cases cover all 21 syntax
constructors. Negative cases distinguish evidence invalidity, current trust
refusal and resource noncompletion. Malformed host objects and private result
mutation require binding-specific tests because they are not all expressible as
well-formed shared syntax. Compact well-scoped terms cannot approach u32 binder
index capacity under the fixed depth ceiling; the fixture does not pretend to
exercise that arithmetic limit using an escaping variable.

Dependency identifiers retain exact Unicode spelling, use UTF-8 lexicographic
order and have set semantics in an accepted result. The Unicode controls put
an astral scalar after a high BMP scalar, distinguish composed and decomposed
names, and count repeated input dependency entries before deduplication. Every
accepted case is also replayed with each resource allowance raised individually;
its exact checked statement, candidate and actual dependencies must survive.

## TextBox: an explicit counterexample

Fix one source Text kind, one Go declaration and one interpretation. The source
proper-type domain is `H`, the native proper-type domain `N`, and native
declarations belong to `D`. The receiver's assumed judgments are:

```text
Text : H -> Type
Admits : D -> N -> Type
Rep : H -> N -> Type

native.bool-admitted : Admits(TextBox.any, native.bool)
mapping.bool : Rep(canonical.bool, native.bool)
source.bool-not-text : Text(canonical.bool) -> Empty
```

`Empty` is the defined type `id(bool, true, false)` in the selected foundation.
The receiver admits the exact source refutation as a procedure premise; it does
not infer it from missing membership evidence. The counterexample is a dependent
pair containing native admission and another pair containing representation and
source nonmembership. Both pair types are checked definitions, not assumptions.

`textbox-explicit-counterexample` constructs those pairs. The adjacent controls
replace the expected declaration, supply a Boolean instead of a nonmembership
function, or withdraw the source-procedure assumption. They respectively produce
type mismatch, type mismatch and unadmitted dependency. None is reported as a
new semantic counterexample.

The claim covers this exact witness. It is not a proof of correct admission for
another constraint such as exact `string` or underlying `~string`, nor a proof
about the `Value` field's representation. Those require their own fixed domains,
interpretations and expected statements.

## Page: separate structural and named-family composition

`Member` is the unary judgment for one fixed resolved Data kind in configuration
C. It does not quantify over every kind. `H` and `N` here are the consumer's
source and native model descriptor domains. `Member(T)` restricts the source
input to the fixed Data-kind meaning; `Rep` is the selected static association.
Source and native named families remain opaque identities, separate from their
record bodies:

```text
SourceBody(T) = h.record(h.list(T), h.optional(h.text))
NativeBody(N) = n.record(n.slice(N), n.optional(n.string))

source.page-body(T) : SourceBodyOf(h.page(T), SourceBody(T))
native.page-body(N) : NativeBodyOf(n.page(N), NativeBody(N))
source.page-kind(T) : Member(T) -> Member(h.page(T))
```

The two record positions are fixed: source `items` corresponds to native
`Items []N`, and source optional `next` corresponds to native
`Next Optional[string]`. The native optional symbol represents the chosen
presence/value helper. The source `h.optional` and `h.record` symbols encode
that positional field schema in the consumer model; they do not introduce
standalone Horos proper-type constructors or change Horos syntax. The generic
mapping laws below quantify over model descriptors, not additional Horos
language forms. Their interpretation and correspondence to actual fields belong
to the explicitly named source/native-model and body assumptions. The fixture
does not equate a native named type with an anonymous body by definitional
equality.

The generic mapping laws are separate assumptions:

```text
law.list(T,N) : Rep(T,N) -> Rep(h.list(T), n.slice(N))
law.optional(T,N) : Rep(T,N) -> Rep(h.optional(T), n.optional(N))
law.record(A,B,X,Y) :
  Rep(A,X) -> Rep(B,Y) -> Rep(h.record(A,B), n.record(X,Y))
law.named(A,B,X,Y) :
  SourceBodyOf(A,B) -> NativeBodyOf(X,Y) -> Rep(B,Y) -> Rep(A,X)
```

`body-representation` is a checked definition that applies `law.record` to the
results of `law.list` and `law.optional`, using the separate text/string premise.
No Page theorem is assumed. `page.proof` is a checked definition whose value is:

```text
lambda T, N, member_T, rep_T_N.
  pair(
    source.page-kind(T, member_T),
    law.named(
      h.page(T), SourceBody(T), n.page(N), NativeBody(N),
      source.page-body(T), native.page-body(N),
      body-representation(T, N, rep_T_N)))
```

The pair type is the checked `PageResult(T,N)` definition. The resulting closed
`PageStatement` is the exact universally quantified conditional claim:

```text
forall T : H, N : N:
  Member(T) -> Rep(T,N) ->
    (Member(h.page(T)) and Rep(h.page(T),n.page(N)))
```

The symbolic fixture supplies the actual four-binder lambda. The reuse fixture
references its separately checked definition. Person application uses both its
source membership and representation premises. Nested application binds the
inner pair once, then supplies its first and second projections to the next
theorem application. Replacing the representation projection with membership
fails even though both were delivered by the same accepted inner result.

The public consumer exercise first removes the last `page.proof` definition from
the fixture signature and checks its displayed type/value. It then inserts a
`Define` using the accepted exact expected expression and candidate, checks
Person, and checks nesting. This exercises the usable API without importing a
serialized verdict or converting an accepted theorem into a fresh opaque axiom.

The `pageChangedHelper` signature keeps `n.page`, `Rep`, `PageStatement`,
`NativeBody`, `body-representation` and the entire old `page.proof` unchanged.
It changes the native body premise to describe the same named family using
`n.optional.changed-helper` for `Next`. Rechecking the old definition fails at
the `law.named` application's native body premise: the changed body is not the
old `NativeBody(N)` that its structural proof established. The failure occurs
while validating the final definition, before candidate admission. This control
does not rely on changing the expected family identity.

The separate changed-family, missing-field and different-source controls put
different receiver-bound family identities in the expected type. The
different-mapping control changes the representation relation. Existing evidence
fails in the foundation's type comparison. All these controls test model-level
claims; they do not establish that a Bittype extractor detects actual file
changes. That artifact-to-statement connection is the consumer's separate
obligation.

The generic result's actual dependency list excludes Person premises and the
unrelated alternative mapping, although their declarations remain in the checked
signature. Person and nested results include the two Person assumptions. Removing
`go.page-fields-and-helper` from current policy rejects the existing typed proof;
the native interpretation remains part of its actual basis.

This theorem establishes conditional static representation. Native admission
over `(S,N,E)`, runtime value behavior, source-identity retention after alias
erasure and the adequacy of actual artifact extraction are separate claims.
