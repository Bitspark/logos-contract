# Logos contract

The public contract layer of Logos: proof-account types, program and derivation
codecs, and independent checkers in Rust, Go and TypeScript. It depends on public
Ontos packages. It contains no Logos kernel, engine, search service or private
repository dependency.

Source distribution is independent of registry publication. The initial npm and
crates.io packages are pending authenticated bootstrap publication; the table
names their intended coordinates. Go consumers can use the public source tags
or commit revisions directly.

| Language | Public dependency |
| --- | --- |
| Rust | `logos-contract` on crates.io |
| Go | `github.com/Bitspark/logos-contract/contract/go` |
| TypeScript | `@bitspark/logos-contract` on npmjs.org |

Release tags `vX.Y.Z` and `contract/go/vX.Y.Z` name the same public commit.
Released versions follow the Logos release family. Main may contain unreleased
changes; pin a full commit when consuming those changes. In particular the typed
check-only service was added after 0.24.0 and is not part of that release.

The [contract specification](docs/spec/logos-contract.md) describes the account,
codecs and checker SPI. On revisions containing the typed checker, its
[service contract](docs/spec/typed-check-only.md) and
[TextBox and Page cases](docs/spec/typed-check-only-cases.md) specify the receiver's
authority and the distinction between accepted, invalid, incomplete and
unsupported results. Callers supply native judgments and the exact mapping and
premises; Logos checks the proof. An accepted proof does not establish that its
external premises faithfully describe a captured program.

Changes originate in the Logos repository and are exported here as a single
maintained implementation. Exporting changes distribution metadata and Go
self-import coordinates, with Go formatting performed on the runner. Contract
tests and their fixtures are included. The UTF-8 source census scans the exported
TypeScript tree and retains its decoder behavior checks. Three
repository-wide reader censuses remain in Logos CI because they inspect private
kernel and engine sources; they are not contract runtime dependencies.

The `contract` workflow runs formatting, Clippy, Rust tests and doctests, Go tests
including the race detector, Go vet, TypeScript typechecking and tests, and
package preparation on GitHub runners using public registries without private
credentials. The `release` workflow publishes existing immutable release tags
after that gate passes. No build or test runs on the maintainer's workstation.

Licensed under MIT OR Apache-2.0. See LICENSE-MIT and LICENSE-APACHE.
