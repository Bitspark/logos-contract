#!/usr/bin/env bash
set -euo pipefail

# This standalone gate must also work for an anonymous public consumer. Keep
# source credentials, private registries and local replacements out of it.
if [ "${GITHUB_ACTIONS:-}" != true ]; then
  echo "Run this gate on a GitHub runner." >&2
  exit 1
fi

# One check here executes a 32-bit x86 program: the selector consumer fixture
# under GOARCH=386. A host that cannot execute one runs everything else with
# --without-386, which still compiles that fixture for 386, and a host that can
# runs the fixture alone with --only-386. Between them the two runs are this
# gate. With no argument everything runs in one place.
mode=all
case "${1:-}" in
  '') ;;
  --without-386) mode=without-386 ;;
  --only-386) mode=only-386 ;;
  *)
    echo "usage: check.sh [--without-386 | --only-386]" >&2
    exit 2
    ;;
esac
if [ "$#" -gt 1 ]; then
  echo "usage: check.sh [--without-386 | --only-386]" >&2
  exit 2
fi

cd "$(dirname "$0")/.."
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_TERMINAL_PROMPT=0
export GOPROXY=https://proxy.golang.org,direct GOSUMDB=sum.golang.org
export GOPRIVATE='' GONOPROXY='' GONOSUMDB='' GOWORK=off
export NPM_CONFIG_USERCONFIG=/dev/null NPM_CONFIG_REGISTRY=https://registry.npmjs.org
unset GH_TOKEN GITHUB_TOKEN NODE_AUTH_TOKEN NPM_TOKEN CARGO_REGISTRY_TOKEN

if [ "$mode" = only-386 ]; then
  cd contract/go
  # This run exists for the fixture, so an export without it is an error here,
  # not a shorter test set.
  if [ ! -f wire_selectors_consumer_test.go ]; then
    echo "--only-386: contract/go/wire_selectors_consumer_test.go is not in this tree" >&2
    exit 1
  fi
  go mod download
  GOARCH=386 go test -count=1 wire_selectors_consumer_test.go
  exit 0
fi

cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --all-targets
cargo test --workspace --doc
cargo package -p logos-contract --allow-dirty

(
  cd contract/go
  unformatted=$(gofmt -l .)
  if [ -n "$unformatted" ]; then
    printf 'Go source requires formatting:\n%s\n' "$unformatted" >&2
    exit 1
  fi
  go mod download
  go list -m -json all > "$RUNNER_TEMP/public-contract-modules.json"
  python3 - "$RUNNER_TEMP/public-contract-modules.json" <<'PY'
import json, sys
text = open(sys.argv[1]).read()
decoder = json.JSONDecoder()
while text.strip():
    module, end = decoder.raw_decode(text.lstrip())
    if "Replace" in module:
        raise SystemExit(f"module replacement: {module['Path']}")
    if module['Path'].startswith('github.com/Bitspark/logos/'):
        raise SystemExit(f"private Logos dependency: {module['Path']}")
    text = text.lstrip()[end:]
PY
  go test -count=1 ./...
  go test -race -count=1 ./...
  go vet ./...
  # Selector coordinates retain the portable range on a real 32-bit host.
  # Compile only the external consumer fixture, importing the actual contract;
  # historical exports without this fixture keep their existing test set.
  if [ -f wire_selectors_consumer_test.go ]; then
    if [ "$mode" = without-386 ]; then
      # Compiled and linked for 386, not executed: the --only-386 run executes it.
      GOARCH=386 go test -c -o "$RUNNER_TEMP/wire-selectors-consumer-386.test" wire_selectors_consumer_test.go
    else
      GOARCH=386 go test -count=1 wire_selectors_consumer_test.go
    fi
  fi
)

(
  cd contract/ts
  if [ -f package-lock.json ]; then npm ci --ignore-scripts; else npm install --ignore-scripts; fi
  npm run typecheck
  npm test
  consumer_dir=$(mktemp -d "$RUNNER_TEMP/logos-contract-npm.XXXXXX")
  tarball=$(npm pack --silent --pack-destination "$consumer_dir")
  shopt -s nullglob
  fixtures=(consumer/*.mjs)
  type_fixtures=(consumer/*.mts)
  compiler="$PWD/node_modules/.bin/tsc"
  type_roots="$PWD/node_modules/@types"
  if (( ${#type_fixtures[@]} )); then
    cp "${type_fixtures[@]}" "$consumer_dir/"
  fi
  if (( ${#fixtures[@]} )); then
    cp "${fixtures[@]}" "$consumer_dir/"
  fi
  cd "$consumer_dir"
  echo '{"private":true}' > package.json
  npm install --ignore-scripts --no-audit --no-fund --no-package-lock "./$tarball"
  if (( ${#type_fixtures[@]} )); then
    "$compiler" --strict --noEmit --target ES2022 --module NodeNext --typeRoots "$type_roots" ./*.mts
  fi
  node --input-type=module -e 'import { check } from "@bitspark/logos-contract"; if (typeof check !== "function") throw new Error("missing public checker")'
  if (( ${#fixtures[@]} )); then
    node --test ./*.mjs
  fi
)
