#!/usr/bin/env bash
set -euo pipefail

# This standalone gate must also work for an anonymous public consumer. Keep
# source credentials, private registries and local replacements out of it.
if [ "${GITHUB_ACTIONS:-}" != true ]; then
  echo "Run this gate on a GitHub runner." >&2
  exit 1
fi
cd "$(dirname "$0")/.."
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_TERMINAL_PROMPT=0
export GOPROXY=https://proxy.golang.org,direct GOSUMDB=sum.golang.org
export GOPRIVATE='' GONOPROXY='' GONOSUMDB='' GOWORK=off
export NPM_CONFIG_USERCONFIG=/dev/null NPM_CONFIG_REGISTRY=https://registry.npmjs.org
unset GH_TOKEN GITHUB_TOKEN NODE_AUTH_TOKEN NPM_TOKEN CARGO_REGISTRY_TOKEN

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
)

(
  cd contract/ts
  if [ -f package-lock.json ]; then npm ci --ignore-scripts; else npm install --ignore-scripts; fi
  npm run typecheck
  npm test
  npm pack --dry-run
)
