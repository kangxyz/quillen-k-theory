#!/usr/bin/env bash
# Check source structure, build library/tests, and replay both kernel trust checks.
set -euo pipefail
cd "$(dirname "$0")/.."
lake_args=()
if [[ "${1:-}" == --rehash ]]; then
  lake_args+=(--rehash)
  shift
elif [[ "${QUILLEN_REHASH:-0}" == 1 ]]; then
  lake_args+=(--rehash)
fi
if (( $# )); then
  echo "Usage: $0 [--rehash]" >&2
  exit 2
fi
python3 scripts/generate_imports.py --check
python3 scripts/check_library_layout.py
python3 scripts/check_placeholders.py
python3 -m unittest discover -s scripts -p 'test_*.py'
lake ${lake_args[@]+"${lake_args[@]}"} build Quillen QuillenTest
lake ${lake_args[@]+"${lake_args[@]}"} test
lake ${lake_args[@]+"${lake_args[@]}"} lint
lake ${lake_args[@]+"${lake_args[@]}"} exe lint-style
# Replay explicitly: cached olean files do not re-execute run_cmd trust tests.
lake env lean -j2 QuillenTest/Axioms.lean
consumer="$PWD/examples/downstream"
mkdir -p "$consumer/.lake"
# The client has its own package configuration, manifest and build outputs.
# Reuse the root package's pinned third-party dependencies without lake update.
if [[ ! -e "$consumer/.lake/packages" ]]; then
  ln -s "$PWD/.lake/packages" "$consumer/.lake/packages"
fi
(cd "$consumer" && lake ${lake_args[@]+"${lake_args[@]}"} build && lake env lean -j2 Audit.lean)
