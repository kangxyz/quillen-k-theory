#!/usr/bin/env bash
# Compile canonical integration/public entrypoints and an independent consumer.
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
python3 scripts/check_library_layout.py
python3 scripts/check_placeholders.py
lake "${lake_args[@]}" build Quillen Quillen.Library Quillen.Scheme Quillen.Resolution
consumer="$PWD/examples/downstream"
mkdir -p "$consumer/.lake"
# Reuse only pinned third-party dependency caches. The consumer has its own
# package configuration, manifest, build products and public-import source files.
if [[ ! -e "$consumer/.lake/packages" ]]; then
  ln -s "$PWD/.lake/packages" "$consumer/.lake/packages"
fi
(cd "$consumer" && lake "${lake_args[@]}" build && lake env lean -j2 Audit.lean)
