#!/usr/bin/env bash
# Fetch Mathlib artifacts needed by the workspace and reachable pinned Aglib sources.
set -euo pipefail
cd "$(dirname "$0")/.."
ci_mode=0
if [[ "${1:-}" == --ci ]]; then
  ci_mode=1
  shift
fi
if (( $# )); then
  echo "Usage: $0 [--ci]" >&2
  exit 2
fi
modules_text="$(python3 scripts/cache_sources.py --resolve-deps)"
modules=()
while IFS= read -r module; do
  [[ -n "$module" ]] && modules+=("$module")
done <<< "$modules_text"
if (( ${#modules[@]} == 0 )); then
  echo "No cache inputs were produced" >&2
  exit 1
fi
if (( ! ci_mode )); then
  lake exe cache get "${modules[@]}"
  exit
fi
# Dependency resolution above is the no-proof bootstrap that makes this helper available.
guard="$PWD/.lake/packages/Aglib/scripts/resource_guard.py"
if [[ ! -f "$guard" ]]; then
  echo "The resolved pinned Aglib resource guard is missing." >&2
  exit 2
fi
cache_receipt="${QUILLEN_VERIFY_DIR:-$PWD/.lake/verification/cache-$(date +%Y%m%d-%H%M%S)-$$}-cache.json"
if [[ -e "$cache_receipt" ]]; then
  echo "Use a fresh QUILLEN_VERIFY_DIR for each cache/check invocation." >&2
  exit 2
fi
cache_status=0
# Scoped arguments do not use Aglib's unscoped --bootstrap-cache exception.
python3 "$guard" --capped-toolchain --receipt "$cache_receipt" -- \
  lake exe cache get "${modules[@]}" || cache_status=$?
if [[ -f "$cache_receipt" ]]; then
  cat "$cache_receipt"
fi
exit "$cache_status"
