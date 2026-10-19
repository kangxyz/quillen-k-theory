#!/usr/bin/env bash
# Fetch Mathlib artifacts needed by the workspace and reachable pinned Aglib sources.
set -euo pipefail
cd "$(dirname "$0")/.."
ci_mode=0
scope_args=()
while (( $# )); do
  case "$1" in
    --ci) ci_mode=1; shift ;;
    --plan)
      [[ $# -ge 2 ]] || { echo "--plan requires a path" >&2; exit 2; }
      scope_args=(--plan "$2"); shift 2 ;;
    *) echo "Usage: $0 [--ci] [--plan PATH]" >&2; exit 2 ;;
  esac
done
modules_text="$(python3 scripts/cache_sources.py --resolve-deps ${scope_args[@]+"${scope_args[@]}"})"
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
# Serialize cache-tool compilation while retaining the pinned guard and scoped roots.
python3 scripts/cache_ci.py "$(dirname "$guard")" "$cache_receipt" \
  "${modules[@]}" || cache_status=$?
if [[ -f "$cache_receipt" ]]; then
  cat "$cache_receipt"
fi
exit "$cache_status"
