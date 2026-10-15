#!/usr/bin/env bash
# Check source structure, build library/tests, and replay both kernel trust checks.
set -euo pipefail
cd "$(dirname "$0")/.."
lake_args=()
source_only=0
ci_mode=0
if [[ "${QUILLEN_REHASH:-0}" == 1 ]]; then
  lake_args+=(--rehash)
fi
for argument in "$@"; do
  case "$argument" in
    --source-only) source_only=1 ;;
    --ci) ci_mode=1 ;;
    --rehash) lake_args=(--rehash) ;;
    *) echo "Usage: $0 [--source-only] [--ci] [--rehash]" >&2; exit 2 ;;
  esac
done
python3 scripts/generate_imports.py --check
python3 scripts/check_library_layout.py
python3 scripts/check_placeholders.py
python3 -m unittest discover -s scripts -p 'test_*.py'
if (( source_only )); then
  exit 0
fi
project_root="$PWD"
aglib_scripts="$project_root/.lake/packages/Aglib/scripts"
verification_dir="${QUILLEN_VERIFY_DIR:-$PWD/.lake/verification/$(date +%Y%m%d-%H%M%S)-$$}"
if [[ "$verification_dir" != /* ]]; then
  verification_dir="$PWD/$verification_dir"
fi
if (( ci_mode )); then
  if [[ ! -f "$aglib_scripts/build_serial.py" || ! -f "$aglib_scripts/resource_guard.py" ]]; then
    echo "Resolve the pinned Aglib dependency before guarded CI checks." >&2
    exit 2
  fi
  if [[ -e "$verification_dir" ]]; then
    echo "Use a fresh QUILLEN_VERIFY_DIR for each check invocation." >&2
    exit 2
  fi
  mkdir -p "$verification_dir"
  export LEAN_NUM_THREADS=1
  export AGLIB_BUILD_THREADS="${AGLIB_BUILD_THREADS:-2}"
fi
safe() {
  local phase="$1"
  shift
  if (( ! ci_mode )); then
    "$@"
    return
  fi
  # Aglib owns the policy and compiler wrapper; Quillen only supplies commands.
  python3 - "$aglib_scripts" "$verification_dir/$phase.json" "$@" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, sys.argv[1])
from build_serial import build_threads, capped_toolchain
from resource_guard import limits, run

budget = limits()
budget['native_build_threads'] = build_threads()
with capped_toolchain(Path.cwd(), threads=budget['native_build_threads']) as environment:
    raise SystemExit(run(sys.argv[3:], env=environment, receipt=Path(sys.argv[2]), budget=budget))
PY
}
if (( ci_mode )); then
  python3 "$aglib_scripts/build_serial.py" --root "$PWD" \
    --receipt-dir "$verification_dir/build" ${lake_args[@]+"${lake_args[@]}"} Quillen QuillenTest
else
  lake ${lake_args[@]+"${lake_args[@]}"} build Quillen QuillenTest
fi
safe test lake ${lake_args[@]+"${lake_args[@]}"} test
safe declaration-lint lake ${lake_args[@]+"${lake_args[@]}"} lint
safe style lake ${lake_args[@]+"${lake_args[@]}"} exe lint-style
# Replay explicitly: cached olean files do not re-execute run_cmd trust tests.
safe axioms lake env lean -j2 QuillenTest/Axioms.lean
consumer="$PWD/examples/downstream"
mkdir -p "$consumer/.lake"
# The client has its own package configuration, manifest and build outputs.
# Reuse the root package's pinned third-party dependencies without lake update.
if [[ ! -e "$consumer/.lake/packages" ]]; then
  ln -s "$PWD/.lake/packages" "$consumer/.lake/packages"
fi
(
  cd "$consumer"
  if (( ci_mode )); then
    python3 "$aglib_scripts/build_serial.py" --root "$PWD" \
      --receipt-dir "$verification_dir/client-build" ${lake_args[@]+"${lake_args[@]}"} Consumer
  else
    lake ${lake_args[@]+"${lake_args[@]}"} build
  fi
  safe client-audit lake env lean -j2 Audit.lean
)
