#!/usr/bin/env bash
# Normal affected-scope validation; --full is explicit comprehensive diagnostics.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_run.py "$@"
