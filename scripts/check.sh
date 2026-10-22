#!/usr/bin/env bash
# Native final checks; Lake reuses valid compilation and command evidence.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check_run.py "$@"
