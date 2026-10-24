#!/usr/bin/env bash
# Compatibility entry: cache policy and guarding live in the selected toolkit.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 -c 'from scripts.check_run import main; raise SystemExit(main(action=("cache",)))' "$@"
