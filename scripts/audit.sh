#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
./scripts/check_library.sh "$@"
lake env lean -j2 audits/CentralDeclarationsAudit.lean
lake env lean -j2 audits/LibraryAudit.lean
