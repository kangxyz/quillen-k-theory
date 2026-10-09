#!/usr/bin/env bash
# Fetch only the third-party cache needed by the library and checked client.
set -euo pipefail
cd "$(dirname "$0")/.."
modules=()
while IFS= read -r module; do
  modules+=("$module")
done < <(python3 - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'scripts')
from library_sources import downstream_sources, lean_imports, source_modules, test_modules

root = Path.cwd()
sources = {root / path for path in source_modules(root) | test_modules(root) | downstream_sources(root)}
modules = {name for path in sources for name in lean_imports(path.read_text())
           if name == 'Mathlib' or name.startswith('Mathlib.')}
if not modules:
    raise SystemExit('No mathlib imports found; refusing an unscoped cache download.')
print('\n'.join(sorted(modules)))
PY
)
if (( ${#modules[@]} == 0 )); then
  echo "No cache inputs were produced" >&2
  exit 1
fi
lake exe cache get "${modules[@]}"
