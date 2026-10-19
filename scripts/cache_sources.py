#!/usr/bin/env python3
"""Collect Mathlib cache roots through the reachable pinned Aglib sources."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from library_sources import (
    downstream_sources, lean_imports, module_path, source_modules,
    test_modules, tool_sources,
)


def workspace_imports(root: Path, plan: dict | None = None) -> set[str]:
    if plan is not None:
        if not plan.get('lean'):
            raise ValueError('Static scope does not request dependency cache work')
        client = Path('examples/downstream')
        pending = ([module_path(name) for name in plan['providers'] + plan['tests']] +
                   [client / module_path(name) for name in plan['clients']] +
                   [Path('Tools/LintScoped.lean')])
        seen, imports = set(), set()
        while pending:
            path = pending.pop()
            if path in seen:
                continue
            seen.add(path)
            for name in lean_imports((root / path).read_text()):
                imports.add(name)
                local = module_path(name)
                if name.split('.')[0] == 'Consumer':
                    local = client / local
                if (root / local).is_file():
                    pending.append(local)
        return imports
    sources = (source_modules(root) | test_modules(root) |
               downstream_sources(root) | tool_sources(root))
    return {name for path in sources for name in lean_imports((root / path).read_text())}


def mathlib_cache_roots(root: Path, imports: set[str] | None = None) -> list[str]:
    """Follow only reachable Aglib modules; never send Aglib to Mathlib's cache."""
    imports = workspace_imports(root) if imports is None else imports
    modules = {name for name in imports if name == 'Mathlib' or name.startswith('Mathlib.')}
    pending = [name for name in imports if name == 'Aglib' or name.startswith('Aglib.')]
    visited = set()
    dependency = root / '.lake/packages/Aglib'
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        path = dependency / module_path(name)
        if not path.is_file():
            raise ValueError(f'Missing reachable pinned Aglib source: {path}')
        for imported in lean_imports(path.read_text()):
            if imported == 'Mathlib' or imported.startswith('Mathlib.'):
                modules.add(imported)
            elif imported == 'Aglib' or imported.startswith('Aglib.'):
                pending.append(imported)
    if not modules:
        raise ValueError('No mathlib imports found; refusing an unscoped cache download.')
    return sorted(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--resolve-deps', action='store_true')
    parser.add_argument('--plan', type=Path)
    args = parser.parse_args()
    try:
        # Invalid local source inputs fail before dependency resolution/download.
        plan = json.loads(args.plan.read_text()) if args.plan else None
        imports = workspace_imports(args.root, plan)
        if args.resolve_deps:
            subprocess.run(['lake', 'resolve-deps'], cwd=args.root, check=True,
                           stdout=sys.stderr)
        print('\n'.join(mathlib_cache_roots(args.root, imports)))
    except subprocess.CalledProcessError as error:
        return error.returncode
    except (OSError, ValueError) as error:
        print(f'Cache source collection failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
