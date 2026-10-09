#!/usr/bin/env python3
"""Check current library enrollment, canonical layout and import boundaries."""
import argparse
import json
from pathlib import Path
import sys

from generate_imports import family_facades, generated_files, stale_files
from library_sources import lean_imports, module_name, module_path, source_modules

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = {'audit', 'audits', 'consumer', 'test', 'tests', 'quillentest'}


def import_cycles(graph: dict[str, set[str]]) -> list[str]:
    """Iterative DFS avoids Python recursion limits for long source chains."""
    state = {}
    cycles = []
    for entry in sorted(graph):
        if state.get(entry):
            continue
        state[entry] = 1
        stack = [(entry, iter(sorted(graph[entry])))]
        while stack:
            module, children = stack[-1]
            child = next(children, None)
            if child is None:
                state[module] = 2
                stack.pop()
            elif state.get(child) == 1:
                cycles.append(f'{module} -> {child}')
            elif child in graph and not state.get(child):
                state[child] = 1
                stack.append((child, iter(sorted(graph[child]))))
    return cycles


def check_layout(root: Path) -> tuple[list[str], int]:
    errors = []
    modules = source_modules(root)
    loose = {path.name for path in root.glob('*.lean')} - {'Quillen.lean'}
    if loose:
        errors.append(f'Unclassified project-root Lean files: {sorted(loose)}')
    # Historical migration data is only an obsolete-name lookup, never a proof
    # fingerprint, required-target list or immutable source inventory.
    manifest_path = root / 'docs/module-migration.json'
    manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
    old_paths = {entry['old'] for key in ('modules', 'additional_moves',
                 'removed_aliases', 'audit_moves', 'exploratory_moves')
                 for entry in manifest.get(key, []) if entry['old'] != entry.get('new')}
    old_paths.add('Quillen/Compatibility.lean')
    # Current family surfaces can deliberately reuse an old flat name. Existing
    # manual facades retain their ownership; generated facades are checked below.
    current_facades = {path for path in family_facades(root) if (root / path).is_file()}
    old_paths -= {path.as_posix() for path in current_facades | set(generated_files(root))}
    obsolete = {module_name(path) for path in old_paths if path.startswith('Quillen/')}
    for path in sorted(old_paths):
        if (root / path).exists():
            errors.append(f'Obsolete module still present: {path}')
    stale = stale_files(root)
    if stale:
        errors.append(f'Stale generated imports (missing enrollment or changed facade): {stale}; '
                      'run python3 scripts/generate_imports.py')
    graph = {}
    paths = {root / path for path in modules}
    for folder in ('audits', 'examples'):
        paths.update(path for path in (root / folder).rglob('*.lean')
                     if '.lake' not in path.relative_to(root).parts)
    local_roots = {'Quillen'} | {path.stem for path in root.glob('*.lean')}
    local_roots.update(path.name for path in root.iterdir()
                       if path.is_dir() and not path.name.startswith('.')
                       and any(path.glob('*.lean')))
    for path in sorted(paths):
        relative = path.relative_to(root)
        if not path.is_file():
            errors.append(f'Missing project import source: {relative}')
            continue
        imports = set(lean_imports(path.read_text()))
        old = imports & obsolete
        if old:
            errors.append(f'Obsolete imports in {relative}: {sorted(old)}')
        library = relative in modules
        for imported in sorted(imports):
            parts = imported.split('.')
            forbidden = any(part.strip('«»').casefold() in FORBIDDEN for part in parts)
            if library and forbidden:
                errors.append(f'Forbidden library import in {relative}: {imported}')
            if parts[0] in local_roots and not (root / module_path(imported)).is_file():
                errors.append(f'Unresolved local import in {relative}: {imported}')
            if library and len(relative.parts) > 2 and (
                    imported == 'Quillen' or (parts[0] == 'Quillen' and len(parts) == 2)):
                errors.append(f'Implementation imports broad facade in {relative}: {imported}')
        if library:
            graph[module_name(relative)] = {name for name in imports
                if name == 'Quillen' or name.startswith('Quillen.')}
    errors.extend('Project import cycle: ' + cycle for cycle in import_cycles(graph))
    return errors, len(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        errors, count = check_layout(args.root)
    except (OSError, ValueError, KeyError) as error:
        print(f'Layout check failed: {error}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Canonical layout checked: {count} source modules; exhaustive generated imports; '
          'no forbidden, obsolete or unresolved local imports or cycles.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
