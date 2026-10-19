#!/usr/bin/env python3
"""Select changed Lean modules and actual reverse-import consumers without Lake."""
import argparse
import io
import json
from pathlib import Path
import subprocess
import sys

from library_sources import is_import_surface, lean_imports, module_name

CLIENT = 'examples/downstream/'
AUDITS = {'QuillenTest/Axioms.lean', CLIENT + 'Audit.lean'}
GLOBAL_INPUTS = {'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean',
                 CLIENT + 'lean-toolchain', CLIENT + 'lake-manifest.json',
                 CLIENT + 'lakefile.toml', CLIENT + 'lakefile.lean', 'scripts/nolints.json'}
TOOL_TESTS = {
    'check.sh': ['test_check_script'],
    'check_run.py': ['test_check_script', 'test_cache_sources'],
    'check_scope.py': ['test_check_script'],
    'cache.sh': ['test_check_script', 'test_cache_ci', 'test_cache_sources'],
    'cache_ci.py': ['test_cache_ci', 'test_cache_sources'],
    'cache_sources.py': ['test_cache_sources', 'test_cache_ci', 'test_check_script'],
    'cache_key.py': ['test_cache_key'],
    'check_receipts.py': ['test_check_receipts'],
    'generate_imports.py': ['test_import_generation', 'test_library_layout'],
    'check_library_layout.py': ['test_library_layout'],
    'check_placeholders.py': ['test_placeholders'],
    'library_sources.py': ['test_import_generation', 'test_library_layout', 'test_placeholders',
                           'test_cache_sources', 'test_cache_ci', 'test_check_script'],
}


def tooling_tests(root, paths, full=False):
    selected = set()
    for path in paths:
        if path.endswith('.md'):
            continue
        if path.startswith('scripts/test_') and path.endswith('.py'):
            if not (root / path).is_file():
                raise ValueError(f'Deleted regression {path} needs an explicit replacement fixture')
            selected.add(Path(path).stem)
        elif path.startswith('scripts/'):
            if path == 'scripts/nolints.json':
                continue  # Its global input assessment is handled separately.
            if Path(path).name not in TOOL_TESTS or Path(path).parent != Path('scripts'):
                raise ValueError(f'Unclassified tooling path: {path}; assign its regression selection')
            selected.update(TOOL_TESTS[Path(path).name])
        elif path == '.github/workflows/ci.yml':
            selected.add('test_check_script')
        elif path.startswith('.github/'):
            raise ValueError(f'Unclassified tooling path: {path}; assign its regression selection')
    if full:
        selected.update(path.stem for path in (root / 'scripts').glob('test_*.py'))
    return sorted(selected)


def git(root, *arguments):
    result = subprocess.run(['git', *arguments], cwd=root, capture_output=True, text=True)
    if result.returncode:
        raise ValueError(f'Git input unavailable ({" ".join(arguments)}): {result.stderr.strip()}')
    return result.stdout


def identity(path):
    if path.startswith(CLIENT):
        return 'client:' + module_name(path[len(CLIENT):])
    return module_name(path)


def snapshot(root, revision=None):
    paths = git(root, 'ls-tree', '-r', '--name-only', revision) if revision else git(
        root, 'ls-files', '--cached', '--others', '--exclude-standard')
    lean_paths = [path for path in paths.splitlines() if path.endswith('.lean') and
                  '.lake' not in Path(path).parts]
    contents = None
    if revision:
        # Read only Lean blobs in one batch; documentation evidence can be large.
        process = subprocess.run(['git', 'cat-file', '--batch'], cwd=root, capture_output=True,
                                 input=''.join(f'{revision}:{path}\n' for path in lean_paths).encode())
        if process.returncode:
            raise ValueError(f'Git source snapshot unavailable: {revision}')
        contents = io.BytesIO(process.stdout)
    result = {}
    for path in lean_paths:
        if not (path.startswith(('Quillen/', 'QuillenTest/', 'Tools/', CLIENT)) or
                path in {'Quillen.lean', 'QuillenTest.lean'}):
            raise ValueError(f'Unclassified Lean source: {path}; assign an explicit scope')
        if revision:
            header = contents.readline().decode().split()
            if len(header) != 3 or header[1] != 'blob':
                raise ValueError(f'Invalid Git source object: {revision}:{path}')
            text = contents.read(int(header[2])).decode('utf-8')
            if contents.read(1) != b'\n':
                raise ValueError(f'Truncated Git source object: {path}')
        elif (root / path).is_file():
            text = (root / path).read_text()
        else:
            continue
        result[path] = text
    return result


def provider_batches(providers, current):
    """Lint each topological provider layer before compiling affected dependents."""
    imports = {module_name(path): lean_imports(text) for path, text in current.items()
               if path.startswith('Quillen/') or path == 'Quillen.lean'}
    selected = set(providers)
    dependencies = {}
    for module in providers:
        seen, pending = set(), list(imports.get(module, []))
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(imports.get(name, []))
        dependencies[module] = seen & selected
    batches = []
    while dependencies:
        ready = sorted(name for name, inputs in dependencies.items() if not inputs)
        if not ready:
            raise ValueError('Cycle in affected provider graph')
        batches.append(ready)
        dependencies = {name: inputs - set(ready) for name, inputs in dependencies.items()
                        if name not in ready}
    return batches


def select(root, base=None, head=None, full=False):
    revision = git(root, 'rev-parse', '--verify', head or 'HEAD').strip()
    initial = base == 'EMPTY_TREE'
    if full and base:
        raise ValueError('--full and --base are mutually exclusive')
    if initial:
        if len(git(root, 'rev-list', '--parents', '-n1', revision).split()) != 1:
            raise ValueError('EMPTY_TREE is only valid for a true initial commit')
        paths = git(root, 'ls-tree', '-r', '--name-only', revision).splitlines()
    elif base:
        git(root, 'rev-parse', '--verify', f'{base}^{{commit}}')
        paths = git(root, 'diff', '--name-only', '--no-renames', base,
                    *([head] if head else [])).splitlines()
    else:
        paths = git(root, 'diff', '--name-only', '--no-renames', 'HEAD',
                    *([head] if head else [])).splitlines()
    paths += git(root, 'ls-files', '--others', '--exclude-standard').splitlines() if not head else []
    paths = sorted(set(paths))
    for path in paths:
        if path in GLOBAL_INPUTS:
            if not full and not initial:
                raise ValueError(f'{path} changes global validation inputs; assess invalidation and '
                                 'supply an explicit diagnostic --full only if intended')
        elif not (path.endswith('.lean') or path.endswith('.md') or
                  path.startswith(('docs/', 'scripts/', '.github/')) or
                  path in {'LICENSE', '.gitignore', 'AGENTS.md'}):
            raise ValueError(f'Unclassified changed path: {path}; assign an explicit scope')
    regressions = tooling_tests(root, paths, full)
    if not full and not any(path.endswith('.lean') for path in paths):
        return dict(schema=1, revision=revision, base=base, head=head, full=False,
                    changed=paths, tooling_tests=regressions,
                    providers=[], tests=[], clients=[], provider_batches=[],
                    trust=False, client_trust=False, lean=False)
    # A missing or shallow base is an error, never a request for whole-library work.
    old = {} if initial else snapshot(root, base or revision)
    current = snapshot(root, head)
    changed = {path for path in old.keys() | current.keys() if old.get(path) != current.get(path)}
    if any(path.startswith('Tools/') for path in changed) and not full and not initial:
        raise ValueError('Lean checker changes need an explicit validation scope (--full diagnostics)')
    reverse = {}
    for sources in (old, current):
        for path, text in sources.items():
            if path in AUDITS:
                continue  # Their imports are replaced by the selected trust closure at replay.
            for dependency in lean_imports(text):
                key = 'client:' + dependency if dependency.split('.')[0] == 'Consumer' else dependency
                reverse.setdefault(key, set()).add(identity(path))
    affected = {identity(path) for path in changed}
    pending = list(affected)
    while pending:
        for consumer in reverse.get(pending.pop(), ()):
            if consumer not in affected:
                affected.add(consumer)
                pending.append(consumer)
    selected = set(current) if full else {path for path in current if identity(path) in affected}
    # Generated import-only roots enroll sources statically; do not use them as
    # blanket build targets. A real consumer importing a facade retains that import.
    selected = {path for path in selected if path not in AUDITS and
                not path.startswith('Tools/') and
                (full or path in changed or not is_import_surface(current[path]))}
    providers = sorted(module_name(path) for path in selected if
                       path.startswith('Quillen/') or path == 'Quillen.lean')
    tests = sorted(module_name(path) for path in selected if
                   path.startswith('QuillenTest/') or path == 'QuillenTest.lean')
    clients = sorted(module_name(path[len(CLIENT):]) for path in selected if path.startswith(CLIENT))
    trust = bool(providers or 'QuillenTest/Axioms.lean' in changed or full)
    client_trust = bool(clients or CLIENT + 'Audit.lean' in changed or full)
    # An audit-template-only edit replays its existing coverage explicitly.
    if trust and not providers:
        providers = sorted(module_name(path) for path in current if path.startswith('Quillen/')
                           and not is_import_surface(current[path]))
    if client_trust and not clients:
        clients = sorted(module_name(path[len(CLIENT):]) for path in current if
                         path.startswith(CLIENT + 'Consumer/') and not is_import_surface(current[path]))
    return dict(schema=1, revision=revision, base=base, head=head, full=full,
                changed=sorted(set(paths) | changed), tooling_tests=regressions,
                providers=providers, tests=tests, clients=clients,
                provider_batches=provider_batches(providers, current),
                trust=trust, client_trust=client_trust,
                lean=bool(providers or tests or clients))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--base')
    parser.add_argument('--head')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--github-output', type=Path)
    args = parser.parse_args()
    try:
        plan = select(args.root, args.base, args.head, args.full)
        data = json.dumps(plan, indent=2) + '\n'
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(data)
        else:
            print(data, end='')
        if args.github_output:
            with args.github_output.open('a') as output:
                output.write(f'lean={str(plan["lean"]).lower()}\n')
    except (OSError, ValueError) as error:
        print(f'Check scope error: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
