"""Recompute a narrowly assessed Aglib pin transition from exact Git source objects.

No network, Lake, checkout mutation, or trust in caller-supplied target lists.
Source graphs describe Git objects. The runtime checkout has a separate verifier;
unrelated documented helper overlays do not change mathematical source identity.
"""
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

from library_sources import lean_imports, module_name

PIN_PATHS = {'lakefile.toml', 'lake-manifest.json', 'examples/downstream/lake-manifest.json'}
RUNTIME_CONFIG = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
COMMIT = re.compile(r'[0-9a-f]{40}')


def git(root, *args):
    environment = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    result = subprocess.run(['git', '-C', str(root), *args], capture_output=True, env=environment)
    if result.returncode:
        raise ValueError('Aglib source Git input unavailable: ' + ' '.join(args))
    return result.stdout


def repository(path):
    path = Path(path).absolute()
    if any(p.is_symlink() for p in (path, *path.parents)):
        raise ValueError('Aglib source repository path must not traverse a symlink')
    if not path.is_dir() or git(path, 'rev-parse', '--is-inside-work-tree').strip() != b'true':
        raise ValueError('Aglib source must be an explicit non-bare Git worktree root')
    if Path(git(path, 'rev-parse', '--show-toplevel').decode().strip()).resolve() != path.resolve():
        raise ValueError('Aglib source path is not its Git repository root')
    return path


def object_commit(source, revision):
    if not isinstance(revision, str) or not COMMIT.fullmatch(revision):
        raise ValueError('Aglib pins must be exact full lowercase commit identities')
    if git(source, 'rev-parse', '--verify', revision + '^{commit}').decode().strip() != revision:
        raise ValueError('Aglib source object is not the pinned commit')


def snapshot(source, revision):
    object_commit(source, revision)
    names = git(source, 'ls-tree', '-rz', '--full-tree', revision).split(b'\0')
    entries = []
    for entry in filter(None, names):
        header, path = entry.split(b'\t', 1)
        path = path.decode(); mode, kind, oid = header.decode().split()
        if not ((path == 'Aglib.lean' or path.startswith('Aglib/')) and path.endswith('.lean')):
            continue
        if mode != '100644' or kind != 'blob':
            raise ValueError('Aglib production source must be a regular Git blob: ' + path)
        entries.append((path, oid))
    if not entries: raise ValueError('No Aglib production sources at pinned commit')
    # A single explicit batch avoids one Git process per production module.
    process = subprocess.run(['git', '-C', str(source), 'cat-file', '--batch'],
                             input=''.join(oid + '\n' for _, oid in entries).encode(),
                             capture_output=True,
                             env={k:v for k,v in os.environ.items() if not k.startswith('GIT_')})
    if process.returncode: raise ValueError('Aglib source batch unavailable')
    stream = io.BytesIO(process.stdout); result = {}
    for path, oid in entries:
        fields = stream.readline().decode().split()
        if len(fields) != 3 or fields[:2] != [oid, 'blob']:
            raise ValueError('Invalid Aglib source blob batch')
        content = stream.read(int(fields[2]))
        if stream.read(1) != b'\n': raise ValueError('Truncated Aglib source batch')
        result[path] = content
    return result


def _source_input(root, revision, path):
    if revision is not None:
        exists = subprocess.run(['git', 'cat-file', '-e', f'{revision}:{path}'], cwd=root,
                                capture_output=True)
        return git(root, 'show', f'{revision}:{path}') if exists.returncode == 0 else None
    target = root / path
    if target.is_symlink(): raise ValueError('Redirected validation configuration: ' + path)
    return target.read_bytes() if target.is_file() else None


def _pin(config, manifest=False):
    if config is None: raise ValueError('Missing Aglib pin owner')
    parsed = json.loads(config) if manifest else tomllib.loads(config.decode())
    entries = parsed.get('packages' if manifest else 'require', [])
    entries = [entry for entry in entries if entry.get('name') == 'Aglib']
    if len(entries) != 1: raise ValueError('Expected exactly one Aglib requirement')
    pin = entries[0].get('rev')
    if not isinstance(pin, str) or not COMMIT.fullmatch(pin):
        raise ValueError('Aglib pin is not an exact commit')
    if manifest and entries[0].get('inputRev') != pin:
        raise ValueError('Aglib rev/inputRev disagree')
    return pin


def assess(root, before, after, global_inputs, source):
    """Validate the sole supported global delta and return verified graph roots."""
    source = repository(source)
    old_inputs = {p: _source_input(root, before, p) for p in sorted(global_inputs)}
    new_inputs = {p: _source_input(root, after, p) for p in sorted(global_inputs)}
    changed = {p for p in global_inputs if old_inputs[p] != new_inputs[p]}
    if changed != PIN_PATHS:
        raise ValueError('Assessed Aglib upgrade requires only all three exact pin-owner changes')
    old = _pin(old_inputs['lakefile.toml']); new = _pin(new_inputs['lakefile.toml'])
    if old == new: raise ValueError('Aglib assessment requires a real pin transition')
    for path in sorted(PIN_PATHS):
        manifest = path.endswith('.json')
        if _pin(old_inputs[path], manifest) != old or _pin(new_inputs[path], manifest) != new:
            raise ValueError('Root/downstream Aglib pins disagree')
        count = 2 if manifest else 1
        if old_inputs[path].count(old.encode()) != count or old_inputs[path].replace(old.encode(), new.encode()) != new_inputs[path]:
            raise ValueError('Global change exceeds exact Aglib rev/inputRev substitution: ' + path)
    snapshots = {rev: snapshot(source, rev) for rev in (old, new)}
    # Stable runtime/config prerequisites are part of this narrow supported case.
    for path in sorted(RUNTIME_CONFIG | {'scripts/build_serial.py', 'scripts/resource_guard.py'}):
        if git(source, 'rev-parse', f'{old}:{path}') != git(source, 'rev-parse', f'{new}:{path}'):
            raise ValueError('Aglib runtime/config changed; needs separate assessment: ' + path)
    previous, current = snapshots[old], snapshots[new]
    paths = {p for p in previous.keys() | current.keys() if previous.get(p) != current.get(p)}
    roots = sorted(module_name(p) for p in paths)
    graph = {}
    for contents in snapshots.values():
        for path, content in contents.items():
            graph.setdefault(module_name(path), set()).update(lean_imports(content.decode()))
    graph_identity = hashlib.sha256(json.dumps({k: sorted(v) for k,v in sorted(graph.items())},
                                              sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    descriptor = {'kind': 'exact-aglib-pin-v1', 'old': old, 'new': new,
                  'old_tree': git(source, 'rev-parse', old + '^{tree}').decode().strip(),
                  'new_tree': git(source, 'rev-parse', new + '^{tree}').decode().strip(),
                  'union_graph_sha256': graph_identity, 'changed_production_modules': roots,
                  'global_input_sha256': {p: hashlib.sha256(v).hexdigest() if v is not None else None
                                          for p,v in sorted(new_inputs.items())},
                  'basis': 'exact-git-objects; runtime mathematical sources checked separately'}
    return roots, graph, descriptor


def verify_runtime(source, revision):
    """Check actual production Lean/config against pinned objects; helpers have their own guards."""
    # Prepared dependency containers may be links to an owned artifact directory.
    # Resolve that container only; the package root and all mathematical paths
    # remain regular files/directories under the explicit resolved Git root.
    source = Path(source).absolute()
    source = repository(source.parent.resolve() / source.name)
    if git(source, 'rev-parse', 'HEAD').decode().strip() != revision:
        raise ValueError('Runtime Aglib checkout is not at the assessed pin')
    expected = snapshot(source, revision)
    for path in RUNTIME_CONFIG:
        expected[path] = git(source, 'show', f'{revision}:{path}')
    actual = {p.relative_to(source).as_posix() for p in (source / 'Aglib').rglob('*.lean')}
    if (source / 'Aglib.lean').exists(): actual.add('Aglib.lean')
    if actual != set(expected) - RUNTIME_CONFIG:
        raise ValueError('Runtime Aglib mathematical source set drift')
    for path, content in expected.items():
        target = source / path
        if any(p.is_symlink() for p in (target, *target.parents)) or not target.is_file() or target.read_bytes() != content:
            raise ValueError('Runtime Aglib mathematical/config drift: ' + path)
    return {'resolved_dependency_root': str(source), 'revision': revision,
            'mathematical_and_config_files': len(expected)}
