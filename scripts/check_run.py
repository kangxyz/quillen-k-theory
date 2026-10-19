#!/usr/bin/env python3
"""Execute a selected check plan, retaining compatible Lake outputs."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from check_scope import GLOBAL_INPUTS, git, select


def execute(root, plan, *, ci=False, rehash=False, output=None):
    if not plan['lean']:
        print('Static scope: no Lean, dependency cache, or native cache work selected.')
        return
    aglib = root / '.lake/packages/Aglib/scripts'
    if ci and not all((aglib / name).is_file() for name in ('build_serial.py', 'resource_guard.py')):
        raise ValueError('Resolve the pinned Aglib dependency before guarded CI checks')
    requested = os.environ.get('QUILLEN_VERIFY_DIR')
    if requested:
        directory = Path(requested)
        if not directory.is_absolute():
            directory = root / directory
        if directory.exists():
            raise ValueError('Use a fresh QUILLEN_VERIFY_DIR for each check invocation')
        directory.mkdir(parents=True, exist_ok=False)
    else:
        (root / '.lake/verification').mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix='checks-', dir=root / '.lake/verification'))
    (directory / 'scope.json').write_text(json.dumps(plan, indent=2) + '\n')
    lake = ['lake'] + (['--rehash'] if rehash else [])
    if ci:
        sys.path.insert(0, str(aglib))
        from build_serial import build_threads, capped_toolchain
        from resource_guard import limits, run

    def safe(phase, command, cwd=root):
        print(f'{phase}: {" ".join(command)}', flush=True)
        if not ci:
            subprocess.run(command, cwd=cwd, check=True)
            return
        budget = limits()
        budget['native_build_threads'] = build_threads()
        with capped_toolchain(cwd, threads=budget['native_build_threads']) as environment:
            command = list(command)
            if command[:3] == ['lake', 'env', 'lean']:
                command[2] = environment['LEAN']
            code = run(command, cwd=cwd, env=environment,
                       receipt=directory / f'{phase}.json', budget=budget)
            if code:
                raise subprocess.CalledProcessError(code, command)

    mappings = []
    lint_runtime_ready = False
    lint_runner = directory / 'LintScoped.lean'
    lint_text = (root / 'Tools/LintScoped.lean').read_text()
    nonempty_guard = ('    if decls.isEmpty then\n'
                      '      throwError "Selected modules define no declarations; specify defining leaf modules"\n')
    if lint_text.count(nonempty_guard) != 1:
        raise ValueError('Scoped linter interface changed; review empty-facade adaptation')
    # Import-only facades have vacuous declaration checks but still need every
    # native text check. Keep the maintained linter's checks and exclusions.
    lint_runner.write_text(lint_text.replace(nonempty_guard, ''))

    def build(phase, modules, cwd=root):
        if not modules:
            return
        if ci:
            mapping = directory / f'{phase}-outputs.jsonl'
            command = [sys.executable, str(aglib / 'build_serial.py'), '--root', str(cwd),
                       '--receipt-dir', str(directory / phase), '--outputs', str(mapping)]
            if rehash:
                command.append('--rehash')
            subprocess.run([*command, *modules], cwd=cwd, check=True)
            mappings.append(mapping)
        else:
            safe(phase, [*lake, 'build', *modules], cwd)

    def lint(phase, modules, cwd=root):
        nonlocal lint_runtime_ready
        if modules:
            if not lint_runtime_ready:
                # These are the runner's exact pinned imports, not project roots.
                # Lake reuses compatible outputs; a cold runner builds only this
                # named tooling dependency closure under the same resource guard.
                safe('lint-runtime', [*lake, 'build', 'Batteries.Tactic.Lint',
                                      'Mathlib.Tactic.Linter.TextBased'])
                lint_runtime_ready = True
            safe(phase, ['lake', 'env', 'lean', '--run', str(lint_runner),
                         *modules], cwd)

    def prepare_audit(phase, template, import_name, modules):
        if not modules:
            return
        text = (root / template).read_text()
        marker = f'import {import_name}\n'
        if text.count(marker) != 1:
            raise ValueError(f'Cannot scope changed audit template: {template}')
        scoped = directory / f'{phase}.lean'
        scoped.write_text(text.replace(marker, ''.join(f'import {module}\n' for module in modules)))
        return scoped

    def audit(phase, template, import_name, modules, cwd=root):
        scoped = prepare_audit(phase, template, import_name, modules)
        if scoped is not None:
            safe(phase, ['lake', 'env', 'lean', '-j2', str(scoped)], cwd)

    for index, modules in enumerate(plan['provider_batches']):
        build(f'providers-{index}', modules)
        lint(f'provider-lint-{index}', modules)
    if plan['full'] or plan['base'] == 'EMPTY_TREE':
        safe('full-native-style', [*lake, 'exe', 'lint-style'])
    if plan['trust']:
        audit('axioms', 'QuillenTest/Axioms.lean', 'Quillen', plan['providers'])
    build('tests', plan['tests'])
    lint('test-lint', plan['tests'])
    # QuillenTest is a lean_lib test driver, with compile-time assertions and no
    # runtime main. A successful selected build (or compatible cached artifact)
    # supplies this coverage. Only explicit comprehensive diagnostics replay it.
    if plan['full']:
        for index, module in enumerate(plan['tests']):
            safe(f'test-{index}', ['lake', 'env', 'lean', '-j2', module.replace('.', '/') + '.lean'])
    if plan['clients']:
        client = root / 'examples/downstream'
        (client / '.lake').mkdir(exist_ok=True)
        packages = client / '.lake/packages'
        if not packages.exists():
            packages.symlink_to(root / '.lake/packages', target_is_directory=True)
        # Keep the documented repair inputs available even if build or lint
        # fails. Preparing this source does not execute or discharge the audit.
        client_audit = (prepare_audit('client-audit', 'examples/downstream/Audit.lean',
                                      'Consumer', plan['clients'])
                        if plan['client_trust'] else None)
        build('client-build', plan['clients'], client)
        lint('client-lint', plan['clients'], client)
        if client_audit is not None:
            safe('client-audit', ['lake', 'env', 'lean', '-j2', str(client_audit)], client)
    # Export only successful, verified selected build mappings. No second build
    # and no aggregate roots are introduced at the publication boundary.
    if output:
        if not ci:
            raise ValueError('--native-outputs requires --ci')
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(''.join(path.read_text() for path in mappings))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--source-checked', action='store_true',
                        help='reuse successful source checks for the same unchanged inputs')
    parser.add_argument('--ci', action='store_true')
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('--base')
    parser.add_argument('--head')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--native-outputs', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        if args.plan:
            if args.base or args.head or args.full:
                raise ValueError('--plan cannot be combined with --base/--head/--full')
            plan = json.loads(args.plan.read_text())
            if plan['head']:
                modified = git(root, 'diff', '--name-only', plan['revision']).splitlines()
                untracked = git(root, 'ls-files', '--others', '--exclude-standard', '--',
                                'Quillen', 'QuillenTest', 'Tools', 'examples/downstream',
                                *sorted(GLOBAL_INPUTS)).splitlines()
                if git(root, 'rev-parse', 'HEAD').strip() != plan['revision'] or any(
                        path.endswith('.lean') or path in GLOBAL_INPUTS
                        for path in modified + untracked):
                    raise ValueError('Checked-out Lean/check configuration differs from the selected head')
            if plan != select(root, plan['base'], plan['head'], plan['full']):
                raise ValueError('Selected scope is stale; regenerate the plan for these inputs')
        else:
            plan = select(root, args.base, args.head, args.full)
        if not args.source_checked:
            for command in ([sys.executable, 'scripts/generate_imports.py', '--check'],
                            [sys.executable, 'scripts/check_library_layout.py'],
                            [sys.executable, 'scripts/check_placeholders.py']):
                subprocess.run(command, cwd=root, check=True)
            for test in plan['tooling_tests']:
                subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'scripts',
                                '-p', test + '.py'], cwd=root, check=True)
        if args.source_only:
            return 0
        execute(root, plan, ci=args.ci, rehash=args.rehash or os.environ.get('QUILLEN_REHASH') == '1',
                output=args.native_outputs)
    except subprocess.CalledProcessError as error:
        return error.returncode if error.returncode > 0 else 128 - error.returncode
    except (OSError, ValueError, KeyError) as error:
        print(f'Check failed: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
