#!/usr/bin/env python3
"""Quillen selection and accepted check predicates for the shared Lean runner."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import re
import tomllib
import sys

from check_scope import GLOBAL_INPUTS, git, select
from check_run import client_check_scope, scoped_lint_source, verify_assessed_inputs, load_tooling
load_tooling(Path(__file__).resolve().parents[1])
from library_sources import module_path
from lean_ci.engine import Application, implementation_identity
from lean_ci.github import ancestor, select as accepted_baseline
from lean_ci.recipe import native_recipe
from lean_ci.resources import ResourceConfig
from lean_ci.runtime import NativeRuntime
from lean_ci.state import check_binding, digest, file_hash

from ci_policy import LEGACY_HEAD, PROTOCOL

POLICY = ['scripts/check.sh', 'scripts/check_run.py', 'scripts/ci_adapter.py',
          'scripts/check_scope.py', 'scripts/ci_policy.py', 'scripts/dependency_scope.py', 'scripts/library_sources.py',
          'scripts/generate_imports.py', 'Tools/LintScoped.lean', 'Tools/LintStyle.lean',
          'QuillenTest/Axioms.lean', 'examples/downstream/Audit.lean',
          '.github/workflows/ci.yml', *sorted(GLOBAL_INPUTS)]
DRIVERS = ['.lake/packages/batteries/scripts/runLinter.lean',
           '.lake/packages/mathlib/scripts/lint-style.lean']
RUNTIME_MODULES = ['Batteries.Tactic.Lint', 'Mathlib.Tactic.Linter.TextBased']


def input_paths(root):
    """Enroll selector/source-check bytes, names and absent configuration candidates."""
    files = set(POLICY)
    roots = ['Quillen', 'QuillenTest', 'Tools', 'scripts', 'examples/downstream']
    files.update(['Quillen.lean', 'QuillenTest.lean', 'examples/downstream/Consumer.lean',
                  'CONTRIBUTING.md', 'docs/DEVELOPMENT.md', 'docs/SCOPE.md'])
    directories = set(roots) | {'examples/downstream'}
    for name in roots:
        path = root / name
        if path.is_dir():
            for current, children, names in os.walk(path):
                children[:] = sorted(n for n in children if n not in {'.lake', '.git', '__pycache__'})
                current = Path(current)
                directories.add(current.relative_to(root).as_posix())
                files.update((current / name).relative_to(root).as_posix() for name in names
                             if Path(name).suffix in ('.lean', '.py', '.sh', '.json', '.toml'))
    return sorted(files | directories)


def audit_source(root, template, import_name, modules):
    text = (root / template).read_text()
    marker = f'import {import_name}\n'
    if text.count(marker) != 1:
        raise ValueError('Cannot scope changed audit template: ' + template)
    return text.replace(marker, ''.join(f'import {module}\n' for module in modules))


def check_task(name, command, *, modules=(), generated=None, generated_index=None, **fields):
    task = {'id': name, 'kind': 'check', 'command': list(map(str, command)),
            'modules': list(modules), 'capped': True, **fields}
    if generated is not None:
        task.update(generated=generated, generated_argument_index=generated_index,
                    generated_path=task['command'][generated_index])
    return task


def tasks(root, plan, phase, directory):
    scope = plan['scope']
    source = [check_task('source/' + name, [sys.executable, 'scripts/' + script, *arguments],
                         capped=False, input_boundary='quillen-enrolled-source-and-controls')
              for name, script, arguments in (
                  ('imports', 'generate_imports.py', ['--check']),
                  ('layout', 'check_library_layout.py', []),
                  ('placeholders', 'check_placeholders.py', []))]
    source += [check_task('source/' + name,
                         [sys.executable, '-m', 'unittest', 'discover', '-s', 'scripts', '-p', name + '.py'],
                         capped=False, input_boundary='quillen-enrolled-source-and-controls')
               for name in scope['tooling_tests']]
    if not scope['lean'] or plan.get('source_only'):
        return native_recipe(root, directory, source_checks=source, phase='source')
    lint_text = (root / 'Tools/LintScoped.lean').read_text()
    lint_program = scoped_lint_source(lint_text)
    lint_path = directory / 'LintScoped.lean'
    root_checks = [check_task('full-native-lint', ['lake', 'lint', '--no-build', '--', '--no-build'],
                              modules=['Quillen'], check_kind='native-lint'),
                   check_task('full-native-style', ['lake', 'exe', 'lint-style'],
                              modules=['Quillen', 'Tools.LintStyle'], check_kind='native-style',
                              input_boundary='quillen-complete-native-style-source')]
    if scope['trust']:
        path = directory / 'axioms.lean'
        root_checks.append(check_task('axioms', ['lake', 'env', 'lean', '-j2', path],
                           modules=scope['providers'], check_kind='audit',
                           generated=audit_source(root, 'QuillenTest/Axioms.lean', 'Quillen', scope['providers']),
                           generated_index=4))
    if scope['tests']:
        root_checks.append(check_task('test-lint', ['lake', 'env', 'lean', '--run', lint_path, *scope['tests']],
                           modules=scope['tests'], check_kind='scoped-lint',
                           generated=lint_program, generated_index=4))
    if scope['full']:
        root_checks += [check_task('diagnostic/test-' + str(index),
                         ['lake', 'env', 'lean', '-j2', str(module_path(name))],
                         modules=[name], check_kind='diagnostic')
                        for index, name in enumerate(scope['tests'])]
    modules = list(dict.fromkeys([*scope['providers'], 'Quillen', *scope['tests'], *RUNTIME_MODULES]))
    root_group = {'id': 'root', 'modules': modules, 'checks': root_checks,
                  'build_task': {'id': 'root/build', 'kind': 'graph-build', 'modules': modules, 'capped': True,
                      'command': ['lake', '--rehash', 'build', *modules, 'batteries/runLinter', 'lint-style']}}
    clients = []
    if scope['clients']:
        client_scope = client_check_scope(root, scope['clients'])
        checks = []
        for index, batch in enumerate(client_scope['environment_batches']):
            checks.append(check_task('client-lint/' + str(index),
                          ['lake', 'env', 'lean', '--run', lint_path, *batch],
                          modules=batch, check_kind='scoped-lint',
                          generated=lint_program, generated_index=4))
        if client_scope['facade_text_modules']:
            path = directory / 'LintFacadeText.lean'
            checks.append(check_task('client-facade-text',
                          ['lake', 'env', 'lean', '--run', path, *client_scope['facade_text_modules']],
                          modules=client_scope['facade_text_modules'], check_kind='facade-text',
                          certificates=client_scope['facade_certificates'],
                          generated=scoped_lint_source(lint_text, text_only=True), generated_index=4))
        if scope['client_trust']:
            for index, batch in enumerate(client_scope['audit_batches']):
                path = directory / f'client-audit-{index}.lean'
                checks.append(check_task('client-audit/' + str(index),
                              ['lake', 'env', 'lean', '-j2', path], modules=batch, check_kind='audit',
                              generated=audit_source(root, 'examples/downstream/Audit.lean', 'Consumer', batch),
                              generated_index=4))
        clients = [{'id': 'client', 'cwd': 'examples/downstream', 'modules': scope['clients'],
                    'selection': 'library', 'checks': checks}]
    prepare = [{'id': 'prepare', 'kind': 'process', 'command': [sys.executable, 'scripts/ci_adapter.py', '--prepare',
                  scope.get('dependency_assessment', {}).get('new', ''),
                  'local' if plan.get('source_basis', {}).get('kind') == 'working-tree' else 'ci'],
                'establishes_inputs': True}]
    # Source evidence and generated audit recovery inputs precede native execution.
    # Materializing declarations is deterministic; it never executes the audit.
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'scope.json').write_text(json.dumps(scope, indent=2) + '\n')
    if scope['clients']:
        (directory / 'client-scope.json').write_text(json.dumps(client_scope, indent=2) + '\n')
    for task in [*root_checks, *(t for client in clients for t in client['checks'])]:
        if task.get('generated'):
            Path(task['generated_path']).write_text(task['generated'])
    return native_recipe(root, directory, source_checks=source, prepare=prepare,
                         root_workspace=root_group, clients=clients,
                         exports=['root', *(['client'] if clients else [])], phase=phase)


def binding(root, task, toolchain, reflection=None, observations=None):
    cwd = Path(task['cwd'])
    hasher = observations.hash_file if observations else file_hash
    arguments = list(task['command'])
    if task.get('generated'):
        arguments[task['generated_argument_index']] = '<generated-input>'
    native = bool(task.get('check_kind'))
    if native and task.get('check_kind') != 'native-style':
        raw = [str(root / name) for name in POLICY]
        raw += [str(cwd / module_path(name)) for name in task['modules']]
    else:
        paths = input_paths(root)
        raw = [str(root / name) for name in paths if not (root / name).is_dir()]
    runtime = RUNTIME_MODULES if task.get('check_kind') in ('scoped-lint', 'facade-text') else ()
    extra = [str(root / name) for name in DRIVERS] if native else []
    if task.get('check_kind') == 'native-lint':
        extra += [str(root / '.lake/packages/batteries/.lake/build/bin/runLinter')]
    if task.get('check_kind') == 'native-style':
        extra += [str(root / '.lake/build/bin/lint-style')]
    value = check_binding(cwd, task.get('check_kind', 'source'), task['modules'], arguments,
                          raw + extra, runtime, toolchain=toolchain,
                          generated=digest(task['generated']) if task.get('generated') else None,
                          hash_file=hasher)
    roots = list(task['modules'])
    if runtime:
        roots += RUNTIME_MODULES
    value['reflective_imports'] = reflection.closure(roots) if reflection and native else None
    value['source_enrollment'] = paths if not native or task.get('check_kind') == 'native-style' else sorted(raw)
    value['selection'] = task['modules']
    value['facade_certificates'] = task.get('certificates')
    value['python_runtime'] = {'executable': hasher(Path(sys.executable)), 'version': sys.version,
                               'environment': {name: os.environ.get(name) for name in
                                   ('PYTHONPATH', 'PYTHONHOME', 'PYTHONHASHSEED', 'PYTHONDONTWRITEBYTECODE')}}
    return value


def acquire_assessment_source(root, base, head, provided=None):
    """Acquire only exact upstream Git objects needed by the existing pin assessor."""
    def pin(revision):
        text = git(root, 'show', revision + ':lakefile.toml')
        entries = [entry for entry in tomllib.loads(text).get('require', []) if entry.get('name') == 'Aglib']
        return entries[0].get('rev', '') if len(entries) == 1 else ''
    old, new = pin(base), pin(head)
    if old == new or provided:
        return provided
    if not all(re.fullmatch('[0-9a-f]{40}', value) for value in (old, new)):
        raise ValueError('Assessed Aglib source acquisition requires exact commit pins')
    source = Path(tempfile.mkdtemp(prefix='quillen-aglib-scope-')).resolve()
    subprocess.run(['git', 'init', '-q', str(source)], check=True)
    subprocess.run(['git', '-C', str(source), 'fetch', '--no-tags', '--depth=1',
                    'https://github.com/kangxyz/aglib.git', old, new], check=True)
    if os.environ.get('GITHUB_ENV'):
        with Path(os.environ['GITHUB_ENV']).open('a') as output:
            output.write('QUILLEN_AGLIB_SOURCE=' + str(source) + '\n')
    return source


class QuillenAdapter:
    def __init__(self, *, source_only=False, full=False, head=None, aglib_source=None, scope_file=None):
        self.source_only, self.full, self.head = source_only, full, head
        self.aglib_source = aglib_source or os.environ.get('QUILLEN_AGLIB_SOURCE')
        self.scope_file = scope_file
        if scope_file:
            if full or head:
                raise ValueError('--plan cannot be combined with --head/--full')
            original = json.loads(Path(scope_file).read_text())
            self.full, self.head = original['full'], original['head']

    def local_inputs(self, root, requested_base=None, targets=()):
        return input_paths(root)

    def select_scope(self, root, requested_base=None, targets=(), source_basis=None):
        if targets:
            raise ValueError('Quillen exact target selection is owned by the affected-source selector')
        if self.scope_file:
            original = json.loads(Path(self.scope_file).read_text())
            if requested_base and requested_base != original['base']:
                raise ValueError('--plan cannot change its comparison base')
            requested_base = original['base']
        scope = select(root, requested_base, self.head, self.full, aglib_source=self.aglib_source)
        if self.scope_file and json.loads(Path(self.scope_file).read_text()) != scope:
            raise ValueError('Selected scope is stale; regenerate the plan for these inputs')
        if scope['head']:
            enrolled = set(input_paths(root))
            changed = git(root, 'diff', '--name-only', scope['revision']).splitlines()
            changed += git(root, 'ls-files', '--others', '--exclude-standard').splitlines()
            if git(root, 'rev-parse', 'HEAD').strip() != scope['revision'] or any(
                    name in enrolled or name.endswith('.lean') or name.startswith('scripts/')
                    for name in changed):
                raise ValueError('Checked-out source/check controls differ from the selected committed head')
        verify_assessed_inputs(root, scope)
        return {'scope': scope, 'source_only': self.source_only}

    def validate_local(self, root, plan):
        if git(root, 'rev-parse', 'HEAD').strip() != plan['source_basis']['head']:
            raise ValueError('Local HEAD changed during final checks')
        if self.select_scope(root, plan['scope']['base'])['scope'] != plan['scope']:
            raise ValueError('Local affected source selection changed during checking')

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        baseline = accepted_baseline(root, repository, default_branch, head, requested_base, api, protocol=PROTOCOL)
        self.aglib_source = acquire_assessment_source(root, baseline['base'], head, self.aglib_source)
        scope = select(root, baseline['base'], head=head, aglib_source=self.aglib_source)
        scope.update(native=scope['lean'], publish=scope['lean'])
        return {'baseline': baseline, 'scope': scope}

    def required_phases(self, root, plan):
        return ['source', 'native'] if plan['scope']['lean'] else ['source']

    def validate_plan(self, root, plan):
        baseline, scope = plan['baseline'], plan['scope']
        if (scope['head'] != plan['head'] or scope['head'] != baseline['head']
                or scope['base'] != baseline['base']
                or not ancestor(root, baseline['base'], baseline['verified_base'])
                or not ancestor(root, baseline['verified_base'], plan['head'])):
            raise ValueError('CI source scope differs from its accepted ancestor')
        expected = select(root, baseline['base'], head=plan['head'], aglib_source=self.aglib_source)
        expected.update(native=expected['lean'], publish=expected['lean'])
        if expected != scope:
            raise ValueError('CI selected checks differ from committed source policy')
        verify_assessed_inputs(root, scope)
        # Independent tooling is checked against its exact workflow checkout pin.
        # No mathematical dependency pin supplies execution authority.
        tooling = Path(sys.modules['lean_ci'].__file__).resolve().parents[2]
        import re
        workflow = (root / '.github/workflows/ci.yml').read_text()
        pins = re.findall(r'repository: kangxyz/aglib\s+ref: ([0-9a-f]{40})\s+path: \.cache-tooling', workflow)
        if not pins or len(set(pins)) != 1 or git(tooling, 'rev-parse', 'HEAD').strip() != pins[0]:
            raise ValueError('Executed shared tooling differs from the independently pinned workflow checkout')
        for path in (tooling / 'ci/lean_ci').glob('*.py'):
            relative = path.relative_to(tooling).as_posix()
            committed = subprocess.check_output(['git', 'show', 'HEAD:' + relative], cwd=tooling)
            if committed != path.read_bytes():
                raise ValueError('Executed shared tooling has uncommitted implementation bytes')
        if plan['implementation'] != implementation_identity():
            raise ValueError('Executed shared tooling identity differs from the plan')

    tasks = staticmethod(tasks)
    binding = staticmethod(binding)

    def observe_inputs(self, root, observations):
        for name in DRIVERS:
            observations.optional_hash(root / name)
        observations.observe_resolution(root / 'examples/downstream/.lake/packages')


def create_application(root, *, committed=False, **options):
    config = ResourceConfig(prefix='QUILLEN', profile_keys=('R5_LEAN_REMOTE_PROFILE',),
                            memory_keys=('AGLIB_LEAN_MEMORY_MB',), rss_keys=('AGLIB_RSS_LIMIT_MB',),
                            build_thread_keys=('AGLIB_BUILD_THREADS',))
    return Application(root, QuillenAdapter(**options), NativeRuntime(root, resource_config=config))


def prepare(root, assessed_revision='', mode='ci'):
    client = root / 'examples/downstream'
    if mode == 'local' and (not (root / '.lake/packages').is_dir() or not (client / '.lake').is_dir()):
        raise ValueError('Prepare the pinned root dependencies and examples/downstream/.lake before final checks; '
                         'then retry with the existing state/progress. Source-only checks require no cache setup.')
    (client / '.lake').mkdir(exist_ok=True)
    packages = client / '.lake/packages'
    if not packages.exists():
        packages.symlink_to(root / '.lake/packages', target_is_directory=True)
    if not packages.is_dir():
        raise ValueError('Downstream package resolution is unavailable')
    if assessed_revision:
        from dependency_scope import verify_runtime
        verify_runtime(root / '.lake/packages/Aglib', assessed_revision)


if __name__ == '__main__':
    if len(sys.argv) != 4 or sys.argv[1] != '--prepare':
        raise SystemExit('Only --prepare REVISION MODE is supported; use scripts/check.sh for validation')
    prepare(Path(__file__).resolve().parents[1], sys.argv[2], sys.argv[3])
