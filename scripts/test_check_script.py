#!/usr/bin/env python3
"""Command-stub regression tests; never launch Lean or Lake builds."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CheckScriptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-check-command-')
        self.root = Path(self.tmp.name).resolve()
        (self.root / 'scripts').mkdir()
        for name in ('check.sh', 'check_run.py', 'check_scope.py', 'library_sources.py'):
            shutil.copyfile(ROOT / 'scripts' / name, self.root / 'scripts' / name)
        for name in ('generate_imports.py', 'check_library_layout.py', 'check_placeholders.py'):
            (self.root / 'scripts' / name).write_text('pass\n')
        self.write('scripts/test_fixture.py', 'import os, unittest\nclass Fixture(unittest.TestCase):\n'
                   '    def test_static(self):\n'
                   '        self.assertNotEqual(os.environ.get("FAIL_UNRELATED"), "1")\n')
        (self.root / 'Tools').mkdir(exist_ok=True)
        shutil.copyfile(ROOT / 'Tools/LintScoped.lean', self.root / 'Tools/LintScoped.lean')
        self.write('.gitignore', '.lake/\nbin/\ncommands.log\n__pycache__/\n')
        self.write('QuillenTest.lean', 'import QuillenTest.T\n')
        self.write('examples/downstream/Consumer.lean', 'import Consumer.Use\n')
        self.write('Quillen/P.lean', 'def p := 1\n')
        self.write('Quillen/C.lean', 'import Quillen.P\ndef c := p\n')
        self.write('Quillen/U.lean', 'def u := 1\n')
        self.write('Quillen.lean', 'import Quillen.P Quillen.C Quillen.U\n')
        self.write('QuillenTest/T.lean', 'import Quillen.C\nexample : True := trivial\n')
        self.write('QuillenTest/Axioms.lean', 'import Quillen\n-- audit body\n')
        self.write('examples/downstream/Consumer/Use.lean', 'import Quillen.C\ndef use := c\n')
        self.write('examples/downstream/Audit.lean', 'import Consumer\n-- audit body\n')
        (self.root / '.lake/packages').mkdir(parents=True)
        (self.root / 'bin').mkdir()
        self.log = self.root / 'commands.log'
        lake = self.root / 'bin/lake'
        lake.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
with open(os.environ['RUN_LOG'], 'a') as output:
    output.write(json.dumps([os.getcwd(), sys.argv[1:]]) + '\\n')
if '--run' in sys.argv and os.environ.get('FAIL_LINT') == '1':
    raise SystemExit(10)
if Path.cwd().name == 'downstream':
    if 'build' in sys.argv and os.environ.get('FAIL_CLIENT_BUILD') == '1':
        raise SystemExit(17)
    if '--run' in sys.argv and os.environ.get('FAIL_CLIENT_LINT') == '1':
        raise SystemExit(18)
''')
        lake.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + ':' + os.environ['PATH'],
                        RUN_LOG=str(self.log))
        self.env.pop('QUILLEN_REHASH', None)
        self.env.pop('QUILLEN_VERIFY_DIR', None)
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'baseline')

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=self.root, text=True).strip()

    def tearDown(self):
        self.tmp.cleanup()

    def run_check(self, *arguments):
        return subprocess.run(['bash', 'scripts/check.sh', *arguments], cwd=self.root,
                              env=self.env, text=True, capture_output=True)

    def commands(self):
        return [json.loads(line)[1] for line in self.log.read_text().splitlines()]

    def test_docs_and_evidence_only_do_not_invoke_lean_or_create_cache_outputs(self):
        self.write('docs/evidence.json', '{}\n')
        self.write('Quillen/README.md', 'Documentation\n')
        output = self.root / 'native.jsonl'
        result = self.run_check('--ci', '--native-outputs', str(output))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.log.exists())
        self.assertFalse(output.exists())
        self.assertFalse((self.root / '.lake/verification').exists())

    def test_proof_and_docs_changes_select_no_unrelated_python_suites(self):
        from check_scope import select
        self.env['FAIL_UNRELATED'] = '1'
        self.write('docs/evidence.json', '{}\n')
        plan = select(self.root)
        self.assertEqual(plan['changed'], ['docs/evidence.json'])
        self.assertEqual(plan['tooling_tests'], [])
        self.assertFalse(plan['lean'])
        self.write('Quillen/P.lean', 'def p := 2\n')
        plan = select(self.root)
        self.assertIn('docs/evidence.json', plan['changed'])
        self.assertEqual(plan['tooling_tests'], [])
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('Ran ', result.stderr)

    def test_changed_tool_runs_its_named_regression_only(self):
        from check_scope import select
        self.env['FAIL_UNRELATED'] = '1'
        self.write('scripts/cache_key.py', '# changed cache configuration helper\n')
        self.write('scripts/test_cache_key.py',
                   'import unittest\nfrom pathlib import Path\nclass Selected(unittest.TestCase):\n'
                   '    def test_selected(self):\n'
                   '        Path(".lake/selected-regression").write_text("ran")\n')
        plan = select(self.root)
        self.assertEqual(plan['tooling_tests'], ['test_cache_key'])
        result = self.run_check('--source-only')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.root / '.lake/selected-regression').is_file())
        self.assertFalse(self.log.exists())

    def test_unknown_tooling_requires_explicit_regression_selection(self):
        self.write('scripts/new_helper.py', '# unassigned regression scope\n')
        result = self.run_check('--source-only')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('assign its regression selection', result.stderr)
        self.assertFalse(self.log.exists())

    def test_provider_lint_precedes_affected_consumers_and_tests(self):
        self.write('Quillen/P.lean', 'def p := 2\n')
        result = self.run_check('--rehash')
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = self.commands()
        builds = [cmd for cmd in commands if 'build' in cmd]
        self.assertEqual(builds, [['--rehash', 'build', 'Quillen.P'],
                                  ['--rehash', 'build', 'Batteries.Tactic.Lint', 'Mathlib.Tactic.Linter.TextBased'],
                                  ['--rehash', 'build', 'Quillen.C'],
                                  ['--rehash', 'build', 'QuillenTest.T'],
                                  ['--rehash', 'build', 'Consumer.Use']])
        self.assertIn('Quillen.P', commands[2])
        self.assertIn('--run', commands[2])
        lints = [cmd for cmd in commands if '--run' in cmd]
        self.assertEqual([cmd[cmd.index('--run') + 2:] for cmd in lints],
                         [['Quillen.P'], ['Quillen.C'], ['QuillenTest.T'], ['Consumer.Use']])
        for module, lint_command in zip(
                ('Quillen.P', 'Quillen.C', 'QuillenTest.T', 'Consumer.Use'), lints):
            self.assertLess(commands.index(['--rehash', 'build', module]),
                            commands.index(lint_command))
        self.assertLess(commands.index(lints[0]),
                        commands.index(['--rehash', 'build', 'Quillen.C']))
        self.assertLess(commands.index(lints[1]),
                        commands.index(['--rehash', 'build', 'QuillenTest.T']))
        self.assertNotIn('Quillen.U', str(commands))
        self.assertNotIn(['--rehash', 'build', 'Quillen'], commands)
        self.assertFalse(any('QuillenTest/T.lean' in cmd for cmd in commands))
        audit = next((self.root / '.lake/verification').glob('*/axioms.lean')).read_text()
        self.assertIn('import Quillen.P\n', audit)
        self.assertNotIn('import Quillen\n', audit)

    def test_test_only_edit_does_not_select_producer_build_or_client(self):
        self.write('QuillenTest/T.lean', 'import Quillen.C\nexample : True := by trivial\n')
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([cmd for cmd in self.commands() if 'build' in cmd],
                         [['build', 'QuillenTest.T'],
                          ['build', 'Batteries.Tactic.Lint', 'Mathlib.Tactic.Linter.TextBased']])
        self.assertFalse(any('QuillenTest/T.lean' in cmd for cmd in self.commands()))

    def test_explicit_full_diagnostics_replay_only_selected_test_sources(self):
        result = self.run_check('--full')
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = self.commands()
        replays = [cmd[-1] for cmd in commands if cmd[:3] == ['env', 'lean', '-j2'] and
                   cmd[-1].startswith('QuillenTest')]
        self.assertEqual(replays, ['QuillenTest.lean', 'QuillenTest/T.lean'])
        # Trust replay stays separate and scopes the existing audit body imports.
        audit = next((self.root / '.lake/verification').glob('*/axioms.lean')).read_text()
        self.assertIn('import Quillen.P\n', audit)
        self.assertTrue(any(cmd[-1].endswith('/axioms.lean') for cmd in commands))
        self.assertTrue(any(cmd[-1].endswith('/client-audit.lean') for cmd in commands))

    def test_lint_failure_stops_before_dependent_build(self):
        self.write('Quillen/P.lean', 'def p := 2\n')
        self.env['FAIL_LINT'] = '1'
        result = self.run_check()
        self.assertEqual(result.returncode, 10, result.stderr)
        self.assertEqual(len(self.commands()), 3)

    def test_client_failure_keeps_selected_recovery_audit(self):
        self.write('examples/downstream/Consumer/Use.lean',
                   'import Quillen.C\ndef use := c + 1\n')
        for variable, code in [('FAIL_CLIENT_BUILD', 17), ('FAIL_CLIENT_LINT', 18)]:
            with self.subTest(failure=variable):
                self.env.pop('FAIL_CLIENT_BUILD', None)
                self.env.pop('FAIL_CLIENT_LINT', None)
                self.env[variable] = '1'
                self.log.write_text('')
                before = set((self.root / '.lake/verification').glob('*'))
                result = self.run_check()
                self.assertEqual(result.returncode, code, result.stderr)
                created = set((self.root / '.lake/verification').iterdir()) - before
                self.assertEqual(len(created), 1)
                directory = created.pop()
                plan = json.loads((directory / 'scope.json').read_text())
                self.assertTrue(plan['client_trust'])
                self.assertTrue((directory / 'LintScoped.lean').is_file())
                source = (directory / 'client-audit.lean').read_text()
                self.assertIn('-- audit body', source)
                for module in plan['clients']:
                    self.assertIn(f'import {module}\n', source)
                self.assertFalse(any(cmd[-1].endswith('/client-audit.lean')
                                     for cmd in self.commands()))

    def test_unknown_flags_and_missing_base_fail_without_lake(self):
        for args in (['--unknown'], ['--base', 'missing-base']):
            result = self.run_check(*args)
            self.assertEqual(result.returncode, 2, result.stderr)
        self.assertFalse(self.log.exists())

    def test_changed_facade_is_compiled_and_native_linted(self):
        self.write('Quillen.lean', 'import Quillen.P Quillen.C\n')
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.commands()[0], ['build', 'Quillen'])
        self.assertIn('--run', self.commands()[2])

    def test_rename_and_deleted_edges_select_surviving_consumers(self):
        from check_scope import select
        self.git('mv', 'Quillen/P.lean', 'Quillen/New.lean')
        self.write('Quillen/C.lean', 'import Quillen.New\ndef c := p\n')
        plan = select(self.root)
        self.assertIn('Quillen.New', plan['providers'])
        self.assertIn('Quillen.C', plan['providers'])
        self.assertNotIn('Quillen.P', plan['providers'])
        self.assertEqual(plan['tests'], ['QuillenTest.T'])
        self.assertEqual(plan['clients'], ['Consumer.Use'])
        self.assertNotIn('Quillen.U', plan['providers'])

    def test_deletion_with_stale_import_is_selected_and_fails_during_real_build(self):
        from check_scope import select
        (self.root / 'Quillen/P.lean').unlink()
        plan = select(self.root)
        self.assertIn('Quillen.C', plan['providers'])
        self.assertNotIn('Quillen.P', plan['providers'])
        self.assertTrue(plan['lean'])

    def test_unknown_and_global_inputs_never_fallback_to_full(self):
        from check_scope import select
        self.write('unknown.dat', 'runtime?')
        with self.assertRaisesRegex(ValueError, 'Unclassified'):
            select(self.root)
        (self.root / 'unknown.dat').unlink()
        self.write('lean-toolchain', 'leanprover/lean4:fixture')
        with self.assertRaisesRegex(ValueError, 'global validation inputs'):
            select(self.root)

    def test_true_initial_commit_selects_actual_added_sources(self):
        from check_scope import select
        plan = select(self.root, base='EMPTY_TREE', head='HEAD')
        self.assertTrue(plan['lean'])
        self.assertFalse(plan['full'])
        self.assertIn('Quillen.U', plan['providers'])
        self.assertIn('Quillen', plan['providers'])

    def test_committed_plan_rejects_local_source_and_configuration_drift(self):
        from check_scope import select
        plan = self.root / '.lake/scope.json'
        plan.write_text(json.dumps(select(self.root, head='HEAD')))
        for path in ('Quillen/P.lean', 'Quillen/New.lean', 'lean-toolchain'):
            target = self.root / path
            previous = target.read_text() if target.exists() else None
            target.write_text('changed input\n')
            result = self.run_check('--source-checked', '--plan', str(plan))
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn('differs from the selected head', result.stderr)
            if previous is None:
                target.unlink()
            else:
                target.write_text(previous)
        self.assertFalse(self.log.exists())

    def test_zero_before_branch_recovers_available_independent_merge_base(self):
        self.git('update-ref', 'refs/remotes/origin/main', 'HEAD')
        self.write('Quillen/P.lean', 'def p := 2\n')
        self.git('add', 'Quillen/P.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'changed provider')
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        step = workflow.split('      - name: Select affected checks before installing Lean\n', 1)[1]
        script = step.split('        run: |\n', 1)[1].split('      - name:', 1)[0]
        script = '\n'.join(line[10:] for line in script.splitlines())
        environment = dict(self.env, FULL='false', EVENT_NAME='push', BASE_SHA='0' * 40,
                           DEFAULT_BRANCH='main', RUNNER_TEMP=str(self.root / '.lake'),
                           GITHUB_OUTPUT=str(self.root / '.lake/github-output'))
        result = subprocess.run(['bash', '-euo', 'pipefail', '-c', script], cwd=self.root,
                                env=environment, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads((self.root / '.lake/check-scope.json').read_text())
        self.assertEqual(plan['base'], self.git('rev-parse', 'refs/remotes/origin/main'))
        self.assertEqual(plan['providers'], ['Quillen.C', 'Quillen.P'])
        self.assertFalse(plan['full'])

    def test_ci_gates_every_lean_bootstrap_and_export_has_no_build_step(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        self.assertIn('bash scripts/check.sh --source-only --plan "$RUNNER_TEMP/check-scope.json"', workflow)
        for name in ('Check out shared native Lake cache tooling', 'Install the pinned Lean toolchain',
                     'Restore exact pinned dependencies', 'Fetch matching Mathlib dependency proof cache',
                     'Compute project cache configuration', 'Restore incremental project builds'):
            step = workflow.split('      - name: ' + name + '\n', 1)[1].split('      - name:', 1)[0]
            self.assertIn("if: steps.scope.outputs.lean == 'true'", step)
        self.assertIn('default: false', workflow)
        self.assertNotIn('native-cache-export', workflow)
        self.assertIn('needs.library.outputs.native-artifact !=', workflow)

    def test_native_export_uses_exact_verified_targets_without_second_build(self):
        self.write('Quillen/P.lean', 'def p := 2\n')
        aglib = '.lake/packages/Aglib/scripts/'
        self.write(aglib + 'build_serial.py', '''from contextlib import contextmanager
import json, os, subprocess, sys
from pathlib import Path

def build_threads(): return 1
@contextmanager
def capped_toolchain(root, threads=1):
    yield dict(os.environ, LEAN='lean-stub')

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--root'); p.add_argument('--receipt-dir')
    p.add_argument('--outputs'); p.add_argument('--rehash', action='store_true')
    p.add_argument('targets', nargs='+')
    a = p.parse_args()
    with open(os.environ['RUN_LOG'], 'a') as log:
        log.write(json.dumps([os.getcwd(), ['serial-build', *a.targets]]) + '\\n')
    Path(a.outputs).write_text(''.join(json.dumps({'target': name}) + '\\n' for name in a.targets))
''')
        self.write(aglib + 'resource_guard.py', '''import subprocess
def limits(): return {}
def run(command, *, cwd, env, receipt, budget):
    if len(command) > 2 and command[2] == 'lean-stub': command[2] = 'lean'
    return subprocess.run(command, cwd=cwd, env=env).returncode
''')
        output = self.root / '.lake/native.jsonl'
        result = self.run_check('--ci', '--native-outputs', str(output))
        self.assertEqual(result.returncode, 0, result.stderr)
        selected = [cmd[1:] for cmd in self.commands() if cmd[0] == 'serial-build']
        self.assertEqual(selected, [['Quillen.P'], ['Quillen.C'], ['QuillenTest.T'], ['Consumer.Use']])
        self.assertEqual([json.loads(row)['target'] for row in output.read_text().splitlines()],
                         [name for batch in selected for name in batch])

    def test_cache_enrolls_native_tool_imports_with_modern_modifiers(self):
        shutil.copyfile(ROOT / 'scripts/cache.sh', self.root / 'scripts/cache.sh')
        shutil.copyfile(ROOT / 'scripts/library_sources.py', self.root / 'scripts/library_sources.py')
        shutil.copyfile(ROOT / 'scripts/cache_sources.py', self.root / 'scripts/cache_sources.py')
        (self.root / 'Quillen.lean').write_text('import Mathlib.Data.Nat.Basic\n')
        (self.root / 'Tools/LintScoped.lean').unlink()
        self.write('scripts/test_fixture.py', 'import unittest\nclass Fixture(unittest.TestCase):\n    def test_static(self): pass\n')
        (self.root / 'Tools').mkdir(exist_ok=True)
        (self.root / 'Tools/LintStyle.lean').write_text(
            'public meta import all Mathlib.Tactic.Linter.TextBased\n')
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root,
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(['lake ' + ' '.join(cmd) for cmd in self.commands()],
                         ['lake resolve-deps',
                          'lake exe cache get Mathlib.Data.Nat.Basic Mathlib.Tactic.Linter.TextBased'])

    def test_cache_propagates_enumerator_failure_without_download(self):
        shutil.copyfile(ROOT / 'scripts/cache.sh', self.root / 'scripts/cache.sh')
        shutil.copyfile(ROOT / 'scripts/cache_sources.py', self.root / 'scripts/cache_sources.py')
        (self.root / 'scripts/library_sources.py').write_text('raise SystemExit(17)\n')
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root,
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertFalse(self.log.exists())


if __name__ == '__main__':
    unittest.main()
