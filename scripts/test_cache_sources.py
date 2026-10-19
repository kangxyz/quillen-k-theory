#!/usr/bin/env python3
"""Check dependency cache closure and guarded CI orchestration without Lean."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from cache_sources import mathlib_cache_roots, workspace_imports

ROOT = Path(__file__).resolve().parents[1]


class CacheSourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-cache-sources-')
        self.root = Path(self.tmp.name)
        self.write('Quillen.lean', 'import Mathlib.Direct\n')

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_transitive_aglib_imports_with_modern_modifiers(self):
        self.write('Quillen.lean', 'public meta import all Aglib.First\nimport Mathlib.Direct\n')
        self.write('.lake/packages/Aglib/Aglib/First.lean',
                   'public import Aglib.Second\npublic import Mathlib.First\n')
        self.write('.lake/packages/Aglib/Aglib/Second.lean',
                   'import Aglib.First\nmeta import all Mathlib.Second\n')
        self.write('.lake/packages/Aglib/Aglib/Unused.lean', 'import Mathlib.Unreachable\n')
        self.assertEqual(mathlib_cache_roots(self.root),
                         ['Mathlib.Direct', 'Mathlib.First', 'Mathlib.Second'])

    def test_native_tool_test_and_client_sources_are_included(self):
        self.write('Tools/LintStyle.lean', 'import Mathlib.Style\n')
        self.write('QuillenTest.lean', 'import Mathlib.Trust\n')
        self.write('examples/downstream/Consumer.lean', 'import Mathlib.Client\n')
        self.write('examples/downstream/.lake/packages/Bad.lean', 'import Mathlib.Ignored\n')
        self.assertEqual(mathlib_cache_roots(self.root),
                         ['Mathlib.Client', 'Mathlib.Direct', 'Mathlib.Style', 'Mathlib.Trust'])

    def test_missing_reachable_dependency_fails_closed(self):
        self.write('Quillen.lean', 'import Aglib.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Missing reachable pinned Aglib source'):
            mathlib_cache_roots(self.root)

    def test_plan_fetches_only_selected_import_closure_and_linter_runtime(self):
        self.write('Quillen/P.lean', 'import Aglib.P\n')
        self.write('Quillen/Unrelated.lean', 'import Mathlib.Unrelated\n')
        self.write('QuillenTest/T.lean', 'import Quillen.P\nimport Mathlib.Test\n')
        self.write('examples/downstream/Consumer/Use.lean', 'import Quillen.P\n')
        self.write('Tools/LintScoped.lean', 'import Mathlib.Tactic.Linter.TextBased\n')
        self.write('.lake/packages/Aglib/Aglib/P.lean', 'import Mathlib.Provider\n')
        plan = dict(lean=True, providers=['Quillen.P'], tests=['QuillenTest.T'],
                    clients=['Consumer.Use'])
        self.assertEqual(mathlib_cache_roots(self.root, workspace_imports(self.root, plan)),
                         ['Mathlib.Provider', 'Mathlib.Tactic.Linter.TextBased', 'Mathlib.Test'])
        with self.assertRaisesRegex(ValueError, 'Static scope'):
            workspace_imports(self.root, dict(lean=False))

    def test_root_import_uses_the_pinned_aglib_root(self):
        self.write('Quillen.lean', 'import Aglib\n')
        self.write('.lake/packages/Aglib/Aglib.lean', 'import Aglib.Leaf\n')
        self.write('.lake/packages/Aglib/Aglib/Leaf.lean', 'import Mathlib.Leaf\n')
        self.assertEqual(mathlib_cache_roots(self.root), ['Mathlib.Leaf'])

    def test_empty_scope_never_requests_the_whole_mathlib_cache(self):
        self.write('Quillen.lean', '/- import Mathlib.Hidden -/\n')
        with self.assertRaisesRegex(ValueError, 'unscoped cache download'):
            mathlib_cache_roots(self.root)

    def cache_fixture(self):
        for name in ['cache.sh', 'cache_ci.py', 'cache_sources.py', 'library_sources.py']:
            self.write('scripts/' + name, (ROOT / 'scripts' / name).read_text())
        lake = self.write('bin/lake', '''#!/usr/bin/env python3
import json, os, pathlib, sys
root = pathlib.Path.cwd()
with open(os.environ['COMMAND_LOG'], 'a') as out:
    out.write(json.dumps(sys.argv[1:]) + '\\n')
if sys.argv[1:] == ['resolve-deps']:
    if os.environ.get('FAIL_RESOLVE'):
        raise SystemExit(23)
    target = root / '.lake/packages/Aglib/Aglib/Resolved.lean'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text('import Mathlib.Resolved\\n')
''')
        lake.chmod(0o755)
        return dict(os.environ, PATH=str(self.root / 'bin') + ':' + os.environ['PATH'],
                    COMMAND_LOG=str(self.root / 'commands.jsonl'))

    def test_resolution_precedes_dependency_source_collection(self):
        self.write('Quillen.lean', 'import Aglib.Resolved\nimport Mathlib.Direct\n')
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root,
                                env=self.cache_fixture(), capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = [json.loads(line) for line in
                    (self.root / 'commands.jsonl').read_text().splitlines()]
        self.assertEqual(commands, [['resolve-deps'],
                                    ['exe', 'cache', 'get', 'Mathlib.Direct', 'Mathlib.Resolved']])

    def test_failed_resolution_prevents_cache_download(self):
        env = self.cache_fixture()
        env['FAIL_RESOLVE'] = '1'
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertEqual((self.root / 'commands.jsonl').read_text().splitlines(),
                         [json.dumps(['resolve-deps'])])

    def test_ci_cache_acquisition_uses_resolved_guard_and_scoped_targets(self):
        self.write('Quillen.lean', 'import Aglib.Resolved\nimport Mathlib.Direct\n')
        env = self.cache_fixture()
        self.write('.lake/packages/Aglib/scripts/build_serial.py', '''
from contextlib import contextmanager
import os
@contextmanager
def capped_toolchain(root):
    lean = root / 'fake-capped-lean'
    lean.write_text('#!/usr/bin/env python3\\nimport sys\\n'
                    'assert sys.argv[1:] in [["--print-prefix"], ["--githash"]]\\n'
                    'print("fixture metadata")\\n')
    lean.chmod(0o755)
    yield dict(os.environ, LEAN=str(lean))
''')
        self.write('.lake/packages/Aglib/scripts/resource_guard.py', '''
from pathlib import Path
import json, os, subprocess, sys
def run(command, *, env, receipt):
    assert command[2:4] == ['--guarded-cache', env['LEAN']]
    with open(os.environ['COMMAND_LOG'], 'a') as out:
        out.write(json.dumps(['guard', str(receipt)] + command) + '\\n')
    return subprocess.call(command, env=env)
''')
        result = subprocess.run(['bash', 'scripts/cache.sh', '--ci'], cwd=self.root, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = [json.loads(line) for line in
                    (self.root / 'commands.jsonl').read_text().splitlines()]
        self.assertEqual(commands[0], ['resolve-deps'])
        self.assertEqual(commands[1][0], 'guard')
        self.assertTrue(commands[1][1].endswith('-cache.json'))
        self.assertNotIn('--bootstrap-cache', commands[1])
        self.assertEqual(commands[1][-4:],
                         ['--guarded-cache', str((self.root / 'fake-capped-lean').resolve()),
                          'Mathlib.Direct', 'Mathlib.Resolved'])
        self.assertEqual(commands[2],
                         ['exe', 'cache', 'get', 'Mathlib.Direct', 'Mathlib.Resolved'])


class GuardedCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-ci-commands-')
        self.root = Path(self.tmp.name).resolve()
        (self.root / 'scripts').mkdir()
        for name in ('check_run.py', 'check_scope.py', 'library_sources.py'):
            shutil.copyfile(ROOT / 'scripts' / name, self.root / 'scripts' / name)
        (self.root / 'Tools').mkdir()
        shutil.copyfile(ROOT / 'Tools/LintScoped.lean', self.root / 'Tools/LintScoped.lean')
        (self.root / 'QuillenTest').mkdir()
        (self.root / 'QuillenTest/Axioms.lean').write_text('import Quillen\n-- audit\n')
        (self.root / 'driver.py').write_text('''import sys
sys.path.insert(0, 'scripts')
from pathlib import Path
from check_run import execute
plan = dict(lean=True, providers=['Quillen.P'], provider_batches=[['Quillen.P']],
            tests=['QuillenTest.T'], clients=['Consumer.Use'], trust=True,
            client_trust=True, full=False, base=None)
if '--source-only' not in sys.argv:
    try:
        execute(Path.cwd(), plan, ci='--ci' in sys.argv, rehash='--rehash' in sys.argv)
    except Exception as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(getattr(error, 'returncode', 2))
''')
        (self.root / 'examples/downstream').mkdir(parents=True)
        (self.root / 'examples/downstream/Audit.lean').write_text('import Consumer\n-- audit\n')
        (self.root / 'examples/downstream/Consumer').mkdir()
        (self.root / 'examples/downstream/Consumer/Use.lean').write_text(
            'import Quillen.P\ndef use := 1\n')
        self.aglib = self.root / '.lake/packages/Aglib/scripts'
        self.aglib.mkdir(parents=True)
        (self.root / 'bin').mkdir()
        self.log = self.root / 'commands.jsonl'
        (self.aglib / 'build_serial.py').write_text('''
from contextlib import contextmanager
import json, os, sys
def build_threads(): return int(os.environ['AGLIB_BUILD_THREADS'])
@contextmanager
def capped_toolchain(root, threads=1):
    yield dict(os.environ, CAPPED_THREADS=str(threads), LEAN_NUM_THREADS='1',
               LEAN=os.environ['CAPPED_LEAN'])
if __name__ == '__main__':
    with open(os.environ['COMMAND_LOG'], 'a') as out:
        out.write(json.dumps({'kind':'build', 'argv':sys.argv[1:], 'cwd':os.getcwd()})+'\\n')
''')
        (self.aglib / 'resource_guard.py').write_text('''
import json, os, subprocess
def limits():
    return {'lean_memory_mb':int(os.environ['AGLIB_LEAN_MEMORY_MB']),
            'rss_limit_mb':int(os.environ['AGLIB_RSS_LIMIT_MB']),
            'lean_threads':1, 'max_active_lean':1}
def run(command, *, cwd, env, receipt, budget):
    with open(os.environ['COMMAND_LOG'], 'a') as out:
        out.write(json.dumps({'kind':'guard', 'argv':command, 'budget':budget,
                             'threads':env['CAPPED_THREADS'], 'cwd':str(cwd),
                             'receipt':str(receipt)})+'\\n')
    return subprocess.call(command, cwd=cwd, env=env)
''')
        python = self.root / 'bin/python3'
        python.write_text('''#!/usr/bin/env bash
if [[ "${1:-}" == - || "${1:-}" == */build_serial.py ]]; then
  exec "$REAL_PYTHON" "$@"
fi
exit 0
''')
        python.chmod(0o755)
        lake = self.root / 'bin/lake'
        lake.write_text('#!' + sys.executable + '\n' + '''
import os, subprocess, sys
if os.environ.get('FAIL_LINT') and '--run' in sys.argv[1:]:
    raise SystemExit(41)
if sys.argv[1:2] == ['env']:
    raise SystemExit(subprocess.call(sys.argv[2:]))
''')
        lake.chmod(0o755)
        self.capped_lean = self.root / 'bin/capped-lean'
        self.capped_lean.write_text('#!' + sys.executable + '\n' + '''
import json, os, sys
with open(os.environ['ACTUAL_LEAN_LOG'], 'a') as output:
    output.write(json.dumps(sys.argv[1:]) + '\\n')
''')
        self.capped_lean.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + ':' + os.environ['PATH'],
                        REAL_PYTHON=sys.executable, COMMAND_LOG=str(self.log),
                        CAPPED_LEAN=str(self.capped_lean),
                        ACTUAL_LEAN_LOG=str(self.root / 'actual-lean.jsonl'),
                        QUILLEN_VERIFY_DIR=str(self.root / 'verification'),
                        AGLIB_LEAN_MEMORY_MB='12800', AGLIB_RSS_LIMIT_MB='13824',
                        AGLIB_BUILD_THREADS='2')
        self.env.pop('QUILLEN_REHASH', None)

    def tearDown(self):
        self.tmp.cleanup()

    def run_check(self, *arguments):
        return subprocess.run([sys.executable, 'driver.py', *arguments], cwd=self.root,
                              env=self.env, capture_output=True, text=True)

    def test_ci_uses_shared_policy_and_preserves_native_commands(self):
        result = self.run_check('--ci', '--rehash')
        self.assertEqual(result.returncode, 0, result.stderr)
        entries = [json.loads(line) for line in self.log.read_text().splitlines()]
        builds = [entry for entry in entries if entry['kind'] == 'build']
        self.assertEqual(builds[0]['argv'][-1], 'Quillen.P')
        self.assertEqual(builds[1]['argv'][-1], 'QuillenTest.T')
        self.assertEqual(builds[2]['argv'][-1], 'Consumer.Use')
        guarded = [entry for entry in entries if entry['kind'] == 'guard']
        lean_commands = [entry['argv'] for entry in guarded if entry['argv'][:2] == ['lake', 'env']]
        self.assertTrue(all(command[2] == str(self.capped_lean) for command in lean_commands))
        self.assertTrue(any(command[-1] == 'Quillen.P' and '--run' in command for command in lean_commands))
        for entry in guarded:
            self.assertEqual(entry['threads'], '2')
            self.assertEqual(entry['budget'], {'lean_memory_mb':12800, 'rss_limit_mb':13824,
                'lean_threads':1, 'max_active_lean':1, 'native_build_threads':2})
        self.assertEqual(guarded[-1]['cwd'], str(self.root / 'examples/downstream'))

    def test_ci_audits_execute_capped_lean_even_with_poisoned_bare_lean(self):
        bare_lean = self.root / 'bin/lean'
        bare_lean.write_text('#!/bin/sh\nexit 97\n')
        bare_lean.chmod(0o755)
        result = self.run_check('--ci')
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = [json.loads(line) for line in
                    (self.root / 'actual-lean.jsonl').read_text().splitlines()]
        self.assertTrue(any(command[-1].endswith('/axioms.lean') for command in commands))
        self.assertTrue(any(command[-1].endswith('/client-audit.lean') for command in commands))
        self.assertTrue(any('--run' in command for command in commands))

    def test_ci_rewrites_only_exact_lake_env_lean_prefix(self):
        alternate = self.root / 'bin/lean-other'
        alternate.write_text('#!/bin/sh\nexit 0\n')
        alternate.chmod(0o755)
        script = self.root / 'scripts/check_run.py'
        source = script.read_text()
        original = "['lake', 'env', 'lean', '--run', str(lint_runner),"
        self.assertIn(original, source)
        script.write_text(source.replace(original, "['lake', 'env', 'lean-other', '--run', str(lint_runner),"))
        result = self.run_check('--ci')
        self.assertEqual(result.returncode, 0, result.stderr)
        entries = [json.loads(line) for line in self.log.read_text().splitlines()]
        self.assertTrue(any(entry['argv'][:3] == ['lake', 'env', 'lean-other']
                            for entry in entries if entry['kind'] == 'guard'))

    def test_source_only_needs_no_dependency_or_toolchain(self):
        shutil.rmtree(self.root / '.lake')
        result = self.run_check('--source-only', '--ci')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(self.log.exists())

    def test_ci_native_lint_failure_stops_before_audits(self):
        self.env['FAIL_LINT'] = '1'
        result = self.run_check('--ci')
        self.assertEqual(result.returncode, 41, result.stderr)
        self.assertNotIn('/axioms.lean', self.log.read_text())

    def test_relative_receipt_root_stays_at_project_root_for_client(self):
        self.env['QUILLEN_VERIFY_DIR'] = 'verification'
        result = self.run_check('--ci')
        self.assertEqual(result.returncode, 0, result.stderr)
        entries = [json.loads(line) for line in self.log.read_text().splitlines()]
        guarded = [entry for entry in entries if entry['kind'] == 'guard']
        self.assertEqual(guarded[-1]['receipt'],
                         str(self.root / 'verification/client-audit.json'))

    def test_explicit_receipt_root_must_be_fresh(self):
        Path(self.env['QUILLEN_VERIFY_DIR']).mkdir()
        result = self.run_check('--ci')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('fresh QUILLEN_VERIFY_DIR', result.stderr)
        self.assertFalse(self.log.exists())


if __name__ == '__main__':
    unittest.main()
