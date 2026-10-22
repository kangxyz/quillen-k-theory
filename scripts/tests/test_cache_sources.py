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

ROOT = Path(__file__).resolve().parents[2]


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

    def test_in_package_tests_and_explicit_client_sources_are_included(self):
        self.write('QuillenTest/Positive.lean', 'import Mathlib.Trust\n')
        self.write('examples/downstream/Consumer.lean', 'import Mathlib.Client\n')
        self.write('examples/downstream/.lake/packages/Bad.lean', 'import Mathlib.Ignored\n')
        self.assertEqual(mathlib_cache_roots(self.root),
                         ['Mathlib.Client', 'Mathlib.Direct', 'Mathlib.Trust'])

    def test_missing_reachable_dependency_fails_closed(self):
        self.write('Quillen.lean', 'import Aglib.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Missing reachable pinned Aglib source'):
            mathlib_cache_roots(self.root)

    def test_explicit_cache_targets_follow_only_their_actual_import_closure(self):
        self.write('Quillen/P.lean', 'import Aglib.P\n')
        self.write('Quillen/Unrelated.lean', 'import Mathlib.Unrelated\n')
        self.write('QuillenTest/T.lean', 'import Quillen.P\nimport Mathlib.Test\n')
        self.write('.lake/packages/Aglib/Aglib/P.lean', 'import Mathlib.Provider\n')
        self.assertEqual(mathlib_cache_roots(self.root, workspace_imports(self.root, ['QuillenTest.T'])),
                         ['Mathlib.Provider', 'Mathlib.Test'])
        with self.assertRaisesRegex(ValueError, 'existing local'):
            workspace_imports(self.root, ['Consumer.Use'])

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


if __name__ == '__main__':
    unittest.main()
