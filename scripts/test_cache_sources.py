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


class SharedResourcePolicyTests(unittest.TestCase):
    def test_adapter_retains_remote_profile_and_resource_aliases(self):
        from ci_adapter import create_application
        runtime = create_application(ROOT).runtime
        config = runtime.resource_config
        self.assertIn('R5_LEAN_REMOTE_PROFILE', config.names('profile'))
        self.assertIn('AGLIB_BUILD_THREADS', config.names('build_thread'))
        self.assertIn('AGLIB_LEAN_MEMORY_MB', config.names('memory'))
        self.assertIn('AGLIB_RSS_LIMIT_MB', config.names('rss'))
        self.assertEqual(type(runtime).__module__, 'lean_ci.runtime')

    def test_emitted_r5_remote_profile_preserves_managed_wrapper_and_caps(self):
        from ci_adapter import create_application
        from lean_ci.build import capped_toolchain, build_threads
        from lean_ci.resources import limits, capped_command, frontend_args
        from unittest.mock import patch
        with tempfile.TemporaryDirectory(prefix='quillen-r5-profile-') as temporary:
            sysroot = Path(temporary).resolve()
            (sysroot / 'bin').mkdir()
            wrapper = sysroot / 'bin/lean'
            wrapper.write_text('#!/bin/sh\nexit 99\n')
            wrapper.chmod(0o755)
            profile = {'schema_version': 1, 'jobs': 3, 'threads': 5,
                       'lean_memory_mib': 8192, 'rss_limit_mib': 12288,
                       'lean': str(wrapper)}
            environment = {'PATH': os.environ.get('PATH', ''),
                           'R5_LEAN_REMOTE_PROFILE': json.dumps(profile),
                           'LEAN': str(wrapper), 'LEAN_SYSROOT': str(sysroot),
                           'AGLIB_BUILD_THREADS': '1', 'AGLIB_LEAN_MEMORY_MB': '64',
                           'AGLIB_RSS_LIMIT_MB': '128'}
            with patch.dict(os.environ, environment, clear=True):
                runtime = create_application(ROOT).runtime
            config = runtime.resource_config
            budget = limits(runtime.environment, physical_bytes=64 * 1024**3, config=config)
            self.assertEqual(budget['remote_profile'], profile)
            self.assertEqual((budget['lake_jobs'], budget['max_active_lean'],
                              budget['lean_threads'], budget['native_build_threads'],
                              budget['lean_memory_mb'], budget['rss_limit_mb']),
                             (3, 3, 5, 5, 8192, 12288))
            self.assertEqual(build_threads(runtime.environment, config), 5)
            with patch('lean_ci.build.subprocess.check_output',
                       side_effect=AssertionError('managed profile queried Elan')):
                with capped_toolchain(ROOT, threads=1, environment=runtime.environment, config=config) as inherited:
                    self.assertEqual(inherited['LEAN'], str(wrapper))
                    self.assertEqual(inherited['LEAN_SYSROOT'], str(sysroot))
                    self.assertEqual(inherited['LAKE_OVERRIDE_LEAN'], 'true')
                    self.assertEqual(inherited['LEAN_NUM_THREADS'], '3')
                    self.assertEqual(inherited['PATH'].split(os.pathsep)[0], str(wrapper.parent))
                    self.assertEqual(capped_command(['lake', 'env', 'lean', '--run', 'Tool.lean'],
                                                     inherited, config),
                                     ['lake', 'env', str(wrapper), '--run', 'Tool.lean'])
                    self.assertEqual(frontend_args(environment=inherited, config=config),
                                     [str(wrapper), '-j5', '-M8192'])

    def test_source_only_shared_execution_needs_no_lean_or_dependency(self):
        from ci_adapter import create_application
        from unittest.mock import patch
        from lean_ci.resources import run as guarded_run
        from functools import partial
        with tempfile.TemporaryDirectory(prefix='quillen-shared-static-') as temporary:
            directory = Path(temporary)
            root = directory / 'project';root.mkdir()
            (root/'scripts').mkdir()
            for name in ('generate_imports.py','check_library_layout.py','check_placeholders.py'):
                (root/'scripts'/name).write_text('pass\n')
            (root/'.gitignore').write_text('__pycache__/\n')
            def git(*arguments):
                return subprocess.check_output(['git',*arguments],cwd=root)
            git('init','-q');git('add','.')
            git('-c','user.name=Fixture','-c','user.email=fixture@example.invalid',
                'commit','-qm','source-only fixture')
            application = create_application(root,source_only=True)
            with patch.object(application.runtime,'compiler_identity',side_effect=AssertionError('Lean queried')), \
                 patch.dict(os.environ,{'PYTHONDONTWRITEBYTECODE':'1'}), \
                 patch('lean_ci.runtime.resources.run', side_effect=partial(guarded_run, sampler=lambda group: [])):
                result = application.check(state=directory/'state')
            self.assertEqual(result['status'],'complete')
            self.assertEqual(result['performed_checks'],
                             ['source/imports','source/layout','source/placeholders'])
            self.assertFalse((root/'.lake').exists())
            # Compatible continuation reuses the individual source checks.
            with patch.object(application.runtime,'compiler_identity',side_effect=AssertionError('Lean queried')), \
                 patch.dict(os.environ,{'PYTHONDONTWRITEBYTECODE':'1'}), \
                 patch('lean_ci.runtime.resources.run', side_effect=partial(guarded_run, sampler=lambda group: [])):
                resumed = application.check(state=directory/'state')
            self.assertEqual(resumed['reused_checks'],result['performed_checks'])


if __name__ == '__main__':
    unittest.main()
