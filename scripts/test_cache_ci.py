#!/usr/bin/env python3
"""Check cache compiler serialization without invoking Lean or Lake."""
from concurrent.futures import ThreadPoolExecutor
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

from cache_ci import guarded_cache, serialized_frontend

ROOT = Path(__file__).resolve().parents[1]
METADATA = {'--print-prefix': b'/fake prefix\n', '--githash': b'abc123\n'}


class CacheFrontendTests(unittest.TestCase):
    def test_concurrent_launches_are_serial_and_preserve_arguments_and_status(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-launch-') as temporary:
            root = Path(temporary)
            lean = root / 'lean'
            # Exclusive creation detects any overlapping compiler launches.
            original = '''#!/usr/bin/env python3
from pathlib import Path
import sys, time
root = Path(__file__).parent
active = root / 'active'
try:
    with active.open('x'):
        time.sleep(0.08)
        (root / (sys.argv[1] + '.args')).write_text(repr(sys.argv[2:]))
finally:
    active.unlink(missing_ok=True)
raise SystemExit(int(sys.argv[1]))
'''
            lean.write_text(original)
            lean.chmod(0o755)
            with serialized_frontend(lean, METADATA):
                def launch(status):
                    return subprocess.run([str(lean), str(status), '-j1', 'a b'],
                                          capture_output=True, text=True)
                with ThreadPoolExecutor(max_workers=4) as workers:
                    results = list(workers.map(launch, range(4)))
                self.assertEqual([result.returncode for result in results], list(range(4)),
                                 [result.stderr for result in results])
                for status in range(4):
                    self.assertEqual((root / f'{status}.args').read_text(), "['-j1', 'a b']")
            self.assertEqual(lean.read_text(), original)
            self.assertFalse((root / 'lean-capped').exists())

    def test_original_wrapper_is_restored_after_failure(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-restore-') as temporary:
            lean = Path(temporary) / 'lean'
            lean.write_text('original')
            with self.assertRaisesRegex(RuntimeError, 'probe'):
                with serialized_frontend(lean, METADATA):
                    raise RuntimeError('probe')
            self.assertEqual(lean.read_text(), 'original')

    def test_nested_exact_locators_return_exact_bytes_without_real_launches(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-nested-') as temporary:
            root = Path(temporary)
            lean = root / 'lean'
            lean.write_text('''#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, sys
with Path(__file__).with_name('launches.jsonl').open('a') as output:
    output.write(json.dumps(sys.argv[1:]) + '\\n')
if sys.argv[1:] in [['--print-prefix'], ['--githash']]:
    raise SystemExit('cached queries must not launch the real compiler')
else:
    for query, expected in [('--print-prefix', b'/fake prefix\\n'), ('--githash', b'abc123\\n')]:
        child = subprocess.run([str(Path(__file__).with_name('lean')), query],
                               capture_output=True, timeout=3)
        assert child.returncode == 0 and child.stdout == expected
''')
            lean.chmod(0o755)
            with serialized_frontend(lean, METADATA):
                result = subprocess.run([str(lean), 'Compile.lean'],
                                        capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / 'launches.jsonl').read_text().splitlines(),
                             [json.dumps(['Compile.lean'])])

    def test_nonexact_locator_queries_still_wait_for_compiler_lock(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-malformed-') as temporary:
            root = Path(temporary)
            lean = root / 'lean'
            marker = root / 'entered'
            lean.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\n'
                            f'Path({str(marker)!r}).write_text("entered")\n')
            lean.chmod(0o755)
            with serialized_frontend(lean, METADATA):
                for arguments in (['--print-prefix', 'File.lean'],
                                  ['--githash', '--print-prefix'],
                                  ['--print-prefix', '--run', 'File.lean'], ['--version']):
                    with self.subTest(arguments=arguments):
                        marker.unlink(missing_ok=True)
                        with (root / 'lean.lock').open('a') as lock:
                            fcntl.flock(lock, fcntl.LOCK_EX)
                            child = subprocess.Popen([str(lean), *arguments])
                            try:
                                time.sleep(0.15)
                                self.assertIsNone(child.poll())
                                self.assertFalse(marker.exists())
                            finally:
                                fcntl.flock(lock, fcntl.LOCK_UN)
                                child.wait(timeout=5)
                        self.assertEqual(child.returncode, 0)
                        self.assertTrue(marker.exists())

    def test_child_signal_releases_lock_and_propagates_failure(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-signal-') as temporary:
            lean = Path(temporary) / 'lean'
            lean.write_text('#!/usr/bin/env python3\nimport os, signal, sys\n'
                            'if len(sys.argv) == 1: os.kill(os.getpid(), signal.SIGTERM)\n')
            lean.chmod(0o755)
            with serialized_frontend(lean, METADATA):
                result = subprocess.run([str(lean)], timeout=5)
                self.assertEqual(result.returncode, 143)
                self.assertEqual(subprocess.run([str(lean), 'retry'], timeout=5).returncode, 0)

    def test_ci_shell_passes_only_enumerated_roots_to_pinned_guard(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-command-') as temporary:
            root = Path(temporary)
            scripts = root / 'scripts'
            scripts.mkdir()
            for name in ('cache.sh', 'cache_ci.py', 'cache_sources.py', 'library_sources.py'):
                shutil.copyfile(ROOT / 'scripts' / name, scripts / name)
            (root / 'Quillen.lean').write_text('import Mathlib.Data.Nat.Basic\n')
            aglib = root / '.lake/packages/Aglib/scripts'
            aglib.mkdir(parents=True)
            (aglib / 'build_serial.py').write_text('''from contextlib import contextmanager
from pathlib import Path
import os
@contextmanager
def capped_toolchain(root):
    lean = root / 'capped-lean'
    lean.write_text('original capped wrapper')
    yield dict(os.environ, LEAN=str(lean))
''')
            (aglib / 'resource_guard.py').write_text('''from pathlib import Path
import json, os
def run(command, *, env, receipt):
    assert command[2:4] == ['--guarded-cache', env['LEAN']]
    receipt.write_text(json.dumps({'command':command}))
    return int(os.environ.get('FAKE_CACHE_STATUS', '0'))
''')
            bin_dir = root / 'bin'
            bin_dir.mkdir()
            lake = bin_dir / 'lake'
            lake.write_text('#!/bin/sh\n[ "$*" = resolve-deps ] || exit 99\n')
            lake.chmod(0o755)
            receipt = root / 'verify-cache.json'
            environment = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ['PATH'],
                               QUILLEN_VERIFY_DIR=str(root / 'verify'), FAKE_CACHE_STATUS='19')
            result = subprocess.run(['bash', 'scripts/cache.sh', '--ci'], cwd=root,
                                    env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 19, result.stderr)
            self.assertEqual(json.loads(receipt.read_text())['command'],
                             [sys.executable, str((scripts / 'cache_ci.py').resolve()), '--guarded-cache',
                              str((root / 'capped-lean').resolve()), 'Mathlib.Data.Nat.Basic'])
            self.assertEqual((root / 'capped-lean').read_text(), 'original capped wrapper')

    def test_metadata_failure_stops_before_cache_and_preserves_status(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-metadata-fail-') as temporary:
            root = Path(temporary)
            lean = root / 'lean'
            lean.write_text('#!/usr/bin/env python3\nimport sys\n'
                            'sys.stdout.buffer.write(b"partial output")\n'
                            'raise SystemExit(17)\n')
            lean.chmod(0o755)
            self.assertEqual(guarded_cache(lean, ['Mathlib.Direct']), 17)
            self.assertFalse((root / 'lean-capped').exists())

    def test_successful_preflight_is_sequential_and_cache_status_propagates(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-preflight-') as temporary:
            root = Path(temporary)
            lean = root / 'lean'
            lean.write_text('''#!/usr/bin/env python3
from pathlib import Path
import json, sys
with Path(__file__).with_name('queries.jsonl').open('a') as output:
    output.write(json.dumps(sys.argv[1:]) + '\\n')
sys.stdout.buffer.write(b'bytes without newline')
''')
            lean.chmod(0o755)
            bin_dir = root / 'bin'
            bin_dir.mkdir()
            lake = bin_dir / 'lake'
            lake.write_text('#!/bin/sh\nexit 23\n')
            lake.chmod(0o755)
            from unittest.mock import patch
            with patch.dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ['PATH']):
                self.assertEqual(guarded_cache(lean, ['Mathlib.Direct']), 23)
            self.assertEqual((root / 'queries.jsonl').read_text().splitlines(),
                             [json.dumps(['--print-prefix']), json.dumps(['--githash'])])

    def test_compiler_restores_wrapper_path_before_nested_bare_locator(self):
        with tempfile.TemporaryDirectory(prefix='quillen-cache-hostile-path-') as temporary:
            root = Path(temporary)
            bin_dir = root / 'bin'
            bin_dir.mkdir()
            lean = bin_dir / 'lean'
            lean.write_text('''#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, sys
with Path(__file__).with_name('actual-launches.jsonl').open('a') as output:
    output.write(json.dumps(sys.argv[1:]) + '\\n')
if sys.argv[1:] in [['--print-prefix'], ['--githash']]:
    sys.stdout.buffer.write(b'\\x00\\xffexact bytes without newline')
else:
    for action in ['--print-prefix', '--githash']:
        result = subprocess.run(['lean', action], capture_output=True, timeout=3)
        assert result.returncode == 0
        assert result.stdout == b'\\x00\\xffexact bytes without newline'
''')
            lean.chmod(0o755)
            lake = bin_dir / 'lake'
            lake.write_text('#!/usr/bin/env python3\nimport os, subprocess, sys\n'
                            'assert sys.argv[1:] == ["exe", "cache", "get", "Mathlib.Direct"]\n'
                            'raise SystemExit(subprocess.call([os.environ["LEAN"], "Compile.lean"]))\n')
            lake.chmod(0o755)
            real_bin = root / 'real-bin'
            real_bin.mkdir()
            bypassed = root / 'bypassed'
            hostile = real_bin / 'lean'
            hostile.write_text('#!/usr/bin/env python3\nfrom pathlib import Path\n'
                               f'Path({str(bypassed)!r}).touch()\nraise SystemExit(99)\n')
            hostile.chmod(0o755)
            from unittest.mock import patch
            with patch.dict(os.environ, LEAN=str(lean),
                            PATH=os.pathsep.join([str(real_bin), str(bin_dir), os.environ['PATH']])):
                self.assertEqual(guarded_cache(lean, ['Mathlib.Direct']), 0)
            self.assertFalse(bypassed.exists())
            self.assertEqual((bin_dir / 'actual-launches.jsonl').read_text().splitlines(),
                             [json.dumps(['--print-prefix']), json.dumps(['--githash']),
                              json.dumps(['Compile.lean'])])

    def test_helper_rejects_missing_scoped_roots(self):
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/cache_ci.py'),
                                 'unused', 'unused.json'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('MODULE...', result.stderr)


if __name__ == '__main__':
    unittest.main()
