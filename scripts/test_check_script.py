#!/usr/bin/env python3
"""Check build/audit orchestration with command stubs, without running Lean."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CheckScriptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-check-command-')
        self.root = Path(self.tmp.name).resolve()
        (self.root / 'scripts').mkdir()
        shutil.copyfile(ROOT / 'scripts/check.sh', self.root / 'scripts/check.sh')
        (self.root / 'examples/downstream').mkdir(parents=True)
        (self.root / '.lake/packages').mkdir(parents=True)
        (self.root / 'bin').mkdir()
        self.log = self.root / 'commands.log'
        for command in ('python3', 'lake'):
            stub = self.root / 'bin' / command
            stub.write_text('''#!/usr/bin/env bash
printf '%s|' "$PWD" >> "$RUN_LOG"
printf '%s ' "$(basename "$0")" "$@" >> "$RUN_LOG"
printf '\\n' >> "$RUN_LOG"
if [[ "${FAIL_LAYOUT:-0}" == 1 && "${1:-}" == scripts/check_library_layout.py ]]; then
  exit 9
fi
''')
            stub.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + ':' + os.environ['PATH'],
                        RUN_LOG=str(self.log))
        self.env.pop('QUILLEN_REHASH', None)

    def tearDown(self):
        self.tmp.cleanup()

    def run_check(self, *arguments):
        return subprocess.run(['bash', 'scripts/check.sh', *arguments], cwd=self.root,
                              env=self.env, text=True, capture_output=True)

    def test_rehash_builds_both_packages_and_replays_both_audits(self):
        result = self.run_check('--rehash')
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = [line.rstrip() for line in self.log.read_text().splitlines()]
        expected = [
            'python3 scripts/generate_imports.py --check',
            'python3 scripts/check_library_layout.py',
            'python3 scripts/check_placeholders.py',
            'python3 -m unittest discover -s scripts -p test_*.py',
            'lake --rehash build Quillen QuillenTest',
            'lake env lean -j2 QuillenTest/Axioms.lean',
            'lake --rehash build',
            'lake env lean -j2 Audit.lean',
        ]
        self.assertEqual([line.split('|', 1)[1] for line in commands], expected)
        self.assertEqual([line.split('|', 1)[0] for line in commands],
                         [str(self.root)] * 6 + [str(self.root / 'examples/downstream')] * 2)
        self.assertTrue((self.root / 'examples/downstream/.lake/packages').is_symlink())

    def test_failed_static_guard_stops_before_build(self):
        self.env['FAIL_LAYOUT'] = '1'
        result = self.run_check()
        self.assertEqual(result.returncode, 9)
        self.assertNotIn('lake ', self.log.read_text())

    def test_invalid_arguments_rejected_before_work(self):
        result = self.run_check('--unknown')
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.log.exists())


if __name__ == '__main__':
    unittest.main()
