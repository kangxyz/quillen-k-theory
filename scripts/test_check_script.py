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
if [[ "${FAIL_LINT:-0}" == 1 && "${1:-}" == lint ]]; then
  exit 10
fi
if [[ "${FAIL_STYLE:-0}" == 1 && "${1:-}" == exe && "${2:-}" == lint-style ]]; then
  exit 11
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
            'lake --rehash test',
            'lake --rehash lint',
            'lake --rehash exe lint-style',
            'lake env lean -j2 QuillenTest/Axioms.lean',
            'lake --rehash build',
            'lake env lean -j2 Audit.lean',
        ]
        self.assertEqual([line.split('|', 1)[1] for line in commands], expected)
        self.assertEqual([line.split('|', 1)[0] for line in commands],
                         [str(self.root)] * 9 + [str(self.root / 'examples/downstream')] * 2)
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

    def test_failed_lint_is_not_reported_as_a_pass(self):
        self.env['FAIL_LINT'] = '1'
        result = self.run_check()
        self.assertEqual(result.returncode, 10)
        self.assertNotIn('QuillenTest/Axioms.lean', self.log.read_text())

    def test_failed_native_style_check_stops_before_trust_replay(self):
        self.env['FAIL_STYLE'] = '1'
        result = self.run_check()
        self.assertEqual(result.returncode, 11)
        self.assertNotIn('QuillenTest/Axioms.lean', self.log.read_text())

    def test_cache_enrolls_native_tool_imports_with_modern_modifiers(self):
        shutil.copyfile(ROOT / 'scripts/cache.sh', self.root / 'scripts/cache.sh')
        shutil.copyfile(ROOT / 'scripts/library_sources.py', self.root / 'scripts/library_sources.py')
        (self.root / 'bin/python3').unlink()  # Execute the real source enumerator.
        (self.root / 'Quillen.lean').write_text('import Mathlib.Data.Nat.Basic\n')
        (self.root / 'Tools').mkdir()
        (self.root / 'Tools/LintStyle.lean').write_text(
            'public meta import all Mathlib.Tactic.Linter.TextBased\n')
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root,
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.log.read_text().split('|', 1)[1].strip(),
                         'lake exe cache get Mathlib.Data.Nat.Basic Mathlib.Tactic.Linter.TextBased')

    def test_cache_propagates_enumerator_failure_without_download(self):
        shutil.copyfile(ROOT / 'scripts/cache.sh', self.root / 'scripts/cache.sh')
        (self.root / 'scripts/library_sources.py').write_text('raise SystemExit(17)\n')
        (self.root / 'bin/python3').unlink()
        result = subprocess.run(['bash', 'scripts/cache.sh'], cwd=self.root,
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertFalse(self.log.exists())


if __name__ == '__main__':
    unittest.main()
