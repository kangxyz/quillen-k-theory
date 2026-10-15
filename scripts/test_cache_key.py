#!/usr/bin/env python3
"""Regression tests for the project cache configuration boundary."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from cache_key import config_hash


CONFIG = '''name = "fixture"
version = "0.4.1"
description = "fixture package"
defaultTargets = ["Fixture"]
moreLeanArgs = ["-DmaxRecDepth=1000"]
[[lean_lib]]
name = "Fixture"
leanOptions = { autoImplicit = false }
[[require]]
name = "dependency"
version = "1.0.0"
rev = "abc123"
'''
PACKAGES = ('', 'examples/downstream/')


class CacheKeyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-cache-config-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for package in PACKAGES:
            directory = self.root / package
            directory.mkdir(parents=True, exist_ok=True)
            (directory / 'lakefile.toml').write_text(CONFIG, encoding='utf-8')
            (directory / 'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
            (directory / 'lake-manifest.json').write_text('{"packages":[{"rev":"abc123"}]}\n')

    def test_package_versions_only_are_ignored(self):
        baseline = config_hash(self.root)
        for package in PACKAGES:
            with self.subTest(package=package):
                path = self.root / package / 'lakefile.toml'
                path.write_text(CONFIG.replace('version = "0.4.1"', 'version = "9.0.0"'))
                self.assertEqual(config_hash(self.root), baseline)
                path.write_text(CONFIG.replace('version = "0.4.1"\n', ''))
                self.assertEqual(config_hash(self.root), baseline)
                path.write_text(CONFIG)

    def test_configuration_changes_invalidate_both_packages(self):
        baseline = config_hash(self.root)
        changes = [
            ('autoImplicit = false', 'autoImplicit = true'),
            ('maxRecDepth=1000', 'maxRecDepth=2000'),
            ('defaultTargets = ["Fixture"]', 'defaultTargets = ["Other"]'),
            ('version = "1.0.0"', 'version = "2.0.0"'),
            ('rev = "abc123"', 'rev = "def456"'),
            ('description = "fixture package"', 'description = "different metadata"'),
            ('autoImplicit = false', 'autoImplicit = "false"'),
        ]
        for package in PACKAGES:
            path = self.root / package / 'lakefile.toml'
            for old, new in changes:
                with self.subTest(package=package, setting=old):
                    path.write_text(CONFIG.replace(old, new))
                    self.assertNotEqual(config_hash(self.root), baseline)
                    path.write_text(CONFIG)

    def test_native_storage_policy_absent_true_false_preserves_legacy_key(self):
        baseline = config_hash(self.root)
        for package in PACKAGES:
            path = self.root / package / 'lakefile.toml'
            for enabled in (None, True, False):
                for restored in (None, True, False):
                    flags = ''.join(f'{name} = {str(value).lower()}\n'
                                    for name, value in [('enableArtifactCache', enabled),
                                                        ('restoreAllArtifacts', restored)]
                                    if value is not None)
                    with self.subTest(package=package, enabled=enabled, restored=restored):
                        path.write_text(flags + CONFIG)
                        self.assertEqual(config_hash(self.root), baseline)
            path.write_text(CONFIG)

    def test_nested_storage_named_fields_remain_significant(self):
        baseline = config_hash(self.root)
        for package in PACKAGES:
            path = self.root / package / 'lakefile.toml'
            for table in ('[leanOptions]', '[[require]]\nname="other-dependency"'):
                for field in ('enableArtifactCache', 'restoreAllArtifacts'):
                    digests = []
                    for value in ('true', 'false'):
                        path.write_text(CONFIG + f'\n{table}\n{field}={value}\n')
                        digests.append(config_hash(self.root))
                    self.assertNotIn(baseline, digests)
                    self.assertNotEqual(*digests)
            path.write_text(CONFIG)

    def test_raw_pins_toolchains_and_lean_config_presence(self):
        baseline = config_hash(self.root)
        for package in PACKAGES:
            for name in ('lean-toolchain', 'lake-manifest.json'):
                with self.subTest(package=package, file=name):
                    path = self.root / package / name
                    original = path.read_bytes()
                    path.write_bytes(original.replace(b'abc123', b'def456')
                                     if name.endswith('.json') else b'leanprover/lean4:v4.25.0\n')
                    self.assertNotEqual(config_hash(self.root), baseline)
                    path.write_bytes(original + b' ')
                    self.assertNotEqual(config_hash(self.root), baseline)
                    path.write_bytes(original)
            path = self.root / package / 'lakefile.lean'
            path.write_text('')
            present = config_hash(self.root)
            self.assertNotEqual(present, baseline)
            path.write_text('package fixture where\n  version := v!"1.0.0"\n')
            raw = config_hash(self.root)
            self.assertNotEqual(raw, present)
            path.write_text('package fixture where\n  version := v!"2.0.0"\n')
            self.assertNotEqual(config_hash(self.root), raw)
            path.unlink()
            self.assertEqual(config_hash(self.root), baseline)

    def test_determinism_and_toml_order_comments(self):
        baseline = config_hash(self.root)
        self.assertEqual(config_hash(self.root), baseline)
        for package in PACKAGES:
            path = self.root / package / 'lakefile.toml'
            path.write_text('# harmless comment\n' + CONFIG.replace(
                'name = "fixture"\nversion = "0.4.1"',
                'version = "0.4.1"\nname = "fixture"'))
        self.assertEqual(config_hash(self.root), baseline)
        self.assertRegex(baseline, r'^[0-9a-f]{64}$')

    def test_missing_and_empty_required_inputs_fail(self):
        for package in PACKAGES:
            for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
                with self.subTest(package=package, file=name):
                    path = self.root / package / name
                    original = path.read_bytes()
                    path.unlink()
                    with self.assertRaises(FileNotFoundError):
                        config_hash(self.root)
                    path.write_bytes(b'')
                    with self.assertRaisesRegex(ValueError, 'required input is empty'):
                        config_hash(self.root)
                    path.write_bytes(original)

    def test_malformed_and_unsupported_toml_fail(self):
        for package in PACKAGES:
            path = self.root / package / 'lakefile.toml'
            for content in ('name = [', CONFIG + '\n[extra]\ndate = 2026-10-12\n',
                            CONFIG + '\n[extra]\nvalue = nan\n'):
                with self.subTest(package=package, content=content):
                    path.write_text(content)
                    with self.assertRaises(ValueError):
                        config_hash(self.root)
                    path.write_text(CONFIG)

    def test_cli_digest_and_visible_failure(self):
        script = Path(__file__).with_name('cache_key.py')
        result = subprocess.run([sys.executable, str(script), str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, config_hash(self.root) + '\n')
        (self.root / 'lakefile.toml').write_text('invalid = [')
        result = subprocess.run([sys.executable, str(script), str(self.root)],
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, '')
        self.assertIn('cache configuration error: lakefile.toml:', result.stderr)


if __name__ == '__main__':
    unittest.main()
