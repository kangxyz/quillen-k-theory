#!/usr/bin/env python3
"""Exercise Lean import scanning and dynamically discovered import surfaces."""
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

from generate_imports import (
    COPYRIGHT_HEADER, GENERATED_MARKER, generated_files, render_imports, stale_files,
)
from library_sources import (
    is_import_surface, lean_imports, module_path, project_imports, style_sources,
)


class ImportParserTests(unittest.TestCase):
    def test_comments_strings_and_multiline_imports(self):
        source = '''/- import Quillen.Hidden /- nested -/ -/
public import Quillen.A /- between /- nested -/ names -/ Quillen.B
  Quillen.C -- import Quillen.Hidden
private meta import Mathlib.Foo Quillen.D
/-! documentation containing import Consumer.Hidden -/
def text := "escaped \\" import Quillen.Hidden"
def more := "line one
import Consumer.Hidden
line three"
import
  Quillen.E
  Quillen.F
namespace Stop
'''
        self.assertEqual(lean_imports(source), ['Quillen.A', 'Quillen.B', 'Quillen.C',
                         'Mathlib.Foo', 'Quillen.D', 'Quillen.E', 'Quillen.F'])
        self.assertEqual(project_imports(source), ['Quillen.A', 'Quillen.B', 'Quillen.C',
                         'Quillen.D', 'Quillen.E', 'Quillen.F'])

    def test_indented_modifiers_and_quoted_names(self):
        self.assertEqual(lean_imports('  public meta import «Quillen».A «Consumer».Bad\n'),
                         ['Quillen.A', 'Consumer.Bad'])
        self.assertEqual(module_path('Quillen.«A.B»'), Path('Quillen/A.B.lean'))

    def test_comment_delimiters_in_strings(self):
        self.assertEqual(lean_imports('def s := "/- fake -- comment"\nimport Quillen.A\n'),
                         ['Quillen.A'])

    def test_strings_terminate_import_token_scan(self):
        self.assertEqual(lean_imports('import Quillen.A\n#check "x"\nQuillen.NotAnImport\n'),
                         ['Quillen.A'])

    def test_modern_import_all_does_not_become_a_fake_module(self):
        source = '''module
public meta import /- comment -/ all Quillen.A
import all
  Quillen.B
public import Mathlib.Data.Nat.Basic
'''
        self.assertEqual(lean_imports(source),
                         ['Quillen.A', 'Quillen.B', 'Mathlib.Data.Nat.Basic'])


class ImportGenerationTests(unittest.TestCase):
    def test_large_facade_keeps_complete_imports_and_computed_size_bound(self):
        modules = [f'Quillen.Future.M{i:04d}' for i in range(1600)]
        source = render_imports(modules, '# Future import surface', modern=True)
        self.assertEqual(lean_imports(source), modules)
        self.assertIn('set_option linter.style.longFile 1800', source)
        self.assertTrue(is_import_surface(source))
        self.assertFalse(is_import_surface(source + '\ndef datum : Nat := 0\n'))
        self.assertNotIn('longFile', render_imports(modules[:1], '# Small', modern=True))

    def test_long_import_wraps_without_disabling_line_lint(self):
        name = 'Quillen.' + '.'.join(['LongSubject'] * 7)
        source = render_imports([name], '# Long import', modern=True)
        self.assertEqual(lean_imports(source), [name])
        self.assertTrue(is_import_surface(source))
        self.assertTrue(all(len(line) <= 100 for line in source.splitlines()))
        self.assertNotIn('set_option linter.style.longLine', source)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-generation-')
        self.root = Path(self.tmp.name)
        for module in ('Quillen/Algebra/Z.lean', 'Quillen/Algebra/A.lean',
                       'Quillen/Scheme.lean', 'Quillen/Resolution.lean',
                       'Quillen/Library.lean', 'Quillen/Examples/Client.lean'):
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('-- fixture\n')
        (self.root / 'Quillen.lean').write_text('')

    def tearDown(self):
        self.tmp.cleanup()

    def generate(self):
        for path, content in generated_files(self.root).items():
            (self.root / path).write_text(content)

    def test_deterministic_exhaustive_root_including_manual_facades(self):
        self.generate()
        actual = project_imports((self.root / 'Quillen.lean').read_text())
        self.assertEqual(actual, ['Quillen.Algebra', 'Quillen.Algebra.A', 'Quillen.Algebra.Z',
                         'Quillen.Examples.Client', 'Quillen.Library', 'Quillen.Resolution',
                         'Quillen.Scheme'])
        self.assertEqual(stale_files(self.root), [])
        self.assertEqual(project_imports((self.root / 'Quillen/Algebra.lean').read_text()),
                         ['Quillen.Algebra.A', 'Quillen.Algebra.Z'])

    def test_new_family_requires_generation_without_registry_edit(self):
        self.generate()
        path = self.root / 'Quillen/Future/Deep/New.lean'
        path.parent.mkdir(parents=True)
        path.write_text('')
        self.assertEqual(set(stale_files(self.root)),
                         {Path('Quillen.lean'), Path('Quillen/Future.lean')})
        self.generate()
        self.assertEqual(stale_files(self.root), [])
        self.assertIn('Quillen.Future.Deep.New', project_imports(
            (self.root / 'Quillen/Future.lean').read_text()))

    def test_new_leaf_and_removed_leaf_stale(self):
        self.generate()
        leaf = self.root / 'Quillen/Algebra/New.lean'
        leaf.write_text('')
        self.assertEqual(set(stale_files(self.root)),
                         {Path('Quillen.lean'), Path('Quillen/Algebra.lean')})
        self.generate()
        leaf.unlink()
        self.assertTrue(stale_files(self.root))

    def test_generator_preserves_hand_owned_files_and_implementations(self):
        originals = {path: path.read_bytes() for path in self.root.rglob('*.lean')
                     if path.name != 'Quillen.lean'}
        self.generate()
        self.generate()
        self.assertTrue(all(path.read_bytes() == content for path, content in originals.items()))

    def test_cli_preserves_manual_future_facade_and_enrolls_its_family(self):
        directory = self.root / 'Quillen/Future'
        directory.mkdir()
        (directory / 'Leaf.lean').write_text('-- future implementation\n')
        facade = self.root / 'Quillen/Future.lean'
        original = b'import Quillen.Future.Leaf\n\ndef futureAnswer : Nat := 42\n'
        facade.write_bytes(original)
        # A marker mentioned elsewhere does not transfer ownership.
        facade.write_bytes(original + ('-- ' + GENERATED_MARKER).encode())
        original = facade.read_bytes()
        script = Path(__file__).with_name('generate_imports.py')
        result = subprocess.run([sys.executable, str(script), '--root', str(self.root)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(facade.read_bytes(), original)
        self.assertNotIn(Path('Quillen/Future.lean'), generated_files(self.root))
        self.assertEqual(stale_files(self.root), [])
        root_imports = project_imports((self.root / 'Quillen.lean').read_text())
        self.assertIn('Quillen.Future', root_imports)
        self.assertIn('Quillen.Future.Leaf', root_imports)

    def test_exact_marker_regenerates_owned_future_facade(self):
        directory = self.root / 'Quillen/Future'
        directory.mkdir()
        (directory / 'Leaf.lean').write_text('')
        facade = self.root / 'Quillen/Future.lean'
        facade.write_text(GENERATED_MARKER + 'import Quillen.Future.Removed\n')
        self.assertIn(Path('Quillen/Future.lean'), stale_files(self.root))
        self.generate()
        self.assertEqual(project_imports(facade.read_text()), ['Quillen.Future.Leaf'])

    def test_owned_marker_after_copyright_and_manual_mention_are_distinct(self):
        facade = self.root / 'Quillen/Algebra.lean'
        facade.write_text(COPYRIGHT_HEADER + GENERATED_MARKER + 'import Quillen.Removed\n')
        self.assertIn(Path('Quillen/Algebra.lean'), generated_files(self.root))
        self.generate()
        self.assertTrue(facade.read_text().startswith(COPYRIGHT_HEADER + GENERATED_MARKER))
        manual = COPYRIGHT_HEADER + '/-! Manual module.\n' + GENERATED_MARKER + '-/\n'
        facade.write_text(manual)
        self.generate()
        self.assertEqual(facade.read_text(), manual)

    def test_nested_generation_requires_existing_opt_in_and_preserves_manual_api(self):
        nested = self.root / 'Quillen/Algebra/Nested'
        nested.mkdir()
        (nested / 'Leaf.lean').write_text('')
        owned = nested.with_suffix('.lean')
        owned.write_text(COPYRIGHT_HEADER + GENERATED_MARKER + 'import Quillen.Removed\n')
        manual_dir = self.root / 'Quillen/Algebra/Selected'
        manual_dir.mkdir()
        (manual_dir / 'Leaf.lean').write_text('')
        manual = manual_dir.with_suffix('.lean')
        original = COPYRIGHT_HEADER + 'import Quillen.Algebra.Selected.Leaf\n'
        manual.write_text(original)
        hidden = self.root / 'Quillen/Algebra/NoFacade'
        hidden.mkdir()
        (hidden / 'Leaf.lean').write_text('')
        self.generate()
        self.assertEqual(project_imports(owned.read_text()), ['Quillen.Algebra.Nested.Leaf'])
        self.assertEqual(manual.read_text(), original)
        self.assertFalse(hidden.with_suffix('.lean').exists())
        self.assertEqual(stale_files(self.root), [])
        (nested / 'New.lean').write_text('')
        self.assertIn(Path('Quillen/Algebra/Nested.lean'), stale_files(self.root))

    def test_modern_generation_preserves_mode_and_keeps_test_auditor_legacy(self):
        for path in (self.root / 'Quillen').rglob('*.lean'):
            path.write_text('module\n')
        tests = self.root / 'Tests'
        tests.mkdir()
        (tests / 'Axioms.lean').write_text('import Quillen\n')
        for path, content in generated_files(self.root, modern_library=True).items():
            (self.root / path).write_text(content)
        self.assertEqual(stale_files(self.root), [])
        source = (self.root / 'Quillen.lean').read_text()
        self.assertIn('module\n\npublic import Quillen.Algebra', source)
        self.assertNotIn('\nmodule\n', (self.root / 'Tests.lean').read_text())
        self.assertEqual(lean_imports((self.root / 'Tests.lean').read_text()), ['Tests.Axioms'])
        (self.root / 'Quillen/Algebra/A.lean').write_text('def old : Nat := 1\n')
        with self.assertRaisesRegex(ValueError, 'cannot import legacy sources'):
            generated_files(self.root)

    def test_style_inventory_uses_downstream_package_identity_and_enrolls_tools(self):
        client = self.root / 'examples/downstream/Consumer/Client.lean'
        client.parent.mkdir(parents=True)
        client.write_text('import Quillen.Library\n')
        tool = self.root / 'Tools/LintStyle.lean'
        tool.parent.mkdir()
        tool.write_text('')
        self.assertIn(('Consumer.Client', Path('examples/downstream/Consumer/Client.lean')),
                      style_sources(self.root))
        self.assertIn(('Tools.LintStyle', Path('Tools/LintStyle.lean')), style_sources(self.root))


    def test_trust_root_enrolls_all_tests_without_core_imports(self):
        directory = self.root / 'Tests'
        directory.mkdir()
        (directory / 'Axioms.lean').write_text('import Quillen\n')
        self.generate()
        self.assertEqual(project_imports((self.root / 'Quillen.lean').read_text()),
                         ['Quillen.Algebra', 'Quillen.Algebra.A', 'Quillen.Algebra.Z',
                          'Quillen.Examples.Client', 'Quillen.Library', 'Quillen.Resolution',
                          'Quillen.Scheme'])
        self.assertEqual(lean_imports((self.root / 'Tests.lean').read_text()),
                         ['Tests.Axioms'])
        (directory / 'Future.lean').write_text('import Quillen.Algebra.A\n')
        self.assertEqual(stale_files(self.root), [Path('Tests.lean')])
        self.generate()
        self.assertEqual(lean_imports((self.root / 'Tests.lean').read_text()),
                         ['Tests.Axioms', 'Tests.Future'])


if __name__ == '__main__':
    unittest.main()
