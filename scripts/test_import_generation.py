#!/usr/bin/env python3
"""Exercise Lean import scanning and dynamically discovered import surfaces."""
from pathlib import Path
import tempfile
import subprocess
import sys
import unittest

from generate_imports import GENERATED_MARKER, generated_files, stale_files
from library_sources import lean_imports, module_path, project_imports


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


class ImportGenerationTests(unittest.TestCase):
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


if __name__ == '__main__':
    unittest.main()
