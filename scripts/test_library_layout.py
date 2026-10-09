#!/usr/bin/env python3
"""Behavioral regression tests for library boundaries and enrollment."""
from pathlib import Path
import json
import tempfile
import unittest

from check_library_layout import check_layout, import_cycles
from generate_imports import generated_files

ROOT = Path(__file__).resolve().parents[1]


class LayoutGuardTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-layout-')
        self.root = Path(self.tmp.name)
        self.write('Quillen/Algebra/A.lean', 'import Mathlib.Data.Nat.Basic\n')
        self.write('Quillen/Algebra/B.lean', 'import Quillen.Algebra.A\n')
        self.write('Quillen/Library.lean', 'import Quillen.Algebra.B\n')
        self.write('docs/module-migration.json', json.dumps({
            'modules': [{'old': 'Quillen/Old.lean', 'new': 'Quillen/Algebra/A.lean',
                         'body_sha256': 'historical-only'}],
            'removed_aliases': [{'old': 'Quillen/Obsolete.lean'}]}))
        self.generate()

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def generate(self):
        for path, content in generated_files(self.root).items():
            self.write(path, content)

    def rejected(self, phrase):
        errors, _ = check_layout(self.root)
        self.assertTrue(any(phrase in error for error in errors), '\n'.join(errors))

    def test_current_publication_tree_passes(self):
        errors, _ = check_layout(ROOT)
        self.assertEqual(errors, [])

    def test_proof_changes_and_stale_checkpoint_are_not_permanent_gates(self):
        self.write('Quillen/Algebra/A.lean', '-- future mathematical development\n')
        self.write('CHECKPOINT.json', json.dumps({'source_modules': []}))
        self.assertEqual(check_layout(self.root)[0], [])

    def test_missing_enrollment_even_for_orphan_module(self):
        self.write('Quillen/Algebra/Orphan.lean', '')
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_root_cannot_substitute_a_transitive_closure_for_direct_enrollment(self):
        self.write('Quillen.lean', 'import Quillen.Library\n')
        self.rejected('Stale generated imports')

    def test_library_test_import_bypasses_are_rejected(self):
        for imported in ('Consumer.Bad', 'Tests.Bad', 'QuillenTest.Bad',
                         'audits.Bad', 'Quillen.Tests.Bad', '«Consumer».Bad'):
            with self.subTest(imported=imported):
                self.write('Quillen/Algebra/A.lean',
                           'public meta import Mathlib.Foo /- hidden delimiter -/\n  '
                           + imported + '\n')
                self.rejected('Forbidden library import')

    def test_fake_imports_in_comments_and_strings_do_not_create_failures(self):
        self.write('Quillen/Algebra/A.lean', '''/- import Consumer.Bad /- nested -/ -/
def s := "import Tests.Bad"
''')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_unresolved_import_in_library_and_consumer(self):
        self.write('Quillen/Algebra/A.lean', 'import Quillen.NoSuchModule\n')
        self.rejected('Unresolved local import')
        self.write('Quillen/Algebra/A.lean', '')
        self.write('examples/downstream/Consumer/Bad.lean', 'import Quillen.NoSuchModule\n')
        self.rejected('Unresolved local import')

    def test_direct_indirect_and_self_cycles(self):
        for a, b in (('Quillen.Algebra.B', 'Quillen.Algebra.A'),
                     ('Quillen.Algebra.A', 'Quillen.Algebra.A')):
            with self.subTest(a=a, b=b):
                self.write('Quillen/Algebra/A.lean', 'import ' + a + '\n')
                self.write('Quillen/Algebra/B.lean', 'import ' + b + '\n')
                self.rejected('Project import cycle')

    def test_implementation_broad_facade_import_rejected(self):
        self.write('Quillen/Algebra/A.lean', 'import Quillen.Library\n')
        self.rejected('Implementation imports broad facade')

    def test_obsolete_path_and_consumer_alias_import_rejected(self):
        self.write('Quillen/Old.lean', '')
        self.rejected('Obsolete module still present')
        (self.root / 'Quillen/Old.lean').unlink()
        self.write('examples/Client.lean', 'import Quillen.Obsolete\n')
        self.rejected('Obsolete imports')

    def test_obsolete_name_can_be_reused_as_current_family_facade(self):
        manifest = {'removed_aliases': [{'old': 'Quillen/Algebra.lean'}]}
        self.write('docs/module-migration.json', json.dumps(manifest))
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('Quillen/Algebra.lean', 'import Quillen.Algebra.A\n')
        self.assertEqual(check_layout(self.root)[0], [])

    def test_manual_future_facade_reuses_historical_name_without_registry(self):
        self.write('docs/module-migration.json', json.dumps({
            'removed_aliases': [{'old': 'Quillen/Future.lean'}]}))
        self.write('Quillen/Future/A.lean', '')
        self.write('Quillen/Future.lean', 'import Quillen.Future.A\n\ndef answer : Nat := 42\n')
        self.write('examples/Client.lean', 'import Quillen.Future\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_extra_family_and_facade_supported(self):
        self.write('Quillen/Future/X.lean', '')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_loose_root_source_rejected(self):
        self.write('StrayAudit.lean', 'import Quillen\n')
        self.rejected('Unclassified project-root Lean files')

    def test_deep_acyclic_graph_does_not_hit_recursion_limit(self):
        graph = {f'M{i}': {f'M{i+1}'} for i in range(2000)}
        self.assertEqual(import_cycles(graph), [])
        graph['M2000'] = {'M0'}
        self.assertTrue(import_cycles(graph))


if __name__ == '__main__':
    unittest.main()
