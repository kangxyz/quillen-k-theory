#!/usr/bin/env python3
"""Behavioral regression tests for library boundaries and enrollment."""
from pathlib import Path
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


    def test_trust_tests_accept_production_imports_and_require_enrollment(self):
        self.write('QuillenTest/Axioms.lean', 'import Quillen\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('QuillenTest/NewPositiveTest.lean', 'import Quillen.Algebra.A\n')
        self.rejected('missing enrollment')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])

    def test_core_cannot_import_test_root_or_test_leaf(self):
        self.write('QuillenTest/Check.lean', 'import Quillen.Algebra.A\n')
        self.generate()
        for imported in ('QuillenTest', 'QuillenTest.Check'):
            with self.subTest(imported=imported):
                self.write('Quillen/Algebra/B.lean', 'import ' + imported + '\n')
                self.rejected('Forbidden library import')

    def test_trust_test_cycle_is_detected(self):
        self.write('QuillenTest/A.lean', 'import QuillenTest.B\n')
        self.write('QuillenTest/B.lean', 'import QuillenTest.A\n')
        self.generate()
        self.rejected('Project import cycle')

    def test_unresolved_test_import_is_detected(self):
        self.write('QuillenTest/A.lean', 'import QuillenTest.Missing\n')
        self.generate()
        self.rejected('Unresolved local import')

    def test_downstream_imports_resolve_in_independent_package(self):
        self.write('examples/downstream/Consumer.lean', 'import Consumer.RealClient\n')
        self.write('examples/downstream/Consumer/RealClient.lean', 'import Quillen.Library\n')
        self.assertEqual(check_layout(self.root)[0], [])
        self.write('examples/downstream/Consumer/RealClient.lean', 'import Consumer.Missing\n')
        self.rejected('Unresolved local import')

    def test_manual_future_facade_and_leaf_both_enrolled(self):
        self.write('Quillen/Future/A.lean', '')
        self.write('Quillen/Future.lean', 'import Quillen.Future.A\n\ndef answer : Nat := 42\n')
        self.generate()
        self.assertEqual(check_layout(self.root)[0], [])


if __name__ == '__main__':
    unittest.main()
