#!/usr/bin/env python3
"""Preserve bindings while avoiding discarded native source enrollment."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import ci_adapter as adapter
from lean_ci.state import TemporalInputs, digest


# Freeze the pre-change binding from 46d2386c. Shared native/hash semantics stay real.
LEGACY_BINDING_SOURCE = '''\
def legacy_binding(root, task, toolchain, reflection=None, observations=None):
    cwd = Path(task['cwd'])
    hasher = observations.hash_file if observations else file_hash
    arguments = list(task['command'])
    if task.get('generated'):
        arguments[task['generated_argument_index']] = '<generated-input>'
    paths = input_paths(root)
    raw = [str(root / name) for name in paths if not (root / name).is_dir()]
    native = bool(task.get('check_kind'))
    if native and task.get('check_kind') != 'native-style':
        raw = [str(root / name) for name in POLICY]
        raw += [str(cwd / module_path(name)) for name in task['modules']]
    runtime = RUNTIME_MODULES if task.get('check_kind') in ('scoped-lint', 'facade-text') else ()
    extra = [str(root / name) for name in DRIVERS] if native else []
    if task.get('check_kind') == 'native-lint':
        extra += [str(root / '.lake/packages/batteries/.lake/build/bin/runLinter')]
    if task.get('check_kind') == 'native-style':
        extra += [str(root / '.lake/build/bin/lint-style')]
    value = check_binding(cwd, task.get('check_kind', 'source'), task['modules'], arguments,
                          raw + extra, runtime, toolchain=toolchain,
                          generated=digest(task['generated']) if task.get('generated') else None,
                          hash_file=hasher)
    roots = list(task['modules'])
    if runtime:
        roots += RUNTIME_MODULES
    value['reflective_imports'] = reflection.closure(roots) if reflection and native else None
    value['source_enrollment'] = paths if not native or task.get('check_kind') == 'native-style' else sorted(raw)
    value['selection'] = task['modules']
    value['facade_certificates'] = task.get('certificates')
    value['python_runtime'] = {'executable': hasher(Path(sys.executable)), 'version': sys.version,
                               'environment': {name: os.environ.get(name) for name in
                                   ('PYTHONPATH', 'PYTHONHOME', 'PYTHONHASHSEED', 'PYTHONDONTWRITEBYTECODE')}}
    return value
'''


class BindingEnrollmentTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='quillen-binding-enrollment-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for field, value in [('POLICY', ['policy.json', 'missing.toml']),
                             ('DRIVERS', ['drivers/run.lean']),
                             ('RUNTIME_MODULES', ['Checker.Runtime'])]:
            patcher = patch.object(adapter, field, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        self.write('policy.json', '{}')
        self.write('drivers/run.lean', '-- driver\n')
        self.write('Quillen/Unselected.lean', '-- source enrollment witness\n')
        self.write('Quillen/.lake/ignored.lean', '-- ignored\n')
        for name in ['Quillen.Target', 'Checker.Runtime']:
            relative = name.replace('.', '/')
            self.write(relative + '.lean', '-- selected fixture\n')
            self.write('.lake/build/lib/lean/' + relative + '.olean', 'native fixture')
            self.write('.lake/build/lib/lean/' + relative + '.ilean', 'metadata fixture')
            self.write('.lake/build/ir/' + relative + '.c', 'C fixture')
            self.write('.lake/build/lib/lean/' + relative + '.trace', json.dumps({
                'schemaVersion': '2025-09-10', 'depHash': '0' * 16,
                'outputs': {'m': False, 'o': '0' * 16 + '.olean',
                            'i': '0' * 16 + '.ilean', 'c': '0' * 16 + '.c'}}))
        namespace = dict(vars(adapter))
        exec(compile(LEGACY_BINDING_SOURCE, '<binding at 46d2386c>', 'exec'), namespace)
        self.legacy = namespace['legacy_binding']

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def task(self, kind):
        result = {'cwd': str(self.root), 'command': ['lean', 'generated.lean'],
                  'modules': ['Quillen.Target'] if kind else [],
                  'generated': '-- generated fixture\n', 'generated_argument_index': 1,
                  'certificates': {'fixture': 'retained'}}
        if kind:
            result['check_kind'] = kind
        return result

    def test_bindings_equal_legacy_across_source_and_native_branches(self):
        class Reflection:
            def closure(self, roots):
                return {'schema': 1, 'roots': sorted(roots), 'digest': digest(sorted(roots))}

        for kind in [None, 'source', 'native-style', 'native-lint', 'audit',
                     'scoped-lint', 'facade-text', 'diagnostic']:
            for observed in [False, True]:
                with self.subTest(kind=kind, observed=observed):
                    before = self.legacy(self.root, self.task(kind), {'fixture': 'compiler'},
                                         Reflection(), TemporalInputs() if observed else None)
                    after = adapter.binding(self.root, self.task(kind), {'fixture': 'compiler'},
                                            Reflection(), TemporalInputs() if observed else None)
                    self.assertEqual(before, after)

    def test_ordinary_native_checks_do_not_walk_source_tree(self):
        for kind in ['source', 'native-lint', 'audit', 'scoped-lint', 'facade-text', 'diagnostic']:
            with self.subTest(kind=kind), patch.object(
                    adapter.os, 'walk', side_effect=AssertionError('discarded enrollment walk')):
                value = adapter.binding(self.root, self.task(kind), None)
                self.assertNotIn(str(self.root / 'Quillen/Unselected.lean'), value['raw_inputs'])
                self.assertEqual(value['source_enrollment'], sorted([
                    str(self.root / 'policy.json'), str(self.root / 'missing.toml'),
                    str(self.root / 'Quillen/Target.lean')]))

    def test_source_and_native_style_still_enroll_unselected_sources(self):
        for kind in [None, 'native-style']:
            with self.subTest(kind=kind), patch.object(adapter.os, 'walk', wraps=adapter.os.walk) as walk:
                before = adapter.binding(self.root, self.task(kind), None)
                self.assertGreater(walk.call_count, 0)
            self.assertIn('Quillen/Unselected.lean', before['source_enrollment'])
            self.assertNotIn('Quillen/.lake/ignored.lean', before['source_enrollment'])
            self.write('Quillen/Unselected.lean', '-- changed unselected source\n')
            after = adapter.binding(self.root, self.task(kind), None)
            self.assertNotEqual(before['raw_inputs'], after['raw_inputs'])
            self.write('Quillen/Unselected.lean', '-- source enrollment witness\n')


if __name__ == '__main__':
    unittest.main()
