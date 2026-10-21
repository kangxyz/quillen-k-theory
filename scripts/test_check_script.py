#!/usr/bin/env python3
"""Bounded shared-launcher and CI publication contract tests; no Lean execution."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from check_run import main
from ci_adapter import QuillenAdapter, acquire_assessment_source

ROOT = Path(__file__).resolve().parents[1]


class LauncherTests(unittest.TestCase):
    def test_local_launcher_calls_application_check_with_same_selection(self):
        class Stub:
            def check(self, **kwargs):
                self.arguments = kwargs
                return {'status': 'complete'}
        application = Stub()
        application.adapter = QuillenAdapter()
        with patch('lean_ci.cli.load_application', return_value=application) as load, \
             patch('check_run.load_tooling'), \
             patch.object(sys, 'argv', ['check_run.py', '--base', 'accepted', '--progress', '/tmp/progress']):
            self.assertEqual(main(), 0)
        self.assertEqual(application.arguments['requested_base'], 'accepted')
        self.assertEqual(application.arguments['progress'], Path('/tmp/progress'))
        self.assertFalse(application.adapter.full)
        self.assertTrue(load.call_args.kwargs['local'])

    def test_no_unsafe_previous_push_or_publication_before_finalization(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        self.assertNotIn('github.event.before', workflow)
        self.assertNotIn('BASE_SHA', workflow)
        self.assertIn('kangxyz/aglib/.github/workflows/lean-ci.yml@', workflow)
        self.assertIn('build-targets: Quillen', workflow)
        self.assertNotIn('check_run.py ', workflow)


    def test_local_selector_enrollment_precedes_selection(self):
        adapter = QuillenAdapter()
        paths = adapter.local_inputs(ROOT)
        self.assertIn('scripts/ci_adapter.py', paths)
        self.assertIn('Quillen', paths)
        self.assertIn('examples/downstream/Consumer', paths)
        self.assertIn('lakefile.lean', paths)  # absent shadow/config candidate

    def test_same_pin_does_not_acquire_objects(self):
        with patch('ci_adapter.git', return_value='[[require]]\nname="Aglib"\nrev="' + 'a'*40 + '"'), \
             patch('ci_adapter.subprocess.run') as run:
            self.assertIsNone(acquire_assessment_source(ROOT, 'base', 'head'))
        run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
