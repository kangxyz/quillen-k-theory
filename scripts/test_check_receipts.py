#!/usr/bin/env python3
"""Receipt projections preserve recorded fields without claiming proof coverage."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_receipts import project


class ReceiptProjectionTests(unittest.TestCase):
    def test_completed_receipt_omits_bulk_and_unrecorded_compiler_counts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'providers-0.json'
            data = dict(state='completed', exit_code=0, peak_rss_bytes=12345,
                        command=['lake', 'build', 'Quillen.P'], limits={'lean_threads': 1},
                        last_members=[{'executable': 'lean'}] * 1000)
            path.write_text(json.dumps(data))
            before = path.read_bytes()
            summary = project(path, root)
            self.assertEqual(summary, dict(phase='providers-0', receipt=str(path),
                                          state='completed', exit_code=0, peak_rss_bytes=12345))
            self.assertNotIn('compiler_count', summary)
            self.assertEqual(path.read_bytes(), before)

    def test_failure_retains_native_signal_and_recorded_count(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'client-audit.json'
            path.write_text(json.dumps(dict(state='completed', exit_code=-15,
                                            compiler_count=2, guard_failure='RSS cutoff',
                                            owned_group_gone=False)))
            summary = project(path, root)
            self.assertEqual(summary['exit_code'], -15)
            self.assertEqual(summary['compiler_count'], 2)
            self.assertEqual(summary['failure_summary'], 'RSS cutoff')
            self.assertFalse(summary['owned_group_gone'])
            self.assertNotIn('peak_rss_bytes', summary)

    def test_cli_skips_scope_and_includes_cache_receipt_with_exact_locators(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve() / 'checks'
            root.mkdir()
            (root / 'scope.json').write_text(json.dumps(dict(providers=['Quillen.P'])))
            path = root / 'lint.json'
            path.write_text(json.dumps(dict(state='running', command=['lake', 'env', 'lean'])))
            cache = Path(str(root) + '-cache.json')
            cache.write_text(json.dumps(dict(state='completed', exit_code=0)))
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('check_receipts.py')),
                                     str(root)], text=True, capture_output=True, check=True)
            records = [json.loads(line) for line in result.stdout.splitlines()]
            self.assertEqual(records.pop(0)['receipt_counts'], dict(total=2, emitted=2, omitted=0))
            self.assertEqual([record['receipt'] for record in records], [str(path), str(cache)])
            self.assertNotIn('exit_code', records[0])
            self.assertFalse(any('coverage' in record for record in records))

    def test_cli_caps_total_output_prioritizes_failures_and_locates_full_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            for index in range(8):
                data = dict(state='completed', exit_code=0, compiler_count=100)
                if index == 6:
                    data['exit_code'] = 23
                if index == 7:
                    data['guard_failure'] = 'RSS cutoff'
                (root / f'phase-{index}.json').write_text(json.dumps(data))
            (root / 'scope.json').write_text(json.dumps(dict(providers=['Quillen.P'])))
            environment = dict(os.environ, GITHUB_RUN_ID='42', GITHUB_RUN_ATTEMPT='2',
                               GITHUB_REPOSITORY='fixture/quillen', GITHUB_SERVER_URL='https://github.example')
            result = subprocess.run([sys.executable, str(Path(__file__).with_name('check_receipts.py')),
                                     str(root), '--limit', '3'], env=environment,
                                    text=True, capture_output=True, check=True)
            header, *records = [json.loads(line) for line in result.stdout.splitlines()]
            self.assertEqual(header['receipt_counts'], dict(total=8, emitted=3, omitted=5))
            self.assertEqual([record['phase'] for record in records], ['phase-6', 'phase-7', 'phase-0'])
            self.assertEqual(header['full_receipts'], dict(
                directory=str(root), artifact_name='quillen-check-receipts-42-2',
                artifact_run_url='https://github.example/fixture/quillen/actions/runs/42#artifacts'))
            self.assertNotIn('compiler_count', header)
            self.assertTrue(all(record['compiler_count'] == 100 for record in records))
            self.assertNotIn('coverage', result.stdout)


if __name__ == '__main__':
    unittest.main()
