"""Focused safety and byte-recovery tests; never execute historical restore.py."""

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).absolute().parent
spec = importlib.util.spec_from_file_location('safe_restore_sources', HERE / 'restore_sources.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)


class RestoreTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='restore-test-')
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name).resolve()
        self.archive = self.base / 'archive'
        self.target = self.base / 'repository'
        self.archive.mkdir()
        self.target.mkdir()
        self.files = []
        for name in ('A', 'Z'):
            path = f'Quillen/{name}.lean'
            data = f'-- {name}\n'.encode()
            source = self.archive / 'source' / (path + '.txt')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(data)
            self.files.append(dict(path=path, archive_path='source/' + path,
                                   sha256=hashlib.sha256(data).hexdigest(),
                                   bytes=len(data), action='move_after_verification'))
        self.manifest()

    def manifest(self):
        (self.archive / 'MANIFEST.json').write_text(json.dumps({'files': self.files}))

    def refused(self):
        with self.assertRaises((ValueError, OSError)):
            helper.restore(self.archive, self.target)

    def test_real_full_group_and_certificate(self):
        archive = HERE / helper.ARCHIVE
        expected = {'MANIFEST.json': 'f9320b39ab821894de5298002fe934602ed4487251543ebeb574c82c7189124f',
                    'STAGING-MANIFEST.json': 'd850376ea08ff68d327f38e4fef0b979b0f07e7f0c40ff47562f3a9d4805fff1'}
        for name, digest in expected.items():
            self.assertEqual(hashlib.sha256((archive / name).read_bytes()).hexdigest(), digest)
        source = json.loads((archive / 'MANIFEST.json').read_bytes())['files']
        source = [x for x in source if x['action'] == 'move_after_verification']
        mapping = {x['path']: x['sha256'] for x in source}
        self.assertEqual(len(mapping), 322)
        self.assertEqual([sum(x['path'].startswith(p) for x in source)
                          for p in ('Quillen/', 'QuillenTest/', 'examples/')], [268, 27, 27])
        staging = json.loads((archive / 'STAGING-MANIFEST.json').read_bytes())['files']
        self.assertEqual(len(staging), 188)
        for item in staging:
            self.assertTrue(item['canonical_sources'])
            for canonical in item['canonical_sources']:
                self.assertEqual(canonical['sha256'], item['sha256'])
                # The declared duplicate may be a retained live source rather than
                # a member of the restored group; independently compare its hash.
                path = canonical['original_path']
                candidate = archive / 'source' / (path + '.txt')
                if not candidate.exists():
                    candidate = HERE.parent.parent / path
                self.assertEqual(hashlib.sha256(candidate.read_bytes()).hexdigest(), item['sha256'])
        for mode, count in ((False, 322), (True, 188)):
            dry = helper.restore(archive, self.target, staging=mode, dry_run=True)
            self.assertEqual(dry, dict(selected=count, identical=0, created=0, dry_run=True))
            if not mode:
                self.assertEqual(list(self.target.iterdir()), [])
            result = helper.restore(archive, self.target, staging=mode)
            self.assertEqual(result['created'], count)
            again = helper.restore(archive, self.target, staging=mode)
            self.assertEqual((again['created'], again['identical']), (0, count))
            members = staging if mode else source
            for item in members:
                self.assertEqual((self.target / item['path']).read_bytes(),
                                 (archive / (item['archive_path'] + '.txt')).read_bytes())
        self.assertEqual(len(list(self.target.rglob('*.lean'))), 510)

    def test_corrupt_member_blocks_all_writes(self):
        (self.archive / (self.files[-1]['archive_path'] + '.txt')).write_bytes(b'corrupt')
        self.refused()
        self.assertEqual(list(self.target.iterdir()), [])

    def test_historical_storage_is_not_a_fallback(self):
        for item in self.files:
            stored = self.archive / (item['archive_path'] + '.txt')
            stored.rename(self.archive / item['archive_path'])
        self.refused()
        self.assertEqual(list(self.target.iterdir()), [])

    def test_conflicting_file_untouched(self):
        conflict = self.target / self.files[-1]['path']
        conflict.parent.mkdir()
        conflict.write_bytes(b'keep this')
        self.refused()
        self.assertEqual(conflict.read_bytes(), b'keep this')
        self.assertFalse((self.target / self.files[0]['path']).exists())

    def test_bad_paths_and_fields(self):
        original = self.files[0].copy()
        cases = [('path', '../escape.lean'), ('path', '/absolute.lean'),
                 ('path', 'Quillen/../escape.lean'), ('path', 'Quillen//A.lean'),
                 ('archive_path', 'source/../escape.lean'),
                 ('archive_path', '/source/Quillen/A.lean'),
                 ('archive_path', 'staging/Quillen/A.lean'),
                 ('archive_path', 'source/Quillen/A.lean.txt'),
                 ('path', 'Quillen/A.lean.txt'), ('path', 'docs/A.lean'),
                 ('sha256', '0' * 63), ('bytes', True), ('action', 'unknown')]
        for key, value in cases:
            with self.subTest(key=key, value=value):
                self.files[0] = dict(original, **{key: value})
                self.manifest()
                self.refused()
                self.assertEqual(list(self.target.iterdir()), [])

    def test_destination_parent_and_leaf_symlinks(self):
        outside = self.base / 'outside'
        outside.mkdir()
        (self.target / 'Quillen').symlink_to(outside, target_is_directory=True)
        self.refused()
        self.assertEqual(list(outside.iterdir()), [])
        (self.target / 'Quillen').unlink()
        (self.target / 'Quillen').mkdir()
        (self.target / self.files[0]['path']).symlink_to(outside / 'missing')
        self.refused()
        self.assertEqual(list(outside.iterdir()), [])

    def test_source_symlink_and_manifest_symlink(self):
        member = self.archive / (self.files[-1]['archive_path'] + '.txt')
        other = self.base / 'payload'
        member.rename(other)
        member.symlink_to(other)
        self.refused()
        self.assertEqual(list(self.target.iterdir()), [])
        member.unlink()
        other.rename(member)
        manifest = self.archive / 'MANIFEST.json'
        other = self.base / 'manifest'
        manifest.rename(other)
        manifest.symlink_to(other)
        self.refused()

    def test_source_parent_and_root_symlinks(self):
        source = self.archive / 'source'
        outside = self.base / 'source'
        source.rename(outside)
        source.symlink_to(outside, target_is_directory=True)
        self.refused()
        alias = self.base / 'alias'
        alias.symlink_to(self.target, target_is_directory=True)
        with self.assertRaises(OSError):
            helper.restore(self.archive, alias)

    def test_duplicate_destinations_and_json_keys(self):
        self.files.append(self.files[0].copy())
        self.manifest()
        self.refused()
        (self.archive / 'MANIFEST.json').write_text('{"files": [], "files": []}')
        self.refused()

    def test_interruption_resumes_and_late_conflict_never_clobbers(self):
        publish = helper.publish
        def interrupted(root, path, data):
            if path == self.files[-1]['path']:
                raise KeyboardInterrupt
            return publish(root, path, data)
        with mock.patch.object(helper, 'publish', side_effect=interrupted):
            with self.assertRaises(KeyboardInterrupt):
                helper.restore(self.archive, self.target)
        result = helper.restore(self.archive, self.target)
        self.assertEqual((result['identical'], result['created']), (1, 1))
        path = 'Quillen/Late.lean'
        (self.target / path).write_bytes(b'concurrent writer')
        with helper.root_directory(self.target) as root:
            with self.assertRaises(ValueError):
                publish(root, path, b'archive')
        self.assertEqual((self.target / path).read_bytes(), b'concurrent writer')
        self.assertEqual(list(self.target.rglob('.restore-*')), [])


if __name__ == '__main__':
    unittest.main()
