#!/usr/bin/env python3
"""Restore the research-only TT archive into an explicit existing directory.

Default: 322 source files. --staging: only the 188 duplicate staging files.
--dry-run validates without creating directories. Payloads are stored at
historical archive_path + ".txt" and restored to the unchanged .lean destination.
No facade or version changes are made. Restoration is not mathematical
acceptance. Requires POSIX dir_fd,
O_NOFOLLOW and hard links. Stop other processes from relocating directories
while restoring; descriptor traversal prevents symlink redirection, but cannot
prevent a privileged actor moving an already-open directory outside the root.
An interrupted run can be rerun: identical files are skipped. A killed process
may leave an unreferenced .restore-* temporary file, which is never consumed.
"""

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import uuid

ARCHIVE = 'tt-raw-route-20261020T1521Z'
DIRECTORY = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def relative(value):
    """Reject aliases, traversal, platform separators and noncanonical paths."""
    if (not isinstance(value, str) or not value or '\\' in value
            or any(ord(c) < 32 for c in value)
            or any(c in ('', '.', '..') for c in value.split('/'))
            or value.startswith('/') or ':' in value):
        raise ValueError(f'Unsafe relative path: {value!r}')
    return value.split('/')


@contextmanager
def directory(root, parts, create=False):
    """Walk relative to an anchored descriptor, never following symlinks."""
    fd = os.dup(root)
    try:
        for part in parts:
            if create:
                try:
                    os.mkdir(part, dir_fd=fd)
                except FileExistsError:
                    pass
            child = os.open(part, DIRECTORY, dir_fd=fd)
            os.close(fd)
            fd = child
        yield fd
    finally:
        os.close(fd)


@contextmanager
def root_directory(path):
    # abspath would silently collapse '..'; reject it before normalization.
    raw = os.fspath(path)
    if '..' in raw.split('/'):
        raise ValueError('Root must not contain parent traversal')
    absolute = os.path.abspath(raw)
    fd = os.open('/', DIRECTORY)
    try:
        with directory(fd, absolute.split('/')[1:] if absolute != '/' else []) as root:
            yield root
    finally:
        os.close(fd)


def read_file(root, path):
    parts = relative(path)
    with directory(root, parts[:-1]) as parent:
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                     dir_fd=parent)
        with os.fdopen(fd, 'rb') as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                raise ValueError(f'Not a regular file: {path}')
            return stream.read()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'Duplicate JSON field: {key}')
        result[key] = value
    return result


def entries(root, staging):
    name = 'STAGING-MANIFEST.json' if staging else 'MANIFEST.json'
    manifest = json.loads(read_file(root, name), object_pairs_hook=unique_object)
    if not isinstance(manifest, dict) or not isinstance(manifest.get('files'), list):
        raise ValueError('Manifest must contain a files array')
    selected, seen = [], set()
    for item in manifest['files']:
        if not isinstance(item, dict):
            raise ValueError('Manifest member must be an object')
        if not staging:
            if item.get('action') == 'preserve_original_document_snapshot':
                continue
            if item.get('action') != 'move_after_verification':
                raise ValueError('Unknown source action')
        path, source, digest, size = (item.get(k) for k in
                                     ('path', 'archive_path', 'sha256', 'bytes'))
        relative(path)
        relative(source)
        prefixes = ('tmp/',) if staging else ('Quillen/', 'QuillenTest/',
                                              'examples/downstream/Consumer/')
        if not path.startswith(prefixes) or not path.endswith('.lean'):
            raise ValueError(f'Unexpected destination: {path}')
        if source != ('staging/' if staging else 'source/') + path:
            raise ValueError(f'Unexpected archive path: {source}')
        if not isinstance(digest, str) or not re.fullmatch('[0-9a-f]{64}', digest):
            raise ValueError(f'Malformed SHA256: {path}')
        if type(size) is not int or size < 0 or path in seen:
            raise ValueError(f'Invalid size or duplicate destination: {path}')
        seen.add(path)
        selected.append((path, source + '.txt', digest, size))
    if not selected:
        raise ValueError('Empty source group')
    return selected


def existing(root, path, data):
    try:
        current = read_file(root, path)
    except FileNotFoundError:
        return False
    if current != data:
        raise ValueError(f'Refusing overwrite: {path}')
    return True


def publish(root, path, data):
    parts = relative(path)
    with directory(root, parts[:-1], create=True) as parent:
        temporary = '.restore-' + uuid.uuid4().hex
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o644, dir_fd=parent)
        try:
            with os.fdopen(fd, 'wb') as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            with directory(root, parts[:-1]) as current:
                a, b = os.fstat(parent), os.fstat(current)
                if (a.st_dev, a.st_ino) != (b.st_dev, b.st_ino):
                    raise ValueError(f'Destination parent changed: {path}')
                try:
                    os.link(temporary, parts[-1], src_dir_fd=parent,
                            dst_dir_fd=current, follow_symlinks=False)
                except FileExistsError:
                    # A concurrent identical publisher is safe; all others fail.
                    if not existing(root, path, data):
                        raise ValueError(f'Destination disappeared during publication: {path}')
                    return False
                os.fsync(current)
            return True
        finally:
            os.unlink(temporary, dir_fd=parent)


def restore(archive, repository, *, staging=False, dry_run=False):
    """Preflight the whole selection, then publish missing files without clobber."""
    with root_directory(archive) as source, root_directory(repository) as target:
        prepared = []
        for path, archived, digest, size in entries(source, staging):
            data = read_file(source, archived)
            if len(data) != size or hashlib.sha256(data).hexdigest() != digest:
                raise ValueError(f'Archive checksum/size mismatch: {archived}')
            present = existing(target, path, data)
            prepared.append((path, data, present))
        created = 0
        if not dry_run:
            for path, data, present in prepared:
                if not present:
                    created += publish(target, path, data)
        return {'selected': len(prepared), 'identical': sum(x[2] for x in prepared),
                'created': created, 'dry_run': dry_run}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path, help='Existing destination directory')
    parser.add_argument('--staging', action='store_true', help='Select only staging duplicates')
    parser.add_argument('--dry-run', action='store_true', help='Validate without writing')
    args = parser.parse_args()
    try:
        # Do not resolve: resolving would hide symlinks in the helper/archive path.
        result = restore(Path(os.path.abspath(__file__)).parent / ARCHIVE,
                         args.repository, staging=args.staging, dry_run=args.dry_run)
    except (OSError, ValueError) as error:
        parser.exit(1, f'Restoration refused: {error}\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
