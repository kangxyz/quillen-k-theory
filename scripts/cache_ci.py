#!/usr/bin/env python3
"""Fetch scoped Mathlib artifacts with serialized, capped compiler launches."""
from contextlib import contextmanager
from pathlib import Path
import sys


@contextmanager
def serialized_frontend(lean: Path):
    """Keep Lake's asynchronous jobs from overlapping compiler processes."""
    original = lean.with_name('lean-capped')
    lean.rename(original)
    lock = lean.with_name('lean.lock')
    try:
        lean.write_text(
            '#!/usr/bin/env python3\n'
            'import fcntl, subprocess, sys\n'
            f'with open({str(lock)!r}, "a") as lock:\n'
            '    fcntl.flock(lock, fcntl.LOCK_EX)\n'
            f'    result = subprocess.run([{str(original)!r}, *sys.argv[1:]])\n'
            '    code = result.returncode\n'
            '    raise SystemExit(code if code >= 0 else 128 - code)\n')
        lean.chmod(0o755)
        yield
    finally:
        original.replace(lean)


def main():
    if len(sys.argv) < 4:
        print('Usage: cache_ci.py AGLIB_SCRIPTS RECEIPT MODULE...', file=sys.stderr)
        return 2
    sys.path.insert(0, sys.argv[1])
    from build_serial import capped_toolchain
    from resource_guard import run
    with capped_toolchain(Path.cwd()) as environment:
        with serialized_frontend(Path(environment['LEAN'])):
            return run(['lake', 'exe', 'cache', 'get', *sys.argv[3:]],
                       env=environment, receipt=Path(sys.argv[2]))


if __name__ == '__main__':
    raise SystemExit(main())
