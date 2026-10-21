#!/usr/bin/env python3
"""Fetch scoped Mathlib artifacts with serialized, capped compiler launches."""
from contextlib import contextmanager
from pathlib import Path
import subprocess
import sys

LOCATORS = ('--print-prefix', '--githash')


@contextmanager
def serialized_frontend(lean: Path, metadata: dict[str, bytes]):
    """Keep Lake's asynchronous jobs from overlapping compiler processes."""
    original = lean.with_name('lean-capped')
    lean.rename(original)
    lock = lean.with_name('lean.lock')
    try:
        lean.write_text(
            '#!/usr/bin/env python3\n'
            'import fcntl, os, subprocess, sys\n'
            # Lake may prepend its real toolchain bin to the compiler's PATH.
            'os.environ["PATH"] = os.path.dirname(__file__) + os.pathsep + os.environ.get("PATH", "")\n'
            f'metadata = {metadata!r}\n'
            # Imported Cache.IO initializers must not launch another real Lean.
            'if len(sys.argv) == 2 and sys.argv[1] in metadata:\n'
            '    sys.stdout.buffer.write(metadata[sys.argv[1]])\n'
            '    raise SystemExit(0)\n'
            f'with open({str(lock)!r}, "a") as lock:\n'
            '    fcntl.flock(lock, fcntl.LOCK_EX)\n'
            f'    result = subprocess.run([{str(original)!r}, *sys.argv[1:]])\n'
            '    code = result.returncode\n'
            '    raise SystemExit(code if code >= 0 else 128 - code)\n')
        lean.chmod(0o755)
        yield
    finally:
        original.replace(lean)


def guarded_cache(lean: Path, modules: list[str]) -> int:
    """Run only inside the outer resource guard's owned process group."""
    metadata = {}
    for action in LOCATORS:
        result = subprocess.run([str(lean), action], stdout=subprocess.PIPE)
        if result.returncode:
            return result.returncode if result.returncode >= 0 else 128 - result.returncode
        metadata[action] = result.stdout
    # Both locator children have completed and been reaped before any compiler.
    with serialized_frontend(lean, metadata):
        result = subprocess.run(['lake', 'exe', 'cache', 'get', *modules])
    return result.returncode if result.returncode >= 0 else 128 - result.returncode


def main():
    if len(sys.argv) < 4:
        print('Usage: cache_ci.py AGLIB_SCRIPTS RECEIPT MODULE...', file=sys.stderr)
        return 2
    if sys.argv[1] == '--guarded-cache':
        return guarded_cache(Path(sys.argv[2]), sys.argv[3:])
    sys.path.insert(0, sys.argv[1])
    from build_serial import capped_toolchain
    from resource_guard import run
    with capped_toolchain(Path.cwd()) as environment:
        return run([sys.executable, str(Path(__file__).resolve()), '--guarded-cache',
                    environment['LEAN'], *sys.argv[3:]],
                   env=environment, receipt=Path(sys.argv[2]))


if __name__ == '__main__':
    raise SystemExit(main())
