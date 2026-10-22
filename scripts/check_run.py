#!/usr/bin/env python3
"""Run the shared native checks for the Quillen Lake package."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def load_tooling(root, tooling_root=None):
    """Load an installed distribution or an explicitly selected tooling checkout."""
    value = tooling_root or os.environ.get('LEAN_CI_TOOLING_ROOT')
    if value:
        checkout = Path(value).expanduser().resolve()
        package = checkout / 'scripts'
        if not (package / 'lean_ci/__init__.py').is_file():
            raise ValueError('Tooling checkout does not provide scripts/lean_ci: ' + str(checkout))
        sys.path.insert(0, str(package))
        os.environ['LEAN_CI_TOOLING_ROOT'] = str(checkout)
    try:
        import lean_ci
    except ImportError as error:
        raise ValueError('Install pinned lean-incremental-ci or set LEAN_CI_TOOLING_ROOT') from error
    return lean_ci



def resource_config():
    from lean_ci.resources import ResourceConfig
    return ResourceConfig(prefix='QUILLEN', profile_keys=('R5_LEAN_REMOTE_PROFILE',),
                          memory_keys=('AGLIB_LEAN_MEMORY_MB',), rss_keys=('AGLIB_RSS_LIMIT_MB',),
                          build_thread_keys=('AGLIB_BUILD_THREADS',))


def main(argv=None):
    try:
        load_tooling(ROOT)
        from lean_ci.cli import main as native_main
        source_checks = tuple((sys.executable, str(ROOT / 'scripts' / script), '--root', '.') for script in
                              ('check_library_layout.py', 'check_placeholders.py'))
        return native_main(['check', *(sys.argv[1:] if argv is None else argv)],
                           root=ROOT, production=('Quillen',), source_checks=source_checks,
                           resource_config=resource_config(), environment=dict(os.environ))
    except (OSError, ValueError, ImportError, subprocess.SubprocessError) as error:
        print('Check error: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    raise SystemExit(main())
