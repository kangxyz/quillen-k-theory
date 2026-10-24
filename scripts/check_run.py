#!/usr/bin/env python3
"""Select installed tooling or the explicitly requested checkout, then dispatch."""
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def main(argv=None, action=('check',)):
    checkout = os.environ.get('LEAN_CI_TOOLING_ROOT')
    if checkout:
        package = Path(checkout).expanduser().resolve() / 'scripts'
        if not (package / 'lean_ci/__init__.py').is_file():
            print('Tooling checkout does not provide scripts/lean_ci: ' + str(package.parent), file=sys.stderr)
            return 2
        sys.path.insert(0, str(package))
    try:
        from lean_ci.cli import main as native_main
        from lean_ci.quillen import options as required_library_policy
    except ImportError:
        print('Install lean-incremental-ci 0.3 or newer, or select its checkout with LEAN_CI_TOOLING_ROOT', file=sys.stderr)
        return 2
    arguments = list(sys.argv[1:] if argv is None else argv)
    return native_main([*action, *arguments], root=ROOT)


if __name__ == '__main__':
    raise SystemExit(main(['--root', str(ROOT), *sys.argv[1:]]))
