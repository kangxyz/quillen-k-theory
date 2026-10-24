#!/usr/bin/env python3
"""Compatibility entry for lean-ci quillen imports."""
import sys
from check_run import ROOT, main

if __name__ == '__main__':
    raise SystemExit(main(['--root', str(ROOT), *sys.argv[1:]], action=('quillen', 'imports')))
