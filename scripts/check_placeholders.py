#!/usr/bin/env python3
"""Reject proof placeholders/custom assumptions, ignoring Lean comments and strings.

The kernel dependency audit in audits/LibraryAudit.lean remains the authoritative check.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
failed = False
sources = [root / 'Quillen.lean', *sorted((root / 'Quillen').rglob('*.lean'))]
sources += [p for folder in ['examples', 'audits'] for p in (root / folder).rglob('*.lean')
            if '.lake' not in p.relative_to(root).parts]
for path in sources:
    source = path.read_text()
    clean = list(source)
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                clean[i:i+2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                clean[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': clean[i] = ' '
                i += 1
        elif quoted:
            if source[i] == '\\' and i + 1 < len(source):
                clean[i:i+2] = '  '; i += 2
            else:
                if source[i] == '"': quoted = False
                if source[i] != '\n': clean[i] = ' '
                i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end == -1: end = len(source)
            clean[i:end] = ' ' * (end-i); i = end
        elif source.startswith('/-', i):
            clean[i:i+2] = '  '; depth = 1; i += 2
        elif source[i] == '"':
            clean[i] = ' '; quoted = True; i += 1
        else:
            i += 1
    for match in re.finditer(r'\b(sorry|admit|axiom)\b', ''.join(clean)):
        line = source.count('\n', 0, match.start()) + 1
        print(f'{path.relative_to(root)}:{line}: forbidden token {match.group()}')
        failed = True
if failed:
    sys.exit(1)
print('Source-token audit passed: no proof placeholders or custom assumptions.')
