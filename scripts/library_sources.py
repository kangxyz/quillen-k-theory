"""Source-only Lean import inventory; no Lake or checkpoint dependency."""
from pathlib import Path
import re

# Lean identifiers used as module components, including quoted identifiers.
IDENT = r'(?:[^\W\d][\w\u0080-\uffff\'!?]*|«[^»\n]+»)'
MODULE = re.compile(IDENT + r'(?:\.' + IDENT + r')*')
IMPORT_START = re.compile(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b', re.M)
KEYWORDS = {'import', 'public', 'private', 'meta', 'prelude', 'module', 'namespace',
            'section', 'end', 'open', 'set_option', 'noncomputable', 'universe',
            'variable', 'def', 'theorem', 'lemma', 'example', 'instance', 'abbrev',
            'axiom', 'constant', 'class', 'structure', 'inductive', 'attribute',
            'export', 'initialize', 'mutual', 'syntax', 'macro', 'elab'}


def strip_comments_and_strings(source: str) -> str:
    """Mask nested Lean comments and escaped strings, retaining token boundaries.

    A masked string is a non-whitespace sentinel, so an import cannot continue
    through a string into apparent module names later in the source.
    """
    result = list(source)
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                result[i:i + 2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                result[i:i + 2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n':
                    result[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            result[i:i + 2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                result[i] = ' '; i += 1
        elif source[i] == '"':
            result[i] = '#'; i += 1
            while i < len(source):
                char = source[i]
                if char != '\n':
                    result[i] = ' '
                i += 1
                if char == '\\' and i < len(source):
                    if source[i] != '\n':
                        result[i] = ' '
                    i += 1
                elif char == '"':
                    break
        elif source[i] == '«':
            # Comment/string delimiters inside a quoted identifier are literal.
            end = source.find('»', i + 1)
            i = len(source) if end < 0 else end + 1
        else:
            i += 1
    return ''.join(result)


def lean_imports(source: str) -> list[str]:
    """Read single/multiple/multiline imports with optional Lean modifiers."""
    clean = strip_comments_and_strings(source)
    imports = []
    for start in IMPORT_START.finditer(clean):
        position = start.end()
        while position < len(clean):
            while position < len(clean) and clean[position].isspace():
                position += 1
            match = MODULE.match(clean, position)
            if not match or match.group() in KEYWORDS:
                break
            # Normalize quoted ordinary identifiers to prevent namespace bypasses.
            token = re.sub(r'«([^»]+)»', lambda m: m[1] if
                           re.fullmatch(r'[^\W\d]\w*', m[1]) else m[0], match.group())
            imports.append(token)
            position = match.end()
    return imports


def project_imports(source: str) -> list[str]:
    return [module for module in lean_imports(source)
            if module == 'Quillen' or module.startswith('Quillen.')]


def module_path(module: str) -> Path:
    parts = [part[1:-1] if part.startswith('«') else part
             for part in re.findall(IDENT, module)]
    return Path(*parts[:-1], parts[-1] + '.lean')


def module_name(path: Path | str) -> str:
    return Path(path).with_suffix('').as_posix().replace('/', '.')


def source_modules(root: Path) -> set[Path]:
    return {Path('Quillen.lean')} | {
        path.relative_to(root) for path in (root / 'Quillen').rglob('*.lean')}


def test_modules(root: Path) -> set[Path]:
    """Positive trust tests have a separate generated integration root."""
    if not (root / 'QuillenTest').exists() and not (root / 'QuillenTest.lean').exists():
        return set()
    return {Path('QuillenTest.lean')} | {
        path.relative_to(root) for path in (root / 'QuillenTest').rglob('*.lean')}


def downstream_sources(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in (root / 'examples/downstream').rglob('*.lean')
            if '.lake' not in path.relative_to(root).parts}


def import_closure(root: Path, entrypoints: list[str | Path]) -> set[Path]:
    seen: set[Path] = set()
    pending = [Path(path) for path in entrypoints]
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        if not (root / path).is_file():
            raise ValueError(f'Missing project import source: {path}')
        seen.add(path)
        pending.extend(module_path(module)
                       for module in project_imports((root / path).read_text()))
    return seen
