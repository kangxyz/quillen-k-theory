# Recoverable research sources

## Incoming TT research group

The supplied 2026-10-20 recovery package contains 268 application-specific
raw-route production sources, 27 dedicated tests and 27 downstream clients in
[the frozen source manifest](archive/tt-raw-route-20261020T1521Z/MANIFEST.json).
Its [staging manifest](archive/tt-raw-route-20261020T1521Z/STAGING-MANIFEST.json)
preserves 188 duplicate staging sources. Five original guide snapshots and the
producer's historical classifications, hashes and recovery metadata are retained
byte-for-byte in the same directory. Four additional incoming route guides are
identified by [their exact hashes](archive/tt-raw-route-20261020T1521Z/INCOMING-GUIDES.json).

These sources were already archived by the supplied recovery package. None of
the 268 production paths belonged to accepted library commit `25387c65`.
This integration therefore imports a research archive rather than deleting
those modules from the maintained library. The incoming package's 0.10.0 label
is preserved as provenance; the live dependency and compiler configuration
continues to use the accepted library basis.

The archive is outside `Quillen/`, `QuillenTest/` and the downstream `Consumer/`
source roots. It is not enrolled by their generated entries. The live tensor
proof has its own source closure and does not depend on this archive.
Lean payloads are stored as `.lean.txt` data files, with the original bytes
unchanged. The [storage map](archive/tt-raw-route-20261020T1521Z/STORAGE.json)
records the correspondence to the historical manifests' `.lean` paths.
Historical manifests, receipt references and guide snapshots describe their
original source/layout and acceptance scope. They do not supply a current
whole-library validation or a completed prescribed raw-model comparison.

## Source recovery

Use the maintained [restoration helper](archive/restore_sources.py) from the
repository root. First inspect the planned recovery into an explicit existing
directory:

```sh
python3 docs/archive/restore_sources.py /absolute/path/to/repository --dry-run
```

Omit `--dry-run` to restore the 322 source files. `--staging` selects only the
188 staging duplicates. The helper reads the `.lean.txt` payloads and restores
their original `.lean` destination names. It verifies every selected member and existing
destination before writing, rejects redirected paths and symlinks, skips
identical files, and refuses to overwrite different content. It publishes new
files without clobbering existing files. Its focused tests are in
[test_restore_sources.py](archive/test_restore_sources.py).

The frozen group's original `restore.py` and README are historical data. Their
old sibling-directory instructions are superseded by this maintained entry;
they are not the restoration procedure for the integrated layout.
After source recovery, regenerate imports and run the affected checks before
adopting any restored source. Recovery itself is not mathematical acceptance.

## Terminal-chart compatibility snapshot

The former 115-line
`MWholeNerveTerminalChartComparisonClients.lean` implementation contained ten
theorems whose statements and proofs directly repeated their live canonical
owner. Its [snapshot and alias map](archive/terminal-chart-clients-20261021/MANIFEST.json)
preserve the original bytes and exact correspondence.
The snapshot also uses a `.lean.txt` data filename.

The live module keeps all ten public names as deprecated aliases to
`MWholeNerveTerminalChartComparison`. Every original hypothesis, chart sign,
universe and independent coordinate is retained by those canonical types.
The snapshot is for comparison and provenance; the research-group restoration
helper does not replace this live compatibility module.

The inventory of the supplied recovery snapshot found no exact source
duplicates. Of its 127 implementation leaves without active internal consumers,
126 were retained after a bounded reuse review. Known R5 callers use two of
those leaves, and several others provide documented generic interfaces or distinct endpoint identities. A
consumer count alone is not a redundancy or deletion certificate.
