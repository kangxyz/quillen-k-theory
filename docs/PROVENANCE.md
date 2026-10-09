# Initial source provenance

The initial release is extracted from the user-supplied archive
`quillen-k-theory-checkpoint-20261009-1455.tar.gz`.

- Archive SHA-256: `ce80f298c01b311b8eb36b9bcb2633483efb111f01533a430f1652925cb6c8bc`.
- Checkpoint timestamp: `2026-10-09T14:55:00Z`.
- Original library source inventory: 1,033 Lean modules.
- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

Every original module under `Quillen/` is retained byte for byte, including its
imports, definitions, proofs, namespace choices, and hypotheses. The original
`Quillen.lean` integration entrypoint is replaced by a generated exhaustive
entrypoint, and new import-only subject facades are added. The root and
downstream dependency manifests and toolchains retain their original pins.

The supplied archive remains the historical checkpoint artifact. Its
`CHECKPOINT.json`, raw `logs/`, and checkpoint packager/verifier are not part of
normal library development and are omitted from this repository. Their member
hashes describe the old archive rather than the evolving repository.
Mathematical notes, audit source, downstream examples, and the historical
[status report](history/STATUS_20261009_1455.md) are retained.

This extraction changes organization and publication tooling; it does not
complete any open theorem or assign a new mathematical review status. The
release's actual build and trust checks appear in [RELEASE.md](RELEASE.md).
Future changes use ordinary Git history, review, and CI rather than editing a
permanent ledger of the initial proofs.
