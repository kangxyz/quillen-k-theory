# Independent review: actual relative split-fiber inclusion

Accepted 2026-10-09 08:46 UTC. The three exact sources in
`logs/relative-rows-split-fiber-sources.sha256` passed complete semantic inspection,
fresh isolated compilation, a fixed 35-origin recursive axiom audit, and 24
original-map consumers, all warning-free. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. Before/after source hashes match. The fresh dependency paths
are recorded in `logs/relative-split-independent-build.log`.

The one-step row genuinely consists of the original objects zero, X, zero.
Exactness uses the existing exact identity/zero-arrow embeddings and pointwise
pushouts; it does not assume arbitrary ambient pushouts. Pulling this row back
along the collapse ordinal yields the actual exact relative-row inclusion.
The original first object and map are unchanged, the whole tail is the actual
chosen zero row, and outer reindexing is strictly compatible. The zero-row
formula includes every component map. All structural statements retain
independent object and hom universes.

The independent consumers include actual degree-zero rows, original object and
morphism evaluation, exactness, chosen-zero preservation, and both first and
tail equalities after arbitrary outer reindexing. This is a structural input to
relative additivity. No relative-row realization equivalence, weak-cartesian
gluing theorem, or global fibration conclusion is asserted.

Replay: `/tmp/quillen-split-fiber-review-0843.sh` in this workspace; retained audit
`audits/RelativeRowsSplitFiberIndependentAudit.lean` and the
`logs/relative-split-independent-*` logs contain the portable verification record.
