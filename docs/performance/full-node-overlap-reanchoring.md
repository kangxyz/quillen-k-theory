> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#full-node-overlap-reanchoring) · [Context](original-context.md) · [Case index](README.md) · [Previous record](evaluation-unit-comparison-proofs.md) · [Next record](shared-cache-metadata-during-final-checks.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Full-node overlap reanchoring

The concrete `overlap_reanchor` proof in
[`BassProjectionFourEdgeTargetOverlapReanchor`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetOverlapReanchor.lean)
compares the original complete 31-node carrier surfaces. Directly specializing
finite-parameter naturality exhausted the default 200,000-heartbeat budget
during weak-head normalization. A declaration-local 400,000 trial also failed.

The retained proof first states the transport over abstract Model arrows and
whole dependent-node families. Its concrete application unfolds only the
outer overlap composite, fixes the finite index to 31 nodes, and supplies the
original `nodes_reanchor` equations before evaluation. All four public
statements, canonical data, two clocks and external parameter conditions are
unchanged. Compilation and the selected environment/text checks pass at the
default 200,000 budget and 12,800 MiB frontend limit; this module retains no
heartbeat override.

The [continuation record](../evidence/TTCheckpointContinuation20261019.json)
identifies the source and validation scope. This is a successful proof-typing
repair, without a claim of general or measured speedup.

The polynomial anchor in
[`GlobalRawBassInputCompositionTerminalColumns`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputCompositionTerminalColumns.lean)
exhausted the same default budget when
converting an 18-node projection reference. Its retained proof applies a
private whole-functor transport lemma to the original equality transports and
composition isomorphism. All five public statements, canonical nodes, normalized
pullbacks, anchors and clocks are unchanged; this proof also compiles with no
heartbeat override. The continuation record distinguishes both repairs and
their actual dependency and validation bases.

The associativity proof in
[`SupportedRawPullbackCoherence`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedRawPullbackCoherence.lean)
uses the original ambient pullback comparison after applying the faithful
forgetful functor. A private reflexive object equation and explicit functor
and arrow projection simplifications make that same comparison available to
the elaborator. The associator, transports, hypotheses and public statements
are unchanged. The evidence record keeps its original targeted dependency
basis separate from the final dependency upgrade.

