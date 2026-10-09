# The original relative-row ordinal transitions are weakly cartesian

## Actual endpoint

`Quillen.Waldhausen.Fibration.RelativeRows.rowTransitionComparison_isWeakHomotopyEquivalence`
proves the complete weak-equivalence property of the original constant-path
comparison for every ordinal map between actual relative rows. Its sole
structural input is `NestedWeakEquivalences V`, for `C : Type u` with
`Category.{u} C`. Genuine degreewise additivity is invoked from the accepted
`RelativeRows.Realization` theorem.

The comparison's parameter is the original realized tail, its source is the
original realized ordinal restriction, and its entire path is literally
constant at the composite base image. `rowTransitionComparison_apply` retains
these three coordinates by reflexivity. The result includes actual component
surjectivity and every finite based homotopy-set bijection, including dimension
zero and arbitrary source points.

## Proof and precise naturality requirement

The generic layer `Topology/Realization/SplitFiberCartesian.lean` starts with
actual row comparisons to simplicial products, their genuine realization
homotopy equivalences with the prescribed forward maps, a commuting tail
square, and a strictly natural split inclusion. It proves the exact identity

`target first projection ∘ original fiber transition ∘ source split inclusion = identity`.

The source split inclusion and target first projection already induce all
finite homotopy-set bijections. Complete empty-aware weak cancellation proves
the original fiber transition weak. Connectedness of the source realization,
base realization and common first factor then gives weak cartesianness of the
original canonical comparison through the proved fiber/LES detection theorem.

First-object evaluation is not assumed outer-natural. Only the original tail
square and split inclusion are natural. No continuous family of inverses or
paths is selected. No unrestricted realization/product homeomorphism is used.

The actual relative-row wrapper supplies the genuine connectedness instances
and chosen Waldhausen zero point, and transports the projections using their
proved exact equalities with the original tail maps.

## Checked boundary

- `Quillen/Topology/Realization/SplitFiberCartesian.lean`
- `Quillen/Waldhausen/Fibration/RelativeRows/TransitionCartesian.lean`

Source manifest: `logs/split-row-transition-cartesian-sources.sha256`.
Both sources and twelve exact-map consumers checked warning-free. The origin
scan found eleven declarations, including generated equation/proof constants;
only `propext`, `Classical.choice` and `Quot.sound` occur recursively.
`audits/SplitRowTransitionCartesianAudit.lean` fixes that count. The consumers
cover source and full path coordinates, original fiber transitions, actual
relative-row maps, dimension zero and component surjectivity.

This proves the original transition-square inputs to realization gluing. The
finite weak-cartesian pushout theorem and global connected-row diagonal fiber
comparison remain separate obligations.
