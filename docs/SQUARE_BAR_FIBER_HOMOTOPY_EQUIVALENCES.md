# Genuine equivalences of the original square and two-sided-bar fibers

## Generic original-map endpoint

`HomotopyFiber.mapHomotopyEquivOfEquivalences e eb sq a` is a genuine homotopy
equivalence between the original path-space fibers of a strictly commuting
square. Its inputs are genuine homotopy equivalences of total and base spaces.
Its forward map is definitionally the original
`HomotopyFiber.map e.toFun eb.toFun sq a`.

The source coordinate is literally `e` of the old source. The entire path is
literally postcomposition of the old path by `eb.toFun`; no padding or
reparameterization occurs in this forward map. The spaces may be empty and
need no connectedness, separation or local compactness assumptions. The scope
is one arbitrary common universe, matching the existing pullback machinery.

## Proof

The actual source projection `HomotopyPullback q eb.toFun → Y` is a genuine
homotopy equivalence because `eb` is. Its composite with the canonical
constant-path comparison is exactly `e.toFun`; genuine homotopy-equivalence
cancellation therefore gives the canonical comparison itself as a genuine
homotopy equivalence.

`HomotopyFiber.sourceEquiv` gives a genuine equivalence on the corresponding
fibers over the unchanged parameter base. Its forward map is exactly
`comparisonFiber`. The accepted explicit prefix/suffix homotopy identifies
this with `baseFiberComparison` after the original square fiber map.
`baseFiberHomotopyEquiv`, homotopy invariance, and genuine cancellation yield
the original square fiber map with actual continuous inverse and inverse
homotopies. This uses no weak-to-strong or Whitehead argument.

## Actual bar augmentations

`TwoSidedBar.dropFiberHomotopyEquiv` and
`TwoSidedBar.evaluationFiberHomotopyEquiv` apply the generic theorem to the
already proved genuine total/base bar augmentation equivalences. Their forward
maps are definitionally the unchanged `dropFiberMap` and `evaluationFiberMap`.
The latter targets the original diagonal fiber. Earlier weak bar-fiber results
remain unchanged.

These are unbased space equivalences with exact original forward maps. The
existing based homotopy-group API applies using any actual equality of the
forward basepoint image; no basedness of a selected inverse is assumed.

## Validation

Frozen source manifest: `logs/square-bar-fiber-he-sources.sha256`.
Both sources compiled warning-free on their first check. The recursive scan
passed all eighteen module-origin declarations, including generated proofs,
using only `propext`, `Classical.choice` and `Quot.sound`.
`audits/SquareBarFiberHomotopyEquivalenceAudit.lean` fixes that count and checks
nineteen consumers: original comparison/fiber forward maps, entire source and
path coordinates, both actual inverse homotopies, explicit dimension zero,
original group-map identification, empty fibers, and both original bar maps.
The fixed-count rerun is recorded in `logs/square-bar-fiber-he-fixed18-product-check.log`.

Finite weak-cartesian gluing and the global relative diagonal fiber theorem
remain separate obligations.
