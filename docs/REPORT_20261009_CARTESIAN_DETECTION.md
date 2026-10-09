# Original-map weak-cartesian detection

The frozen source `Quillen/Topology/HomotopyFiber/CartesianDetection.lean`
compiles warning-free. Its manifest is `logs/cartesian-detection-sources.sha256`.

For an actual commuting square `g ∘ a = b ∘ f`, `transitionFiber` is the
original induced homotopy-fiber map, retaining the original postcomposed
path. `comparisonFiber` is the fiber map of the actual canonical map into
the homotopy pullback. An explicit homotopy slides the intermediate point
along its path, assigning its prefix to the inner path and retaining the
suffix as the outer path. It fixes the original constant-path basepoint.

`comparisonFiber_bijective` transfers every finite based homotopy-set
bijection, including dimension zero, from the original transition to the
comparison fiber map. `comparison_bijective_of_fiberMap` then applies the
proved long exact sequence and path transport to show that the canonical
square comparison induces bijections in all degrees at every source point.
It assumes actual connected source and base, a connected target fiber, and
an explicit source point over the supplied base point. Thus the source is
nonempty and the homotopy-pullback target is genuinely path connected;
there is no vacuous empty-source weak-equivalence assertion.

The own recursive origin audit scanned all 25 declarations and the nine
actual-map/path/fixed-basepoint/all-degree/explicit-degree-zero consumers
passed. The count-frozen audit is `audits/CartesianDetectionAudit.lean`.
This is a local square theorem. No global diagonal fiber theorem or weak
pushout-cube theorem is asserted in this boundary.
