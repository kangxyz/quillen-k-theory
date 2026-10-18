# Metric order complexes and numerable domination

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Topology.MetricOrderComplex.RealizationHomotopyEquiv`](RealizationHomotopyEquiv.lean) | Vertex-fixed weak/metric realization and based-loop homotopy equivalences |
| [`Topology.MetricOrderComplex.Equiconnection`](Equiconnection.lean), [`Topology.MetricOrderComplex.LoopEquiconnection`](LoopEquiconnection.lean) | Actual metric connector and compact-open loop convex geometry |

## Metric realization equivalence and local equiconnection

`Topology.MetricOrderComplex.RealizationReconstruction` proves exact set-level
reconstruction. `FiniteCharts`, `CutoffRealization`,
`Topology.Realization.CylinderContinuity` and `RealizationHomotopyEquiv` supply
a continuous cutoff-reconstruction reverse map to the original coordinate map,
with actual homotopies fixed at every vertex and a compact-open based-loop
homotopy equivalence. The unrestricted raw set inverse is not asserted
continuous, and no homeomorphism between the two topologies is claimed.
See the [metric-equivalence client](../../../examples/downstream/Consumer/MetricOrderHomotopyEquiv.lean).

`CommonMass`, `CommonPoint`, `CommonPointContinuity`, `AffineSegment` and
`Equiconnection` prove a jointly continuous local connector on the open domain
of positive common mass, equivalently L1 distance less than two. The identity
`2 * commonMass + distance = 2` controls moving-support tails. Two affine
segments pass through the normalized common point; each support is a genuine
chain, using intersection support rather than a false union-chain claim.
The connector has exact endpoints and fixes the whole diagonal. Shared positive
coordinates persist, yielding connector-convex open vertex stars. See the
[metric-connector client](../../../examples/downstream/Consumer/MetricOrderEquiconnection.lean).

## Actual numerable nerve domination

`Topology.MetricSpace.CoverRadius` constructs a positive Lipschitz subordinate
radius for an arbitrary open cover of a metric space. Its one-eighth balls
give the actual point-star refinement in `MetricPointStarRefinement`.
Metric paracompactness supplies a subordinate partition of unity. No uniform
Lebesgue number or compactness of the metric space is assumed.

`OrderedConnectorInterpolation`, `ConnectorSimplexFaces` and
`ConnectorMonoCoherence` construct order-sensitive finite interpolation,
carrier preservation, and face/mono coherence. The raw interpolation is not
asserted coherent under degeneracies. `OrderedNerveRealizationMap` instead
defines `nerveReturnMap` through the nondegenerate-simplex colimit. On a
degenerate simplex, its canonical epimorphism to the unique nondegenerate
image first pushes forward and sums repeated weights, before interpolation.
No associativity of the local connector is assumed.

`FiniteNerveCharts` and `POUNerveClassifier` construct `partitionNerveMap`
into the actual weak ordered-cover-nerve realization, using the original
partition coefficients. Local finite closed-support control proves continuity
in that weak topology; coordinatewise continuity is not a replacement.
`NumerableRealizationDomination` uses point-star convex carriers and the
original connector to construct `numerableDominationHomotopy`, from the
actual return-after-classifier composite to the identity. Its theorem
`exists_numerable_realization_domination` constructs the simplicial set,
both continuous maps and the homotopy from the displayed cover, vertices,
convexity, point-star refinement and subordinate partition data.

`MetricRealizationDomination` derives these inputs for a metric space with an
actual local connector and open connector-convex cover. Thus
`MetricOrderComplex.LoopDomination` constructs domination for the literal
metric-order loop space, and `ClassifyingSpace.LoopDomination` transports it
to original categorical loops. `RankedChainOrder.universalLoopDominationData`
retains independent object and morphism universes `u, v`, with a simplicial
model in `max u v`. A chosen inverse or domination certificate is not an
input to this construction. This is the geometric bridge used by the exact original-Q comparison.
See the [nerve-return](../../../examples/downstream/Consumer/OrderedNerveReturn.lean)
and [numerable-domination](../../../examples/downstream/Consumer/NumerableDomination.lean)
clients.
