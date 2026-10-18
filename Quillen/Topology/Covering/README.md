# Coverings and path classes

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.Covering.Pullback`](Pullback.lean), `PullbackFiber` | Shared literal mixed-universe matching pairs, actual covering/kernel pi1 equivalence and mapAt fiber-pi1 equivalence with original projection and connecting equations |
| [`Topology.Covering.PathClassPrebundle`](PathClassPrebundle.lean), [`Topology.Covering.LocalConnectorHypotheses`](LocalConnectorHypotheses.lean) | Actual surjective path-class cover from original local geometry |
| [`Topology.Covering.PathClassEndpoint`](PathClassEndpoint.lean), [`Topology.Covering.PathClassSimplyConnected`](PathClassSimplyConnected.lean) | Exact path-class endpoint equation and genuinely simply connected chart-topologized total |
| [`Topology.Covering.HomotopyPullbackTransfer`](HomotopyPullbackTransfer.lean), [`Topology.Covering.LocalConnectorTransfer`](LocalConnectorTransfer.lean) | Actual pullback cover transfer under the displayed homotopy equivalence |

## Supplied coverings and regular chains

`Topology.Realization.SimplexConnectivity`, `Topology.Covering.SingularSimplices`
and `Topology.Covering.PathClasses` construct the connectivity and actual
lifting/path-class tools for a supplied covering. `Topology.LocalCoefficients`
owners `RegularChains`, `CoveringChains`, `RegularFunctoriality` and
`CoveringNaturality` supply the displayed regular-chain identification and its
functoriality. The regular-chain identification requires a supplied cover with
simply connected total space and a chosen point; arbitrary-cover lifting is a
separate result. Its common-model universe and explicit `ULift` coefficient
convention are part of the statements.

These chain identifications retain the displayed supplied cover and its
simply connected total space. The path-class endpoint/universality construction
proves simple connectedness for its actual chart-topologized total
space under the stated local geometric assumptions. This does not remove
hypotheses from unrelated supplied-cover interfaces. The
[covering-chain client](../../../examples/downstream/Consumer/RegularCoveringChains.lean)
and the [path-class client](../../../examples/downstream/Consumer/CoveringPathClasses.lean)
exercise the actual maps and paths.
