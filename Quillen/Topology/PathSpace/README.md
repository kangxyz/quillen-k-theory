# Compact-open path and loop spaces

## Compact-open loop geometry

`Topology.LocalEquiconnection.Loops` constructs the pointwise connector on
literal based paths with their original compact-open topology. Compactness
of the interval proves that its permitted pair domain is open; the
whole-diagonal identity fixes both endpoints. `LoopConvexCover` shrinks a
finite interval subcover to compact pieces, producing actual open
connector-convex neighborhoods of every based loop. `Topology.PathSpace.Metric`
retains the original path topology.

`Topology.MetricOrderComplex.LoopEquiconnection` applies these constructions
to metric-order vertex loops, with an actual convex-open cover. The
[loop-geometry client](../../../examples/downstream/Consumer/MetricOrderLoops.lean)
checks the maps and neighborhoods. The existing
`Topology.HomotopyEquiv.BasedReplacement`, `BasedLoop` and
`Topology.ClassifyingSpace.PosetLoop` interfaces supply the compact-open loop
comparison used to transport this geometry.
