# Relative obstruction and cone homology

## Obstruction and vanishing

`Topology.HomotopyCofiber.UnreducedFirstObstruction` uses the actual iterated
fiber-path and simply-connected interfaces to prove relative first-obstruction
geometry. The constant-chain, mapping-cylinder, point-relative and finite-boundary
owners culminate in `Topology.HomotopyCofiber.UnreducedConeHomology`: actual
relative finite-chain witnesses and positive homology vanishing for the
unreduced cone, starting from the original constant-chain `QuasiIso` hypothesis. The full relative-homology/cone comparison isomorphism is not
implemented; its critical-path vanishing consequence is available.

See [first-obstruction](../../../examples/downstream/Consumer/UnreducedFirstObstruction.lean),
[finite relative-boundary](../../../examples/downstream/Consumer/PointRelativeHomology.lean)
and [cone-homology](../../../examples/downstream/Consumer/UnreducedConeHomology.lean)
clients for the displayed hypotheses and maps.
