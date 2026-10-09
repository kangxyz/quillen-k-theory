# Actual realization model for double cylinders

`Quillen/Topology/Realization/DoubleCylinder.lean` defines the simplicial double cylinder as the actual pushout of the two simplicial interval endpoints and the original coproduct of the attaching maps. Geometric realization preserves that pushout. The checked interval-cylinder isomorphism and actual binary-sum isomorphism identify its defining span with the unchanged topological double-cylinder span.

For simplicial maps `f : X ⟶ Y`, `g : X ⟶ Z`, and any displayed topological pushout `sq` of their original realizations, `DoubleCylinder.realizationHomeomorph f g sq` is an actual homeomorphism from the simplicial double-cylinder realization to the displayed pushout. The original cylinder and end legs have exact forward-map formulas. The inverse laws follow from genuine pushout uniqueness.

`DoubleCylinderCompactGraph.lean` transports compact-test graph closure through that actual homeomorphism. Its `compactMap_isClosed_graph`, `compactMap_matching_isClosed`, and `compactMap_pullback_quotient` retain the unchanged displayed base and literal pullback quotient. The last theorem requires the test parameter to be compact and locally compact. The test, quotient source, and quotient target have independent universes. No global Hausdorff instance or arbitrary quotient-pullback preservation is assumed.

This supplies the closed matching locus needed by finite-parametric collar lifting. It does not supply that lifting or the remaining global homotopy-fiber gluing theorem.

## Validation

Both sources compiled warning-free, then were frozen in `logs/realization-double-cylinder-sources.sha256`. An ordered source recheck and exhaustive recursive audit passed all 40 defining-module origins and 12 exact consumers, with only `propext`, `Classical.choice`, and `Quot.sound`. Terminal status: 2026-10-09 13:19:55 UTC. All frozen source hashes matched afterward.

Audit: `audits/RealizationDoubleCylinderAudit.lean`.
Initial checked audit: `audits/exploratory/RealizationDoubleCylinderAuditInitial.lean`.
Log: `logs/realization-double-cylinder-audit-initial.log`.
The final audit has an explicit fixed-40 guard for independent replay; no redundant author rerun is claimed. Independent acceptance is recorded separately.
