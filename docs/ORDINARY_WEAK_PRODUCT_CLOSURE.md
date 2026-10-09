# Complete weak equivalences of literal topological product maps

`IsWeakHomotopyEquivalence.prodMap` proves the complete empty-aware weak
property of the original continuous map `(x,y) ↦ (f x,g y)`. The source and
target factors may have four independent universes. No connectedness,
nonemptiness, separation or local compactness assumptions are used.

`homotopyProdMap` is the actual pair of projection maps on generalized
homotopy sets. `homotopyProdMap_bijective` pairs actual loops and their full
boundary-relative homotopies, for every index type, including `Fin 0`.
`homotopyProdMap_succ` agrees literally with the existing positive-dimensional
`piProdMap`, preserving its original group operations.

Strict naturality identifies the original product map on homotopy sets with
the pair of original factor maps. Actual component paths pair pointwise, so
component surjectivity is proved separately. Empty factors are covered.
`prodMap_id` and `id_prodMap` retain the original untouched-factor maps.

This concerns ordinary topological products. It asserts no realization/product
homeomorphism and makes no weak-to-strong upgrade.

## Validation

Source: `Quillen/Topology/HomotopyGroups/ProductWeakEquivalence.lean`.
Frozen manifest: `logs/ordinary-weak-product-sources.sha256`.
The source and thirteen consumers passed their first check warning-free.
`audits/OrdinaryWeakProductAudit.lean` recursively checks exactly nine origins,
including generated projection proofs, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Consumers cover independent universes,
all-index projections, the literal original positive group maps, strict
naturality, component paths, dimension zero, both untouched-factor maps, and
each empty-factor case.

The source/audit first check is in
`logs/square-bar-fiber-he-fixed18-product-check.log`; the fixed-count rerun is
recorded in `logs/ordinary-weak-product-fixed9.log`.
