# Compact Hausdorff pushouts along closed embeddings

`Quillen/Topology/Pushout/CompactHausdorff.lean` supplies a generic topological
prerequisite for finite-realization separation arguments.

## Exact endpoint

For `A B C D : TopCat.{u}`, the original maps `i : A ⟶ B`, `f : A ⟶ C`,
`g : B ⟶ D`, `j : C ⟶ D`, and an actual `sq : IsPushout i f g j`:

- `compactSpace_pushout sq` proves `CompactSpace D` from `CompactSpace B` and
  `CompactSpace C` alone.
- `t2Space_pushout_of_compact_closedEmbedding sq hi` proves `T2Space D` from
  `CompactSpace B`, `T2Space B`, `CompactSpace C`, `T2Space C`, and
  `hi : IsClosedEmbedding i`.

No compactness or separation assumption on `A`, and no separation or product
comparison assumption on `D`, is supplied. Compactness of `A` follows from its
closed embedding in `B`. The result applies to the displayed topological pushout
with its actual colimit topology, without replacing the topology or the maps.

## Proof and supporting endpoints

`pushout_sum_surjective sq` proves the original sum of the two legs is onto using
the actual underlying set pushout. Its continuous image proves compactness.

`isClosedMap_pushout_left_of_compact sq hi` needs only compactness of `A` and
Hausdorffness of `C`. For a closed cell subset `W`, the inverse image of its image
on the old space is `f '' (i ⁻¹' W)`. This is compact, hence closed. Its inverse
image on the cell is the union of `W` and the closed attaching-locus image over
that set. The actual colimit-topology criterion makes `g '' W` closed in `D`.
Together with the previously proved closedness of the right leg, this makes the
original sum map closed.

`t2Space_of_closed_surjection` is a generic independent-universe helper. A closed
continuous surjection from compact Hausdorff `X` to T₁ `Y` makes `Y` Hausdorff:
the two compact fibers have separated open neighborhoods; complements of images
of their complements are disjoint open neighborhoods downstairs. In the pushout
application, the existing proved T₁ closed-embedding pushout theorem supplies
T₁, so no separation conclusion is hidden in the endpoint assumptions.

The module reuses the existing genuine closed-embedding, complement injectivity,
and T₁ proofs from `Realization/EdgePathPresentation/Interiors.lean`. No existing
implementation source was changed. This module proves no finite-realization,
product-realization, or K-theory comparison itself.

## Authored verification boundary

The final direct source check is warning-free. The defining-origin audit
`audits/CompactHausdorffPushoutAudit.lean` has a fixed count of **5**, recursively
allowing only `propext`, `Classical.choice`, and `Quot.sound`. Consumers test the
independent-universe closed-surjection helper, compactness without any separation
input, the weaker actual-cell-leg closedness theorem, and both final pushout
properties without supplying an `A` instance. All checks use `lean -j1` and the
shared slot1 lock, with acquisition logging.

Frozen source and exact evidence: `logs/compact-hausdorff-pushout-20261009/`.
`sources.sha256` fixes the production source; `check3.log` is the clean source
check, `audit-final.log` is the fixed-count audit, `rehash.log` verifies source
stability, and `artifacts.sha256` records this authored verification boundary.
Independent acceptance is delegated to the parent reviewer.
