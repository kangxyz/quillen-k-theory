# Whole target action and reference reanchoring

Research archive notice (0.10.0): application-specific raw-route modules described below have been archived where indicated by their links; they are not active library imports. Retained results and useful exposition remain here. See the [archive scope and restoration guide](../../../../docs/RESEARCH_ARCHIVE.md). The final maintained construction is documented in [TensorBassConstruction](TensorBassConstruction.md).

Fix a coefficient arrow `f : a ⟶ b`, a Model `V`, references
`E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))`, and a
specified natural isomorphism `δ : E'.functor ≅ E.functor`. Put
`U = normalizedMap (coefficientMap P f)` and
`δU = isoWhiskerRight δ U.functor`.

The original ordinary scalar cone action commutes strictly with the original
reference reanchoring:

```
(Reanchor.cone P b (E ≫ U) (E' ≫ U) δU).comp (TargetCone.coneMap P f E)
  = (TargetCone.coneMap P f E').comp (Reanchor.cone P a E E' δ).
```

`TargetCone.coneMap_reanchor_square`, in
[`BassProjectionFourEdgeTargetConeReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetConeReanchor.lean),
proves this equality of continuous maps. `coneMap_reanchor` is its pointwise
version, and `coneMap_reanchor_family` preserves any supplied continuous
scalar family `p : C(T, scalarCone P a E)` for arbitrary topological `T`.
There are no compactness, dimension or connectedness assumptions on `T`.
In particular, external cube coordinates and old loop/seed times can remain
independent product factors.

## Complete scalar restrictions

The proof retains every original constructor and reference anchor:

- [`TargetChartReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetChartReanchor.lean)
  proves full-node and whole-parameter naturality of each genuine
  polynomial-source chart. The positive and inverse charts keep their
  separate original projection equalities.
- [`TargetTreeReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetTreeReanchor.lean)
  combines these two sectors with the four original overlap cylinders using
  six-cell extensionality.
- [`TargetSurfaceReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetSurfaceReanchor.lean)
  retains the complete terminal reference anchor and proves the entire old
  target-surface square, at every comparison time.
- [`TargetLaurentReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetLaurentReanchor.lean)
  proves the action square on every original Laurent point, not only on the
  beta image. The source and terminal reference transports are both retained.
- [`TargetSpanReference`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetSpanReference.lean)
  and [`TargetSpanReanchor`](../../../../../archives/tt-raw-route-20261020T1521Z/source/Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetSpanReanchor.lean)
  prove the whole target-span square before beta. The genuine polynomial
  map, the original five-node polynomial square, the asymmetric original
  half/quarter/quarter clocks and the central overlap all remain unchanged.

On the source cone, the whole Laurent baseline uses the Laurent square and
the original tip is fixed. The original lower half uses the entire surface
square, while the original upper half uses the entire target-span square.
Finite pushout extensionality then proves the whole cone result. Full-node
equalities precede realization throughout; equality after native evaluation
and native injectivity are not assumptions.

## Scope

This is a closure theorem for the displayed, actually constructed coefficient
cone action and input-reference change. It does not supply lifts of arbitrary
native families, a uniform higher-stage Bass successor, or compatible
extensions for all higher-stage original faces. The specified weak-zero
localization null is a separate primitive; isomorphism reanchoring does not
replace or choose that null.
