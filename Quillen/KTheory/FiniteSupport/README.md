# Positive finite-support K-theory

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.FiniteSupport.Decomposition` | Positive finite-support K-equivalence by original evaluations and finite sums of original inclusions |

## Field determinants and finite-support K-theory

The finite-support construction computes the original positive Quillen groups
by their original coordinate maps. The field construction identifies the
original upper finite-module Q K1
with field units by determinant, including the literal positive matrix-cube
equation over every field and in every finite rank.

## Actual finite-support families

For a small abelian family `C`, `CategoryTheory.Pi.FiniteCategoryFamily C` is
the full subcategory of actual families `M` with finite
`{i | not IsZero (M i)}`. The
[general family modules](../../Aglib/CategoryTheory/Pi/README.md)
provide pointwise exactness, finite stages, restriction, zero extension, and
singleton inclusion. Zero extension is equivalent to the original stage even
when its off-support objects are arbitrary zero objects.

Import
[`Quillen.KTheory.FiniteSupport.Decomposition`](Decomposition.lean).
The public `Quillen.FiniteSupport.decompositionKEquiv C n` has type

```text
Additive (K_(n+1)(FiniteCategoryFamily C))
  ≃+ directSum_i Additive (K_(n+1)(C_i)).
```

The exact structure is the standard abelian one. The hypotheses are an index
`I : Type u`, coordinates `C i : Type (max u v)` with homs in the same
`max u v` universe, and abelian coordinate categories. The index can be smaller
than the categories; coherent small models in `u+1` are included.

`decompositionKEquiv_apply` identifies each coordinate with the original
`finiteCategoryEvaluation.KMap`. `decompositionKEquiv_singleton` sends the
original `singletonExactInclusion.KMap` to `DirectSum.of`.
`decompositionKEquiv_symm_apply` identifies the inverse with the finite sum of
these original inclusion maps over the actual support. Empty support is
included. `K1DecompositionEquiv` and `K2DecompositionEquiv` are the required
degree specializations; no K0 direct-sum theorem is asserted.

The proof uses the original finite-product projections, a strict diagram of
actual finite-stage Q-categories, a proved nerve colimit, and common zero
vertices. `FilteredStages.stageKMap_eq_raw` proves the rebasing equation to the
original normalized K-map. It does not assume strictness of normalized Q
functors or a categorical continuity result as background data.

The separate
[upper-universe client](../../../examples/downstream/Consumer/LowDegreeFieldSupport.lean)
inhabits the original-coordinate K1 interface and lifts every finite K2 family
by the original inclusion maps. It selects universes explicitly with
`K1DecompositionEquiv.{u, u + 1}` and `K2DecompositionEquiv.{u, u + 1}`.
