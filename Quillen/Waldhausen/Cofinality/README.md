# Cofinality interfaces

## Dense cofinality and degree zero

The input `h` of type
[`Cofinality.DenseCofiberData W P`](DenseSubcategory.lean)
contains membership of zero, invariance along weak arrows, extension and quotient
closure for cofiber squares, and a complement `B` with `P (A ⨿ B)` for every `A`.
With `[HasBinaryCoproducts C]` these construct the dense full subcategory and grading.

With `D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)`
and the corresponding `Fibration.RowFactorization.SecondEndpointSection`,
`h.inclusionKEquivGeneral D hs n` compares
the subcategory's `K (n + 1)` with `W.K (n + 1)` by inclusion.
`inclusion_KMap_injective_general` covers every degree. Separately,
`inclusion_KZero_exact_general` gives an injective K₀ inclusion, its range as the
kernel of change to `h.grading.nested.coarse`, and surjectivity onto that coarse
K₀ endpoint. K₀ inclusion surjectivity is not asserted. These original-map results
allow independent `u, v`.
