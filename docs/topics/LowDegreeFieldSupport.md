# Field determinants and finite-support K-theory

The finite-support construction computes the original positive Quillen groups
by their original coordinate maps. The field construction computes the stable
elementary quotient by determinant and transports it to projective Q K1. Its
identification with the separately specified positive matrix cube remains an
explicit geometric comparison.

## Actual finite-support families

For a small abelian family `C`, `CategoryTheory.Pi.FiniteCategoryFamily C` is
the full subcategory of actual families `M` with finite
`{i | not IsZero (M i)}`. The
[general family modules](../../Quillen/Aglib/CategoryTheory/Pi/README.md)
provide pointwise exactness, finite stages, restriction, zero extension, and
singleton inclusion. Zero extension is equivalent to the original stage even
when its off-support objects are arbitrary zero objects.

Import
[`Quillen.KTheory.FiniteSupport.Decomposition`](../../Quillen/KTheory/FiniteSupport/Decomposition.lean).
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
[upper-universe client](../../examples/downstream/Consumer/LowDegreeFieldSupport.lean)
inhabits the original-coordinate K1 interface and lifts every finite K2 family
by the original inclusion maps. It selects universes explicitly with
`K1DecompositionEquiv.{u, u + 1}` and `K2DecompositionEquiv.{u, u + 1}`.

## Stable determinant and the original projective comparison

Import
[`Quillen.Algebra.Group.StableFieldDeterminant`](../../Quillen/Algebra/Group/StableFieldDeterminant.lean).
In `Quillen.StableGeneralLinear`, `det` is defined on the actual stable matrix
group over every commutative ring. Over every field, `ker_det` identifies its
kernel with the actual stable elementary subgroup, and `quotientDetEquiv`
identifies the actual elementary quotient with field units. Finite matrix
values and the literal ring-change square are proved. Rank zero and small
finite fields have no exceptional hypotheses.

[`ElementaryProjectiveKOne`](../../Quillen/KTheory/Field/ElementaryProjectiveKOne.lean)
composes the original elementary-quotient/completion and positive Q
comparisons. Its ring-change theorem retains the specified basepoint tracks.
[`ProjectiveDeterminant`](../../Quillen/KTheory/Field/ProjectiveDeterminant.lean)
defines `StableCompletion.projectiveDetEquiv` by the inverse of that composite.
Its matrix equation uses the original stable-completion representative, and
its scalar-extension square uses `rightBaseChangeExact`.

The finite-projective/finite-module and explicit opposite-ring comparisons
are in `ProjectiveFiniteModules` and `FiniteModuleRingEquivalence`.
`ScalarExtensionComparison` compares native right base change with literal
finite-module tensor extension, including the actual upper SmallModel K-map
square. These transports preserve the original objects and functors.

[`ModuleDeterminant`](../../Quillen/KTheory/Field/ModuleDeterminant.lean)
defines `Quillen.Field.moduleDetEquiv` on the actual
`(finiteModuleExactStructure F).SmallK.{u+1} 1`, with literal tensor-extension
naturality and determinant on the transported native completion representative.
This is still an unmarked determinant until the separate cube equation below
has been proved.

## Remaining boundary

The literal capped Q automorphism cube and coordinate transpose are constructed
in `Quillen.KTheory.Automorphism`. Their comparison with the original
completion representative is a separate family-of-paths theorem. Until it is
proved, the transported determinant is unmarked; the requested equation
`D_Q(positiveMatrixCube(g)) = det(g)` is not claimed.

No Matsumoto theorem, residue-field assembly, finite-field G2 vanishing,
low-degree localization action, or origin-DVR unit generation follows merely
from the constructions above. Their dependencies and selected next proofs are
recorded in the [implementation plan](../development/LowDegreeFieldSupport.md).
