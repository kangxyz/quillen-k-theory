# Field determinants and finite-support K-theory

The finite-support construction computes the original positive Quillen groups
by their original coordinate maps. The field construction identifies the
original upper finite-module Q K1
with field units by determinant, including the literal positive matrix-cube
equation over every field and in every finite rank.

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
[`MatrixCubeComparison`](../../Quillen/KTheory/Field/MatrixCubeComparison.lean)
proves `Quillen.Field.moduleDetEquiv_matrix_cube`: this same determinant
sends the literal `Automorphism.Cube.automorphismFirstCube` of the original
upper-small matrix automorphism to `Matrix.GeneralLinearGroup.det g`.
The theorem covers every field and every rank, including zero. The proof
uses the actual finite-stage localized homotopy, standard-matrix coordinate
transport, and inverse-first/right-cap normalization. It does not require
a global completion-to-positive H-map.

## Native Dedekind residue support

Import
[`Quillen.GTheory.Dedekind.ResidueFieldAssembly`](../../Quillen/GTheory/Dedekind/ResidueFieldAssembly.lean).
For a commutative Dedekind domain `R`,
`Quillen.DedekindResidue.residueFieldAssemblyKEquiv R n` identifies

```text
directSum_p Additive (G(p.asIdeal.ResidueField, n+1))
  ≃+ Additive (SupportedG(R⁰, n+1)).
```

The target is exactly the native torsion-support term of finite-module
localization. Primary decomposition, actual ideal-power filtrations and
quotient-ring dévissage prove the equivalence. The canonical algebra map
`R/p → p.asIdeal.ResidueField` supplies the original scalar-restriction
comparison. `residueFieldAssemblyKEquiv_of` and its finite-sum formula retain
the original support pushforwards. `supportedKMap_comp_residueFieldAssembly`
retains the sum of original R-restrictions into ambient G-theory. No
residue-field finiteness assumption is needed. K1 and K2 specializations are
explicit; the source is finite-module G-theory in the same native universe.

[`Dedekind.Localization`](../../Quillen/GTheory/Dedekind/Localization.lean)
detects the positive generic image by all native residue coordinates. Under
the explicit premise that the original generic G1 map is injective, every
finite residue-G1 family is the boundary of one generic G2 class, retaining
both the raw boundary-to-assembly equation and every coordinate.
[`LocalDvrBoundaryNaturality`](../../Quillen/GTheory/Dedekind/LocalDvrBoundaryNaturality.lean)
identifies the original local-DVR boundary after actual generic tensor
extension with each global residue coordinate in degrees
`G(n+2) → G(n+1)`. Its kernel-intersection theorem and finite-family lift
retain these actual local boundaries and the original generic-G1-injectivity
premise.

[`Affine.UniverseComparison`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/UniverseComparison.lean)
provides `publicSpecGRingEquiv` in all degrees for Noetherian rings, through
model-universe transport of the same original coherent category. The
residue-field comparison preserves the original public scheme pushforward.
[`Affine.LocalizationNaturality`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/LocalizationNaturality.lean)
identifies literal `Scheme.pullbackG` for localization at any submonoid with
original finite-module localization in every degree. The comparison with
`Scheme.boundaryG` remains open.

For geometric support, the general candidate
[`FiniteClosed`](../../Quillen/Aglib/AlgebraicGeometry/Modules/Coherent/Support/FiniteClosed.lean)
proves exact finite-S coherent splitting on a locally Noetherian scheme when
each point of S is closed. Its forward functor is the original sum of
singleton inclusions.
[`FiniteClosedFamilies`](../../Quillen/Aglib/AlgebraicGeometry/Modules/Coherent/Support/FiniteClosedFamilies.lean)
constructs the canonical finite-family equivalence for an injective family
of closed points on a locally Noetherian scheme. On a Noetherian scheme
ordinary support containment in that point range implies finite support.

[`FinitePointAssembly`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/ClosedImmersion/FinitePointAssembly.lean)
then supplies `fieldAssemblyKEquiv` in every positive degree, including K1
and K2. Its hypotheses are a Noetherian `X : Scheme.{u}`, an index
`I : Type u`, an injective closed-point family, and closed immersions
`Spec (fields i) ⟶ X` from specified fields with those singleton images.
The target is actual support containment in the original upper-small
coherent category. Singleton, finite-sum and ambient equations identify
the forward map with the original public field-scheme pushforwards.

## Native Milnor symbols

[`MilnorK2.Basic`](../../Quillen/KTheory/MilnorK2/Basic.lean), `Map` and `Symbols`
preserve the original R5 integer tensor quotient, symbol and field maps in
`Quillen.MilnorK2`. The separately checked transparent retarget proposal leaves
the R5 implementation untouched until integration.
[`FiniteField`](../../Quillen/KTheory/MilnorK2/FiniteField.lean) proves
`k2_eq_zero_of_finite` and `finiteField_k2_subsingleton` under exactly
`[Field k] [Finite k]`, including orders two and three.

## DVR tame kernel and split residue

[`MilnorK2.Residue`](../../Quillen/KTheory/MilnorK2/Residue.lean) and
[`DVR.Basic`](../../Quillen/KTheory/MilnorK2/DVR/Basic.lean) construct the
actual DVR tame map with ordered convention `∂{u,π}=ū` and
`∂{π,u}=ū⁻¹`.
[`DVR.TameKernel`](../../Quillen/KTheory/MilnorK2/DVR/TameKernel.lean) proves
`ker_tame_eq_unitSymbolSpan` for every actual DVR `R` and fraction field `K`:
the Milnor tame kernel is the integer span of symbols of two units of `R`.
This is an algebraic Milnor theorem; Quillen products and unit generation
require their own comparisons.

[`GTheory.DVR.SplitResidue`](../../Quillen/GTheory/DVR/SplitResidue.lean)
proves `localizationKMap_injective_of_residueSection` for the original
generic finite-module G map in every degree when the actual residue map
has a ring section. The native test realizes this for `PowerSeries ℚ`.
No section for the requested smooth-curve origin is asserted.

## Remaining boundary

Q1 and Q2 achieve the first native milestone. Matsumoto and positive symbol
marking, actual finite-field Quillen G2 vanishing, low-degree localization
actions, ordered Quillen boundary compatibility, origin-DVR Quillen unit
generation, and the literal scheme localization-boundary comparison remain
open. R5 retarget patches are unapplied, and the new closed-support bridge
is not yet validated. The complete programme retains the obligations in the
[implementation plan](../development/LowDegreeFieldSupport.md).
