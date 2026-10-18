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
original finite-module localization in every degree.
[`Affine.PrincipalBoundaryComparison`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/PrincipalBoundaryComparison.lean)
also identifies the original principal scheme boundary with finite-module
localization for every Noetherian ring and element, including G1 to G0.
[`Dedekind.PrincipalDvrBoundaryComparison`](../../Quillen/GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean)
identifies this boundary with the original native local-DVR boundary, retaining
any specified fraction field and the actual generic/closed pullbacks.
A separate, unapplied R5 proposal now transports its literal sheaf-stalk
boundary through the actual stalk, residue and generic isomorphisms. Its
original generic-G2 kernel intersection and finite residue-G1 family lift
are independently accepted; the latter retains original generic-G1
injectivity as an explicit premise.

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

Milnor objects, symbols, field maps and residue maps are imported directly from
Aglib `16aa08a9` through their precise native leaves. Its public group is
`MilnorK.K F 2`; `MilnorK.twoEquiv` is the canonical ordered-symbol and field-map
comparison to the retained tensor quotient `MilnorK.K2.Group F`.
The additional candidate
[`FiniteField`](../../Quillen/Aglib/KTheory/MilnorK/K2/FiniteField.lean) proves
`k2_eq_zero_of_finite` and `finiteField_k2_subsingleton` for both presentations
under exactly `[Field k] [Finite k]`, including orders two and three. Quillen
keeps no duplicate Milnor foundational implementation or old module aliases.

[`StableSteinbergUniversal`](../../Quillen/Algebra/Group/StableSteinbergUniversal.lean)
proves unique lifting into an arbitrary surjective central extension of the
original elementary group. The actual ordered torus defect in
[`StableSteinbergSymbols`](../../Quillen/Algebra/Group/StableSteinbergSymbols.lean)
is bilinear and Steinberg, yielding `milnorToKernel` directly from Aglib's
supplied interfaces with its original field-map square.
[`SteinbergFiberComparison`](../../Quillen/KTheory/Field/SteinbergFiberComparison.lean)
constructs the actual plus-map fiber central extension and the resulting
map from the Steinberg kernel to original finite-projective right-module K2.
Finite-module transport must be a subsequent explicit composition. Kernel symbol
generation, Milnor-map injectivity, fiber perfectness, comparison isomorphism,
field naturality of the topological comparison and positive product marking
remain separate obligations.

## Low-degree identity-automorphism operations

[`IdentityAutomorphism`](../../Quillen/KTheory/LowDegreeScalarAction/IdentityAutomorphism.lean)
defines original `E.K 0 →* E.K 1` and `E.K 1 →* E.K 2` operations for
`Aut (Id C)`. The group laws in both variables are proved, including identities.
The natural-automorphism laws use `C : Type (max u v)` and `Category.{v} C`,
covering native finite-module/projective categories and their upper SmallModel.
The actual Q-space action theorem supplies source additivity in degree zero.
Representative equations retain the original track-first cubes and their
degree-zero inverse relative to spatial-first normalization.
[`ScalarUnit`](../../Quillen/KTheory/LowDegreeScalarAction/ScalarUnit.lean)
instantiates these operations for actual scalar units and proves original-KMap
naturality, including chosen models without a linear-category instance.
[`ExactNaturality`](../../Quillen/KTheory/LowDegreeScalarAction/ExactNaturality.lean)
proves the whole normalized-Q homotopy square from ordinary componentwise
compatibility. The signed loop-shift and path-space boundary formulas are also
proved.
[`SerreBoundary`](../../Quillen/KTheory/LowDegreeScalarAction/SerreBoundary.lean)
proves the whole original Serre fiber/action square and the inverse-sign
connecting formula. Its
[`SmallModelBoundary`](../../Quillen/KTheory/LowDegreeScalarAction/SmallModelBoundary.lean)
transport gives the original finite-module scalar-boundary formula with no
model or formal-quotient linear instance.
[`ObjectClass`](../../Quillen/KTheory/LowDegreeScalarAction/ObjectClass.lean)
identifies the action on the original object class with `automorphismClass`,
hence the inverse positive cube. Its upper free rank-n field-module determinant
is `(r^n)^-1`, including rank zero. Principal K0 boundary calibration and
ordered symbol marking remain separate.

The source-coordinate contraction formula in
[`SourceContractionBoundary`](../../Quillen/Topology/HomotopyFiber/SourceContractionBoundary.lean)
and the whole cancellation prism in
[`NaturalTransformationLoopCancellation`](../../Quillen/Topology/ClassifyingSpace/NaturalTransformationLoopCancellation.lean)
supply boundary geometry without assuming a calibration equation.
[`PrincipalRankOne`](../../Quillen/Aglib/Algebra/Category/FGModuleCat/PrincipalRankOne.lean)
retains the literal multiplication/quotient maps and actual localized scalar
automorphism. Regularity supplies monicity; Noetherianity supplies the
categorical short-exact and conflation statements. These providers do not
close the remaining principal K0 boundary calibration.

## DVR tame kernel and split residue

The provided Aglib `MilnorK.K2.Residue` and `MilnorK.K2.DVR.Basic` supply
the actual DVR tame map with ordered convention `∂{u,π}=ū` and
`∂{π,u}=ū⁻¹`; Aglib also supplies the compatible uniform residue.
The additional candidate
[`DVR.TameKernel`](../../Quillen/Aglib/KTheory/MilnorK/K2/DVR/TameKernel.lean) proves
`ker_tame_eq_unitSymbolSpan` for every actual DVR `R` and fraction field `K`:
the Milnor tame kernel is the integer span of symbols of two units of `R`.
Its uniform-residue kernel is the comap of this span along the supplied
`MilnorK.twoEquiv`.
This is an algebraic Milnor theorem; Quillen products and unit generation
require their own comparisons.

[`GTheory.DVR.SplitResidue`](../../Quillen/GTheory/DVR/SplitResidue.lean)
proves `localizationKMap_injective_of_residueSection` for the original
generic finite-module G map in every degree when the actual residue map
has a ring section. The native test realizes this for `PowerSeries ℚ`.
A separate, unapplied R5 origin proposal constructs the section from the
existing geometric triangles and strictly checks its original trait G/K
pullback injectivity; independent ordinary mathematical review accepted it.
The genuine-model scheme corollaries retain the normality input of the
existing diagram constructor.

## Remaining boundary

Q1 and Q2 achieve the first native milestone. Matsumoto and positive symbol
marking, actual finite-field Quillen G2 vanishing, principal K0 boundary
calibration, ordered Quillen boundary compatibility, origin-DVR Quillen unit
generation remain open. R5's distinct sheaf-stalk transport and the first and
third affine localization consequences have a separately validated proposal.
R5 retarget patches are unapplied. The field-determinant and closed-support
bridges passed strict checks, scoped audits and independent mathematical review;
their compatible source projections do not certify full installed R5 CI.
The complete programme retains the obligations in the
[implementation plan](../development/LowDegreeFieldSupport.md).
