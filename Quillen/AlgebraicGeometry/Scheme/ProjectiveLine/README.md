# The two-chart projective line and its sheaf geometry

## The actual two-chart line

For `R : CommRingCat.{u}`, `AlgebraicGeometry.Scheme.ProjectiveLine.twoChartLine R`
glues two polynomial spectra along their Laurent overlap. `Charts`,
`AffineCechCover`, and `ChartAffineness` retain the original affine open maps
and intersection. The line is qcqs; its projection `p` is flat and separated.
`globalSectionsIso R` identifies its sections with `R` by the original base
map. `coefficientMap_isPullback` in `BaseChangeGluing` proves cartesian coefficient
change for every ring map, without flatness or noetherianity. Here all module
paths have prefix `Quillen.AlgebraicGeometry.Scheme.ProjectiveLine`, while
declarations have prefix `AlgebraicGeometry.Scheme.ProjectiveLine`.

`Tautological` constructs a line subbundle `L` of the structure-module square
with columns `(1,t)` and `(s,1)` and Laurent transition `T`, inverse `T⁻¹`.
`TautologicalQuotient` constructs its actual line cokernel `Q`, chart rows
`(-t,1)` and `(-1,s)`, inverse transition, and the original short exact sequence.
The additive exact `TwistMinusFunctor` is a kernel negative-twist functor on
all module sheaves and preserves finite local freeness. `TwistMinusUnit`
identifies its structure-module value with `L`, retaining the inclusion;
`VectorBundleTwistMinus` gives exact twisted bundle pullback and `twistedPullbackKMap`.
Its identification with tensor by `L` remains a separate comparison.

## Signed Čech cohomology

`Scheme.Sheaf.TwoOpenSheafSequence` proves the signed Čech short exact sheaf
sequence for every sheaf on a genuine two-open cover, with the original
restriction-adjunction units, local splittings, and arrow naturality. It has
no quasicoherence, flasqueness, affine, or noetherian premise.
`TwoOpenCohomology` gives the section-complex sequence for flasque-term
complexes and actual injective resolutions; `AffineOpenCohomology` and
`SectionsHomologyZero` retain the restricted resolution and its augmentation.
`twoAffineRightDerivedOneIsoCokernel` in `TwoOpenFirstCohomology` identifies
first derived sections of a quasicoherent sheaf on a two-affine cover with
the cokernel of the literal signed restriction difference, retaining the
quotient square without requiring an affine overlap. `TwoAffineCohomology`
adds higher vanishing when the overlap is affine.

Applying these results to the original charts gives:

| Sheaf on the two-chart line | Actual derived sections |
| --- | --- |
| Any quasicoherent sheaf | Vanishing in degrees `n + 2`, by `isZero_rightDerived_globalSections_add_two` |
| Structure module | Sections `R` and no positive cohomology; `structureSheaf_difference_coordinates` retains the signed Laurent calculation |
| Negative tautological line `L` | Zero in every degree, including sections, by `TautologicalSections` and `TautologicalCohomology` |
| Tautological quotient `Q` | Sections `R × R` through the original quotient projection and no positive cohomology, by `TautologicalQuotientCohomology` |

These statements include nonreduced and zero rings; arbitrary quasicoherent
sheaves are not asserted to have vanishing first cohomology.

## Relative direct image and base change

`StructureSheafDirectImage`, `TautologicalDirectImage`, and `DerivedDirectImage`
compute direct image under `p`: the structure module has canonical image the
base structure module and no positive derived images, while `L` has zero
derived image in every degree. The D+ comparisons retain the geometric
projection unit, the given injective resolution, and principal-open section
complexes. `VectorBundleDirectImage` proves the unit invertible on pullbacks
of affine-base vector bundles and their derived negative twists zero.
`VectorBundleComplexDirectImage` extends this to complexes with explicit lower
and upper term bounds and finite locally free terms, retaining the degreewise
geometric unit. The proofs do not assume sections commute with sheaf homology.

`derivedCechTriangle R M` computes `Rp_*M` for every quasicoherent single as
the first vertex of a distinguished triangle; the other vertices are ordinary
direct images of the chart pair and overlap. Its differential is the
pushforward of the signed sheaf restriction difference, and its connecting
arrow is the original short-exact connecting map through the installed
overlap-unit inverse. Actual affine chart and overlap units discharge acyclicity.
`ProjectiveLine.DerivedFlatBaseChange` proves the canonical mate invertible on
every such single for flat cartesian base change of `p`. Its self-base-change
isomorphism uses the actual relative square and projections; its hom is the
original mate followed by the installed flat-pullback single comparison.

## Finite-projective Čech models and the original derived image

For every quasicoherent sheaf `M` on `twoChartLine R`,
[`ModuleChartSections`](ModuleChartSections.lean)
constructs its actual polynomial chart-section modules and their Laurent
overlap isomorphism. `chartSectionDifference_coordinates` identifies the
original first-minus-second restriction difference with the scalar-extension
unit on the positive chart minus the transported negative-chart unit. The
negative scalar map sends the polynomial coordinate to `T⁻¹`; the positive
map sends it to `T`. These coordinates and their adjunction-unit equations
are constructed from the sheaf, rather than assumed transition data.

When `M` is finite locally free, both chart modules are finite projective over
`R[X]`. They need not be free on the entire chart or finite over `R`.
[`VectorBundleCech`](VectorBundleCech.lean)
gives a homotopy-equivalent complex of finite projective `R`-modules supported
in degrees zero and one. Its theorem
`exists_original_vectorBundle_cech_model` concerns the literal signed section
differential of the original pushed sheaf sequence. All commutative base
rings are included, with no noetherian, regular, nonzero, or reduced hypothesis.

The finite model comes from Laurent cutoff bounds, finite-free retractions
of the polynomial chart modules, and rectangular projector transition matrices.
[`LaurentProjectorFiniteDefects`](../../../Aglib/Algebra/Polynomial/Laurent/ProjectorFiniteDefects.lean)
factors both parametrix defects through actual finite coefficient modules.
The algebraic step in
[`FiniteParametrix`](../../../Aglib/Algebra/Module/FiniteParametrix.lean)
takes `d : A → B` and `s : B → A` with factorizations
`d s + t r = id_B` through `F` and `s d + u v = id_A` through `G`.
If `A` and `F` are projective and `F` and `G` finite, the enlarged split map
`[d,t] : A × F → B` has a finite-projective kernel: a genuine retraction gives
projectivity, and the proved surjection from `G × F` gives finite generation.
Its second projection to `F` supplies the replacement differential and the
original chain maps and homotopies. This proves finite generation without a
uniform coefficient-support window for the older kernel embedding in
`FiniteCoefficientRetract`; that older criterion retains its own premises.

[`CechCounit`](CechCounit.lean)
uses the original affine counits on both pushed Čech terms and their naturality
square. `originalSheafCechSectionsIso` in
[`CechSheafComplex`](CechSheafComplex.lean)
reconstructs the signed sheaf complex as the cone of the degree-zero
difference, shifted by `-1`. It does not assume quasicoherence of the total
ordinary direct image of `M` or commutation of sections with homology.

`derivedCechConeIso R M` identifies the actual D+ projection image, included
in the ambient derived category, with that original shifted sheaf cone.
The comparison rotates the existing derived Čech triangle, fixes its two
ordinary vertices by identity maps, and retains the connecting square and
the explicit minus-one shift. This identification needs quasicoherence,
independently of a perfectness assumption.

Combining it with the finite model proves perfection of the installed image
for every vector-bundle single. Finite induction through the actual brutal-layer
triangles extends the result to complexes with explicit lower and upper term
bounds and finite locally free terms. The strict representatives and precise
perfect-object statements are recorded in
[projective-line perfect models](../../PerfectComplexes/ProjectiveLine/README.md).
The existence theorem does not choose coefficient-natural finite replacements
or global bounded vector-bundle representatives of arbitrary locally perfect
objects on the line.

## The twisted diagonal triangle

On the relative square, `DiagonalIncidence` constructs
`p₁*L → p₂*Q → Δ_*Q`. The four original affine-rectangle scalars are
`t-u`, `tv-1`, `1-su`, and `v-s`. `DiagonalMonomorphism`,
`DiagonalClosedImmersion`, and `DiagonalCokernel` prove incidence monic,
the relative diagonal closed, and the original quotient the actual cokernel.
The resulting sequence is short exact over every commutative ring, using the
genuine rectangle cover, principal kernels, and cartesian adjunction mates.

`DiagonalTensorTriangle` treats affine-base bundle coefficients;
`DiagonalBundleTensorTriangle` tensors by `p₁*E` for every projective-line
vector bundle `E`, using actual tensor restriction and local exactness. The
distinguished triangles retain incidence, quotient, connecting arrows, and
coefficient naturality. `DiagonalTensorPushforward` identifies the ordinary
diagonal-supported term by the original projection arrow.
`DiagonalDerivedTensorTriangle` identifies the third vertex with installed
`RΔ_*(E ⊗ Q)`. `DiagonalProjectedTensorTriangle` then applies derived second
projection; canonical composition and the geometric section identity identify
the third vertex with the degree-zero single of `E ⊗ Q`. The first two
vertices remain actual derived-image objects. `DiagonalGenerationEndpoints`
and `DiagonalGenerationNaturality` give the natural vector-bundle endpoint
identifications. `DiagonalLineRotation` applies the exact original line tensor
and rotation, retaining the standard negative shifted incidence.
[OriginalLineContraction](OriginalLineContraction.lean) and
[DiagonalPerfectGenerationRotation](DiagonalPerfectGenerationRotation.lean)
supply the nested line contractions and derived-roof-compatible rotated
identifications for the intrinsic-perfect extension below.

[`DiagonalRestrictedStalkExactness`](DiagonalRestrictedStalkExactness.lean)
proves that the original incidence sequence, stalked along the diagonal and
restricted through the original projection stalk map, stays short exact after
tensor with any coefficient module. The quotient is the flat quotient-line
stalk; the coefficient module need not be flat.
[`DiagonalAllCoefficientTensor`](DiagonalAllCoefficientTensor.lean)
transfers it through the canonical tensor/pullback stalk comparisons and
joint stalk reflection to both literal global tensor sequences. They are
short exact for every line-module coefficient and every base-module coefficient.
[`DiagonalAllCoefficientPushforward`](DiagonalAllCoefficientPushforward.lean)
identifies the original diagonal-supported tensor term for arbitrary
coefficients through the same projection/section arrows, exactly recovering
the old bundle isomorphism.

[`DiagonalCoefficientFunctors`](DiagonalCoefficientFunctors.lean)
realizes exactness of all three actual vertex functors. The third is the original
quotient-line tensor followed by exact diagonal pushforward through that same
ordinary natural comparison. For arbitrary bounded-below coefficient complexes,
[`DiagonalComplexTensorTriangle`](DiagonalComplexTensorTriangle.lean)
constructs the literal degreewise short exact sequence and canonical distinguished
D+ triangle. Its whole triangle functor inverts actual quasi-isomorphisms and
descends through the original localization; the explicit inverse/forward roof
formula and connecting square preserve every derived morphism.
`DiagonalComplexProjectedTriangle` uses the original exact tensor/pushforward
units and section comparison to identify the projected third term naturally
with R(− tensor Q). `DiagonalComplexSingleComparison` proves the explicit whole
original vector-bundle single-triangle correspondence. No flatness,
quasicoherence, perfectness, noetherianity or upper term bound is imposed on the
coefficient complex. [`OriginalPerfectGeneration`](OriginalPerfectGeneration.lean)
now identifies the original endpoints naturally on every intrinsic-perfect
D+ input, uses the specified determinant contractions and units, and gives
the signed rotated triangle p*Rp*K→K→L⊗p*(Rp*(K⊗L)[1]). Its coefficients are
perfect, its original connecting map is natural on genuine roofs, and its
full original bundle-single correspondence is explicit.

## Source interfaces

| Source / interface | Description |
| --- | --- |
| `AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleCech` | Actual finite-projective chart-section Čech model for every finite locally free sheaf |
| `AlgebraicGeometry.Scheme.ProjectiveLine.DerivedCechCone` | Original derived projection image and signed sheaf Čech cone comparison |
