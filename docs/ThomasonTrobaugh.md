# Perfect-complex localization

The library provides connective K-theory of strict and locally perfect
complexes, vector-bundle comparisons, derived pullback, localization, support
excision, and Mayer–Vietoris. The original restriction maps and relative
homotopy-fiber boundaries remain the public maps. Localization has an exact
image endpoint in degree zero. Separate functorial Bass groups are defined by
cokernel recursion.

This guide describes those models and comparisons. Full nonconnective
Thomason–Trobaugh localization remains open; see [Scope.md](Scope.md#spectra-and-bass-groups).
All declaration names below belong to `Quillen.PerfectComplexes` unless another
namespace is specified. Their source is under
`Quillen.AlgebraicGeometry.PerfectComplexes`.

## Complexes and support

For `X : AlgebraicGeometry.Scheme.{u}`, `Complex X` is the category of
integer-indexed cochain complexes of module sheaves. `strictPerfect X` requires
globally bounded terms, each finite locally free. `StrictPerfect X` is the
corresponding full category.

`Derived X` localizes complexes at quasi-isomorphisms. `locallyPerfect X`
requires an isomorphism in that localization, near each point, to a strict
perfect complex on the neighborhood; `Perfect X` is its full category. These
objects need not be termwise quasi-coherent or globally bounded.
See [Strict.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean) and
[Local.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Local.lean).

`StrictK X n` and `PerfectK X n`, for `n : ℕ`, are the connective S-construction
groups in `Type (u + 1)`. Their ambient-monomorphism cofibrations have quotients
in the specified class. `splitStrictKEquiv` and `splitPerfectKEquiv` compare
these with degreewise split cofibrations, retaining quasi-isomorphisms as weak
equivalences.

For an open immersion `j : U ⟶ X`, a supported perfect complex is acyclic after
restriction to `U`. `PerfectSupportedK j n` is its K-group, and
`perfectSupportedKMap j n` forgets support.
See [PerfectSupport.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/PerfectSupport.lean).

## Relative localization for every open immersion

`perfectOpenWeakWaldhausen j` retains the objects, cofibrations, and chosen zero
of `Perfect X`, with weak equivalences detected by quasi-isomorphism on `U`.
Its groups `PerfectOpenK j n` fit into the canonical factorization

```text
PerfectK X n --perfectOpenKMap--> PerfectOpenK j n
            --perfectOpenKRestrict--> PerfectK U n.
```

The composite is `perfectKRestrict j n`. The relative group is defined on `X`;
identifying its open endpoint requires a further comparison.
See [OpenFunctor.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/OpenFunctor.lean).

The actual homotopy-fiber boundary is `perfectOpenConnectingHom j n`.
`perfectOpen_positiveLongExactSequence` gives the recurring exact positions in

```text
PerfectK X (n+1) → PerfectOpenK j (n+1) → PerfectSupportedK j n
                → PerfectK X n → PerfectOpenK j n.
```

Exactness is range equals kernel. `perfectOpenKMap_zero_surjective` supplies
surjectivity onto relative K₀.
See [OpenLongExactSequence.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/OpenLongExactSequence.lean).
For an arbitrary open, `PerfectOpenKZeroImage j` is exactly
`(perfectKRestrict j 0).range`; the general image construction first quotients
the relative group by its endpoint kernel.

## Model comparisons and pullback

Every row below includes degree zero and uses its canonical comparison map.

| Conditions | Comparison | Source |
| --- | --- | --- |
| Every scheme `X` | `vectorBundleToStrictKEquiv X n` | [GilletWaldhausen.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/GilletWaldhausen.lean) |
| Affine `X` | `affineStrictToPerfectKEquiv`, `affineVectorBundleToPerfectKEquiv` | [Affine/SchemeKEquivalence.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SchemeKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictToPerfectOpenKEquiv R j n` | [Affine/OpenKEquivalence.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/OpenKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictSupportedToPerfectKEquiv R j n` | [Affine/SupportedStrictPerfectKEquivalence.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedStrictPerfectKEquivalence.lean) |
| Quasi-compact `X`, arbitrary localization open `U` and auxiliary open `T` | `boundedFlatPerfectSupportedOpenKEquiv j T n` | [BoundedFlat/SupportedOpenComparison.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean) |

The affine comparisons impose no regularity or noetherianity and allow
non-quasi-compact opens. The bounded-flat supported relative comparison needs
no quasi-separatedness and no compactness of either open. These are comparisons
of the specified models on the ambient scheme; their K₀ statements do not
supply full open-target surjectivity.

`strictKPullback` accepts every scheme map. `perfectKPullback` accepts arbitrary
maps between quasi-compact schemes, uses bounded-above flat representatives,
and gives `PerfectKFunctor`. Its identity, composition, restriction, and
comparison-naturality laws include zero.
See [DerivedPullbackFunctor.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean).

## Global qcqs endpoint and connective sequence

Assume `X` is quasi-compact and quasi-separated and `j : U ⟶ X` is an open
immersion with quasi-compact `U`. In Lean these conditions are
`[CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [IsOpenImmersion j]`.

`qcqsPerfectOpenKEquiv j n` identifies `PerfectOpenK j (n+1)` with
`PerfectK U (n+1)` using the original `perfectOpenKRestrict` as forward map.
`qcqsPerfectOpenKZeroImageEquiv j` identifies relative K₀ with precisely
`PerfectOpenKZeroImage j`. The endpoint is injective and its image is exactly
the image of original absolute restriction.
See [GlobalCofinality.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalCofinality.lean).

`qcqsPerfectConnectingHom j n` is the relative boundary precomposed with the
inverse positive endpoint equivalence. Its composite with relative restriction
is the entire original `perfectOpenConnectingHom`; this equation determines it.
Writing `Kₙ(X)` for `PerfectK X n` and `Kₙ(X on X ∖ U)` for the supported group,
`qcqsPerfect_positiveLongExactSequence` gives recurring exactness in

```text
Kₙ₊₁(X) → Kₙ₊₁(U) → Kₙ(X on X ∖ U) → Kₙ(X) → Kₙ(U).
```

`qcqsPerfect_zeroTail` supplies

```text
K₁(X) → K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U).
```

The tail is exact at `K₁(U)`, the supported K₀, and `K₀(X)`.
It asserts no surjectivity onto full `K₀(U)`.
See [GlobalLocalization.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean).
Ordinary open-pair naturality holds for every commuting base-map square with
qcqs bases and quasi-compact opens, without flat or cartesian assumptions,
including the boundary into supported K₀.
See [GlobalLocalizationNaturality.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalizationNaturality.lean).

Principal opens of affines are a special case over every commutative ring,
including zero divisors and localization at zero. The focused interface is
`Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectLocalization`.

## Geometric inputs and finite families

The global endpoint uses actual derived roofs, opposite weak-arrow joint data,
dual approximation, and perfect-complement density. Its public theorem has no
additional user-supplied roof, cylinder, or density premise.

For qcqs `X` with quasi-compact opens `U,T`, source-supported roofs keep a common
locally perfect source acyclic on `T`. Targets need not vanish there.
Finite supported roofs require locally perfect targets; finite supported
equalities and chain homotopies allow targets with quasi-coherent homology and
individual lower bounds `(B i).IsGE (b i)`. The target hypotheses apply at every
index of the given family, including indices outside the selected finite set.
Empty finite families are included. Infinite families and higher coherence are
not asserted.
See [FiniteSupportedRoofs.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/FiniteSupportedRoofs.lean)
and [FiniteSupportedEquality.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/FiniteSupportedEquality.lean).

Supported density extends a locally perfect `E` on `U`, acyclic on `U ∩ T`,
to a derived retract of a global perfect `P` acyclic on `T`. A constructed
perfect complement `C` gives `P|U ≅ E ⊕ C`. No fixed self-shift stabilization
is imposed.
See [GlobalSupportedDensity.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalSupportedDensity.lean).

## Auxiliary support and its naturality

For an auxiliary open `T`, `PerfectSupportedOpenK j T n` uses objects acyclic
on `T`, with weak equivalences detected on `U`. The absolute open endpoint is
supported away from `j ⁻¹ᵁ T`; the fiber is supported away from `U ∪ T`.
If `X` is qcqs and `U,T` are quasi-compact, its positive endpoint is
`qcqsPerfectSupportedOpenKEquiv`, and degree zero identifies the exact restriction
image. `qcqsPerfectSupportedConnectingHom`,
`qcqsPerfectSupported_positiveLongExactSequence`, and
`qcqsPerfectSupported_zeroTail` retain these original maps.
See [SupportedOpen/GlobalLocalization.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/GlobalLocalization.lean).

The actual supported boundary and positive inverse endpoint are natural for
arbitrary commuting support and localization squares between qcqs ambient
schemes with quasi-compact localization and auxiliary opens. Neither flatness
nor cartesianness is required. Relative boundary naturality needs only
quasi-compact ambient schemes; relative restriction additionally needs
quasi-compact localization opens.
See [SupportedOpen/PairNaturality.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairNaturality.lean).
Fixed-base inclusions `S ≤ T` and forgetting support also commute with the
boundaries. See [SupportedOpen/AuxiliaryNaturality.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/AuxiliaryNaturality.lean).

## Support excision and Mayer–Vietoris

For any open immersion `j : U ⟶ X` and auxiliary open `T` with
`j(U) ∪ T = X`, `perfectSupportedExcisionKEquiv` identifies the original
supported groups on `X` and `U` in every nonnegative degree. Its forward map is
restriction, and its inverse is the actual exact extension-by-zero map. The
unit and counit give weak equivalences and realization homotopy inverses.
No quasi-compactness or quasi-separatedness is assumed.
See [SupportedOpen/Excision.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Excision.lean).

For a qcqs scheme `X = U ∪ V` with quasi-compact opens, the original restrictions
and boundary give the connective sequence

```text
Kₙ₊₁(U) × Kₙ₊₁(V) → Kₙ₊₁(U ∩ V) → Kₙ(X)
                    → Kₙ(U) × Kₙ(V) → Kₙ(U ∩ V).
```

`PerfectMayerVietoris.overlapDifference` is the first restricted class multiplied
by the inverse of the second. `qcqs_positiveExactSequence` supplies the recurring
positions; `qcqs_completeZeroTail` includes exactness at the local K₀ pair.
`qcqs_matching_zero_classes_glue` gives a global K₀ class for any matching local
pair. It does not require either single-open restriction to be surjective.
See [MayerVietoris.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/MayerVietoris.lean).

`SupportedMayerVietoris` gives the supported sequence and matching-class gluing
with a quasi-compact auxiliary acyclicity open `Z`; its boundary is compatible
with forgetting support. The geometric cover reflection and cylinder inputs are
discharged in the qcqs wrappers. No surjectivity onto overlap K₀ or negative
boundary is asserted.
See [SupportedOpen/MayerVietoris.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietoris.lean)
and [SupportedOpen/MayerVietorisForget.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietorisForget.lean).


## Derived sheaf operations and projective-line geometry

The derived comparisons below use the actual bounded-below module-sheaf
derived categories and installed right-derived units. Their generic sheaf owners
have prefix `Quillen.AlgebraicGeometry.Scheme.Sheaf`; projective-line owners
have prefix `Quillen.AlgebraicGeometry.Scheme.ProjectiveLine`.

### Direct image, tensor, and canonical base-change mates

`AffinePushforwardAcyclicity` proves positive-degree acyclicity of quasicoherent
sheaves for every affine morphism, without finite, flat, or noetherian assumptions.
`AffineDerivedPushforward` and `AffineBoundedDerivedPushforward` retain the
given injective augmentation and installed unit on singles and bounded
termwise-quasicoherent complexes. `FlatInjectivePushforward` supplies flat
injective direct image and the bounded-below injective derived-Hom adjunction.
Independently, `FlasquePushforwardAcyclicity` proves flasque acyclicity for every
scheme map. `FlasqueComplex` and `FlasqueComplexDerivedPushforward` extend the
installed unit comparison to bounded-below flasque complexes without an upper
bound. Direct images of injectives are claimed flasque in this general argument,
rather than injective.

`DerivedPushforwardComposition` constructs the canonical
`R(g ∘ f)_* ≅ Rg_* Rf_*`, with the original ordinary composition and both
installed units. `Scheme.VectorBundle.ProjectionFormula` and
`DerivedProjectionFormula` give the ordinary and bounded-below projection
formulas for every scheme map with finite locally free coefficient. The forward
ordinary arrow is the original geometric adjunction-unit composite; both-variable
naturality and the derived-unit equations are retained. These vector-bundle
paths have prefix `Quillen.AlgebraicGeometry`. Composition alone does not assert
triple-composition coherence.

The sheafified tensor bifunctor and actual finite-free retract exactness live in
`Quillen.Algebra.Category.ModuleCat.Sheaf.{Tensor,TensorExact}`.
`Scheme.Sheaf.TensorRestriction` and `Scheme.VectorBundle.TensorLocalExactness`
give genuine open restriction and exactness for finite locally free coefficients.
They use the actual presheaf tensor, sheafification, affine basis, and finite-free
retractions; full monoidal coherence remains separate.

`CartesianBaseChange`, `AffineScalarAdjunction`, `AffineScalarSquare`, and
`AffineBaseChange` identify the geometric pullback/direct-image mate with the
scalar extension/restriction mate on a genuine affine cartesian square. The
ordinary mate is invertible on every quasicoherent sheaf without flatness or
finite-generation assumptions and retains the original tensor and unit formulas.
`CartesianBaseChangePasting`, `CartesianBaseChangeHorizontal`, and
`CartesianBaseChangeLocalization` retain vertical/horizontal composition
factors and open-cover detection; their local invertibility hypotheses are
explicit.

`DerivedFlatBaseChange` constructs the canonical bounded-below derived mate
from that same ordinary mate. Its defining equation keeps both installed
composite units. The base leg is flat and the square cartesian; flatness of the
pulled-back leg is derived from the square. Exact flat pullback preserves homology
without assuming preservation of injectives. Shift, horizontal/vertical pasting,
and target-open equations are in `DerivedFlatBaseChangeShift`,
`DerivedFlatBaseChangeHorizontal`, `DerivedFlatBaseChangeVertical`, and
`DerivedFlatBaseChangeLocalization`; cover conservativity is in
`DerivedOpenCoverConservativity` and `DerivedFlatBaseChangeOpenCover`.

`DerivedOpenBaseChange` gives the installed D+ open-restriction comparison for
arbitrary scheme maps. `CartesianOpenBaseChangeMate` and
`DerivedFlatBaseChangeOpen` identify it with the canonical mate and prove that
mate invertible on every bounded-below complex for an open base leg.
`AffineDerivedBaseChange`, `AffineDerivedBaseChangeCoordinates`, and
`AffineDerivedBaseChangeLocal` prove invertibility on quasicoherent singles
and their integer shifts for an affine morphism and flat base change, including
arbitrary affine coordinates and nonaffine ambient schemes. They do not assert
general bounded-below flat-base-change invertibility.

For finite flat maps of locally noetherian schemes,
`PerfectComplexes.DerivedPushforwardComparison` identifies actual strict direct
image with installed D+ direct image. `PerfectComplexes.Affine.DerivedFiniteFlatPushforward`
preserves intrinsic perfectness for affine source and locally noetherian target.
These paths have prefix `Quillen.AlgebraicGeometry`. General-source perfect
preservation and unrestricted unbounded derived pushforward remain separate.

### The actual two-chart line

For every commutative ring `R`, `Quillen.Scheme.ProjectiveLine.twoChartLine R`
is the actual gluing of the two polynomial charts along the Laurent overlap.
It is qcqs, its projection `p` is flat and separated, and `globalSectionsIso R`
gives its global sections `R`. `Charts`, `AffineCechCover`, and `ChartAffineness`
retain the original open maps and genuine affine intersections.
`BaseChangeGluing` proves cartesian base change for every ring coefficient map
with its original chart equations, without flatness or noetherianity.

`Tautological` constructs a line subbundle `L` of the structure-module square,
with chart columns `(1,t)` and `(s,1)` and Laurent transition `T`, inverse `T⁻¹`.
`TautologicalQuotient` gives the actual line cokernel `Q`, its short exact
sequence, chart rows `(-t,1)` and `(-1,s)`, and inverse Laurent transition.
`TwistMinusFunctor` is an additive exact kernel negative-twist endofunctor on
all module sheaves, preserving finite local freeness. `TwistMinusUnit` identifies
its structure-module value with `L`, retaining the original inclusion;
`VectorBundleTwistMinus` gives its original exact vector-bundle pullback and K-map.
Tensor identification of this kernel twist is a separate comparison.

`Scheme.Sheaf.TwoOpenSheafSequence` gives the signed Čech short exact sheaf
sequence for every sheaf on a two-open cover, with original restriction-adjunction
units, local splittings, and arrow naturality. No quasicoherence, flasqueness,
affineness, or noetherian hypothesis is imposed on that sheaf sequence.
`TwoOpenCohomology` gives the corresponding short exact section-complex sequence
for flasque-term complexes and actual injective resolutions.
`AffineOpenCohomology` retains the actual restricted resolution;
`SectionsHomologyZero` uses its genuine augmentation.
For a two-affine cover, `TwoOpenFirstCohomology` identifies actual first derived
sections of a quasicoherent sheaf with the cokernel of the literal signed
restriction map, retaining the quotient square and requiring no affine overlap.
The public equivalence is `twoAffineRightDerivedOneIsoCokernel`.
`TwoAffineCohomology` gives higher vanishing when the overlap is affine.
These sheaf routes have prefix `Quillen.AlgebraicGeometry.Scheme.Sheaf`.

Consequently `Cohomology` proves quasicoherent vanishing above degree one on
the two-chart line through
`Quillen.Scheme.ProjectiveLine.isZero_rightDerived_globalSections_add_two`.
`StructureSheafCohomology` retains
`structureSheaf_difference_coordinates` and proves vanishing in every positive
degree. `TautologicalSections` and `TautologicalCohomology` prove all-degree
vanishing for `L`, including global sections. `TautologicalQuotientCohomology`
identifies sections of `Q` with `R × R` through the original quotient projection
and proves positive-degree vanishing. All statements include nonreduced and
zero base rings; positive vanishing is not asserted for every quasicoherent sheaf.

`StructureSheafDirectImage`, `TautologicalDirectImage`, and `DerivedDirectImage`
compute the actual relative projection: the structure module has canonical
direct image the base structure module and no positive derived images, while
`L` has zero derived image in every degree. The installed D+ unit comparisons
retain the original geometric projection unit, given injective resolution, and
principal-open section complexes. `VectorBundleDirectImage` gives the invertible
unit on pullbacks of affine-base vector bundles and zero image of their negative
twists. `VectorBundleComplexDirectImage` extends those statements to bounded
complexes, retaining the original degreewise geometric unit and strictToPlus
objects. Sections are not assumed to commute with sheaf homology.

`DerivedCechTriangle` computes relative `Rp(M)` for every quasicoherent sheaf
as the first vertex of a distinguished triangle whose other vertices are ordinary
direct images of the chart pair and overlap. The differential is the pushforward
of the signed sheaf restriction difference; the connecting arrow is the original
short-exact connecting map through the installed overlap-unit inverse.
Actual affine chart/overlap units discharge the acyclicity premises.
`Scheme.Sheaf.AffineCompositeDerivedBaseChange` and `TwoOpenDerivedBaseChange`
transport the canonical mate through this same signed triangle.
`ProjectiveLine.DerivedFlatBaseChange` proves it invertible on every quasicoherent
single for flat cartesian base change of `p`. The self-base-change isomorphism
uses the actual relative square and its two projections; its hom is the original
mate followed by the installed flat-pullback single comparison. These paths have
prefix `Quillen.AlgebraicGeometry`. Coefficient perfection and general
bounded-below base change are not inferred.

### The twisted diagonal triangle

On the relative square of the two-chart line, `DiagonalIncidence` constructs
the actual complex `p₁*L → p₂*Q → Δ_*Q`. Its four original affine-rectangle
scalars are `t-u`, `tv-1`, `1-su`, and `v-s`.
`DiagonalMonomorphism`, `DiagonalClosedImmersion`, and `DiagonalCokernel`
prove the incidence monic, the relative diagonal closed, and the original
quotient the actual cokernel. The resulting twisted sequence is short exact
over every commutative ring. Its proof uses the genuine rectangle cover,
principal kernels, and actual cartesian adjunction mates, retaining both maps.

`DiagonalTensorTriangle` first treats affine-base bundle coefficients;
`DiagonalBundleTensorTriangle` treats every projective-line vector bundle `E`
using genuine tensor restriction/local exactness. The distinguished triangle
retains incidence, quotient, connecting arrows, and coefficient naturality.
`DiagonalTensorPushforward` identifies its ordinary diagonal-supported term
by the original projection arrow. `DiagonalDerivedTensorTriangle` identifies
the third vertex with the installed `RΔ_*(E ⊗ Q)`.
`DiagonalProjectedTensorTriangle` applies derived second projection; canonical
derived composition and identity identify the third vertex with the single of
`E ⊗ Q`. The first two vertices remain actual derived-image objects. This is
the twisted sequence and its triangles; projective generation and the
projective-bundle formula are still open.

## Bass groups and spectral comparisons

### Cokernel recursions and original geometric seeds

`Bass.negativeKFunctor i` takes the original two-polynomial-to-Laurent cokernel
recursively, seeded by additive homotopical perfect K₀. Index `i : ℕ` means
degree `-i`. It accepts arbitrary maps between quasi-compact schemes.
`Bass.supportedNegativeKFunctor` has the supported K₀ seed on pairs with
quasi-compact ambient scheme and arbitrary vanishing open. Their routes are
[BassNegativeGroups.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/BassNegativeGroups.lean)
and [Bass/SupportedGroups.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean).
`Quillen.Bass.affineSchemeNegativeKIso` compares ring and scheme recursions
naturally in every nonpositive degree, with literal original K₀ at zero.
The classical perfect-complex K₀ specialization preserves this homotopical seed;
it does not identify the seed with the triangulated-derived presentation.
`Quillen.KTheory.Bass.RightExactness` and `IterationExactness` preserve pointwise
right exactness and cokernels at every ring-indexed stage, without constructing
negative localization boundaries.

`affineBassTransition` uses the genuine Laurent `T` and `T⁻¹`, scalar action,
whole spectrum homotopy, and original source-leg cone null cylinder. It retains
parameter-correct looping. Raw bounded-flat coefficient squares use actual
geometric pullbacks, original normalization/composition tracks, and independent
comparison, loop, and structure parameters.
`Affine.BassSpanComparisonTrack` and `BoundedFlatBassTransitionNaturality`
give their full coefficient and seed homotopies.
`BassInclusionComparison`, `BassGeometricComparison`, and `BassTransitionInclusion`
retain the original bounded-flat/perfect comparison and seeds: the one-step
cone and looped-step maps are completely weak at positive levels and stable in
every integer degree, and the single seed square is a proved whole homotopy.
No caller-supplied geometric filler or seed compatibility premise remains.
These affine routes are under `Quillen.AlgebraicGeometry.PerfectComplexes.Affine`.

### Strict sections and one-step evaluation

`BoundedFlat.Sections` forms cocartesian sections of the actual geometric
Grothendieck construction. Identity evaluation is an exact categorical
equivalence; canonical sections have the original coefficient-pullback values.
The original global chosen-zero family is retained under evaluation and strict
coefficient reindexing. Section morphisms have universe `u+1`, versus original
bounded-flat morphisms in `u`; common-universe comparisons retain the actual
forward maps. `SectionWaldhausen`, `SectionReindexExact`,
`SectionSpectrumEquivalence`, and `SectionPrespectrum` give the pointwise
Waldhausen structure, all-level homotopy equivalence, and genuine strict
iterated-S coefficient diagram. These routes have prefix
`Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat`.

Actual coefficient evaluation, its chosen-zero normalization, and Model
composition/relative composition tracks are kept by `SectionEvaluation`,
`SectionEvaluationNormalization`, `SectionSpectrumNaturality`,
`SectionModelComposition`, `SectionModelRelativeComposition`,
`SectionModelTrackNaturality`, `SectionModelTargetTrack`, and
`SectionCoefficientComposition`. They retain original cocartesian transition
isomorphisms, Spec composition transports, associators, and whole whiskered
geometric tracks; a categorical comparison is not silently treated as strict
geometric evaluation naturality.

`Affine.SectionLaurentUnit`, `SectionLaurentPullback`, and `SectionBassSeed`
construct the original literally coefficient-natural scalar action and strict
seed `F → B(F)`, including zero-level loops and the source-null cylinder.
`Quillen.KTheory.Bass.StrictDiagram` is the actual endofunctor using the literal
Laurent square, double mapping cylinder, cone, and parameter looping.
`SectionBassDiagram` iterates it; every `SectionBassTransition` is `B^i` of
the same proved seed. No supplied seed premise or new transition unit is used.

`SectionBassEvaluation` constructs the original strict-to-raw span, cone, and
looped-step maps using the proved full comparison filler.
`SectionBassEvaluationEquivalence` proves those same maps completely weak at
every level, including zero, and stable in all integer degrees. The target is
the original raw bounded-flat step; its coefficient maps are not strictified.
`SectionBassEvaluationNull`, `SectionLaurentEvaluationHomotopy`,
`SectionBassSeedEvaluation`, and `SectionBassPerfectSeedEvaluation` retain the
actual null/unit moving squares and compare the single strict, raw, and perfect
seeds without a compatibility assumption. Full all-iterate comparison with the
original geometric tower remains a separate obligation.

### Finite-stage excision and bottom groups

For `f : E ⟶ F`, the canonical cone-fiber comparison is
`E ⟶ homotopyFiber (mappingConeInclusion f)`. It uses the original cone
cylinder as its full fiber path; the source is the original `E`.

The original S-level growth, chosen-point HEP, and finite double-cylinder gap
discharge cone-fiber stable excision for original S-model maps in
`Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision`.
`Affine.SectionBassConnectivity` propagates all-point growth through every
finite Bass stage `i`: at original level `n+i+2`, degrees `k < n+2` vanish
at every point. `SectionBassConeExcision` proves the original comparison stable
for every map between actual stages `i,j`, with connectivity `2*n+2` at level
`n+max(i,j)+2`. All growth and point-HEP premises are discharged; the seed itself
is not asserted stable.

`Quillen.Topology.Prespectrum.ConeStableExactness` and `ConeStableNaturality`
transport the genuine fiber sequence through that same cone comparison. The
boundary is the signed fiber boundary followed by its inverse; exactness keeps
the original arrow and cone inclusion. `SectionBassStableSequence` specializes
the recurring signed positions. `SectionBassWholeTrackCone` and the finite-stage
pushout owners retain supplied whole tracks and discharge their row-excision
conditions. `SectionBassPushoutStableEquivalence`,
`SectionBassPushoutHomotopyStableEquivalence`, `SectionBassFunctorStableEquivalence`,
and `SectionBassIterateStableEquivalence` preserve stability of the original
maps from explicit stable corner maps. The generic
`Quillen.KTheory.Bass.StrictDiagramStableEquivalence` keeps its topology/growth
premises, while `ModelDiagramStableEquivalence` discharges them for actual
strict iterated-S Model diagrams and exact-equivalence transformations.

`BoundedFlatBassSpanStableGroups` proves the raw polynomial span generated at
degree zero by its two original inclusions, with negative vanishing and genuine
raw comparison excision. `BoundedFlatStableKZero`, `BassFirstCokernel`, and
`BassFirstStableGroup` identify existing PerfectK-based `negativeKFunctor 1`
with raw first-step degree minus one. The Laurent representative is the original
K₀ comparison, cone inclusion, and signed loop shift; its kernel is positive-chart
image minus inverse-chart image. `Quillen.KTheory.Bass.TwoChartSigns` negates
only the second polynomial summand. `BassFirstStableNaturality` uses the
unchanged raw coefficient stable maps and proves their group-functor laws;
`SectionBassFirstStableGroup` transports through the actual one-step evaluation.
A separate finite-projective-module presentation is not an input.

At stage `i`, `SectionBassStableConnectivity` proves vanishing below `-i` and
span generation in degree `-i`. `SectionBassSuccessor`,
`SectionBassSuccessorStable`, `SectionBassBottomGroups`, `SectionBassBottomCokernel`,
and `SectionBassBottomComparison` give, for every natural `i`, a natural
isomorphism from existing `negativeKFunctor i` to degree `-i` of actual finite
stage `i`. They retain the original recursive Laurent quotient, both chart signs,
coefficient maps, and stage-zero evaluation. These are diagonal bottom groups;
no fixed-degree later-stage stabilization follows. Comparison with the earlier
evaluation-based first-stage isomorphism is also separate.

### Telescope, localization map, and supported self-comparison

`Affine.SectionBassTelescope` is the actual reduced telescope with original
stage inclusions, heights, and `B^i(seed)` gluings. `SectionBassStableColimit`
gives the natural canonical colimit isomorphism in every integer stable degree.
All original stages and levels have proved T1 and chosen-point HEP, including
level zero. `SectionBassTelescopeCone` and `SectionBassTelescopeExcision`
identify the actual coefficient cone with the colimit of the original finite
cones and prove genuine stable cone-fiber equivalence and recurring signed
exactness. The boundary retains its finite-stage formula and original fiber
boundary; no whole-telescope connectivity premise remains.
`SectionBassTelescopeNaturality` preserves this boundary on commuting coefficient
squares. Generic strict cone/pushout interchange keeps independent cone time
and telescope height, with no extra separation or HEP assumption; parameter-loop
interchange is stable for T1 stages.

`SectionBassNegativeMap` composes the finite-bottom isomorphism with the original
stage inclusion. Its coefficient, Laurent quotient, and next-stage seed/cylinder
formulas are proved. Injectivity, surjectivity, and fixed-degree stabilization
are not asserted. `SectionLocalizedComparison` identifies the actual evaluation
inverse in stable localization, retaining original perfect K-maps.
`SectionBassLocalizedSpectrum` gives a natural initial map from the original
localized perfect spectrum to the actual telescope; it does not assert
nonnegative-group isomorphisms. The connective spectrum's own negative stable
groups still vanish.

`SectionBassTelescopeLooping`, `SectionBassTelescopeCommutation`, and
`SectionBassTelescopeSelfMap` assemble actual interchange and tail maps into a
coefficient-natural stable map from this telescope to its Bass image in every
integer degree. Its initial face is exactly the original Laurent seed followed
by Bass of the original initial inclusion. The construction retains all original
transitions and independent cylinder/loop parameters, without assuming any
finite transition stable. This self-comparison alone does not identify classical
negative groups of the telescope.

For `j : U ⟶ Spec R` with `[IsOpenImmersion j]`,
`Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairBaseChange` chooses one actual
pullback of `j` for each object of `Under R`. The projection equations and strict
coefficient laws use those same endpoints; the identity-algebra projection is
an isomorphism to `j`, rather than equality of chosen opens.
`BoundedFlat.SupportedSectionDiagram` uses the actual supported sections and
exact coefficient reindexing. `SupportedSectionComparison` normalizes evaluation
by a canonical zero-object isomorphism, and `SupportedSectionSpectrumEquivalence`
gives whole inverse homotopies, complete weakness at every level, and all-integer
stability. `SupportedSectionModelNaturality` gives an actual whole coefficient
track, rather than strict evaluation naturality.

`Affine.SupportedSectionLaurentUnit`, `SupportedSectionDiagramLaurent`, and
`SupportedSectionBassSeed` give the genuinely natural fixed-open Laurent seed
with original scalar parameters, zeros, and null cylinders. No seed/coherence
hypothesis is supplied. The separately expanded evaluated-term scalar transfer
is not a premise. `SupportedSectionForgetLaurent` and `SupportedSectionForgetSeed`
prove the actual support-inclusion scalar and strict seed squares;
`Quillen.KTheory.Bass.StrictUnderDiagram` retains restriction along `Under.forget`.
`SupportedSectionBassTower` and `SupportedSectionBassForgetTower` give the
supported finite stages, actual telescope, and maps to all ambient stages and
the ambient telescope.

`SupportedSectionBassTelescopeSelfMap` is a stable map to the supported
telescope's Bass image at every coefficient and integer degree. The original
supported Model and Bass topology discharge its T1 premises.
`SupportedSectionBassTelescopeSelfMapForget` proves the whole square with the
existing support-forgetting telescope arrow and unchanged ambient self-map;
no compatibility assumption remains. The identity algebra retains the actual
pulled-back open. These are maps and self-comparisons, without a stabilization
or full-open localization conclusion.

## Relative-open sections and scalar cofibers

`BoundedFlat.OpenConeComparison` proves the actual geometric acyclic-support
cone stably equivalent to the original coarse relative-open S-prespectrum in
every signed degree, with the original target face, null cylinder, and signed
connecting map. Its geometric fibration and S-model excision premises are
discharged. This is the coarse endpoint, retaining the genuine K₀ image
obstruction to replacement by full open perfect K-theory.

`BoundedFlat.SectionOpenEquivalence` and `SectionOpenComparison` give exact
evaluation for the section coarse relative-open weak class and whole two-sided
prespectrum homotopies. The comparison is completely weak at every level and
stable in every integer degree; the fine/coarse square retains the unchanged
maps. `SupportedSectionOpenNull` reverses the actual weak zero-to-supported-section
transformation, producing the specified coherent null cylinder of forgetting
support followed by relative-open restriction. Stability of this supported-section
cone requires its separate source comparison.

`OpenConeFiberLoop` gives the genuine supported mapping cone and canonical
fiber loop of an open-weak perfect arrow. `Affine.PolynomialScalarCone`
specializes to the global polynomial `X`, restricting to Laurent unit `T`:
its actual termwise scalar map is weak on that open. `ScalarCofiber` identifies
the original categorical cofiber with this supported cone and transports the
relative-acyclic K₀ class equality through the unchanged canonical fiber map.
`Quillen.CategoryTheory.Limits.CokernelPushout` retains the displayed zero;
`Quillen.Waldhausen.SplitComplexes.FactorizationCofiber` retains the genuine
factorization extension object, quotient, and target inclusion.
`Quillen.Algebra.Homology.MappingConeSign` identifies `Cone(-f)` with `Cone(f)`
by negating only the shifted source and fixing the target, and
`SplitComplexes.FactorizationSign` uses that exact sign isomorphism.

The object/class comparison is not the Laurent-unit localization boundary
identity. The actual relative-loop comparison, basepoint translation, and
zero-section pushforward-class calculation remain open. No blanket perfect
zero-section dévissage or omission of possible Nil contributions is asserted.

## Remaining obligations

- Identify the supported-section cone with the geometric localization cone, retain its original null track and boundary, and handle the honest degree-zero image endpoint before asserting full-open or nonconnective localization.
- Prove the original Laurent-unit boundary/relative-loop calculation, basepoint translation, and zero-section class formula with their actual maps and possible Nil contributions.
- Establish fixed-degree stabilization of the finite seed transitions and bijectivity of the natural negative-class maps into the telescope. The finite-bottom isomorphisms and stable Bass self-comparisons do not discharge these obligations.
- Compare all iterates with the complete original geometric Bass tower, identify classical telescope negative groups, and prove the fundamental theorem, negative localization boundaries, and nonconnective descent.
- Prove coefficient perfection and projective generation for the derived diagonal route, the projective-bundle formula, Proj identification, and the full twisting-sheaf family. The finite-coefficient retract criterion retains its projectivity/splitting and uniform finite-window conditions.
- Extend perfect preservation to the claimed general-source/unbounded direct-image scope, and establish general bounded-below flat-base-change invertibility beyond the available QC-single and open specializations.
- Extend strict/local equivalence to arbitrary nonaffine schemes and perfect pullback to arbitrary non-quasi-compact schemes; compare the Waldhausen and triangulated-derived Grothendieck presentations.
- Supply any needed general stable cofiber excision, replacement cofiber preservation, and higher raw-spectrum/telescope coherence. The categorical stable localization has no asserted standard stable model structure or triangulation.

The broader interface and verification boundaries are in [Scope.md](Scope.md).
Successful compilation and foundation audits concern the encoded statements;
they do not supply any of these missing comparisons.
