# Perfect-complex localization

The library provides connective K-theory of strict and locally perfect
complexes, vector-bundle comparisons, derived pullback, localization, support
excision, and Mayer–Vietoris. The original restriction maps and relative
homotopy-fiber boundaries remain the public maps. Localization has an exact
image endpoint in degree zero. Separate functorial Bass groups are defined by
cokernel recursion.

This guide owns the perfect objects, supported/relative models, and their
connective geometric localization comparisons. The generic spectrum and
Bass-recursion interfaces are in [SpectraAndBass.md](SpectraAndBass.md);
scheme K/G and generic sheaf geometry are in [SchemeKTheory.md](SchemeKTheory.md).
Full nonconnective
Thomason–Trobaugh localization remains open; see [Scope.md](../reference/Scope.md#spectra-and-bass-groups).
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
See [Strict.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean) and
[Local.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Local.lean).

`StrictK X n` and `PerfectK X n`, for `n : ℕ`, are the connective S-construction
groups in `Type (u + 1)`. Their ambient-monomorphism cofibrations have quotients
in the specified class. `splitStrictKEquiv` and `splitPerfectKEquiv` compare
these with degreewise split cofibrations, retaining quasi-isomorphisms as weak
equivalences.

For an open immersion `j : U ⟶ X`, a supported perfect complex is acyclic after
restriction to `U`. `PerfectSupportedK j n` is its K-group, and
`perfectSupportedKMap j n` forgets support.
See [PerfectSupport.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/PerfectSupport.lean).

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
See [OpenFunctor.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenFunctor.lean).

The actual homotopy-fiber boundary is `perfectOpenConnectingHom j n`.
`perfectOpen_positiveLongExactSequence` gives the recurring exact positions in

```text
PerfectK X (n+1) → PerfectOpenK j (n+1) → PerfectSupportedK j n
                → PerfectK X n → PerfectOpenK j n.
```

Exactness is range equals kernel. `perfectOpenKMap_zero_surjective` supplies
surjectivity onto relative K₀.
See [OpenLongExactSequence.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenLongExactSequence.lean).
For an arbitrary open, `PerfectOpenKZeroImage j` is exactly
`(perfectKRestrict j 0).range`; the general image construction first quotients
the relative group by its endpoint kernel.

## Model comparisons and pullback

Every row below includes degree zero and uses its canonical comparison map.

| Conditions | Comparison | Source |
| --- | --- | --- |
| Every scheme `X` | `vectorBundleToStrictKEquiv X n` | [GilletWaldhausen.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/GilletWaldhausen.lean) |
| Affine `X` | `affineStrictToPerfectKEquiv`, `affineVectorBundleToPerfectKEquiv` | [Affine/SchemeKEquivalence.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SchemeKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictToPerfectOpenKEquiv R j n` | [Affine/OpenKEquivalence.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/OpenKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictSupportedToPerfectKEquiv R j n` | [Affine/SupportedStrictPerfectKEquivalence.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedStrictPerfectKEquivalence.lean) |
| Quasi-compact `X` | `BoundedBelow.inclusion_KMap_bijective X n` | [BoundedBelowComparison.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedBelowComparison.lean) |
| Quasi-compact `X`, arbitrary localization open `U` and auxiliary open `T` | `boundedFlatPerfectSupportedOpenKEquiv j T n` | [BoundedFlat/SupportedOpenComparison.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenComparison.lean) |

The affine comparisons impose no regularity or noetherianity and allow
non-quasi-compact opens. The bounded-flat supported relative comparison needs
no quasi-separatedness and no compactness of either open. These are comparisons
of the specified models on the ambient scheme; their K₀ statements do not
supply full open-target surjectivity.

`BoundedBelow.Obj X` retains the original locally perfect complexes and all
their original chain maps, with an existential lower bound on terms. Its literal
inclusion into `Perfect X` induces a weak equivalence of the original delooping
map and a bijection of the canonical K-map in every connective degree, including
zero, on every quasi-compact scheme. The proof constructs actual opposite App2:
good truncation gives a weak arrow out of the source, and the existing opposite
cocylinder supplies the retained commuting factorization. Native S-duality
transfers it to the original inclusion. No Godement premise or exactness of a
global truncation functor is assumed. This supplies a source-model comparison.
The natural Godement totalization now has its original augmentation
quasi-isomorphism, exact/cofibration and weak-arrow preservation, and
installed derived-pushforward comparison for every lower-bounded input.
[`FlasqueBoundedBelow`](../../Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueBoundedBelow.lean)
constructs the actual termwise-flasque full model and exact total functor.
Its two forward natural weak units yield mutually inverse original inclusion
and total K-maps for every scheme and every nonnegative degree, including
zero. [`FlasqueBoundedBelowComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueBoundedBelowComparison.lean)
identifies its literal composite inclusion into all perfect complexes on
quasi-compact schemes.
[`FlasqueCoefficientZero`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueCoefficientZero.lean)
and `FlasqueCoefficientOne` now construct literal exact G₀=p_* and
G₁=p_*T(−⊗L)[1], with actual flasque-perfect outputs, original maps and signed
shift. Their exact product and natural installed-unit/augmentation/shift
comparisons are supplied over every commutative ring, including zero.
[`FlasqueTwoSummands`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueTwoSummands.lean)
now constructs actual exact Phi by totalizing the original O/O(-1) coproduct.
Its natural forward weak unit and actual coproduct comparisons retain the
original local sum.
[`FlasqueNativePhiKMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueNativePhiKMap.lean)
identifies its original K-map with the EXISTING native two-summand map through
literal model inclusion and actual affine transport, preserving both unchanged
Product.KEquiv maps and all degrees including zero. This has independent
ordinary review, native public-root interfaces and a complete 143-origin audit.
[`StrictPositiveRetraction`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/StrictPositiveRetraction.lean)
proves the original canonical positive unit weak on strict affine coefficients
and its actual forward weak-span K-map equality. `StrictPositiveSourceComparison`
proves the literal strictTotal source K-map bijective over every R and in every
natural degree, including zero; no natural strictification is supplied.
[`FlasqueShift`](../../Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueShift.lean)
proves the literal signed shift induces inversion on the original model
K-groups for every scheme and natural degree, including zero, through its
actual identity-cone conflation and weak-zero transformation.
[`EulerInverse`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/EulerInverse.lean)
proves K(E2[1])=K(E0) for the original determinant-normalized projected Euler
functors on strict affine coefficients. The actual conflation, weak-zero
middle and original additivity supply this equality; `EulerConnecting` retains
the canonical connecting isomorphism separately. These eight sources have
independent review, native interfaces and a complete 257-origin audit.
[`FlasqueGPhiMatrix`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueGPhiMatrix.lean)
assembles all four actual entries into the original product-category
K(G)∘K(Phi)=id and literal composite KMap(Phi⋙G)=id. The proof uses the
original positive unit, O(-1) weak-zero maps, Euler comparison and signed
shift, then the proved strictTotal source K-map surjectivity and unchanged
Product.KEquiv. Independent complex ordinary review, 24 original native
public-root examples and a complete 145-origin audit cover every R,
including the zero ring, and every natural degree, including zero. The
opposite PhiG identity and its three original endpoint weak spans are now
supplied by the affine inverse family below.
[`FlasqueTensorDiagonalAdditivity`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueTensorDiagonalAdditivity.lean)
now gives original K(Gamma E2)=K(Gamma E1)*K(Gamma E3), with Gamma the
actual LEFT-L tensor followed by totalization, a genuine mapped conflation
and exact Reedy extension.
[`FlasquePhiColumns`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasquePhiColumns.lean)
gives K(Phi)(K(G)(x)) as the positive composite times the inverse unshifted
negative composite, retaining the original coproduct, product coordinates,
chosen zero and actual base shift. Independent ordinary reviews, 29 original
public-root examples and a complete 53-origin audit passed. The actual
three Gamma endpoint K-map identifications now close PhiG.
[`FlasquePhiInverse`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasquePhiInverse.lean)
proves K(Phi)∘K(G)=id and literal KMap(G⋙Phi)=id. Both SAME original model
K-map composites are identity. Its existing native affine two-summand map
is bijective through the literal model inclusions and actual affine inverse
geometry, and nativeAffineTwoSummandKEquiv has that literal forward map.
The 26 endpoint/contraction prerequisites have independent reviews, 80
original current public-root examples and a complete 514-origin audit.
The final Gamma/transport/inverse ten-source family has independent complex
ordinary review, 68 original examples and a complete 129-origin audit.
These are all-ring/all-natural-degree results, including the zero ring
and K0. The specialized P3 endpoint-unit/connecting comparisons, general
qcqs/support extension and final TT identification remain separate.

`strictKPullback` accepts every scheme map. `perfectKPullback` accepts arbitrary
maps between quasi-compact schemes, uses bounded-above flat representatives,
and gives `PerfectKFunctor`. Its identity, composition, restriction, and
comparison-naturality laws include zero.
See [DerivedPullbackFunctor.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean).

## Global qcqs endpoint and connective sequence

Assume `X` is quasi-compact and quasi-separated and `j : U ⟶ X` is an open
immersion with quasi-compact `U`. In Lean these conditions are
`[CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [IsOpenImmersion j]`.

`qcqsPerfectOpenKEquiv j n` identifies `PerfectOpenK j (n+1)` with
`PerfectK U (n+1)` using the original `perfectOpenKRestrict` as forward map.
`qcqsPerfectOpenKZeroImageEquiv j` identifies relative K₀ with precisely
`PerfectOpenKZeroImage j`. The endpoint is injective and its image is exactly
the image of original absolute restriction.
See [GlobalCofinality.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalCofinality.lean).

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
See [GlobalLocalization.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean).
Ordinary open-pair naturality holds for every commuting base-map square with
qcqs bases and quasi-compact opens, without flat or cartesian assumptions,
including the boundary into supported K₀.
See [GlobalLocalizationNaturality.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalizationNaturality.lean).

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
See [FiniteSupportedRoofs.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/FiniteSupportedRoofs.lean)
and [FiniteSupportedEquality.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/FiniteSupportedEquality.lean).

Supported density extends a locally perfect `E` on `U`, acyclic on `U ∩ T`,
to a derived retract of a global perfect `P` acyclic on `T`. A constructed
perfect complement `C` gives `P|U ≅ E ⊕ C`. No fixed self-shift stabilization
is imposed.
See [GlobalSupportedDensity.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalSupportedDensity.lean).

## Auxiliary support and its naturality

For an auxiliary open `T`, `PerfectSupportedOpenK j T n` uses objects acyclic
on `T`, with weak equivalences detected on `U`. The absolute open endpoint is
supported away from `j ⁻¹ᵁ T`; the fiber is supported away from `U ∪ T`.
If `X` is qcqs and `U,T` are quasi-compact, its positive endpoint is
`qcqsPerfectSupportedOpenKEquiv`, and degree zero identifies the exact restriction
image. `qcqsPerfectSupportedConnectingHom`,
`qcqsPerfectSupported_positiveLongExactSequence`, and
`qcqsPerfectSupported_zeroTail` retain these original maps.
See [SupportedOpen/GlobalLocalization.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/GlobalLocalization.lean).

The actual supported boundary and positive inverse endpoint are natural for
arbitrary commuting support and localization squares between qcqs ambient
schemes with quasi-compact localization and auxiliary opens. Neither flatness
nor cartesianness is required. Relative boundary naturality needs only
quasi-compact ambient schemes; relative restriction additionally needs
quasi-compact localization opens.
See [SupportedOpen/PairNaturality.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairNaturality.lean).
Fixed-base inclusions `S ≤ T` and forgetting support also commute with the
boundaries. See [SupportedOpen/AuxiliaryNaturality.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/AuxiliaryNaturality.lean).

## Support excision and Mayer–Vietoris

For any open immersion `j : U ⟶ X` and auxiliary open `T` with
`j(U) ∪ T = X`, `perfectSupportedExcisionKEquiv` identifies the original
supported groups on `X` and `U` in every nonnegative degree. Its forward map is
restriction, and its inverse is the actual exact extension-by-zero map. The
unit and counit give weak equivalences and realization homotopy inverses.
No quasi-compactness or quasi-separatedness is assumed.
See [SupportedOpen/Excision.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Excision.lean).

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
See [MayerVietoris.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/MayerVietoris.lean).

`SupportedMayerVietoris` gives the supported sequence and matching-class gluing
with a quasi-compact auxiliary acyclicity open `Z`; its boundary is compatible
with forgetting support. The geometric cover reflection and cylinder inputs are
discharged in the qcqs wrappers. No surjectivity onto overlap K₀ or negative
boundary is asserted.
See [SupportedOpen/MayerVietoris.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietoris.lean)
and [SupportedOpen/MayerVietorisForget.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietorisForget.lean).


## Geometric sheaf inputs

Generic finite direct image, bounded-below derived direct image, canonical
base-change mates, and the actual two-chart projective-line computations are
owned by [SchemeKTheory.md](SchemeKTheory.md#derived-direct-image-tensor-and-projection-formulas).
That guide records the ordinary arrows, installed D+ units, finite-locally-free
projection formula, quasicoherent-single and bounded-complex scopes, and the
twisted diagonal triangle. Its original all-coefficient complex SES, D+
triangle, genuine roof/connecting naturality and naturally projected quotient-line
vertex are now supplied, with explicit vector-bundle single correspondence.
[`OriginalPerfectGeneration`](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalPerfectGeneration.lean)
now supplies the natural intrinsic-perfect generation triangle over every R,
including zero, retaining the original self-base-change/projection endpoints,
connecting maps on roofs, determinant contractions, units and signed rotation.
Its G₀/G₁ coefficients are perfect and the original bundle-single triangle is
recovered. The exact affine two-summand K-inverse is now supplied by
FlasquePhiInverse; the global/support extension remains separate.

### Projective-line strict models

For every `R : CommRingCat.{u}` and finite locally free sheaf `M` on the actual
`twoChartLine R`, the original signed sheaf Čech complex has a strict-perfect
homotopy model on `Spec R`. The finite-projective chart-module construction
and its actual counit and signed-cone comparisons are explained in
[SchemeKTheory.md](SchemeKTheory.md#finite-projective-čech-models-and-the-original-derived-image).
The relevant imports have prefix
`Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine`; declaration names
in this table have prefix `Quillen.PerfectComplexes.ProjectiveLine`:

| Module | Actual perfect-complex interface |
| --- | --- |
| [`CechModel`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/CechModel.lean) | `exists_strictSheafCech_model`: a strict-perfect sheaf model with both chain maps and homotopies |
| [`DerivedPushforwardVectorBundle`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/DerivedPushforwardVectorBundle.lean) | `exists_derivedPushforward_vectorBundle_strict_model` and `perfect_derivedPushforward_vectorBundle`: a strict representative and intrinsic perfection of the installed D+ projection image |
| [`BoundedDerivedPushforward`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/BoundedDerivedPushforward.lean) | `perfect_derivedPushforward_of_bounded_vectorBundle_terms`: perfection for explicitly bounded complexes of finite locally free terms |

The derived representative is an isomorphism in the ambient derived category
after the actual D+ inclusion, with the original projection functor unchanged.
The bounded theorem takes `K : CochainComplex.Plus (twoChartLine R).Modules`,
integer bounds `a,b`, zero terms below `a` and above `b`, and finite local
freeness of every term. Its proof uses shifts of bundle singles and finite
induction through actual brutal-layer triangles. No noetherian, regular,
free-chart, nonzero, or reduced hypothesis is imposed on the base ring.

This supplies the vector-bundle and explicitly bounded vector-bundle subfamilies
of the projection-perfectness problem. It does not produce global bounded
vector-bundle representatives for arbitrary locally perfect inputs, identify
the two projected diagonal vertices with functorial perfect coefficients, or
prove projective generation. The finite-defect parametrix proof uses a genuine
split kernel and finite generators; it does not instantiate the older
`FiniteCoefficientRetract` uniform support-window premise.

## Bass groups and geometric spectral comparisons

The generic recursion, finite-bottom groups, and telescope-identification
boundary are developed in [SpectraAndBass.md](SpectraAndBass.md). This section
records their perfect-K₀ seeds, geometric step/evaluation maps, and support
interfaces used by the localization comparison.

### Cokernel recursions and original geometric seeds

`Bass.negativeKFunctor i` takes the original two-polynomial-to-Laurent cokernel
recursively, seeded by additive homotopical perfect K₀. Index `i : ℕ` means
degree `-i`. It accepts arbitrary maps between quasi-compact schemes.
`Bass.supportedNegativeKFunctor` has the supported K₀ seed on pairs with
quasi-compact ambient scheme and arbitrary vanishing open. Their routes are
[BassNegativeGroups.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/BassNegativeGroups.lean)
and [Bass/SupportedGroups.lean](../../Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean).
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

The native ambient extension
[`CoefficientBassOriginalNegativeComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassOriginalNegativeComparison.lean)
uses the original scheme Bass recursion on the actual coefficient fibers of
any compact scheme over `Spec R`. For every `i`, it gives the degree `-i`
finite-stage isomorphism, naturally in coefficient arrows, preserving the
original perfect K₀ evaluation and Laurent quotient. The actual native
polynomial and Laurent products supply both chart transport squares.
The finite comparison preserves original scheme restriction between compact
endpoints through `CoefficientBassOriginalNegativeNaturality`. Supported groups
and seed/transition invertibility remain separate.
[`CoefficientBassNegativeMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassNegativeMap.lean)
composes it with the original native telescope inclusion, preserving the
successor Laurent representative. This class map is natural in coefficient
arrows. `CoefficientBassSchemeRestrictionTelescope` preserves the actual
Laurent action, seed, transitions and every telescope face under arbitrary
scheme restriction. `CoefficientBassNegativeMapNaturality` gives the original
class-map square for compact endpoints. Bijectivity and fixed-degree
stabilization remain unproved.

The original Raw1 polynomial-span unit is supplied by
[`CoefficientPolynomialUnit`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientPolynomialUnit.lean)
and `CoefficientPolynomialSpanUnit`: both original inclusion tracks keep their
exact times, and the whole identity cylinder is retained. `NormalizedUnitCoherence`,
`NormalizedUnitTrack`, `NormalizedUnitRoutes` and `OriginalUnitSquare` derive it
from the genuine geometric units and actual chosen-zero normalization.
`CoefficientBassUnitCharts` supplies the two original Laurent chart squares;
the six-face Bass identity cube and hence the whole Bass identity remain open.

[`SplitTripleSimplex`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SplitTripleSimplex.lean)
and `SplitTripleParameters` place the normalized triple and all four binary
normalization intermediates in one actual eight-slot diagram. Its six complete
displayed-component triangles have compatible whole-level scalar lifts.
[`TripleNativeEvaluation`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TripleNativeEvaluation.lean)
now identifies their assembled evaluation with the EXPORTED original triple
comparison at every level, both times and every input, including the full
degree-zero loop coordinate. The two faithful producer factorizations preserve
whole values. [`DoubleSquareMergedSimplex`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/DoubleSquareMergedSimplex.lean)
provides the larger common 18-node diagram and full original faces.
`DoubleSquareRectangleNative`, `DoubleSquareOriginalRectangle` and
`DoubleSquareRectangleFaces` prove the whole original rectangle evaluation,
complete geometric route faces and continuous three-side collapse. Generic
`ScalarChartPause` retains its boundary and side-lift premises. The joint Bass
family, all six compatible original boundary surfaces and the composition
interior cube remain separate obligations. The [TT roadmap](../development/TTLocalization.md#e-compare-to-the-original-raw-geometric-completion-e2)
records their exact role in genuine Raw2 and all-level geometric evaluation.

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

Native joint scheme/coefficient sections now supply global coarse/fine/graded
Models, actual cofinality and K₀ image exactness, canonical nulls, original
Laurent seeds and whole seed/null compatibility. `CoefficientOpenBassTower`
and `CoefficientOpenBassTelescope` retain those finite stages and transitions;
the actual graded contraction makes the original coarse-to-fine completion
restriction stable in every integer degree for qcqs ambient schemes and
quasi-compact opens. `CoefficientSupportedSections` and
`CoefficientSupportedOpenModels` supply the actual auxiliary-supported Models,
with supported cofinality and completed localization still separate.
`SupportedOpen.GrothendieckPullback`, `ImageQuotientPullback` and
`CoefficientSupportedOpenGrading` now supply the actual supported quotient
and G_Z/q_Z, retaining original relative-image witnesses; their coefficient
action needs compact P/Q, while pointwise grading has no compactness premise.
Supported cofinality/null/cones and completed localization remain separate.
`CoefficientSectionEvaluationNaturality`, `CoefficientSectionEvaluationUnit`
and `CoefficientLaurentEvaluation` preserve the actual evaluation tracks and
forward units. Seed/iterate/telescope geometric comparison and classical Kᴮ
identification remain open; see the [TT roadmap](../development/TTLocalization.md).

`BoundedFlat.OpenConeComparison` proves the actual geometric acyclic-support
cone stably equivalent to the original coarse relative-open S-prespectrum in
every signed degree, with the original target face, null cylinder, and signed
connecting map. Its geometric fibration and S-model excision premises are
discharged. This is the coarse endpoint, retaining the genuine K₀ image
obstruction to replacement by full open perfect K-theory.

[`SupportedOpen.ConeComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ConeComparison.lean)
packages the original perfect-complex auxiliary-support coarse comparison for
arbitrary schemes and opens, with the same signed boundary.
[`SupportedOpen.ExcisionSpectrum`](../../Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ExcisionSpectrum.lean)
realizes cover support excision by the original normalized restriction spectrum
map and retains its original K-map in every nonnegative degree, including zero.
Neither interface requires compactness or constructs a global completed theory.

`BoundedFlat.SectionOpenEquivalence` and `SectionOpenComparison` give exact
evaluation for the section coarse relative-open weak class and whole two-sided
prespectrum homotopies. The comparison is completely weak at every level and
stable in every integer degree; the fine/coarse square retains the unchanged
maps. `SupportedSectionOpenNull` reverses the actual weak zero-to-supported-section
transformation, producing the specified coherent null cylinder of forgetting
support followed by relative-open restriction. `SupportedSectionAcyclicEvaluation`
and `SupportedSectionAcyclicComparison` supply its exact source evaluation;
`SupportedSectionOpenNullNaturality` retains the entire reversed null track.
[`BoundedFlat.SupportedSectionOpenConeComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionOpenConeComparison.lean)
then proves `boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence`
for every open immersion into an affine base, in every signed degree.
Its connecting equation keeps the original fiber lift and null cylinder.
The endpoint is the coarse relative-open section Model; replacing it by the
full open endpoint retains a further comparison.

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

[`CofiberObjectTrack`](../../Quillen/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean)
gives `Quillen.Waldhausen.Structure.cofiberObjectLoopTrack` for a displayed
cofibration and its zero-pushout quotient, in a category with zero morphisms.
When the cofibration is weak,
[`CofiberPrismComposition`](../../Quillen/Waldhausen/GrothendieckComparison/CofiberPrismComposition.lean)
gives `Quillen.Waldhausen.Structure.cofiberPrismCompositionLoops`. The actual
source–quotient–middle triangle and its cubes retain independent nerve,
comparison, and loop coordinates. The canonical
fiber transport retains literal left concatenation and the prescribed
identity-cofiber suffix; its normalization on the first homotopy group of the
loop space agrees with that of the standard suffix-removal path. This agreement
does not identify the full paths.

For an open immersion `j : U ⟶ X`, a global scalar `r : Γ(X, ⊤)`, a specified
unit `q : Γ(U, ⊤)ˣ` with `j.appTop r = ↑q`, and `K : Perfect X`,
[`ScalarCofiberSourcePath`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSourcePath.lean),
`ScalarCofiberIteratedFiber`, and `ScalarCofiberPasting` compute the canonical
iterated-fiber loop of the actual supported scalar cofiber. The source scalar
need not be a unit and no qcqs assumption is added.
[`perfectScalarCofiberBoundaryOrientation`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberBoundaryOrientation.lean)
is an endpoint-relative homotopy to the parameter reversal of the original
forward weak scalar square. It remains at `K`'s original object-loop component.
[`perfectScalarCofiberFiberBoundaryPath`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFiberBoundaryPath.lean)
keeps the prescribed path from its loop inclusion to the translated canonical
fiber point. The two original triangles and fine weak projection determine
these paths; no replacement scalar or fiber map is chosen.

[`ScalarCofiberKOneNormalization`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberKOneNormalization.lean)
uses inverse-prefix translation and a specified cancellation path to normalize
the actual object-loop component to coarse K₁, without assuming its K₀ class
vanishes. This normalization is the inverse of the existing identity-cofiber
component equivalence. The boundary class equals the inverse of the independently
normalized forward scalar square, including the literal polynomial-coordinate
specialization. Identification with the independently prescribed Laurent
automorphism class, its connecting-map formula, the zero-section pushforward
class and possible Nil terms remain separate. No blanket perfect zero-section
dévissage is asserted.

## Image-quotient grading and cone maps

For an exact functor `F` from a Waldhausen structure `W` to `V`, the actual
image quotient is the algebraic Grothendieck group of `V` modulo the image
of the original algebraic map of `F`. The coarse weak class is equality of
these endpoint grades, retaining the original objects, cofibrations, and zero.
The following generic imports are under
`Quillen.Waldhausen.GrothendieckComparison`, with declaration namespace
`Quillen.Waldhausen.AlgebraicGrothendieck`:

| Module | Conclusion with original maps |
| --- | --- |
| [`ImageQuotient`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotient.lean) | `imageQuotient_coarseKZeroValueMap_bijective` identifies coarse K₀ with the genuine image quotient |
| [`ImageQuotientExact`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientExact.lean) | `imageQuotient_changeWeakKMap_surjective` and `imageQuotient_changeWeakKMap_range_ker` give surjectivity and kernel equal to the original exact-functor K₀ image |
| [`ImageQuotientCone`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientCone.lean), [`ImageQuotientConeZero`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientConeZero.lean) | `imageQuotientConeMap` retains the specified whole null track; `imageQuotientConeMap_stable_zero_bijective` proves its stable degree-zero bijectivity |

The K₀ conclusions retain `hF : IsExact W.cof W.weq V.cof V.weq F` and
`T : FunctorialFactorization V.smallModel` for the fine target. They do not
assume a K₀ presentation or localization exactness. The unshifted cone map
uses the reversed specified zero-to-normalized-image transformation, and its
inclusion face is exactly the original change-of-weakness map. Bijectivity in
degree zero alone does not make it a stable equivalence in all signed degrees.

[`OpenDeficitGradingStable`](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenDeficitGradingStable.lean)
specializes this to `perfectOpenDeficitGradingMap j`. Stable degree-zero
bijectivity holds for every open immersion. When `X` is qcqs and `U` is
quasi-compact, concentration of its actual source and graded target supplies
`perfectOpenDeficitGradingMap_isStableEquivalence` in every integer degree.
This is the raw-perfect objectwise comparison; coefficient naturality, the
inherited Laurent seed, and the original section comparison require their
own compatible maps.

## Graded full-open coefficient diagrams

Fix an open immersion `j : U ⟶ Spec R`. At `a : Under R`, the full-open
section category is the category of actual cocartesian sections of the
bounded-flat pullback pseudofunctor over `Under a`. Original evaluation lands
on the specified pullback open `openSpace j a`; its perfect K₀ class modulo
the image of the actual relative-open restriction is the section grade.
Only weak equivalences change to endpoint-grade equality. The inherited zero,
objects, and cofibrations remain those of the full-open section category.
The Models and prespectra live in universe `u + 1`.

The pointwise original restriction is now
`boundedFlatAffineSectionFullOpenModelMap j a` in
[`BoundedFlat.FullOpenSectionRestrictionModel`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenSectionRestrictionModel.lean).
It is an exact Model morphism with literal preservation of the entire chosen
zero section, for every open `j` and coefficient `a`. Likewise
[`FullOpenGradedSectionStable`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenGradedSectionStable.lean)
proves `boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd`
for each `d : ℤ` with `d ≠ 0`, without requiring compactness of `U`.
[`Consumer.FullOpenGradedSectionStable`](../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean)
uses that concentration for any supplied morphism between the actual graded
Models; it does not construct a missing comparison or settle degree zero.

For the coefficient **diagrams** below, additionally assume `[CompactSpace U]`.
The coefficient category is `Under R`, with arbitrary ring coefficient arrows;
neither coefficient flatness nor affineness of `U` is assumed. Actual quotient
pullback and its original evaluation equation make reindexing exact for grade
weakness. `BoundedFlat.FullOpenGradedSectionDiagram` gives a strict Model diagram,
its iterated-S prespectrum diagram, and the natural fine-to-graded map `q`.

The geometric Laurent and Bass imports under
`Quillen.AlgebraicGeometry.PerfectComplexes.Affine` expose the following
interfaces, with declaration names in `Quillen.PerfectComplexes`:

| Module | Coefficient-compatible result |
| --- | --- |
| [`FullOpenGradedLaurentContraction`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedLaurentContraction.lean), [`FullOpenGradedLaurentContractionNaturality`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedLaurentContractionNaturality.lean) | The whole forward-`T` Laurent self-track contracts to the constant track of the same coefficient map, naturally at both independent times |
| [`FullOpenSectionBassSeedChangeWeak`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionBassSeedChangeWeak.lean) | `boundedFlatAffineFullOpenSectionBassSeed_changeWeak`: `seedFine ≫ Bass.map(q) = q ≫ seedGraded` |
| [`FullOpenGradedSectionBassSeedDiagramNull`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedSectionBassSeedDiagramNull.lean) | The original graded Bass seed has a constructed whole coefficient-natural null |
| [`FullOpenGradedSectionBassTransitionNull`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedSectionBassTransitionNull.lean) | Every unchanged transition has zero stable map for every stage `k : ℕ`, coefficient `a`, and signed degree `d : ℤ` |
| [`FullOpenGradedSectionBassTelescope`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedSectionBassTelescope.lean) | Every original stage inclusion has zero stable map, and the actual graded reduced telescope has subsingleton stable groups in every integer degree |

The Laurent contraction fixes its action endpoints and full basepoint line;
it contracts a self-track, not the underlying coefficient map to zero. Its
chosen zero endomorphism is weak by reflexivity of the endpoint grade.
The resulting seed null retains the actual strict-square source-leg cone null,
the reversed null path, and the original forward Laurent action. This null is
constructed from the contraction, rather than supplied as a hypothesis.
The telescope argument uses the original seed transitions and finite-stage
representatives, without an assumption that individual stage groups vanish.
Generic iteration and telescope machinery are described in
[SpectraAndBass.md](SpectraAndBass.md).

The actual fine tower/telescope and induced finite/telescope q maps are provided
by `Affine.FullOpenSectionBassTower`, `FullOpenSectionBassTelescope`,
`FullOpenSectionBassGradingTower` and `FullOpenSectionBassGradingTelescope`.
Fine constructions require only an open immersion; grading retains compact U.

[`FullOpenSectionRestrictionDiagram`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenSectionRestrictionDiagram.lean)
gives the original coefficient-natural r, and
[`FullOpenSectionGradingNull`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenSectionGradingNull.lean)
constructs its whole coefficient-natural null followed by q.
[`FullOpenSectionConeStable`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenSectionConeStable.lean)
proves the actual null descent `Cone(r) → G` stable in every signed degree.
Its zero comparison uses genuine restriction image exactness; the degree-one
kernel uses restriction K₀ injectivity. `Affine.FullOpenSectionBassRestrictionTower`
retains that same null and stable cone descent at every finite Bass stage.

[`FullOpenSectionSpectrumComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/FullOpenSectionSpectrumComparison.lean)
gives a pointwise stable evaluation from the actual direct section Model to the
explicitly lifted bounded-flat original prespectrum. Compact U makes the
composed perfect evaluation stable. The original K-equations and chosen-zero
normalization remain explicit; no seed or telescope evaluation is inferred.

[`FullOpenSectionRestrictionSeed`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionRestrictionSeed.lean)
proves the original r seed square, and
[`FullOpenSectionGradingNullBassSeed`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionGradingNullBassSeed.lean)
proves the canonical-null time-slice seed squares with the actual Laurent tracks.
[`FullOpenSectionBassRestrictionCofiber`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionBassRestrictionCofiber.lean)
forms the original compatible telescope null and proves r∞ stable in every
integer degree by its stable cone descent and graded vanishing.
[`FullOpenSectionBassLocalization`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionBassLocalization.lean)
then gives the supported cone and fiber comparisons to the fine completion,
with the same whole null and original signed boundary. The downstream
`Consumer.FullOpenSectionComparison` constructs the actual localized coefficient
diagram isomorphisms and their natural inverses.

For arbitrary open arrows over `Spec R`, `BoundedFlat.CoefficientOpenSections`
and `CoefficientOpenGrading` now construct actual global C/F/G and coefficient-natural
r/q, using the joint native geometry and one global zero. C/F/r require no
compactness; the graded coefficient diagram requires compact source and ambient
schemes. Global cofinality, honest K₀ image exactness, canonical nulls and
original Laurent seed/tower transfer are proved. The actual native supported
cone and same-null fiber now compare stably to the fine completion for qcqs
ambient schemes and compact opens, with the original signed boundary, in
`CoefficientFullOpenBassLocalization` and its Models/Seed/Tower/Telescope owners.

Auxiliary support has the actual supported cofinality, K₀ image/kernel,
coefficient-natural null and all-integer initial cone comparison in
`CoefficientSupportedOpenCofinality`, `CoefficientSupportedOpenKZeroExact`,
`CoefficientSupportedOpenNull` and `CoefficientSupportedOpenConeStable`.
Cofinality and cone stability require compact P,Q,T and quasi-separated Q;
image/kernel requires compact P,Q, and q₀ surjectivity only compact P.
`CoefficientSupportedOpenBassSeed` and `SeedCompatibility` now supply the
original supported seeds and every whole-null seed square. The accepted
`CoefficientSupportedOpenBassTower` and `BassTelescope` retain the literal finite
stages, original telescope null, all-signed graded vanishing and stable r_Z∞,
under the same compact P,Q,T and quasi-separated Q conditions for the final
comparison. `CoefficientSupportedFiberLocalizationModels` and its
Seed/Tower/Telescope owners now construct the actual union-support fiber,
literal forget/changeWeak maps and the same-joint-zero whole null.
`CoefficientSupportedFullOpenBassLocalization` supplies its same-null stable
fiber comparison to this fine supported completion and original signed
boundary. Fiber-to-coarse stability and structural identities need only the
open immersion; final fine stability requires compact P,Q,T and
quasi-separated Q. This is constructed section-completion localization.

`CoefficientSectionEvaluationSourceLeg` supplies the original source-leg
movement and raw-cone two-time interchange, without a normalized fine-to-raw
cone/seed comparison. `ProjectiveLine.NativePerfectProjection` extends the
canonical native flat-base-change mate to intrinsic perfect inputs.
`NativePerfectGeneration` supplies affine perfect-coefficient projection and
actual O(−1) vanishing; the positive isomorphism is objectwise chosen.
Perfect pushforward of arbitrary P¹ inputs and projective generation remain open.
The actual tautological line and quotient now have the canonical determinant
pairing L⊗Q≅O, with both original chart formulas. The specified pullback-tensor
mate is invertible for this line under arbitrary scheme maps and arbitrary
other module sheaves. `ProjectiveLine.FiniteAttachment` supplies the shrinking
strict chart-window and terminal cycle tools under their actual top-epi and
lower-term-bound inputs. `Strictification` now produces the actual global
top-cycle epimorphism and strict derived model for bounded-below termwise-QC
locally perfect inputs on P¹ over arbitrary R, including the zero ring.
`NativePerfectPushforward` applies actual Rp to these representatives.
`QuasicoherentRepresentative` now constructs a genuine bounded termwise-QC
model for every intrinsic perfect D+ input, and `IntrinsicPerfectPushforward`
supplies its global strict model and perfection of actual Rp. This includes
the zero ring and needs no supplied replacement or noetherian premise.
Naturality, the exact Waldhausen roof model and projective K-generation remain
separate.
`CoefficientSectionEvaluationTopology` also supplies literal original e/V
levelwise equivalences and span/cone/loop HEP/T1.
`CoefficientSectionEvaluationComposition` has independent ordinary acceptance
for actual normalized pasting, the relative split-track comparison and both
chart/cylinder faces of Hc, without openness, compactness or flatness.
The original source-null/seed comparison and complete raw iteration remain
separate. Its exact native strict build, private-origin trust, enrollment and
affected-client integration pass at the current source identity.
Completed geometric evaluation and classical Kᴮ identification are also open.
The detailed dependency plan is
in the [TT localization roadmap](../development/TTLocalization.md).

## Remaining obligations

- Complete the Laurent-unit connecting-map and zero-section class formulas and retain possible Nil contributions; the normalized forward scalar K₁ comparison is proved.
- Establish fixed-degree stabilization of the finite seed transitions and bijectivity of the natural negative-class maps into the telescope. The finite-bottom isomorphisms and stable Bass self-comparisons do not discharge these obligations.
- Compare all iterates with the complete original geometric Bass tower, identify classical telescope negative groups, and prove the fundamental theorem, negative localization boundaries, and nonconnective descent.
- Transport the actual twoChartLine R intrinsic-perfect projection theorem to native projective lines and the required general bases/supports; identify the natural projected diagonal, prove inverse-twist tensor cancellation and exact K-generation, and establish the projective-bundle formula, Proj identification, and full twisting-sheaf family. Objectwise P1 strictification and perfect Rp for intrinsic D+ inputs are proved; the older finite-coefficient retract criterion retains its own uniform-window premises.
- Extend perfect preservation to the claimed general-source/unbounded direct-image scope, and establish general bounded-below flat-base-change invertibility beyond the available QC-single and open specializations.
- Extend strict/local equivalence to arbitrary nonaffine schemes and perfect pullback to arbitrary non-quasi-compact schemes; compare the Waldhausen and triangulated-derived Grothendieck presentations.
- Supply any needed general stable cofiber excision, replacement cofiber preservation, and higher raw-spectrum/telescope coherence. The categorical stable localization has no asserted standard stable model structure or triangulation.

The broader interface and verification boundaries are in [Scope.md](../reference/Scope.md).
Successful compilation and foundation audits concern the encoded statements;
they do not supply any of these missing comparisons.
