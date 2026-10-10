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

## Bass groups, spectra, and remaining scope

`Bass.negativeKFunctor n` recursively takes the two polynomial-to-Laurent
cokernels, seeded by original homotopical perfect K₀ in additive notation.
`n : ℕ` denotes degree `-n`. It accepts arbitrary maps between quasi-compact
schemes. `Bass.supportedNegativeKFunctor` has the analogous supported K₀ seed
on pairs with quasi-compact ambient scheme and arbitrary vanishing open.
See [BassNegativeGroups.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/BassNegativeGroups.lean)
and [Bass/SupportedGroups.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedGroups.lean).

`Quillen.Bass.affineSchemeNegativeKIso` compares the affine ring and geometric
scheme-product recursions naturally in all nonpositive degrees, with literal
original K₀ in degree zero. `affineBassTransition` constructs one spectral Bass
step from the actual Laurent unit and inverse, scalar action, and whole
structure-compatible homotopy. See [Affine/BassStep.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassStep.lean).
Coherent functorial spectral iteration, identification with the cokernel groups,
the fundamental theorem, and negative localization/descent remain open. These
groups are not identified with algebraic Grothendieck K₀ or negative stable
groups of a Bass spectrum.

The connective perfect spectra have arbitrary derived pullback on
quasi-compact schemes in the constructed categorical stable localization,
retaining original K-maps and flat pullback. Their negative stable groups still
vanish. The localized inverse of the bounded-flat inclusion does not assert a
strict continuous inverse. See [Library.md](Library.md#stable-fibers-and-localization).

Strict/local comparison on arbitrary nonaffine schemes, perfect pullback on
arbitrary non-quasi-compact schemes, stable cofiber exactness and telescope
comparisons, projective-bundle and Laurent-boundary calculations, and the
nonconnective localization theorem require further work. The actual two-chart
projective line and global sections are available, but higher cohomology and
perfect pushforward remain separate.
See [Scope.md](Scope.md) for the precise boundary.
