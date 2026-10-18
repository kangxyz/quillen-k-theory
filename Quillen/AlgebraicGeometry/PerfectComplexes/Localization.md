# Perfect-complex localization and pullback

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
See [OpenFunctor.lean](OpenFunctor.lean).

The actual homotopy-fiber boundary is `perfectOpenConnectingHom j n`.
`perfectOpen_positiveLongExactSequence` gives the recurring exact positions in

```text
PerfectK X (n+1) → PerfectOpenK j (n+1) → PerfectSupportedK j n
                → PerfectK X n → PerfectOpenK j n.
```

Exactness is range equals kernel. `perfectOpenKMap_zero_surjective` supplies
surjectivity onto relative K₀.
See [OpenLongExactSequence.lean](OpenLongExactSequence.lean).
For an arbitrary open, `PerfectOpenKZeroImage j` is exactly
`(perfectKRestrict j 0).range`; the general image construction first quotients
the relative group by its endpoint kernel.

## Model comparisons and pullback

Every row below includes degree zero and uses its canonical comparison map.

| Conditions | Comparison | Source |
| --- | --- | --- |
| Every scheme `X` | `vectorBundleToStrictKEquiv X n` | [GilletWaldhausen.lean](GilletWaldhausen.lean) |
| Affine `X` | `affineStrictToPerfectKEquiv`, `affineVectorBundleToPerfectKEquiv` | [Affine/SchemeKEquivalence.lean](Affine/SchemeKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictToPerfectOpenKEquiv R j n` | [Affine/OpenKEquivalence.lean](Affine/OpenKEquivalence.lean) |
| Every open `j : U ⟶ Spec R` | `Affine.strictSupportedToPerfectKEquiv R j n` | [Affine/SupportedStrictPerfectKEquivalence.lean](Affine/SupportedStrictPerfectKEquivalence.lean) |
| Quasi-compact `X` | `BoundedBelow.inclusion_KMap_bijective X n` | [BoundedBelowComparison.lean](BoundedBelowComparison.lean) |
| Quasi-compact `X`, arbitrary localization open `U` and auxiliary open `T` | `boundedFlatPerfectSupportedOpenKEquiv j T n` | [BoundedFlat/SupportedOpenComparison.lean](BoundedFlat/SupportedOpenComparison.lean) |

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
[`FlasqueBoundedBelow`](FlasqueBoundedBelow.lean)
constructs the actual termwise-flasque full model and exact total functor.
Its two forward natural weak units yield mutually inverse original inclusion
and total K-maps for every scheme and every nonnegative degree, including
zero. [`FlasqueBoundedBelowComparison`](FlasqueBoundedBelowComparison.lean)
identifies its literal composite inclusion into all perfect complexes on
quasi-compact schemes.

The exact projective-line coefficient models, original two-summand K-maps, affine and native qcqs inverse laws, and compact-open support extension are developed in the [projective-line perfect guide](ProjectiveLine/README.md). Their original units, right/left tensor order, total augmentations, signed shifts, and product normalization are retained there.

[`NativeBassCharts`](ProjectiveLine/NativeBassCharts.lean)
identifies the original two polynomial charts and signed Laurent difference;
on a qcqs base, the range of the actual restriction pair is its kernel in
every nonnegative degree, including zero.
[`NativeCoordinate` ](../Scheme/ProjectiveLine/NativeCoordinate.lean)
constructs the original global first coordinate with identity on the positive
chart and the original polynomial scalar on the negative chart.
[`NativeCoefficientCoordinate`](ProjectiveLine/NativeCoefficientCoordinate.lean)
tensors it with any perfect coefficient, constructs its literal signed cone
supported outside the positive native range, and identifies its negative
restriction with the polynomial scalar cone. These coordinate constructions
need only a quasi-compact base. Identifying the forgotten cone K-class and the
original terminal boundary remains separate.

`strictKPullback` accepts every scheme map. `perfectKPullback` accepts arbitrary
maps between quasi-compact schemes, uses bounded-above flat representatives,
and gives `PerfectKFunctor`. Its identity, composition, restriction, and
comparison-naturality laws include zero.
See [DerivedPullbackFunctor.lean](DerivedPullbackFunctor.lean).

## Global qcqs endpoint and connective sequence

Assume `X` is quasi-compact and quasi-separated and `j : U ⟶ X` is an open
immersion with quasi-compact `U`. In Lean these conditions are
`[CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [IsOpenImmersion j]`.

`qcqsPerfectOpenKEquiv j n` identifies `PerfectOpenK j (n+1)` with
`PerfectK U (n+1)` using the original `perfectOpenKRestrict` as forward map.
`qcqsPerfectOpenKZeroImageEquiv j` identifies relative K₀ with precisely
`PerfectOpenKZeroImage j`. The endpoint is injective and its image is exactly
the image of original absolute restriction.
See [GlobalCofinality.lean](GlobalCofinality.lean).

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
See [GlobalLocalization.lean](GlobalLocalization.lean).
Ordinary open-pair naturality holds for every commuting base-map square with
qcqs bases and quasi-compact opens, without flat or cartesian assumptions,
including the boundary into supported K₀.
See [GlobalLocalizationNaturality.lean](GlobalLocalizationNaturality.lean).

Principal opens of affines are a special case over every commutative ring,
including zero divisors and localization at zero. The focused interface is
`Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectLocalization`.
