# Scheme Bass recursion and nonpositive localization

## Cokernel recursions and original geometric seeds

`Bass.negativeKFunctor i` takes the original two-polynomial-to-Laurent cokernel
recursively, seeded by additive homotopical perfect K₀. Index `i : ℕ` means
degree `-i`. It accepts arbitrary maps between quasi-compact schemes.
`Bass.supportedNegativeKFunctor` has the supported K₀ seed on pairs with
quasi-compact ambient scheme and arbitrary vanishing open. Their routes are
[BassNegativeGroups.lean](../BassNegativeGroups.lean)
and [Bass/SupportedGroups.lean](SupportedGroups.lean).
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

## Original nonpositive localization sequence

Let `A : QuasiCompactOpenPairs`, with removed open `U`, ambient scheme `X`,
compact `U` and qcqs `X`. Write `N_i(X)` and `N_i(X on X−U)` for the original
ambient and supported Bass recursions, where `i : ℕ` denotes degree `-i`.
[`Bass/SupportedLocalizationExactness`](SupportedLocalizationExactness.lean)
and [`Bass/SupportedLocalizationBoundary`](SupportedLocalizationBoundary.lean)
give the recurring exact positions

```text
N_i(X on X−U) → N_i(X) → N_i(U)
  → N_(i+1)(X on X−U) → N_(i+1)(X) → N_(i+1)(U).
```

The arrows at the ambient groups are the original `supportedNegativeKForget`
and `negativeKPullback`. `supportedNegativeLocalizationConnecting` is the
fixed signed same-null fine cone boundary transported through the actual
comparison isomorphisms and both identity-coefficient projection legs.
The degree-zero restriction is the original `perfectKRestrict`.
`supportedLocalization_zeroTail` joins the existing geometric
`qcqsPerfectConnectingHom` from K₁(U) to supported K₀ by exactness at the
literal K₀ groups. It does not identify that geometric connecting map with
the fine connecting map. Arbitrary-pair pullback naturality of the transported
boundary and identification with the classical raw boundary remain open.
The coefficient-level owners are `CoefficientFullOpenBassRestriction`,
`CoefficientNegativeLocalizationExactness` and
`CoefficientNegativeLocalizationBoundary`. The full-open fine row, action,
seed and telescope are definitionally the ambient ones on the open scheme;
the telescope localization map equals original scheme restriction on every
cylinder using only the open-immersion hypothesis. The final group comparisons
use the compactness and separation hypotheses stated above.

The actual native zero section and its pair analogue now split polynomial
projection pullback in every recursive negative degree and every nonnegative
perfect K degree. `Bass.PolynomialZeroSection` and
`Bass.SupportedPolynomialZeroSection` retain the original common-corner
diagonal, its specified evaluation retraction and zero composite with the
original plus-minus chart difference. The supported open need not be compact.
Middle exactness, seed preservation and the stage-i colimit isomorphism do not
follow from this splitting alone.
