# Coherent G-theory, localization, and finite direct image

## Objects and conventions

[`Affine.UniverseComparison`](Affine/UniverseComparison.lean)
provides `publicSpecGRingEquiv` in all degrees for Noetherian rings, through
model-universe transport of the same original coherent category. The
residue-field comparison preserves the original public scheme pushforward.
[`Affine.LocalizationNaturality`](Affine/LocalizationNaturality.lean)
identifies literal `Scheme.pullbackG` for localization at any submonoid with
original finite-module localization in every degree.
[`Affine.PrincipalBoundaryComparison`](Affine/PrincipalBoundaryComparison.lean)
also identifies the original principal scheme boundary with finite-module
localization for every Noetherian ring and element, including G1 to G0.
[`Dedekind.PrincipalDvrBoundaryComparison`](../../../GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean)
identifies this boundary with the original native local-DVR boundary, retaining
any specified fraction field and the actual generic/closed pullbacks.

[`FinitePointAssembly`](ClosedImmersion/FinitePointAssembly.lean)
then supplies `fieldAssemblyKEquiv` in every positive degree, including K1
and K2. Its hypotheses are a Noetherian `X : Scheme.{u}`, an index
`I : Type u`, an injective closed-point family, and closed immersions
`Spec (fields i) ⟶ X` from specified fields with those singleton images.
The target is actual support containment in the original upper-small
coherent category. Singleton, finite-sum and ambient equations identify
the forward map with the original public field-scheme pushforwards.

## Coherent open and closed localization

For an open immersion `j : U ⟶ X`, `SupportedG j n` uses the Serre category of
coherent sheaves whose actual restriction to `U` vanishes. On a noetherian
ambient scheme, with the stated local noetherianity of `U`,
`AlgebraicGeometry.Scheme.localization_longExact j` has maps `inclusionG`, `restrictG`,
and `boundaryG`. It proves all recurring connective exactness positions and
`restrictG_zero_surjective`, including arbitrary opens of `X`.

For a closed immersion `i : Z ⟶ X` with `[IsNoetherian X]`, the
`AlgebraicGeometry.Scheme.Closed` interface constructs the actual open complement and
derives noetherianity of `Z`. `supportedGEquiv i n` identifies G of that
original closed scheme with the supported term by dévissage. Its composite
with supported inclusion is exactly `pushforwardG i n`, the actual coherent
sheaf direct image. The transported `boundaryG i n` gives

```text
… → G_(n+1)(U) → G_n(Z) → G_n(X) → G_n(U) → … → G_0(U) → 0.
```

Principal closed/open and arbitrary-ideal affine specializations preserve the
same geometric maps; the complement of an arbitrary ideal need not be affine.
The [localization guide](../../../Localization/Serre/README.md) explains the Serre theorem and its
finite-module applications underlying these geometric sequences.

## Finite direct image

For an actual finite map `f : Z ⟶ X`, Aglib's
[finite-type quasicoherent pushforward](https://github.com/kangxyz/aglib/blob/52e09db47998f139064acf48a2d3a64494d0dd9a/Aglib/AlgebraicGeometry/Modules/QuasiCoherent/FiniteType/Pushforward.lean)
preserves affine-local finite-type quasicoherent sheaves without noetherian
assumptions. On locally noetherian source and target, the
[Quillen G-map construction](Finite/GeneralPushforward.lean)
uses the native exact functor and constructs
`AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap`.
`GFinitePushforwardFunctor` has identity and composition laws; scheme-isomorphism,
open-base-change, finite-affine, and closed-immersion formulas retain the
original functors and G-maps.

Finite **flat** maps of locally noetherian schemes preserve vector bundles and
give `AlgebraicGeometry.Scheme.Modules.schemeKPushforward` and `KFiniteFlatPushforwardFunctor`.
Target noetherianity is used to make the affine finite flat modules finite
projective; exactness is transported through coherent inclusion.
`KToGFiniteFlatPushforward` is the natural transformation with the original
K-to-G components. These hypotheses do not give vector-bundle direct image
for every finite map or over arbitrary nonnoetherian bases.

[`PerfectComplexes.FiniteFlatPushforward`](../../PerfectComplexes/FiniteFlatPushforward.lean)
uses the same sheaf direct image on strict-perfect complexes, proves
quasi-isomorphism preservation using exact coherent direct image, and defines
`Quillen.PerfectComplexes.strictKFiniteFlatPushforward`.
`FiniteFlatPushforwardNaturality` preserves `vectorBundleToStrictKMap` in every
nonnegative degree. `DerivedPushforwardComparison` identifies strict direct
image with installed D+ direct image. The theorem
[`Affine.perfectDerivedObjects_derivedPushforwardPlus`](../../../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Affine/DerivedFiniteFlatPushforward.lean)
preserves intrinsic D+ perfectness for affine source and a finite flat map to
a locally noetherian target; general-source preservation is separate.

## Source interfaces

| Source / interface | Description |
| --- | --- |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.FinitePointAssembly` | Public field-scheme G assembly into actual upper coherent support, every positive degree; Noetherian scheme, injective closed-point family and specified field closed immersions |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.UniverseComparison` | `publicSpecGRingEquiv` in all degrees over Noetherian rings and original public scheme residue-pushforward comparison |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality` | Literal public `Scheme.pullbackG` equals native localization for every Noetherian ring and submonoid, in all degrees |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.PrincipalBoundaryComparison` | Original principal scheme boundary equals finite-module localization through the canonical affine G-equivalences, in all degrees |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.RingIsoNaturality` | Original Spec ring-isomorphism pullback equals restriction along the inverse ring isomorphism |

## Declaration locators

These additional names use the same objects, hypotheses, and original maps as the linked construction sections. They are locators within those interfaces, not stronger comparison statements.

| Declaration / module | Construction and conditions |
| --- | --- |
| `ClosedImmersion.FinitePointAssembly.fieldAssemblyKEquiv` | [Objects and conventions](#objects-and-conventions) |

## Finite-type interfaces and coherent specialization

For finite direct-image data on arbitrary schemes, use the native `AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward` and `finiteTypePushforwardSpec` interfaces. Their coherent specializations require locally Noetherian source and target.

General finite-type pullback requires a locally Noetherian target and allows an arbitrary source. Its coherent specialization assumes both schemes locally Noetherian. The lower finite-type interface retains these weaker hypotheses; the stronger coherent specialization is used only when its additional source condition is available.
