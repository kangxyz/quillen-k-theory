# Scheme K/G-theory

Scheme K-theory uses actual finite locally free sheaves, and coherent G-theory uses affine-locally finite-type quasicoherent sheaves on locally Noetherian schemes. The canonical comparison is induced by their exact inclusion. The source-family guides below retain the actual sheaf functors, universes, and degree conventions.

## Family guides

- [Coherent localization and finite direct image](Coherent/README.md)
- [Regular K-to-G comparison](Regular/README.md)
- [Two-chart projective-line geometry](ProjectiveLine/README.md)
- [Perfect-complex K-theory](../PerfectComplexes/README.md)

## Objects and conventions

Bounded-below derived sheaf operations and the actual two-chart line are developed in the [derived-operation candidates](../../Aglib/AlgebraicGeometry/Modules/DerivedCategory/README.md) and [projective-line sheaf guide](ProjectiveLine/README.md). The [perfect projective-line guide](../PerfectComplexes/ProjectiveLine/README.md) records the intrinsic-perfect extension and native qcqs K-inverse.

## Public imports

`import Quillen.AlgebraicGeometry.Scheme` exposes the selected K/G,
regular-comparison, and localization interfaces. Pullback, finite direct image,
and the sheaf geometry can be imported through their individual owners:

| Source / interface | Description |
| --- | --- |
| [`Scheme.KTheory`](KTheory.lean), [`Scheme.GTheory`](GTheory.lean) | `AlgebraicGeometry.Scheme.K`, `G`, `restrictK`, `restrictG` |
| [`Scheme.Comparison.KToG`](Comparison/KToG.lean) | `AlgebraicGeometry.Scheme.KToG`, `KToG_restrict` |
| [`Scheme.Pullback`](Pullback.lean), [`Scheme.FlatPullback`](FlatPullback.lean) | `AlgebraicGeometry.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| [`Scheme.Regular`](Regular.lean) | `AlgebraicGeometry.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
| [`Scheme.Localization`](Localization.lean), [`Scheme.ClosedGTheory`](ClosedGTheory.lean) | `AlgebraicGeometry.Scheme.localization_longExact`, `AlgebraicGeometry.Scheme.Closed.supportedGEquiv`, `localization_longExact` |
| [`Scheme.FinitePushforward`](FinitePushforward.lean), [`Scheme.FiniteFlatPushforward`](FiniteFlatPushforward.lean) | `AlgebraicGeometry.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| [`Scheme.Comparison.KToGFinitePushforward`](Comparison/KToGFinitePushforward.lean) | `AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward` |
| [Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/Functoriality/PushforwardComposition.lean) | `AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusCompIso` |
| [Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/ProjectionFormula/Basic.lean) | `AlgebraicGeometry.Scheme.Modules.derivedProjectionFormulaIso` |
| [Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Cohomology/BaseChange/Flat.lean) | `AlgebraicGeometry.Scheme.Modules.derivedFlatBaseChangeMap` |
| [`Scheme.ProjectiveLine.DerivedCechTriangle`](ProjectiveLine/DerivedCechTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.derivedCechTriangle` |
| [`Scheme.ProjectiveLine.VectorBundleCech`](ProjectiveLine/VectorBundleCech.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.exists_original_vectorBundle_cech_model` |
| [`Scheme.ProjectiveLine.DerivedCechCone`](ProjectiveLine/DerivedCechCone.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.derivedCechConeIso` |
| [`Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle`](ProjectiveLine/DiagonalProjectedTensorTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.diagonalCoefficientTensorTriangle` |
| [`Scheme.ProjectiveLine.DiagonalComplexProjectedTriangle`](ProjectiveLine/DiagonalComplexProjectedTriangle.lean) | `AlgebraicGeometry.Scheme.ProjectiveLine.diagonalDerivedComplexCoefficientTriangleFunctor` |

Unqualified declaration names continue in the preceding displayed namespace.
Below, geometric module paths abbreviated as `Scheme.…` have prefix
`Quillen.AlgebraicGeometry.`; declaration namespaces are stated independently.

## Sheaf categories, universes, and degrees

For `X : AlgebraicGeometry.Scheme.{u}`, `AlgebraicGeometry.Scheme.Modules.FiniteLocallyFree X`
is the full category of module sheaves with finite local bases. Its conflations
are actual sheaf short exact sequences, giving `vectorBundleExactStructure X`.
`AlgebraicGeometry.Scheme.K X n` is the K-group of its chosen `u + 1` small model.
This definition is available on every scheme.

`AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X` tests quasicoherence and
finite type on **every** actual affine open chart. `FiniteTypeSheaves X` is
defined over every scheme, as is `AffineFiniteType R` over any affine ring.
On locally noetherian schemes the global category is abelian, with exact
structure `coherentExactStructure X`; its exact sequences are precisely the
ambient sheaf short exact sequences. The
[Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/Coherent/FinitePresentation.lean), [Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/FinitePresentation/AffineTransport.lean), [Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/AlgebraicGeometry/Modules/FinitePresentation/Noetherian.lean)
proves that these sheaves are locally finitely presented under the same
noetherian hypothesis. Generic finite-type definitions alone do not install
these abelian or exact structures.

`AlgebraicGeometry.Scheme.K X n` and `G X n` lie in `Type (u + 1)`, whereas the separately
named `AlgebraicGeometry.Scheme.Affine.G R n` lies in `Type u` for a noetherian
`R : CommRingCat.{u}`. `Affine.moduleEquiv` identifies the latter with finite-module
G-theory through actual affine global sections. These presentations retain
their universe bounds; the global group is not definitionally replaced by
the lower-universe affine group. Each bundled essentially small category uses its actual selected small model; a universe change is not a new arbitrary identification.

K and G have index `n : ℕ` and use exact-category `K_n = π_(n+1)(BQ)`.
In the sheaf sections below, `D+` means `DerivedCategory.Plus X.Modules`,
using cochain complexes indexed by `ℤ` with a lower bound. A sheaf is placed
in degree zero by `singleZeroPlus` or the corresponding derived single functor;
`rightDerived n` denotes the `n`th derived image for `n : ℕ`.

## Restriction, pullback, and the canonical comparison

`restrictK j n` and `restrictG j n` are the canonical small-K maps of actual
open restriction. G-restriction requires local noetherianity of source and
target. `KToG X n` is the original small-K map of
`vectorBundleToCoherentExact X`; `KToG_restrict` preserves the square of
these original restrictions.

`pullbackK f n` accepts every scheme map. Pullback preserves finite local
freeness, and the local splitting of vector-bundle short exact sequences gives
exactness without flatness. Its identity and composition laws define
`KFunctor n` on the opposite of the full scheme category; on open immersions,
`pullbackK_eq_restrictK` identifies the old restriction map.

`pullbackG f n` instead requires `[Flat f]` and locally noetherian source and
target. Exact flat sheaf pullback gives `coherentExactPullback f`, with its
identity, composition, and open-restriction laws. `GFlatFunctor` is defined on
the opposite category of locally noetherian schemes with flat morphisms;
`KToGFlatNatTrans` retains the original K-to-G maps. The theorem
`KToG_pullback` expresses that naturality on each flat map.

The vector-bundle/strict-perfect K comparison holds on every scheme, and
strict-perfect K also has all-map pullback. Pullback on localized perfect K
has its separate quasi-compactness boundary. Those models and their comparisons
are described in [perfect-complex K-theory](../PerfectComplexes/README.md).

## Remaining comparisons and independent consumers

The two-chart line is not identified with Proj or a full twisting-sheaf family. Its intrinsic-perfect derived projection, natural generation triangle, affine two-summand K-inverse, native qcqs K-inverse, and compact-open supported bijection are recorded in the [projective-line perfect guide](../PerfectComplexes/ProjectiveLine/README.md). Arbitrary-base-map naturality and the general projective-bundle formula remain separate. The Čech cone comparison is for quasicoherent singles; general bounded-below flat-base-change invertibility is not inferred. Proper pushforward, general-source perfect preservation, and unrestricted unbounded derived direct image remain open comparisons.

Existing independent clients illustrate these precise interfaces:
[Scheme](../../../examples/downstream/Consumer/Scheme.lean) checks geometric
restrictions and K-to-G naturality;
[Regular](../../../examples/downstream/Consumer/Regular.lean) checks regular
affine/nonaffine comparisons and forward maps;
[ClosedGTheory](../../../examples/downstream/Consumer/ClosedGTheory.lean) and
[AffineClosed](../../../examples/downstream/Consumer/AffineClosed.lean) retain
actual closed/open maps;
[FinitePushforward](../../../examples/downstream/Consumer/FinitePushforward.lean),
[FiniteFlatPushforward](../../../examples/downstream/Consumer/FiniteFlatPushforward.lean),
and [StrictFiniteFlatPushforward](../../../examples/downstream/Consumer/StrictFiniteFlatPushforward.lean)
use direct-image comparison laws;
[AffineDerivedPushforward](../../../examples/downstream/Consumer/AffineDerivedPushforward.lean)
and [DerivedPushforwardComparison](../../../examples/downstream/Consumer/DerivedPushforwardComparison.lean)
use the original installed units to detect equality of derived arrows.
These clients do not add the remaining geometric comparisons.

## Source interfaces

| Source / interface | Description |
| --- | --- |
| `Scheme.Pullback`, `Scheme.FlatPullback` | `AlgebraicGeometry.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| `Scheme.FinitePushforward`, `Scheme.FiniteFlatPushforward` | `AlgebraicGeometry.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| `Scheme.Regular` | `AlgebraicGeometry.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
| `PerfectComplexes.Basic`, `PerfectComplexes.KTheory` | `Quillen.PerfectComplexes.StrictK`, `PerfectK` |
| `PerfectComplexes.OpenFunctor` | `perfectOpenKMap`, `perfectOpenKRestrict`, `perfectKRestrict` |
| `PerfectComplexes.OpenLongExactSequence` | `perfectOpenConnectingHom`, `perfectOpen_positiveLongExactSequence` |
| `PerfectComplexes.GlobalLocalization` | Actual open endpoint, positive comparison and degree-zero image |
| `PerfectComplexes.MayerVietoris` | Two-open connective sequence and matching K₀-class gluing |
