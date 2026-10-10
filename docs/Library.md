# Library guide

## Imports

Prefer individual modules when only one interface is needed. Selected public
entrypoints and generated whole-topic imports are also available.

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | K-groups, exact-functor maps, equivalences, and small models |
| `Quillen.Waldhausen.Basic` | Waldhausen structures, cofibrations, and weak equivalences |
| `Quillen.Waldhausen.KTheory` | Connective K-groups from the S-construction |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |
| `Quillen.Scheme` | Public geometric K/G interfaces |
| `Quillen.Resolution` | Admissible finite-resolution comparisons |
| `Quillen.PerfectComplexes.Basic` | Strict and locally-perfect connective models |
| `Quillen.PerfectComplexes.GilletWaldhausen` | Vector-bundle/strict-perfect comparison |
| `Quillen.PerfectComplexes.DerivedPullbackFunctor` | Perfect K-theory on quasi-compact schemes |
| `Quillen.PerfectComplexes.Affine.PrincipalPerfectLocalization` | Affine principal-open connective localization |
| `Quillen.Waldhausen.Fibration.GeneralComparison` | Change of weak equivalences with explicit cylinder data |
| `Quillen.Waldhausen.Cofinality.GeneralDense` | Dense-subcategory cofinality with explicit closure and cylinder data |
| `Quillen.Waldhausen.QuillenComparison.Equivalence` | The exact-category Q/S comparison |
| `Quillen.Library` | Selected public K/G interfaces |
| `Quillen` | Complete library |

Generated subject imports include `Quillen.Algebra`, `Quillen.CategoryTheory`,
`Quillen.Topology`, `Quillen.KTheory`, `Quillen.Devissage`, `Quillen.Localization`,
`Quillen.GTheory`, `Quillen.PerfectComplexes`, and `Quillen.Waldhausen`.

## Exact categories and K-groups

For an exact structure `E`, the main objects are:

- `E.QCategory`: the restricted-span Q-category.
- `E.KSpace` and `E.kBasepoint`: its classifying space and distinguished point.
- `E.K n`: its connective K-group in degree `n`.
- `E.SmallK n`: K-theory using the chosen small-model interface.

An exact functor `F : ExactFunctor E E'` induces `F.mapQ`, `F.KMap n`, and
`F.smallKMap n`. The API includes identity, composition, and natural-isomorphism
laws. For a composable functor `G`, `ExactFunctor.KMap_comp_apply` identifies
the composite pointwise:

```lean
(F.comp G).KMap n x = G.KMap n (F.KMap n x)
```

`SmallExactCategory.ofExactStructure E` bundles the input, and
`SmallExactCategory.KFunctor n` gives the corresponding group-valued functor.
These interfaces reuse the same K-groups and canonical maps.

## Waldhausen's S-construction

For `W : Quillen.Waldhausen.Structure C`, the structure specifies cofibrations,
weak equivalences, and a zero object. `W.Delooping` realizes the diagonal of
the S-construction nerve, `W.kBasepoint` is its chosen point, and `W.K n` gives
the associated connective groups.

This interface is separate from exact-category Q-theory. The canonical
comparison for exact categories is provided by
`Quillen.Waldhausen.QuillenComparison.Equivalence`. Other models and comparison
maps retain their own hypotheses.

`Quillen.Waldhausen.Fibration.GeneralComparison` provides
`Quillen.Waldhausen.Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general`.
It takes nested weak equivalences, coarse two-out-of-three and extension,
joint-cylinder data, and the second-endpoint section identity. Object and
morphism universes may differ. `Quillen.Waldhausen.Fibration.LongExactSequence`
then supplies the acyclic-inclusion, change-of-weak-equivalences, and connecting
maps with their exactness statements.

`Quillen.Waldhausen.GilletWaldhausen.GeneralComparison` provides
`Quillen.Waldhausen.GilletWaldhausen.boundedTermsSingle_coarse_KEquiv_general`.
Its term property on the stated abelian category must contain zero and be
closed under isomorphisms, extensions, and admissible kernels. The forward map
is the single-complex K-map, in every nonnegative degree.

## Localization and dévissage

`Quillen.Devissage` provides the finite-filtration hypothesis and the induced
K-equivalence for the stated abelian setting. The Serre localization namespace
provides `quotientKMap`, `connectingHom`, and `localizationSequence`, with
individual exactness statements and the connective K₀ tail.

These are maps of the specified inclusions and quotient functors. The exact
premises remain part of each theorem; consult [Scope.md](Scope.md) before using
them outside their stated categorical setting.

## Scheme interfaces and universes

For `X : AlgebraicGeometry.Scheme.{u}`, `Quillen.Scheme.K X n` uses finite
locally free sheaves, while `Quillen.Scheme.G X n` uses coherent sheaves under
the stated local noetherian hypotheses. These public types lie in `Type (u + 1)`.
The strict and locally-perfect scheme K-groups use that same group universe.
The separately named affine interface `Quillen.Scheme.Affine.G R n` lies in
`Type u`; it should not be treated as a definitional alias of global scheme G.

`Quillen.Scheme.restrictK` and `restrictG` are induced by open restriction.
`Quillen.Scheme.KToG` is the canonical inclusion map. Relevant modules include:

- `Quillen.Scheme.OpenImmersionFunctor`: restriction functoriality and naturality.
- `Quillen.Scheme.Localization`: noetherian open localization.
- `Quillen.Scheme.ClosedGTheory`: closed-subscheme dévissage and pushforward.
- `Quillen.Scheme.Regular`: regular K→G comparison with explicit hypotheses.
- `Quillen.Scheme.Pullback`: `Quillen.Scheme.pullbackK` and the contravariant
  `Quillen.Scheme.KFunctor` for all scheme morphisms.
- `Quillen.Scheme.FlatPullback`: `Quillen.Scheme.pullbackG` for flat morphisms
  between locally noetherian schemes, with `Quillen.Scheme.KToG_pullback`.

The regular affine equivalence has no finite Krull-dimension bound. The
nonaffine equivalence retains quasi-compactness and the resolution property.
The pullback APIs have identity and composition laws and agree with open
restriction. Flatness remains part of the coherent G-theory pullback interface.

## Perfect complexes

Names in this section belong to `Quillen.PerfectComplexes`, with `Affine.`
indicating its affine namespace. `StrictPerfect X` consists of globally bounded
complexes of finite locally free sheaves. `Perfect X` consists of complexes of
module sheaves that are locally isomorphic in the quasi-isomorphism localization
to strict perfect complexes. `StrictK X n` and `PerfectK X n` are their
connective S-construction groups.

The principal interfaces are:

| Module | Selected declarations and scope |
| --- | --- |
| `Quillen.PerfectComplexes.SplitComparison` | `splitStrictKEquiv` and `splitPerfectKEquiv` compare split and ambient-monomorphism cofibrations |
| `Quillen.PerfectComplexes.GilletWaldhausen` | `vectorBundleToStrictKEquiv X n` for every scheme and nonnegative degree |
| `Quillen.PerfectComplexes.PullbackFunctor` | `strictKPullback`, `StrictKFunctor`, and `vectorBundleToStrictNatIso` for arbitrary scheme morphisms |
| `Quillen.PerfectComplexes.DerivedPullbackFunctor` | `perfectKPullback` and `PerfectKFunctor` for arbitrary morphisms between quasi-compact schemes |
| `Quillen.PerfectComplexes.Affine.SchemeKEquivalence` | `affineStrictToPerfectKEquiv` and `affineVectorBundleToPerfectKEquiv` for `X` with `IsAffine X` |
| `Quillen.PerfectComplexes.PerfectSupport` | `PerfectSupportedK j n` and its forget-support map `perfectSupportedKMap` |
| `Quillen.PerfectComplexes.OpenLongExactSequence` | `PerfectOpenK j n`, `perfectOpenConnectingHom`, and `perfectOpen_positiveLongExactSequence` for any open immersion |
| `Quillen.PerfectComplexes.Affine.OpenKEquivalence` | `Affine.strictToPerfectOpenKEquiv` for every open immersion into `Spec R` |
| `Quillen.PerfectComplexes.Affine.SupportedStrictPerfectKEquivalence` | `Affine.strictSupportedToPerfectKEquiv` for every open immersion into `Spec R` |
| `Quillen.PerfectComplexes.Affine.PrincipalPerfectCofinality` | `Affine.principalPerfectOpenKEquiv` in positive degrees and `Affine.principalPerfectOpenKZeroImageEquiv` in degree zero |
| `Quillen.PerfectComplexes.Affine.PrincipalPerfectLocalization` | `Affine.principalPerfectConnectingHom`, `Affine.principalPerfect_positiveLongExactSequence`, and `Affine.principalPerfect_zeroTail` |

The vector-bundle/strict-perfect comparison holds in every nonnegative degree
on every scheme. The strict/local and vector-bundle/local affine comparisons
also include degree zero, and retain the canonical comparison maps as their
forward homomorphisms. They require no regularity or noetherianity hypothesis.

For `j : U ⟶ Spec R`, the relative and supported affine comparisons permit any
open `U`, including a non-quasi-compact open. They compare models on the affine
base. Identifying `PerfectOpenK j n` with `PerfectK U n` is a separate endpoint
question. For a principal open, the positive endpoint is an equivalence; its
degree-zero endpoint is precisely `(perfectKRestrict j 0).range`.

The quasi-compact perfect pullback uses bounded-above flat representatives and
agrees with the existing flat-pullback and open-restriction maps. Its identity,
composition, and comparison-naturality statements include degree zero. A
general non-quasi-compact perfect pullback needs further foundations.

See [ThomasonTrobaugh.md](ThomasonTrobaugh.md) for the model definitions,
localization maps, and remaining global and nonconnective scope.

## Cofinality and algebraic classes

`Quillen.Waldhausen.Cofinality` separates group gradings, zero-grade categories,
and dense full subcategories. In `Quillen.Waldhausen.Cofinality.GeneralDense`,
`Quillen.Waldhausen.Cofinality.DenseCofiberData.inclusionKEquivGeneral` gives
the positive-degree equivalence under the specified dense-cofiber and
joint-cylinder data, including the second-endpoint section. The accompanying
degree-zero theorem gives injectivity and the exact tail for its coarse model.

`Quillen.Waldhausen.GrothendieckGroup.Basic` defines
`Quillen.Waldhausen.AlgebraicGrothendieck.Group W` from zero, weak-equivalence,
and cofibration-pushout relations, with `objectClass` and a universal grading
property. This algebraic group has its own API. Its identification with
homotopical `W.K 0` remains a separate comparison.

## Examples and references

The [downstream package](../examples/downstream) contains client proofs for
exact-functor laws, localization, dévissage, regular comparisons, scheme
restriction, and Waldhausen interfaces. It uses a local path dependency with
its own manifest and build directory.

Mathematical references:

- [Quillen, Higher Algebraic K-theory I](https://link.springer.com/chapter/10.1007/BFb0067053).
- [Bühler, Exact Categories](https://arxiv.org/abs/0811.1480).
