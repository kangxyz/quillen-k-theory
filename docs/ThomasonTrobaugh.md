# Perfect-complex localization

The library provides connective K-groups of strict and locally perfect
complexes, comparisons with vector-bundle K-theory, and localization for
principal opens of affine schemes. The general open-immersion interface first
produces a relative Waldhausen model. Identifying that model with perfect
K-theory of the open is a separate geometric comparison.

This guide records the current models and their public maps. It does not claim
the full nonconnective Thomason–Trobaugh localization theorem.

## Complexes, support, and the relative model

The names below belong to `Quillen.PerfectComplexes` unless a namespace is
specified. For `X : AlgebraicGeometry.Scheme.{u}`:

- `Complex X` is the category of integer-indexed cochain complexes of
  `O_X`-module sheaves.
- `strictPerfect X` requires a global bound on the terms and finite local
  freeness of every term. `StrictPerfect X` is the corresponding full category.
- `Derived X` is the localization of these complexes at quasi-isomorphisms.
  `locallyPerfect X` requires, near every point, an isomorphism in this
  localization to a strict perfect complex on that neighborhood.
  `Perfect X` is the corresponding full category. Its objects need not be
  termwise quasi-coherent or globally bounded.
- `StrictK X n` and `PerfectK X n` are the connective S-construction groups,
  for `n : ℕ`. Their public group universe is `Type (u + 1)`.

The definitions are in [Strict.lean](../Quillen/PerfectComplexes/Strict.lean)
and [Local.lean](../Quillen/PerfectComplexes/Local.lean). The main Waldhausen
models use quasi-isomorphisms and ambient-monomorphism cofibrations whose
quotients remain in the specified class. The degreewise split models and
`splitStrictKEquiv`, `splitPerfectKEquiv` compare the two cofibration choices
in every nonnegative degree; this is a change of cofibrations, with the same
weak equivalences.

Fix an open immersion `j : U ⟶ X`. A supported perfect complex is a locally
perfect complex on `X` whose restriction to `U` is acyclic. Thus
`PerfectSupportedK j n` records cohomological support away from `U`, and
`perfectSupportedKMap j n` forgets the support condition.
See [PerfectSupport.lean](../Quillen/PerfectComplexes/PerfectSupport.lean).

`perfectOpenWeakWaldhausen j` retains the objects, cofibrations, and chosen zero
of `Perfect X`. A map is weak in this relative model exactly when its restricted
chain map on `U` is a quasi-isomorphism. Its K-groups are `PerfectOpenK j n`.
The two maps

```text
PerfectK X n → PerfectOpenK j n → PerfectK U n
```

are `perfectOpenKMap j n` and `perfectOpenKRestrict j n`. Their composite is
`perfectKRestrict j n`. The factorization is stated by
`perfectOpenKRestrict_comp_perfectOpenKMap`. The displayed intermediate group
is a relative model on `X`, not an alternative definition of `PerfectK U n`.
See [OpenFibration.lean](../Quillen/PerfectComplexes/OpenFibration.lean) and
[OpenFunctor.lean](../Quillen/PerfectComplexes/OpenFunctor.lean).

## Comparisons and functoriality

The following comparison scopes include degree zero.

| Input | Comparison | Source |
| --- | --- | --- |
| Any scheme `X` | `vectorBundleToStrictKEquiv X n`, from public `Quillen.Scheme.K X n` to `StrictK X n` | [GilletWaldhausen.lean](../Quillen/PerfectComplexes/GilletWaldhausen.lean) |
| Any affine scheme `X`, with `IsAffine X` | `affineStrictToPerfectKEquiv X n` and `affineVectorBundleToPerfectKEquiv X n` | [Affine/SchemeKEquivalence.lean](../Quillen/PerfectComplexes/Affine/SchemeKEquivalence.lean) |
| Any open immersion `j : U ⟶ Spec R` | `Affine.strictToPerfectOpenKEquiv R j n` for the relative models on `Spec R` | [Affine/OpenKEquivalence.lean](../Quillen/PerfectComplexes/Affine/OpenKEquivalence.lean) |
| Any open immersion `j : U ⟶ Spec R` | `Affine.strictSupportedToPerfectKEquiv R j n` for the supported models on `Spec R` | [Affine/SupportedStrictPerfectKEquivalence.lean](../Quillen/PerfectComplexes/Affine/SupportedStrictPerfectKEquivalence.lean) |

These equivalences have the named canonical comparison maps as their forward
homomorphisms. The affine results require neither regularity nor noetherianity.
In the last two rows, `U` need not be affine or quasi-compact. Those comparisons
do not identify the relative model with absolute K-theory of `U`.

`strictKPullback` is defined for every scheme morphism and gives
`StrictKFunctor`. The vector-bundle/strict comparison is a natural isomorphism
for this pullback. `perfectKPullback` is defined for every morphism between
quasi-compact schemes, using bounded-above flat representatives, and gives
`PerfectKFunctor` on `Quillen.Scheme.QuasiCompactSchemes`. It agrees with the
existing flat-pullback and open-restriction maps and satisfies identity,
composition, and naturality of the strict and vector-bundle comparisons.
See [PullbackFunctor.lean](../Quillen/PerfectComplexes/PullbackFunctor.lean) and
[DerivedPullbackFunctor.lean](../Quillen/PerfectComplexes/DerivedPullbackFunctor.lean).

## General relative localization

For every open immersion, `perfectOpenConnectingHom j n` is the homotopy-fiber
boundary with codomain `PerfectSupportedK j n`. The theorem
`perfectOpen_positiveLongExactSequence j n` states exactness at the three
recurring positions:

```text
PerfectK X (n+1) → PerfectOpenK j (n+1) → PerfectSupportedK j n
                → PerfectK X n → PerfectOpenK j n
```

The arrows are `perfectOpenKMap`, `perfectOpenConnectingHom`, and
`perfectSupportedKMap` as appropriate. Exactness is equality of the relevant
homomorphism's range and the next homomorphism's kernel.
`perfectOpenKMap_zero_surjective j` gives surjectivity onto the relative
degree-zero group. It does not give surjectivity of `perfectKRestrict j 0`
onto `PerfectK U 0`.
See [OpenLongExactSequence.lean](../Quillen/PerfectComplexes/OpenLongExactSequence.lean).

For an arbitrary open immersion, `PerfectOpenKZeroImage j` is defined to be
exactly `(perfectKRestrict j 0).range`. The general image comparison first
quotients `PerfectOpenK j 0` by the kernel of its map to this subgroup.
Injectivity of the endpoint is a further claim.
See [OpenKZeroImage.lean](../Quillen/PerfectComplexes/OpenKZeroImage.lean).

## Principal opens of affine schemes

Let `R : CommRingCat.{u}`, `r : R`, and
`j := CoherentScheme.principalOpen R r`. The source of `j` is
`Spec (.of (Localization.Away r))` and its target is `Spec R`.
There is no nonzero, regularity, noetherianity, or non-zero-divisor assumption;
localization at zero is included.

In `Quillen.PerfectComplexes.Affine`:

- `principalPerfectOpenKEquiv R r n` identifies `PerfectOpenK j (n+1)`
  with `PerfectK U (n+1)`. Its forward map is `perfectOpenKRestrict j (n+1)`.
- `principalPerfectOpenKZeroImageEquiv R r` identifies `PerfectOpenK j 0`
  with `PerfectOpenKZeroImage j`. The map to `PerfectK U 0` is injective;
  the equivalence's codomain is the restriction image.
- `principalPerfectConnectingHom R r n` is `perfectOpenConnectingHom j n`
  precomposed with the inverse of the positive endpoint equivalence.
  `principalPerfectConnectingHom_comp_relative` gives its compatibility with
  the full relative boundary.

Write `K_n(X)` for `PerfectK X n` and `K_n(X on X ∖ U)` for
`PerfectSupportedK j n` within this paragraph. Then
`principalPerfect_positiveLongExactSequence R r n` states the recurring
range-equals-kernel identities in each segment

```text
Kₙ₊₁(X) → Kₙ₊₁(U) → Kₙ(X on X ∖ U) → Kₙ(X) → Kₙ(U).
```

Repeating these maps gives a connective group sequence.
`principalPerfect_zeroTail R r` supplies its tail

```text
K₁(X) → K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U).
```

The tail is exact at `K₁(U)`, `K₀(X on X ∖ U)`, and `K₀(X)`.
No surjectivity onto the last group is asserted. These are connective
homotopy-theoretic K-groups; this result does not identify K₀ with an algebraic
Grothendieck presentation or construct a sequence of spectra.

The endpoint and exactness APIs are in
[Affine/PrincipalPerfectCofinality.lean](../Quillen/PerfectComplexes/Affine/PrincipalPerfectCofinality.lean)
and [Affine/PrincipalPerfectLocalization.lean](../Quillen/PerfectComplexes/Affine/PrincipalPerfectLocalization.lean).
For a focused import:

```lean
import Quillen.PerfectComplexes.Affine.PrincipalPerfectLocalization

#check Quillen.PerfectComplexes.Affine.principalPerfectOpenKEquiv
#check Quillen.PerfectComplexes.Affine.principalPerfectOpenKZeroImageEquiv
#check Quillen.PerfectComplexes.Affine.principalPerfect_zeroTail
```

## Remaining scope and references

The absolute endpoint for arbitrary quasi-compact opens, general-scheme
geometric replacement and density, global localization and descent, and the
strict/local comparison on general nonaffine schemes require further work.
Locally-perfect objects on a non-quasi-compact scheme need not have a uniform
cohomological bound, so the bounded-above flat enhancement alone does not give
perfect pullback for every scheme. Spectra, negative K-groups, and nonconnective
localization remain outside the current theory.

Background sources include Thomason and Trobaugh,
*Higher Algebraic K-Theory of Schemes and of Derived Categories*
([paper](https://www.preschema.com/teaching/2020-ss/kdescent/refs/Thomason-Trobaugh%20-%20Higher%20algebraic%20K-theory%20of%20schemes.pdf))
and the [Stacks Project](https://stacks.math.columbia.edu/).
These links provide context; a theorem-by-theorem correspondence with the Lean
development has not been verified. The definitions and signatures linked above
specify the formalized models and hypotheses.
