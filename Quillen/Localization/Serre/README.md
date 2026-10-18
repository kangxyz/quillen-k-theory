# The original Serre localization sequence

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |

## Dévissage, resolution, and connective localization

The library compares K-theory by finite filtrations, finite admissible
resolutions, and passage to a Serre quotient. These are three distinct
interfaces: dévissage is proved for abelian categories, resolution is proved
for a resolving full exact subcategory, and localization is proved for an
abelian category with a Serre class. Their applications to finite modules use
actual scalar localization and restriction of scalars, with the original
canonical maps retained.

## Public imports

Choose the theorem matching the category and the available algebraic data:

| Import after `Quillen.` | Principal declarations |
| --- | --- |
| [`Devissage.Homotopical`](../../Devissage/Homotopical.lean) | `Devissage.classifyingHomotopyEquiv`, `Devissage.KEquiv`, `Devissage.KMap_bijective` |
| [`Resolution`](../../Resolution.lean) | `Resolution.classifyingHomotopyEquiv`, `Resolution.KEquiv`, `Resolution.inclusionKMap_bijective` |
| [`Resolution.LengthOne`](../../Resolution/LengthOne.lean) | `Resolution.KEquivOfLengthOne`, `Resolution.inclusionKMap_bijective_of_length_one` |
| [`Resolution.Bounded`](../../Resolution/Bounded.lean) | `Resolution.KEquivOfBounded`, `Resolution.inclusionKMap_bijective_of_bounded` |
| [`Localization.Serre.LocalizationTheorem`](LocalizationTheorem.lean) | `SerreLocalization.localizationSequence`, `localization_longExact`, `localization_KZero_tail` |
| [`Localization.Serre.LocalizationTarget`](LocalizationTarget.lean) | `SerreLocalization.targetKEquiv`, `actualConnectingHom`, `actual_localization_longExact` |
| [`GTheory.FiniteModules.LocalizationSequence`](../../GTheory/FiniteModules/LocalizationSequence.lean) | `FiniteModuleLocalization.localizationKMap`, `connectingHom`, `localization_longExact` |
| [`AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage`](../../AlgebraicGeometry/Scheme/Coherent/Affine/ClosedDevissage.lean) | `FiniteModuleLocalization.closedSupportGEquiv`, `principalClosedLocalization_longExact` |

Names in the table have prefix `Quillen.`. Unqualified names in a row continue
in that row's displayed namespace. The resolution facade exposes the
objectwise finite theorem and its length-one and bounded specializations.

## Categories, small models, and degree zero

For an exact structure `E`, `E.KSpace` is the realized Q-construction and
`E.K n` is `π_(n+1)(BQ)` for `n : ℕ`. Thus degree zero is homotopical K₀,
`π₁(BQ)`. All equivalences and sequences below include `n = 0`; none introduces
a negative K-group. The independent algebraic Grothendieck presentation is
compared with this group in the
[degree-zero API](../../KTheory/GrothendieckComparison/Equivalence.lean).

The homotopical dévissage and resolution theorems use `C : Type u` with
`[SmallCategory C]`. Serre localization uses `C : Type u` with
`[Category.{u} C]`. For an essentially small category, `E.SmallK` means K-theory
of the transported exact structure on an actual chosen `SmallModel`.
`ExactFunctor.smallKMap` passes through the two small-model equivalences and
then uses the ordinary exact-functor K-map. See
[`SmallModel/Exact.lean`](../../CategoryTheory/SmallModel/Exact.lean).
Choice of a small model does not supply a missing exactness or localization
theorem; those properties are proved for each application.

## The canonical Serre quotient sequence

For an abelian `C` and `[P.IsSerreClass]`, `SerreLocalization.Quotient P` is
the specified categorical localization at `P.isoModSerre`, with its proved
abelian structure. The maps are the actual inclusion `Devissage.KMap P n`
and quotient `SerreLocalization.quotientKMap P n`.

`basedLocalizationFiberComparison_bijective P k` proves that the canonical
based comparison from the subcategory Q-space to the normalized path-space
fiber of the quotient map is bijective on every homotopy set, including π₀.
The structured Theorem B transitions are proved for this quotient. The
result is a weak comparison; it does not assert a global homotopy inverse.
`localizationFiberEquiv` promotes its K-degree homomorphism to an equivalence
without changing that homomorphism.

The connecting map `SerreLocalization.connectingHom P n` is the actual
path-space boundary followed by the comparison inverse. For every `n : ℕ`,
the sequence has all three recurring exactness positions:

```text
K_(n+1)(C) → K_(n+1)(C/P) → K_n(P) → K_n(C) → K_n(C/P).
```

The corresponding range/kernel theorems are
`quotient_range_eq_connecting_ker`, `connecting_range_eq_inclusion_ker`, and
`inclusion_range_eq_quotient_ker`. `localizationSequence` bundles them with
`quotientKZero_surjective`. In particular, `localization_KZero_tail` gives

```text
K_1(C) → K_1(C/P) → K_0(P) → K_0(C) → K_0(C/P) → 0.
```

The last surjection uses Q-space connectedness and the fiber comparison on
π₀; it needs no additional Grothendieck-presentation premise.
[`Consumer.Localization`](../../../examples/downstream/Consumer/Localization.lean)
uses all three exactness positions and that terminal surjection.

To replace the formal quotient by an actual target `D`,
`LocalizationTarget` requires an additive functor `L : C ⥤ D`, with both
categories abelian in the same stated universe and
`[L.IsLocalization P.isoModSerre]`. It constructs the exact quotient-to-target
equivalence and transports the sequence to `SerreLocalization.KMap P L n`
and `actualConnectingHom P L n`. This is a conditional interface for a
specified localization functor; additivity alone does not realize the quotient.

## Boundaries and related reading

These interfaces do not supply arbitrary exact-category dévissage or
localization, a negative boundary after K₀, or full coherence for arbitrary
Serre-pair maps. A specified actual target must retain its localization
property; separately specified realization or comparison data retain their
own conditions. The source links above give the current statements and their
exact hypotheses.

For perfect-complex localization, support, and Mayer–Vietoris, use
[Thomason–Trobaugh interfaces](../../AlgebraicGeometry/PerfectComplexes/README.md). For geometric K/G categories
and their canonical maps, continue with [Scheme K/G-theory](../../AlgebraicGeometry/Scheme/README.md).
