# Dévissage, resolution, and connective localization

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
| [`Devissage.Homotopical`](../../Quillen/Devissage/Homotopical.lean) | `Devissage.classifyingHomotopyEquiv`, `Devissage.KEquiv`, `Devissage.KMap_bijective` |
| [`Resolution`](../../Quillen/Resolution.lean) | `Resolution.classifyingHomotopyEquiv`, `Resolution.KEquiv`, `Resolution.inclusionKMap_bijective` |
| [`Resolution.LengthOne`](../../Quillen/Resolution/LengthOne.lean) | `Resolution.KEquivOfLengthOne`, `Resolution.inclusionKMap_bijective_of_length_one` |
| [`Resolution.Bounded`](../../Quillen/Resolution/Bounded.lean) | `Resolution.KEquivOfBounded`, `Resolution.inclusionKMap_bijective_of_bounded` |
| [`Localization.Serre.LocalizationTheorem`](../../Quillen/Localization/Serre/LocalizationTheorem.lean) | `SerreLocalization.localizationSequence`, `localization_longExact`, `localization_KZero_tail` |
| [`Localization.Serre.LocalizationTarget`](../../Quillen/Localization/Serre/LocalizationTarget.lean) | `SerreLocalization.targetKEquiv`, `actualConnectingHom`, `actual_localization_longExact` |
| [`GTheory.FiniteModules.LocalizationSequence`](../../Quillen/GTheory/FiniteModules/LocalizationSequence.lean) | `FiniteModuleLocalization.localizationKMap`, `connectingHom`, `localization_longExact` |
| [`AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage`](../../Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/ClosedDevissage.lean) | `FiniteModuleLocalization.closedSupportGEquiv`, `principalClosedLocalization_longExact` |

Names in the table have prefix `Quillen.`. Unqualified names in a row continue
in that row's displayed namespace. The resolution facade exposes the
objectwise finite theorem and its length-one and bounded specializations.

## Categories, small models, and degree zero

For an exact structure `E`, `E.KSpace` is the realized Q-construction and
`E.K n` is `π_(n+1)(BQ)` for `n : ℕ`. Thus degree zero is homotopical K₀,
`π₁(BQ)`. All equivalences and sequences below include `n = 0`; none introduces
a negative K-group. The independent algebraic Grothendieck presentation is
compared with this group in the
[degree-zero API](../../Quillen/KTheory/GrothendieckComparison/Equivalence.lean).

The homotopical dévissage and resolution theorems use `C : Type u` with
`[SmallCategory C]`. Serre localization uses `C : Type u` with
`[Category.{u} C]`. For an essentially small category, `E.SmallK` means K-theory
of the transported exact structure on an actual chosen `SmallModel`.
`ExactFunctor.smallKMap` passes through the two small-model equivalences and
then uses the ordinary exact-functor K-map. See
[`SmallModel/Exact.lean`](../../Quillen/CategoryTheory/SmallModel/Exact.lean).
Choice of a small model does not supply a missing exactness or localization
theorem; those properties are proved for each application.

## Abelian finite-filtration dévissage

Let `C` be small and abelian, and let `P : ObjectProperty C` contain zero and
be closed under subobjects, quotients, and finite products. Its full
subcategory has the inherited abelian exact structure
`Devissage.subcategoryExactStructure P`; `Devissage.exactInclusion P` is the
actual exact inclusion into `C`.

`Devissage.FiltrationHypothesis P` says that every object has an actual finite
admissible filtration starting at a zero object, with each successive quotient
in `P`. The inductive
[`ExactStructure.Filtration`](../../Quillen/Devissage/Filtration.lean) records the
short exact sequences and factors. There is no common length bound and no
extension-closure assumption on `P`.

Under this hypothesis, `Devissage.classifyingHomotopyEquiv P h` has the
realized Q-inclusion as its forward map. The proof identifies the inclusion
comma categories with layer posets, contracts them by intersections and
finite-filtration induction, and applies Theorem A. Contractibility and a
homotopy inverse are conclusions of this route, rather than filtration inputs.

Canonical zero-object rebasing gives `Devissage.KEquiv P h n` in every
nonnegative degree. Its coercion is exactly `Devissage.KMap P n`, as recorded
by `KEquiv_coe`; it is not an unspecified isomorphism between the same groups.
[`Consumer.Devissage`](../../examples/downstream/Consumer/Devissage.lean) uses
both the equivalence and this forward-map identity.

## Resolving subcategories and actual finite resolutions

Let `C` be small, preadditive, and have finite biproducts, with exact structure
`E`. The resolution theorem takes a full subcategory defined by `P`, with
zero, isomorphism, finite-product, extension, and admissible-kernel closure.
The kernel condition `E.IsKernelClosed P` applies to a conflation
`A → B → D` when **both** `B` and `D` lie in `P`; it is weaker than closure
under every admissible subobject of a `P`-object. The exact structure is
`ExactSubcategory.exactStructure E P`.

[`ExactStructure.FiniteResolution`](../../Quillen/Resolution/Finite.lean) is an
actual finite tower. An object already in `P` gives a length-zero resolution.
A successor step resolves the terminal object of a conflation using a middle
object in `P` and a previously resolved kernel. Consequently
`E.ResolutionHypothesis P` is precisely
`∀ X, Nonempty (E.FiniteResolution P X)`. Length may depend on `X`; a
numerical projective-dimension assertion must first produce this tower.

`Resolution.classifyingHomotopyEquiv E P h` proves a homotopy equivalence with
the original Q-inclusion as forward map. The proof starts with length-one
comma contractions, proves resolving closure of the finite-length strata, and
uses their genuine filtered Q-nerve colimit. The canonically normalized
inclusion induces `Resolution.KEquiv E P h n`, whose forward homomorphism is
`Resolution.inclusionKMap E P n`.

The shorter interfaces retain the same closure assumptions and canonical map:

| Available resolution data | Comparison |
| --- | --- |
| `∀ X, E.ResolutionLength P 1 X` | `KEquivOfLengthOne E P h n` |
| A common `N : ℕ` and `∀ X, E.ResolutionLength P N X` | `KEquivOfBounded E P N h n` |
| Objectwise finite towers, without a common bound | `KEquiv E P h n` |

There is also a cover formulation in `Resolution.LengthOne`: actual
admissible epimorphisms from `P`-objects suffice under the stronger
`E.IsAdmissibleSubobjectClosed P` condition. It does not replace that condition
by the weaker kernel condition.
[`Consumer.Resolution`](../../examples/downstream/Consumer/Resolution.lean)
uses length-one and objectwise finite resolutions and checks the original
forward maps. For the geometric source of finite vector-bundle resolutions,
see [regular K-to-G comparison](SchemeKTheory.md#regular-k-to-g-comparison).

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
[`Consumer.Localization`](../../examples/downstream/Consumer/Localization.lean)
uses all three exactness positions and that terminal surjection.

To replace the formal quotient by an actual target `D`,
`LocalizationTarget` requires an additive functor `L : C ⥤ D`, with both
categories abelian in the same stated universe and
`[L.IsLocalization P.isoModSerre]`. It constructs the exact quotient-to-target
equivalence and transports the sequence to `SerreLocalization.KMap P L n`
and `actualConnectingHom P L n`. This is a conditional interface for a
specified localization functor; additivity alone does not realize the quotient.

## Finite-module G-localization and closed support

Let `R : Type u` be commutative and noetherian and `S : Submonoid R`.
`FiniteModuleLocalization.G R n` is
`(CoherentScheme.finiteModuleExactStructure.{u,u} R).SmallK n`, in `Type u`.
`SupportedG S n` uses the genuine Serre kernel on the small model: represented
finite modules whose scalar localization is zero. The localization functor,
its Serre-localization property, and its small-model transport are proved.

`localizationKMap S n` is exactly the original scalar-localization
`smallKMap`. `smallAbelianKEquiv` and `smallKMap_comparison` identify it with
the abelian small-model Serre map, including zero normalization.
`localization_longExact S` therefore gives the preceding connective sequence
with `SupportedG S`, `G R`, and `G (Localization S)` and the terminal G₀
surjection. The hypotheses allow arbitrary `S`, including localization at zero.

For `S = Submonoid.powers f`, `smallTorsion_powers_iff_uniform` identifies
support with annihilation by one power of `f` on the whole represented finite
module. Restriction of scalars from `R/(f)` identifies modules killed by `f`;
the finite power filtration then gives `closedSupportGEquiv f n`.
Its forward map is `closedSupportedKMap f n`, and
`closedSupportGEquiv_pushforward` retains the actual closed restriction-of-scalars
map `closedPushforwardKMap`. `principalClosedLocalization_longExact` has closed
term `G (R/(f))` and open term `G (R[f⁻¹])`, with the transported boundary and
the same G₀ endpoint.

[`IdealClosedSupport`](../../Quillen/GTheory/FiniteModules/IdealClosedSupport.lean)
also constructs the actual equivalence between finite `R/I`-modules and
modules killed by `I`.
[`idealPowerFiltration`](../../Quillen/Aglib/Algebra/Category/FGModuleCat/IdealPowerFiltration.lean)
produces a finite filtration when a stated power of `I` annihilates the module.
The general geometric closed/open sequence, including a potentially nonaffine
open complement, is described in
[scheme localization](SchemeKTheory.md#coherent-open-and-closed-localization).

## Boundaries and related reading

These interfaces do not supply arbitrary exact-category dévissage or
localization, a negative boundary after K₀, or full coherence for arbitrary
Serre-pair maps. A specified actual target must retain its localization
property; separately specified realization or comparison data retain their
own conditions. The source links above give the current statements and their
exact hypotheses.

For perfect-complex localization, support, and Mayer–Vietoris, use
[Thomason–Trobaugh interfaces](PerfectComplexes.md). For geometric K/G categories
and their canonical maps, continue with [Scheme K/G-theory](SchemeKTheory.md).
