# Waldhausen categories and K-theory

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Waldhausen.Basic` | Cofibrations, weak equivalences, and chosen zero |
| `Quillen.Waldhausen.KTheory` | Connective S-construction groups |
| `Quillen.Waldhausen.FunctorialFactorization.Basic` | Generic functorial cofibration factorization |

## Waldhausen categories, S-constructions, and comparison theorems

A Waldhausen structure specifies cofibrations, weak equivalences, and a zero
object. Its diagonal S-construction defines connective K-groups. Additivity
and the exact-category Q/S comparison are separate theorems. Approximation,
cofinality, and fibration retain their structural input data; the classical K₀
presentation does not require those extra hypotheses.

## Public imports

`import Quillen.Waldhausen` gives the whole topic. The following imports select
principal interfaces. Declaration names are relative to `Quillen.Waldhausen`.

| Import after `Quillen.Waldhausen.` | Public interface |
| --- | --- |
| [`KTheory`](KTheory.lean) | `Structure.Delooping`, `Structure.kBasepoint`, `Structure.K` |
| [`Functoriality.KMap`](Functoriality/KMap.lean) | `IsExact`, `KMap`, identity, composition, and isomorphism invariance |
| [`Additivity.GroupFormula`](Additivity/GroupFormula.lean) | `Additivity.K_mul_comm`, `Additivity.KMap_additivity_mul` |
| [`SConstruction.Rows.CofiberTwoRow`](SConstruction/Rows/CofiberTwoRow.lean), [`GrothendieckComparison.CofiberPrismComposition`](GrothendieckComparison/CofiberPrismComposition.lean) | `QuotientRows.cofiberTwoRow`, `Structure.cofiberObjectLoopTrack`, `Structure.cofiberPrismCompositionLoops` |
| [`QuillenComparison.ExactNaturality`](QuillenComparison/ExactNaturality.lean) | `QuillenComparison.comparisonKEquiv`, `comparisonKEquiv_exactFunctor_naturality` in that namespace |
| [`Approximation.GeneralKEquivalence`](Approximation/GeneralKEquivalence.lean) | `HasApproximationProperty.KEquivGeneral` |
| [`Cofinality.GeneralDense`](Cofinality/GeneralDense.lean) | `Cofinality.DenseCofiberData.inclusionKEquivGeneral`, `inclusion_KZero_exact_general` in that namespace |
| [`Fibration.GeneralComparison`](Fibration/GeneralComparison.lean), [`Fibration.LongExactSequence`](Fibration/LongExactSequence.lean) | `Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general`, `Fibration.changeWeakConnectingHom` |
| [`Fibration.CanonicalFiberComponentTranslation`](Fibration/CanonicalFiberComponentTranslation.lean) | `Fibration.canonicalFiberComponentEquiv` |
| [`GilletWaldhausen.GeneralComparison`](GilletWaldhausen/GeneralComparison.lean) | `GilletWaldhausen.boundedTermsSingleCoarseKEquivGeneral` |
| [`GrothendieckComparison.SmallModel`](GrothendieckComparison/SmallModel.lean) | `AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel` |
| [`GrothendieckComparison.ImageQuotientConeZero`](GrothendieckComparison/ImageQuotientConeZero.lean) | `AlgebraicGrothendieck.imageQuotient_changeWeakKMap_range_ker`, `AlgebraicGrothendieck.imageQuotientConeMap_stable_zero_bijective` |

## The structure, simplices, and degree convention

For `C : Type u` with `[Category.{v} C]`,
[`Quillen.Waldhausen.Structure C`](Basic.lean) contains
`zero`, `isZero`, and morphism properties `cof` and `weq`. Both classes contain
identities and isomorphisms and are closed under composition. Every zero-to-object
map is a cofibration; pushouts along cofibrations exist and preserve cofibrations;
gluing preserves weak equivalences in those pushouts. Two-out-of-three, an extension
axiom, and cylinder or factorization data are additional conditions.

[`SConstruction`](SConstruction.lean) defines an
`n`-simplex as an `n`-chain of pointwise weak equivalences between Sₙ quotient
diagrams, with zero diagonal, cofibration inclusions, and genuine quotient
pushout squares. Simultaneous reindexing in both directions gives the diagonal
`sSet W.cof W.weq` of `N(wS•C)`, retaining the given weak class.

`W.Delooping` is `|diag N(wS•C)|` in `TopCat.{max u v}`. The all-zero diagram
provides `W.kBasepoint`; `W.K n` is `π_(n+1)(W.Delooping, W.kBasepoint)` for `n : ℕ`.
K₀ is a loop group. [`SConstruction.Connected`](SConstruction/Connected.lean)
proves the delooping is path connected. The definition gives groups in every
degree and higher-homotopy commutativity in positive K-degree; additivity also
supplies commutativity at zero.

## Exact functors and the chosen zero

For `F : C ⥤ D` between structures `W` and `V`,
[`IsExact`](Functor.lean) requires preservation of zero
objects, cofibrations, weak equivalences, and pushouts along cofibrations.
Postcomposition gives `sSetMap hF` and `deloopingMap hF` for an exactness proof
`hF`, sending the source point to the point of the image zero.

The unique isomorphism from the image zero to the target's chosen zero rebases
the functor in [`PointedFunctor`](PointedFunctor.lean).
`Quillen.Waldhausen.KMap hF n` is the resulting homomorphism of original K-groups.
`KMap_id`, `KMap_comp_KMap`, and `KMap_eq_of_iso` retain this normalization.
[`Quillen.Waldhausen.SmallWaldhausenCategory.KFunctor n`](KFunctor.lean)
packages all exact functors, without strict chosen-zero preservation.

`IsExact` permits independent source and target universes. The realization and
K-map signatures here take `C D : Type u` with `[Category.{v} C]` and `[Category.{v} D]`.
In the general comparison theorems, independent universes mean independent object
`u` and morphism `v`, retaining these shared source/target parameters.

## Independent client examples and remaining comparisons

- [`Consumer.WaldhausenAdditivity`](../../examples/downstream/Consumer/WaldhausenAdditivity.lean)
  uses additivity, Q/S naturality, and the matching-universe extension equivalence.

- [`Consumer.KGroupAdditivity`](../../examples/downstream/Consumer/KGroupAdditivity.lean)
  uses literal K₀ multiplication, product groups, and cofibration additivity.

- [`Consumer.WaldhausenFibration`](../../examples/downstream/Consumer/WaldhausenFibration.lean)
  uses fiber and cylinder maps without a fiber-equivalence conclusion.

- [`Consumer.GilletWaldhausenReduction`](../../examples/downstream/Consumer/GilletWaldhausenReduction.lean)
  uses bounded-term coverage and the conditional acyclic/single reduction in the fine model.

- [`Consumer.WaldhausenGrothendieckComparison`](../../examples/downstream/Consumer/WaldhausenGrothendieckComparison.lean)
  detects K₀ injectivity from the classical exact-functor map.

Iterated S-spectra and negative Bass groups have separate constructions.
Approximation does not discharge the fibration section condition; positive cofinality
does not give a K₀ equivalence; bounded-term comparison retains its abelian ambient
category and term closures. See [scope summary](../../docs/SCOPE.md) for remaining global
and geometric comparisons.
