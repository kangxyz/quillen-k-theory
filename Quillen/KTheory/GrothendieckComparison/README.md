# The original K0 presentation comparison

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.GrothendieckComparison.Equivalence` | Classical exact-category K₀ comparison |

## Degree-zero presentation interfaces

| Import after `Quillen.` | Canonical comparison |
| --- | --- |
| `KTheory.GrothendieckComparison.Equivalence` | `ExactStructure.grothendieckKZeroEquiv`, with `grothendieckToKZero` and `kZeroToGrothendieck` |
| `KTheory.GrothendieckComparison.Functor` | `SmallExactCategory.grothendieckFunctor`, `grothendieckKZeroIso` |

These comparisons retain the original object classes and K-maps. Exact-category
presentations use conflation relations; Waldhausen presentations use weak-arrow
and cofibration-pushout relations. Their separate size and naturality interfaces
are described in the [exact](../README.md#degree-zero-presentation-boundary)
and [Waldhausen](../../Waldhausen/GrothendieckComparison/README.md#classical-k₀-and-small-model-transport)
guides. The perfect specialization does not supply a triangulated-derived
presentation.

## Public imports

| Full import | Focused public names |
| --- | --- |
| [`Quillen.KTheory.GrothendieckComparison.Equivalence`](Equivalence.lean) | `ExactStructure.grothendieckKZeroEquiv` |
| [`Quillen.KTheory.GrothendieckComparison.Functor`](Functor.lean) | `SmallExactCategory.grothendieckFunctor`, `SmallExactCategory.grothendieckKZeroIso` |

## The object-and-conflation presentation of K₀

`E.GrothendieckGroup` is the free abelian group on the original objects of
`C`, modulo `[S.X₂] = [S.X₁] + [S.X₃]` for each `E.conflation S`.
`E.grothendieckClass X` is the object generator. Isomorphism invariance and
the zero-object equation are consequences of these relations.
`E.grothendieck_universal` says that every conflation-additive function to an
arbitrary abelian group factors uniquely through this quotient.

The homotopical object class `E.kZeroObjectClass X` is a particular based
loop in BQ, constructed from the two Q-arrows from zero having apex zero
and apex `X`. [`GrothendieckComparison.Basic`](Basic.lean)
constructs `E.grothendieckToKZero` from these loops and the conflation
relations. It is a homomorphism from `Multiplicative E.GrothendieckGroup` to
the existing `E.K 0`; the wrapper changes the notation for the group law.

`E.grothendieckKZeroEquiv` identifies these original groups for independent
object and morphism universes. Its forward map is literally
`E.grothendieckToKZero`, and its inverse is `E.kZeroToGrothendieck`.
The declarations `grothendieckKZeroEquiv_toMonoidHom`,
`grothendieckKZeroEquiv_symm_toMonoidHom`, and
`grothendieckKZeroEquiv_objectClass` retain both maps and every object class.
Both inverse identities hold on all classes.

The comparison has two distinct ingredients. The Q-specific algebraic
factorization through groupoid completion and the realization of its
localization functor construct the
[`topological retraction`](Retraction.lean).
[`CompletionSurjectivity`](../../Topology/ClassifyingSpace/CompletionSurjectivity.lean)
then proves bijectivity of the original completed-loop map for any category,
using one-skeleton fullness and generation by actual continuous arrow paths.
Continuous-path generation is a proved dependency, not a presentation premise.

For exact functors in the stated common universes,
`ExactFunctor.grothendieckKZeroEquiv_naturality` and
`ExactFunctor.kZeroToGrothendieck_naturality` commute with `F.grothendieckMap`
and `F.KMap 0` on every class. For bundled small exact categories,
`CategoryTheory.ExactCategory.SmallExactCategory.grothendieckKZeroIso` is the resulting natural
isomorphism from `grothendieckFunctor` to the original `KFunctor 0`, with
the same forward comparison and inverse retraction as its components.
