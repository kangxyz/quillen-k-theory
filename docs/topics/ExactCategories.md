# Exact categories and canonical Quillen K-maps

An exact structure specifies which kernel–cokernel pairs in an additive
category are conflations. The library constructs its Q-category, realizes
that category, and defines connective K-groups by shifted homotopy groups.
Additive functors preserving conflations induce canonical maps on these
groups. The classical object-and-conflation presentation of K₀ is a later
comparison with those original homotopy groups, with specified maps in both
directions.

## Public imports

Use `import Quillen.KTheory.API` for exact-category K-groups, canonical maps,
equivalences, bundled small categories, and small-model functoriality.
The classical K₀ comparison has its own imports. General exact structures and
exact functors come from `Aglib.CategoryTheory.ExactCategory`; their declaration
namespace is `CategoryTheory.ExactCategory`. Quillen supplies the Q-construction
and K-map extensions in that native namespace. `Quillen.SmallExactCategory` is the
bundled application category.

| Full import | Focused public names |
| --- | --- |
| [Aglib.CategoryTheory.ExactCategory.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/CategoryTheory/ExactCategory/Basic.lean) | `ExactStructure`, `ExactStructure.inflation`, `ExactStructure.deflation` |
| [`Quillen.CategoryTheory.ExactCategory.Functor`](../../Quillen/CategoryTheory/ExactCategory/Functor.lean) | `ExactFunctor`, `ExactFunctor.mapQ` |
| [`Quillen.KTheory.API`](../../Quillen/KTheory/API.lean) | `ExactFunctor.KMap`, `SmallExactCategory.ofExactStructure`, `SmallExactCategory.KFunctor` |
| [`Quillen.CategoryTheory.SmallModel.Exact`](../../Quillen/CategoryTheory/SmallModel/Exact.lean) | `ExactStructure.SmallK`, `ExactFunctor.smallKMap`, `ExactStructure.presentationKEquiv` |
| [`Quillen.KTheory.GrothendieckGroup.Basic`](../../Quillen/KTheory/GrothendieckGroup/Basic.lean) | `ExactStructure.GrothendieckGroup`, `ExactStructure.grothendieck_universal` |
| [`Quillen.KTheory.GrothendieckComparison.Equivalence`](../../Quillen/KTheory/GrothendieckComparison/Equivalence.lean) | `ExactStructure.grothendieckKZeroEquiv` |
| [`Quillen.KTheory.GrothendieckComparison.Functor`](../../Quillen/KTheory/GrothendieckComparison/Functor.lean) | `SmallExactCategory.grothendieckFunctor`, `SmallExactCategory.grothendieckKZeroIso` |

## Exact structure and the Q-category

Let `C : Type u` have `[Category.{v} C]`, `[Preadditive C]`, and
`[HasFiniteBiproducts C]`. An `E : CategoryTheory.ExactCategory.ExactStructure C` contains a predicate
`E.conflation` on `ShortComplex C`. Every selected short complex has the
actual kernel and cokernel universal properties. The other fields give
isomorphism closure, identity and composition for admissible maps, pushouts
along inflations, and pullbacks along deflations, with the corresponding
stability properties. The object and morphism universes may differ.

`E.inflation` and `E.deflation` select the first and second maps of these
conflations. `mono_of_inflation` and `epi_of_deflation` prove their ordinary
categorical mono and epi properties. Mixed base-change properties needed
below are derived from the exact axioms. An ambient abelian category or
existence of arbitrary pullbacks is not part of this input.

The restricted-span construction in
[`QConstruction.Basic`](../../Quillen/CategoryTheory/QConstruction/Basic.lean)
represents an arrow from `X` to `Y` by a span `X ← M → Y`: the left leg is a
deflation and the right leg an inflation. `Quillen.Q` quotients such spans
by isomorphisms of the apex commuting with both legs.
`Q.mkHom_eq_iff_apexIso` records exactly this equality criterion.

Composition uses the genuine pullback of the right leg of the first span
and the left leg of the second. `Q.mkHom_comp` and `Q.comp_apex` retain that
representative and its apex. For an exact structure the required restricted
pullback instances are supplied by its axioms and their consequences;
arbitrary pairs of morphism properties do not automatically define an exact
category. The specialization is `E.QCategory`.

## BQ and the degree convention

[`Quillen.KTheory.Basic`](../../Quillen/KTheory/Basic.lean) defines `E.KSpace` as
`Quillen.ClassifyingSpace E.QCategory`, the realization of the Q-category's
nerve. Its point `E.kBasepoint` is the vertex of the original additive
category's zero object. This definition does not make that vertex a zero
object of the Q-category.

For `n : ℕ`, `E.K n` is `π_(n+1)(BQ(E), 0)`. Thus `E.K 0` is the first
homotopy group of BQ, and `E.K 1` is its second homotopy group. The definition
provides a group in every nonnegative degree and a commutative group in
strictly positive K-degree by higher homotopy commutativity. Commutativity at
K₀ and identification with the classical presentation are separate theorems.

## Exact functors and their canonical maps

For exact structures `E` and `E'`, `CategoryTheory.ExactCategory.ExactFunctor E E'` consists of an
underlying additive functor `F.toFunctor` and preservation of conflations.
Preservation of inflations, deflations, and the pullbacks used by Q-composition
is proved from that data in
[`ExactCategory.Functor`](../../Quillen/CategoryTheory/ExactCategory/Functor.lean).
The functor `F.mapQ` sends an original object to its image and a span to the
span obtained by applying `F.toFunctor` to its apex and legs.

An additive exact functor preserves zero up to its canonical zero-object
isomorphism. [`Map.Basic`](../../Quillen/KTheory/Map/Basic.lean) uses that
isomorphism to rebase the Q-functor. The resulting realization map is pointed
at the specified zero vertices, and `F.KMap n` is its homomorphism
`E.K n →* E'.K n`. Strict equality between the image zero and the target's
chosen zero is unnecessary.

The identity and composition laws use these same maps. In particular,
`(F.comp G).KMap n x = G.KMap n (F.KMap n x)` for composable exact functors.
[`Map.Functoriality`](../../Quillen/KTheory/Map/Functoriality.lean) proves
`ExactFunctor.KMap_comp` using the based realization homotopy;
[`Map.NaturalIso`](../../Quillen/KTheory/Map/NaturalIso.lean) proves
`ExactFunctor.KMap_eq_of_natIso` for an isomorphism of the underlying functors.
The pointwise forms `KMap_id_apply` and `KMap_comp_apply` are in `KTheory.API`.

For a category with matching object and morphism universe `u`,
`SmallExactCategory.ofExactStructure E` packages the existing structure.
[`Quillen.KTheory.Functor`](../../Quillen/KTheory/Functor.lean) defines
`Quillen.SmallExactCategory.KFunctor n : SmallExactCategory.{u} ⥤ GrpCat.{u}`.
Its arrows are actual exact functors, and its maps are precisely their `KMap n`.

## Equivalences and universe boundaries

The raw `KMap`, composition, and natural-isomorphism signatures use
`C D : Type u` with `[Category.{v} C]` and `[Category.{v} D]`. The shared
object universe need not equal the shared morphism universe. The algebraic
definition of an exact functor itself allows independent source and target
universes; that broader definition does not enlarge these realization APIs.

[`Quillen.KTheory.Equivalence`](../../Quillen/KTheory/Equivalence.lean) proves that an
underlying categorical equivalence which reflects both inflations and
deflations induces an equivalence of Q-categories. Given
`[F.mapQ.IsEquivalence]`, `F.KEquivOfMapQIsEquivalence n` is an equivalence of
the original K-groups whose forward homomorphism is exactly `F.KMap n`.
Reflection of admissibility must be retained when establishing the Q-level
hypothesis from an underlying equivalence.

For different morphism universes `v₁` and `v₂`,
[`Map.CommonAmbient`](../../Quillen/KTheory/Map/CommonAmbient.lean) supplies
`F.commonAmbientKMap n` when both object types lie in `Type (max v₁ v₂)`.
The apex in a Q-arrow makes the Q-categories share that ambient universe.
With `[F.mapQ.IsEquivalence]`, `commonAmbientKEquiv` retains this map as its
forward homomorphism. This is a stated common-realization interface.

If `[EssentiallySmall.{w} C]`, `E.smallModel` transports the exact structure
to mathlib's chosen `SmallModel.{w} C`. The exact functors
`E.smallModelToOriginal` and `E.originalToSmallModel` are the chosen
equivalence functors, and `E.SmallK n` is K-theory of that small model.
For source and target essentially small in the same `w`, `F.smallKMap n`
is the K-map of their induced small-model exact functor. Original category
universes may now differ. Identity, composition, and natural-isomorphism
invariance are proved in
[`SmallModel.Functoriality`](../../Quillen/CategoryTheory/SmallModel/Functoriality.lean).

`E.presentationKEquiv e f n` compares two additive small presentations
`e : S ≌ C` and `f : T ≌ C`, with `S` and `T` small in the same universe `w`.
Its forward map comes from `E.presentationComparison e f`. This presentation
independence does not supply an identification with an out-of-universe raw
realization of the original category.

## The object-and-conflation presentation of K₀

`E.GrothendieckGroup` is the free abelian group on the original objects of
`C`, modulo `[S.X₂] = [S.X₁] + [S.X₃]` for each `E.conflation S`.
`E.grothendieckClass X` is the object generator. Isomorphism invariance and
the zero-object equation are consequences of these relations.
`E.grothendieck_universal` says that every conflation-additive function to an
arbitrary abelian group factors uniquely through this quotient.

The homotopical object class `E.kZeroObjectClass X` is a particular based
loop in BQ, constructed from the two Q-arrows from zero having apex zero
and apex `X`. [`GrothendieckComparison.Basic`](../../Quillen/KTheory/GrothendieckComparison/Basic.lean)
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
[`topological retraction`](../../Quillen/KTheory/GrothendieckComparison/Retraction.lean).
[`CompletionSurjectivity`](../../Quillen/Topology/ClassifyingSpace/CompletionSurjectivity.lean)
then proves bijectivity of the original completed-loop map for any category,
using one-skeleton fullness and generation by actual continuous arrow paths.
Continuous-path generation is a proved dependency, not a presentation premise.

For exact functors in the stated common universes,
`ExactFunctor.grothendieckKZeroEquiv_naturality` and
`ExactFunctor.kZeroToGrothendieck_naturality` commute with `F.grothendieckMap`
and `F.KMap 0` on every class. For bundled small exact categories,
`Quillen.SmallExactCategory.grothendieckKZeroIso` is the resulting natural
isomorphism from `grothendieckFunctor` to the original `KFunctor 0`, with
the same forward comparison and inverse retraction as its components.

## Further comparisons and client examples

An exact category also has
[`Waldhausen.ofExactCategory E`](../../Quillen/Waldhausen/ExactCategory.lean),
with inflations as cofibrations and isomorphisms as weak equivalences.
The separate [Q/S comparison](Waldhausen.md#comparison-with-exact-category-q)
identifies its S-model with the original Q-model and respects both canonical
K-map APIs. The all-degree commutativity and conflation-additivity interfaces
are in [`QuillenComparison.KCommutativity`](../../Quillen/Waldhausen/QuillenComparison/KCommutativity.lean)
and [`QuillenComparison.ExactAdditivity`](../../Quillen/Waldhausen/QuillenComparison/ExactAdditivity.lean).
These are later theorems; they are not fields of `ExactStructure` or the
definition of `E.K n`.

The independent downstream clients show concrete uses of these interfaces:

- [`Consumer.ExactFunctor`](../../examples/downstream/Consumer/ExactFunctor.lean)
  bundles an input structure, calculates identity and composition, and retains
  the canonical forward map of a Q-induced equivalence.
- [`Consumer.SmallModel`](../../examples/downstream/Consumer/SmallModel.lean)
  uses small-model maps for original categories with different universes.
- [`Consumer.GrothendieckComparison`](../../examples/downstream/Consumer/GrothendieckComparison.lean)
  detects the kernel of an exact-functor K₀ map on arbitrary homotopical classes
  through the classical Grothendieck map and the inverse comparison.
- [`Consumer.KGroupAdditivity`](../../examples/downstream/Consumer/KGroupAdditivity.lean)
  uses the original Quillen group law and exact-functor conflation additivity.

The constructions here are connective. Negative groups, localization tails,
resolution, and dévissage have their own inputs and comparison theorems;
the K₀ presentation alone does not supply them. The common-universe and
small-presentation comparisons above retain their stated universe boundaries.
See [Scope.md](../reference/Scope.md) for those families and the remaining global comparisons.
