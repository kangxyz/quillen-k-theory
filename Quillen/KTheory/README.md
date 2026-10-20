# Exact-category K-theory and canonical maps

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.API` | Exact-category K-groups, canonical maps, equivalences, and small models |
| `Quillen.KTheory.Plus` | Standard ring plus/Q homotopy equivalences, original K₀–plus product and component interfaces |
| `Quillen.KTheory.Map.RightBaseChangeTensor` | Original zero-normalized K-map equality in every degree |

## Canonical objects and maps

Namespaces record the constructions; module paths record their mathematical
owners. The following notation assumes the input structure and hypotheses
specified by the declaration and its linked topic guide.

| Input | Objects and canonical maps | Guide |
| --- | --- | --- |
| Exact structure `E` | `E.QCategory`, `E.KSpace`, `E.kBasepoint`, `E.K n`, `E.SmallK n` | [Exact categories](README.md) |
| Exact functor `F` | `F.mapQ`, `F.KMap n`, `F.smallKMap n` | [Exact functors](README.md#exact-functors-and-their-canonical-maps) |
| Bundled small exact category | `CategoryTheory.ExactCategory.SmallExactCategory.ofExactStructure`, `KFunctor n` | [Size conventions](../CategoryTheory/SmallModel/README.md#equivalences-and-universe-boundaries) |
| Waldhausen structure `W` | `W.Delooping`, `W.kBasepoint`, `W.K n` | [Waldhausen theory](../Waldhausen/README.md) |
| Bundled small Waldhausen category | `Quillen.Waldhausen.SmallWaldhausenCategory.KFunctor n` | [Chosen zero and functoriality](../Waldhausen/README.md#exact-functors-and-the-chosen-zero) |
| Scheme `X` | `AlgebraicGeometry.Scheme.K X n`, `G X n`, `restrictK`, `restrictG`, `KToG` | [Scheme K/G-theory](../AlgebraicGeometry/Scheme/README.md) |
| Strict/local perfect complexes | `AlgebraicGeometry.Scheme.Modules.Complex.StrictPerfect`, `Perfect`; `Quillen.PerfectComplexes.StrictK`, `PerfectK` | [Perfect complexes](../AlgebraicGeometry/PerfectComplexes/README.md#complexes-and-support) |
| Commuting path square | `Path.Homotopy.squareProjectionReturnMap`, `squareProjectionReturnTrack` | [Original path returns](../Topology/Path/SquareProjectionReturn.lean) |
| Based prespectrum | `Quillen.LoopPrespectrum`, signed stable groups, actual fibers and telescopes | [Spectra](../Topology/Prespectrum/README.md) |
| Ring-indexed Bass recursion | `Quillen.Bass.negativeKFunctor i` on `CommRingCat` | [Bass groups](Bass/README.md#bass-cokernels-and-the-original-laurent-seed) |
| Projective completion | `Quillen.FiniteProjectiveModule.StableCompletion.Completion`, `ZeroComponent`, `stableZeroMap` | [Ring plus model](Plus/README.md) |

The historical underscore spellings of the path-return constructors remain
transparent deprecated aliases of these canonical names.

For composable exact functors, the pointwise map law is
`(F.comp G).KMap n x = G.KMap n (F.KMap n x)`.
`CategoryTheory.ExactCategory.ExactFunctor.KMap_id_apply` and `KMap_comp_apply` are public helpers in
`Quillen.KTheory.API`. Natural-isomorphism and small-model comparisons use the
same canonical maps; their explicit universe and comparison inputs remain in
the individual interfaces.

Scheme/group universe bounds and actual selected-model conventions are recorded in the [scheme guide](../AlgebraicGeometry/Scheme/README.md#sheaf-categories-universes-and-degrees).

## Ring plus and scalar extension

| Import after `Quillen.` | Public names |
| --- | --- |
| `KTheory.Map.RightBaseChange` | Original `rightBaseChangeExact.KMap` identity/composition laws |

## Degree-zero presentation boundary

For an exact structure, `K n` is `π_(n+1)(BQ)`. Its object-and-conflation
Grothendieck group identifies naturally with original K₀. The Waldhausen
weak-arrow/cofibration-pushout presentation also identifies with original K₀,
with explicit small-model transport for independent object and morphism
universes. These are the stated presentations, without an inferred
triangulated-derived presentation of perfect objects.

## Geometric comparison routes

The [scheme family](../AlgebraicGeometry/Scheme/README.md) owns scheme K/G
universes, pullback, regular comparison and finite direct image. The
[perfect-localization family](../AlgebraicGeometry/PerfectComplexes/Localization.md)
owns relative/open comparison, the K0 image boundary and exact connective tail.
Those source families retain the qcqs, compact-open, resolution and universe
hypotheses; they are not strengthened by this K-theory entrypoint.

## Exact categories and canonical Quillen K-maps

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
and K-map extensions in that native namespace. `CategoryTheory.ExactCategory.SmallExactCategory` is the
bundled application category.

| Full import | Focused public names |
| --- | --- |
| [Aglib.CategoryTheory.ExactCategory.Basic](https://github.com/kangxyz/aglib/blob/a7ebd6f6455c0f05e53e83248372ef53967b0103/Aglib/CategoryTheory/ExactCategory/Basic.lean) | `ExactStructure`, `ExactStructure.inflation`, `ExactStructure.deflation` |
| [`Quillen.KTheory.API`](API.lean) | `ExactFunctor.KMap`, `SmallExactCategory.ofExactStructure`, `SmallExactCategory.KFunctor` |
| [`Quillen.KTheory.GrothendieckGroup.Basic`](GrothendieckGroup/Basic.lean) | `ExactStructure.GrothendieckGroup`, `ExactStructure.grothendieck_universal` |

## BQ and the degree convention

[`Quillen.KTheory.Basic`](Basic.lean) defines `E.KSpace` as
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
[`ExactCategory.Functor`](../CategoryTheory/ExactCategory/Functor.lean).
The functor `F.mapQ` sends an original object to its image and a span to the
span obtained by applying `F.toFunctor` to its apex and legs.

An additive exact functor preserves zero up to its canonical zero-object
isomorphism. [`Map.Basic`](Map/Basic.lean) uses that
isomorphism to rebase the Q-functor. The resulting realization map is pointed
at the specified zero vertices, and `F.KMap n` is its homomorphism
`E.K n →* E'.K n`. Strict equality between the image zero and the target's
chosen zero is unnecessary.

The identity and composition laws use these same maps. In particular,
`(F.comp G).KMap n x = G.KMap n (F.KMap n x)` for composable exact functors.
[`Map.Functoriality`](Map/Functoriality.lean) proves
`ExactFunctor.KMap_comp` using the based realization homotopy;
[`Map.NaturalIso`](Map/NaturalIso.lean) proves
`ExactFunctor.KMap_eq_of_natIso` for an isomorphism of the underlying functors.
The pointwise forms `KMap_id_apply` and `KMap_comp_apply` are in `KTheory.API`.

For a category with matching object and morphism universe `u`,
`SmallExactCategory.ofExactStructure E` packages the existing structure.
[`Quillen.KTheory.Functor`](Functor.lean) defines
`CategoryTheory.ExactCategory.SmallExactCategory.KFunctor n : SmallExactCategory.{u} ⥤ GrpCat.{u}`.
Its arrows are actual exact functors, and its maps are precisely their `KMap n`.

## Further comparisons and client examples

An exact category also has
[`Waldhausen.ofExactCategory E`](../Waldhausen/ExactCategory.lean),
with inflations as cofibrations and isomorphisms as weak equivalences.
The separate [Q/S comparison](../Waldhausen/QuillenComparison/README.md#comparison-with-exact-category-q)
identifies its S-model with the original Q-model and respects both canonical
K-map APIs. The all-degree commutativity and conflation-additivity interfaces
are in [`QuillenComparison.KCommutativity`](../Waldhausen/QuillenComparison/KCommutativity.lean)
and [`QuillenComparison.ExactAdditivity`](../Waldhausen/QuillenComparison/ExactAdditivity.lean).
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
See [scope summary](../../docs/SCOPE.md) for those families and the remaining global comparisons.
