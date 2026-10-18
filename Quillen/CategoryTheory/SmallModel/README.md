# Small-model K-theory transport

## Public imports

| Full import | Focused public names |
| --- | --- |
| [`Quillen.CategoryTheory.SmallModel.Exact`](Exact.lean) | `ExactStructure.SmallK`, `ExactFunctor.smallKMap`, `ExactStructure.presentationKEquiv` |

## Equivalences and universe boundaries

The raw `KMap`, composition, and natural-isomorphism signatures use
`C D : Type u` with `[Category.{v} C]` and `[Category.{v} D]`. The shared
object universe need not equal the shared morphism universe. The algebraic
definition of an exact functor itself allows independent source and target
universes; that broader definition does not enlarge these realization APIs.

[`Quillen.KTheory.Equivalence`](../../KTheory/Equivalence.lean) proves that an
underlying categorical equivalence which reflects both inflations and
deflations induces an equivalence of Q-categories. Given
`[F.mapQ.IsEquivalence]`, `F.KEquivOfMapQIsEquivalence n` is an equivalence of
the original K-groups whose forward homomorphism is exactly `F.KMap n`.
Reflection of admissibility must be retained when establishing the Q-level
hypothesis from an underlying equivalence.

For different morphism universes `v₁` and `v₂`,
[`Map.CommonAmbient`](../../KTheory/Map/CommonAmbient.lean) supplies
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
[`SmallModel.Functoriality`](Functoriality.lean).

`E.presentationKEquiv e f n` compares two additive small presentations
`e : S ≌ C` and `f : T ≌ C`, with `S` and `T` small in the same universe `w`.
Its forward map comes from `E.presentationComparison e f`. This presentation
independence does not supply an identification with an out-of-universe raw
realization of the original category.
