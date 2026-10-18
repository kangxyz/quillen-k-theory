# GrothendieckComparison interfaces

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Waldhausen.GrothendieckComparison.SmallModel` | Classical Waldhausen K₀ with independent object and morphism universes |
| `Quillen.Waldhausen.GrothendieckComparison.ImageQuotientExact` | Coarse image-quotient K₀ exactness under exactness and target factorization |

## Degree-zero presentation interfaces

| Import after `Quillen.` | Canonical comparison |
| --- | --- |
| `Waldhausen.GrothendieckComparison.Equivalence` | `Waldhausen.AlgebraicGrothendieck.grothendieckKZeroEquiv` |
| `Waldhausen.GrothendieckComparison.SmallModel` | `Waldhausen.AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel` |

## Image-quotient grading and cone maps

For an exact functor `F` from a Waldhausen structure `W` to `V`, the actual
image quotient is the algebraic Grothendieck group of `V` modulo the image
of the original algebraic map of `F`. The coarse weak class is equality of
these endpoint grades, retaining the original objects, cofibrations, and zero.
The following generic imports are under
`Quillen.Waldhausen.GrothendieckComparison`, with declaration namespace
`Quillen.Waldhausen.AlgebraicGrothendieck`:

| Module | Conclusion with original maps |
| --- | --- |
| [`ImageQuotient`](ImageQuotient.lean) | `imageQuotient_coarseKZeroValueMap_bijective` identifies coarse K₀ with the genuine image quotient |
| [`ImageQuotientExact`](ImageQuotientExact.lean) | `imageQuotient_changeWeakKMap_surjective` and `imageQuotient_changeWeakKMap_range_ker` give surjectivity and kernel equal to the original exact-functor K₀ image |
| [`ImageQuotientCone`](ImageQuotientCone.lean), [`ImageQuotientConeZero`](ImageQuotientConeZero.lean) | `imageQuotientConeMap` retains the specified whole null track; `imageQuotientConeMap_stable_zero_bijective` proves its stable degree-zero bijectivity |

The K₀ conclusions retain `hF : IsExact W.cof W.weq V.cof V.weq F` and
`T : FunctorialFactorization V.smallModel` for the fine target. They do not
assume a K₀ presentation or localization exactness. The unshifted cone map
uses the reversed specified zero-to-normalized-image transformation, and its
inclusion face is exactly the original change-of-weakness map. Bijectivity in
degree zero alone does not make it a stable equivalence in all signed degrees.

[`OpenDeficitGradingStable`](../../AlgebraicGeometry/PerfectComplexes/OpenDeficitGradingStable.lean)
specializes this to `perfectOpenDeficitGradingMap j`. Stable degree-zero
bijectivity holds for every open immersion. When `X` is qcqs and `U` is
quasi-compact, concentration of its actual source and graded target supplies
`perfectOpenDeficitGradingMap_isStableEquivalence` in every integer degree.
This is the raw-perfect objectwise comparison; coefficient naturality, the
inherited Laurent seed, and the original section comparison require their
own compatible maps.

## Classical K₀ and small-model transport

[`AlgebraicGrothendieck.Group W`](../GrothendieckGroup/Basic.lean)
is the free abelian group on objects modulo the chosen-zero relation, equality
along weak arrows, and `[Q] = [B] + [D] - [A]` for every displayed cofibration
pushout `Q = B ⨿_A D`. Its universal grading is algebraic; identification with
homotopical K₀ is separate.

For `C : Type u` with `[SmallCategory C]`,
[`AlgebraicGrothendieck.grothendieckKZeroEquiv W`](Equivalence.lean)
has source `Multiplicative (Group W)` and target the original `W.K 0`. Its forward
`grothendieckToKZero W` uses the original object loops; its inverse is the realized
grading `kZeroToGrothendieck W`. Both inverse identities, original object classes,
and all-class exact-functor naturality are retained.
[`SmallWaldhausenCategory.grothendieckKZeroIso`](Functor.lean)
packages the natural isomorphism to `KFunctor 0`.

For independent object and morphism universes,
[`W.smallModel`](../SmallModel/Basic.lean) uses `AsSmall` to lift
both to `max u v`, rather than shrinking to an essentially small presentation.
Exact up/down maps give a simplicial isomorphism, `W.smallModelDeloopingHomeomorph`,
and `W.smallModelKEquiv n`, preserving the chosen point and canonical K-maps.
`AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel W` combines this homeomorphism
with actual up/down quotient maps, retaining endpoints `Group W` and `W.K 0`,
with transported realized grading as inverse. It preserves object classes, is
natural in both directions on all classes, and agrees with the preceding equivalence
when the universes match.

No cylinder, factorization, `JointData`, or presentation premise is added to either
K₀ comparison. Classifying-space, Theorem B, S-additivity, and continuous-path
generation dependencies remain. A triangulated-derived presentation needs a separate
comparison.

## Exact-functor image quotient at K₀

For `C D : Type u` with `[Category.{v} C]` and `[Category.{v} D]`, let
`hF : IsExact W.cof W.weq V.cof V.weq F`. The algebraic
[`AlgebraicGrothendieck.ImageQuotient W F hF`](../GrothendieckGroup/Image.lean)
is `AlgebraicGrothendieck.Group V` modulo the range of the original `AlgebraicGrothendieck.map W F hF`.
Its object grading `d := AlgebraicGrothendieck.imageQuotientGrading W F hF` defines a coarse structure
on the original target: weak arrows are those with equal quotient grades, while
the cofibrations and chosen zero are unchanged.

Supply `T : FunctorialFactorization V.smallModel`, a specified functorial
cofibration/weak-equivalence factorization in the fine target's small model.
[`imageQuotient_coarseKZeroValueMap_bijective`](ImageQuotient.lean)
then identifies `d.coarseStructure.K 0` with the multiplicatively written algebraic image quotient
through the actual coarse value map. The
[exactness declarations](ImageQuotientExact.lean)
`imageQuotient_changeWeakKMap_range_ker` and `imageQuotient_changeWeakKMap_surjective`
prove that the original changeWeak K₀ map is onto and its kernel is exactly
`(KMap hF 0).range`. These results use the original Grothendieck comparison and
its naturality; no assumed presentation or additional localization-fibration
premise replaces them. Object and morphism universes may differ as stated above.

[`imageQuotientConeMap W F hF`](ImageQuotientCone.lean)
is the unshifted cone descent for the original exact prespectrum map. Its
nullhomotopy reverses the specified zero-to-normalized-image transformation,
and its inclusion face is the original changeWeak prespectrum map.
With the same `T`, `imageQuotientConeMap_stable_zero_bijective` proves bijectivity
in stable degree zero. The proof uses the original connective spectrum's
cone/fiber comparison and vanishing in degree `-1`; the
[general cone-descent interface](../../Topology/Prespectrum/ConeDescZeroComparison.lean)
retains these as explicit hypotheses. An all-degree stable-equivalence conclusion
additionally needs actual concentration of its source and target; it does not
follow from this degree-zero theorem alone.

Focused examples in [QuillenTest.CofiberObjectTrack](../../../QuillenTest/CofiberObjectTrack.lean),
[QuillenTest.CofiberPrismComposition](../../../QuillenTest/CofiberPrismComposition.lean), and
[QuillenTest.ImageQuotientKZeroExact](../../../QuillenTest/ImageQuotientKZeroExact.lean) retain the
original faces, independent coordinates, and preimages under the original K-maps.
