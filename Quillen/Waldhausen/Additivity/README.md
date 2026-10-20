# Additivity interfaces

## Additivity and product groups

For `F G H : C ⥤ D` and source/target structures `V, W`,
[`Additivity.IsCofibrationSequence`](CofibrationSequence.lean)
on `a : F ⟶ G` and `b : G ⟶ H` requires exactness of all three functors, pointwise
cofibrations for `a`, the relative pushout cofibration condition of
[`Additivity.IsCofibrationTransformation`](PushoutEndpoints.lean),
and pointwise cofiber pushout squares for `a` and `b`.

For such a sequence `hs`, `Additivity.KMap_additivity_mul` proves for every `n : ℕ` and `x` that
`KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x` in the original
multiplication, including K₀. The target's `[HasBinaryCoproducts D]` instance
can be supplied by `Additivity.hasBinaryCoproducts W`. `Additivity.K_mul_comm`
and `Additivity.KCommGroup` retain that same group law.

[`ExtensionCategory.KEquiv`](../ExtensionCategory/KEquivalence.lean)
compares extension K-theory with the actual product category by source/cofiber,
with the split-extension K-map as inverse. Composing with
[`Product.KEquiv`](../Product/KEquivalence.lean) gives
[`ExtensionCategory.productKEquiv`](../ExtensionCategory/ProductKEquivalence.lean)
to the product of original K-groups, with the pair of source/cofiber K-maps forward.
The extension equivalences require `[Category.{u} C]` for `C : Type u`; product
and functor-additivity interfaces allow the stated independent `u, v`.

## Literal cofiber rows and object-loop tracks

For `C : Type u` with `[Category.{v} C]` and `[HasZeroMorphisms C]`, let
`W : Structure C`, `i : A ⟶ B`, and `hi : W.cof i`. Supply a quotient `q : B ⟶ Q` with
`hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)`.
`QuotientRows.cofiberTwoRow W i q hi hQ` is the actual S₂ quotient row.
Its [ordinal faces](../SConstruction/Rows/CofiberTwoFaces.lean)
are quotient, middle, and source, in face order `0, 1, 2`.
[`W.cofiberObjectLoopTrack`](../GrothendieckComparison/CofiberObjectTrack.lean)
is the specified realized triangle homotopy from the source object loop followed
by the quotient object loop to the middle object loop, with independent
comparison and loop parameters.

If also `hwi : W.weq i`,
[`QuotientRows.cofiberTwo_quotient_weak`](../SConstruction/Rows/CofiberTwoComparison.lean)
proves the displayed zero-to-quotient arrow weak by gluing. The comparison from
the identity-cofiber row has components `𝟙 A`, `i`, and `0 : W.zero ⟶ Q`;
acyclicity of the quotient is a conclusion, not an extra input.
[`W.cofiberPrismHomotopy`](../GrothendieckComparison/CofiberPrismHomotopy.lean)
retains both full triangles and their constant chosen-zero vertex lines.
`W.cofiberPrismCompositionLoops` curries its actual composition cube into a
continuous square of based loops, keeping comparison, nerve, and loop coordinates
independent. Its nerve faces are the identity-cofiber and original quotient tracks.

For arbitrary composable weak arrows `f : A ⟶ B` and `g : B ⟶ D`, the
[weak-arrow nerve prism](../GrothendieckComparison/WeakObjectCompositionPrism.lean)
has the original first, second, and literal composite-arrow squares as its faces.
[`W.weakObjectSquareCompositionTrack`](../GrothendieckComparison/WeakObjectCompositionTrack.lean)
compares the concatenated original weak-square loop-space paths with the path
for `f ≫ g`, relative to their original object-loop endpoints. This weak-arrow
interface requires `W.weq f` and `W.weq g`, without the cofiber family's
`HasZeroMorphisms` hypothesis.

The higher-family owners
[`NerveSimplexFamily`](../SConstruction/NerveSimplexFamily.lean),
[`SimplexFamily`](../SConstruction/Iterated/SimplexFamily.lean)
and [`SimplexFaces`](../SConstruction/Iterated/SimplexFaces.lean)
construct the genuine Delta[k] family through every finite S-stage and its
jointly continuous realization. Their `ModelSimplex` input is a coherent
chain of exact model functors with strict chosen-zero equations and weak
transformation components. Subchain faces agree exactly with the entire
original Delta[2] triangles; the chosen zero stays fixed for every simplex
parameter and the spectrum structure coordinate stays independent. This
family supplies higher comparison data when its concrete native input and
face equations are realized; it does not construct a missing Bass cube.

[`SimplexTriangleLift`](../SConstruction/Iterated/SimplexTriangleLift.lean)
and `SimplexParameterPaths` identify complete old triangles with barycentric
scalar paths and surfaces at every level. `SimplexWhiskering`,
`SimplexTriangleWhiskering`, `OriginalTriangleTransport` and
`SimplexTriangleSourceTransport` retain actual pre/postcomposition and the
displayed source-equality transports over their whole parameter families.
[`SimplexLiftOperations`](../SConstruction/Iterated/SimplexLiftOperations.lean),
`SimplexLiftReassociation` and `SimplexLiftPasting` preserve supplied pointwise
lifts through native reversal, concatenation, reparameterization, reassociation,
constant-half contraction, cancellation and rotation. Their square descent uses
the actual `ThreeSideSquare.collapse`, including the full degree-zero loop and
an independent spectrum structure coordinate. These laws require the stated
path/surface lifts; they do not produce a lift for every native Bass track.

[`CommonReferenceWhiskering`](../SConstruction/Iterated/CommonReferenceWhiskering.lean)
retains an entire simplex family under the specified common-reference change.
`SimplexDiagonalComposition` and `SimplexProductDiagram` form the actual
composed diagram from two independently varying families.
[`RealizationSimplexComposition`](../SConstruction/Iterated/RealizationSimplexComposition.lean)
identifies stage, realization and whole prespectrum evaluation using the actual
realization-product homeomorphism and monotone grid parameter. Original zeros,
all levels including zero, and the separate structure coordinate are retained.
The prescribed raw point-set Bass comparison now has both chart pauses and
its whole bottom surface with literal shared edges; its remaining compatible
faces and genuine composition cylinder require additional construction.
This separate implementation-comparison target is not a premise of the direct
[tensor/Bass realization of original TT 7.4](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorBassConstruction.md).
