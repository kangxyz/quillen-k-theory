# Waldhausen categories, S-constructions, and comparison theorems

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
| [`KTheory`](../../Quillen/Waldhausen/KTheory.lean) | `Structure.Delooping`, `Structure.kBasepoint`, `Structure.K` |
| [`Functoriality.KMap`](../../Quillen/Waldhausen/Functoriality/KMap.lean) | `IsExact`, `KMap`, identity, composition, and isomorphism invariance |
| [`Additivity.GroupFormula`](../../Quillen/Waldhausen/Additivity/GroupFormula.lean) | `Additivity.K_mul_comm`, `Additivity.KMap_additivity_mul` |
| [`SConstruction.Rows.CofiberTwoRow`](../../Quillen/Waldhausen/SConstruction/Rows/CofiberTwoRow.lean), [`GrothendieckComparison.CofiberPrismComposition`](../../Quillen/Waldhausen/GrothendieckComparison/CofiberPrismComposition.lean) | `QuotientRows.cofiberTwoRow`, `Structure.cofiberObjectLoopTrack`, `Structure.cofiberPrismCompositionLoops` |
| [`QuillenComparison.ExactNaturality`](../../Quillen/Waldhausen/QuillenComparison/ExactNaturality.lean) | `QuillenComparison.comparisonKEquiv`, `comparisonKEquiv_exactFunctor_naturality` in that namespace |
| [`Approximation.GeneralKEquivalence`](../../Quillen/Waldhausen/Approximation/GeneralKEquivalence.lean) | `HasApproximationProperty.KEquivGeneral` |
| [`Cofinality.GeneralDense`](../../Quillen/Waldhausen/Cofinality/GeneralDense.lean) | `Cofinality.DenseCofiberData.inclusionKEquivGeneral`, `inclusion_KZero_exact_general` in that namespace |
| [`Fibration.GeneralComparison`](../../Quillen/Waldhausen/Fibration/GeneralComparison.lean), [`Fibration.LongExactSequence`](../../Quillen/Waldhausen/Fibration/LongExactSequence.lean) | `Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general`, `Fibration.changeWeakConnectingHom` |
| [`Fibration.CanonicalFiberComponentTranslation`](../../Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean) | `Fibration.canonicalFiberComponentEquiv` |
| [`GilletWaldhausen.GeneralComparison`](../../Quillen/Waldhausen/GilletWaldhausen/GeneralComparison.lean) | `GilletWaldhausen.boundedTermsSingleCoarseKEquivGeneral` |
| [`GrothendieckComparison.SmallModel`](../../Quillen/Waldhausen/GrothendieckComparison/SmallModel.lean) | `AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel` |
| [`GrothendieckComparison.ImageQuotientConeZero`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientConeZero.lean) | `AlgebraicGrothendieck.imageQuotient_changeWeakKMap_range_ker`, `AlgebraicGrothendieck.imageQuotientConeMap_stable_zero_bijective` |

## The structure, simplices, and degree convention

For `C : Type u` with `[Category.{v} C]`,
[`Quillen.Waldhausen.Structure C`](../../Quillen/Waldhausen/Basic.lean) contains
`zero`, `isZero`, and morphism properties `cof` and `weq`. Both classes contain
identities and isomorphisms and are closed under composition. Every zero-to-object
map is a cofibration; pushouts along cofibrations exist and preserve cofibrations;
gluing preserves weak equivalences in those pushouts. Two-out-of-three, an extension
axiom, and cylinder or factorization data are additional conditions.

[`SConstruction`](../../Quillen/Waldhausen/SConstruction.lean) defines an
`n`-simplex as an `n`-chain of pointwise weak equivalences between Sₙ quotient
diagrams, with zero diagonal, cofibration inclusions, and genuine quotient
pushout squares. Simultaneous reindexing in both directions gives the diagonal
`sSet W.cof W.weq` of `N(wS•C)`, retaining the given weak class.

`W.Delooping` is `|diag N(wS•C)|` in `TopCat.{max u v}`. The all-zero diagram
provides `W.kBasepoint`; `W.K n` is `π_(n+1)(W.Delooping, W.kBasepoint)` for `n : ℕ`.
K₀ is a loop group. [`SConstruction.Connected`](../../Quillen/Waldhausen/SConstruction/Connected.lean)
proves the delooping is path connected. The definition gives groups in every
degree and higher-homotopy commutativity in positive K-degree; additivity also
supplies commutativity at zero.

## Exact functors and the chosen zero

For `F : C ⥤ D` between structures `W` and `V`,
[`IsExact`](../../Quillen/Waldhausen/Functor.lean) requires preservation of zero
objects, cofibrations, weak equivalences, and pushouts along cofibrations.
Postcomposition gives `sSetMap hF` and `deloopingMap hF` for an exactness proof
`hF`, sending the source point to the point of the image zero.

The unique isomorphism from the image zero to the target's chosen zero rebases
the functor in [`PointedFunctor`](../../Quillen/Waldhausen/PointedFunctor.lean).
`Quillen.Waldhausen.KMap hF n` is the resulting homomorphism of original K-groups.
`KMap_id`, `KMap_comp_KMap`, and `KMap_eq_of_iso` retain this normalization.
[`Quillen.Waldhausen.SmallWaldhausenCategory.KFunctor n`](../../Quillen/Waldhausen/KFunctor.lean)
packages all exact functors, without strict chosen-zero preservation.

`IsExact` permits independent source and target universes. The realization and
K-map signatures here take `C D : Type u` with `[Category.{v} C]` and `[Category.{v} D]`.
In the general comparison theorems, independent universes mean independent object
`u` and morphism `v`, retaining these shared source/target parameters.

## Additivity and product groups

For `F G H : C ⥤ D` and source/target structures `V, W`,
[`Additivity.IsCofibrationSequence`](../../Quillen/Waldhausen/Additivity/CofibrationSequence.lean)
on `a : F ⟶ G` and `b : G ⟶ H` requires exactness of all three functors, pointwise
cofibrations for `a`, the relative pushout cofibration condition of
[`Additivity.IsCofibrationTransformation`](../../Quillen/Waldhausen/Additivity/PushoutEndpoints.lean),
and pointwise cofiber pushout squares for `a` and `b`.

For such a sequence `hs`, `Additivity.KMap_additivity_mul` proves for every `n : ℕ` and `x` that
`KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x` in the original
multiplication, including K₀. The target's `[HasBinaryCoproducts D]` instance
can be supplied by `Additivity.hasBinaryCoproducts W`. `Additivity.K_mul_comm`
and `Additivity.KCommGroup` retain that same group law.

[`ExtensionCategory.KEquiv`](../../Quillen/Waldhausen/ExtensionCategory/KEquivalence.lean)
compares extension K-theory with the actual product category by source/cofiber,
with the split-extension K-map as inverse. Composing with
[`Product.KEquiv`](../../Quillen/Waldhausen/Product/KEquivalence.lean) gives
[`ExtensionCategory.productKEquiv`](../../Quillen/Waldhausen/ExtensionCategory/ProductKEquivalence.lean)
to the product of original K-groups, with the pair of source/cofiber K-maps forward.
The extension equivalences require `[Category.{u} C]` for `C : Type u`; product
and functor-additivity interfaces allow the stated independent `u, v`.

## Literal cofiber rows and object-loop tracks

For `C : Type u` with `[Category.{v} C]` and `[HasZeroMorphisms C]`, let
`W : Structure C`, `i : A ⟶ B`, and `hi : W.cof i`. Supply a quotient `q : B ⟶ Q` with
`hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)`.
`QuotientRows.cofiberTwoRow W i q hi hQ` is the actual S₂ quotient row.
Its [ordinal faces](../../Quillen/Waldhausen/SConstruction/Rows/CofiberTwoFaces.lean)
are quotient, middle, and source, in face order `0, 1, 2`.
[`W.cofiberObjectLoopTrack`](../../Quillen/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean)
is the specified realized triangle homotopy from the source object loop followed
by the quotient object loop to the middle object loop, with independent
comparison and loop parameters.

If also `hwi : W.weq i`,
[`QuotientRows.cofiberTwo_quotient_weak`](../../Quillen/Waldhausen/SConstruction/Rows/CofiberTwoComparison.lean)
proves the displayed zero-to-quotient arrow weak by gluing. The comparison from
the identity-cofiber row has components `𝟙 A`, `i`, and `0 : W.zero ⟶ Q`;
acyclicity of the quotient is a conclusion, not an extra input.
[`W.cofiberPrismHomotopy`](../../Quillen/Waldhausen/GrothendieckComparison/CofiberPrismHomotopy.lean)
retains both full triangles and their constant chosen-zero vertex lines.
`W.cofiberPrismCompositionLoops` curries its actual composition cube into a
continuous square of based loops, keeping comparison, nerve, and loop coordinates
independent. Its nerve faces are the identity-cofiber and original quotient tracks.

For arbitrary composable weak arrows `f : A ⟶ B` and `g : B ⟶ D`, the
[weak-arrow nerve prism](../../Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionPrism.lean)
has the original first, second, and literal composite-arrow squares as its faces.
[`W.weakObjectSquareCompositionTrack`](../../Quillen/Waldhausen/GrothendieckComparison/WeakObjectCompositionTrack.lean)
compares the concatenated original weak-square loop-space paths with the path
for `f ≫ g`, relative to their original object-loop endpoints. This weak-arrow
interface requires `W.weq f` and `W.weq g`, without the cofiber family's
`HasZeroMorphisms` hypothesis.

The higher-family owners
[`NerveSimplexFamily`](../../Quillen/Waldhausen/SConstruction/NerveSimplexFamily.lean),
[`SimplexFamily`](../../Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean)
and [`SimplexFaces`](../../Quillen/Waldhausen/SConstruction/Iterated/SimplexFaces.lean)
construct the genuine Delta[k] family through every finite S-stage and its
jointly continuous realization. Their `ModelSimplex` input is a coherent
chain of exact model functors with strict chosen-zero equations and weak
transformation components. Subchain faces agree exactly with the entire
original Delta[2] triangles; the chosen zero stays fixed for every simplex
parameter and the spectrum structure coordinate stays independent. This
family supplies higher comparison data when its concrete native input and
face equations are realized; it does not construct a missing Bass cube.

[`SimplexTriangleLift`](../../Quillen/Waldhausen/SConstruction/Iterated/SimplexTriangleLift.lean)
and `SimplexParameterPaths` identify complete old triangles with barycentric
scalar paths and surfaces at every level. `SimplexWhiskering`,
`SimplexTriangleWhiskering`, `OriginalTriangleTransport` and
`SimplexTriangleSourceTransport` retain actual pre/postcomposition and the
displayed source-equality transports over their whole parameter families.
[`SimplexLiftOperations`](../../Quillen/Waldhausen/SConstruction/Iterated/SimplexLiftOperations.lean),
`SimplexLiftReassociation` and `SimplexLiftPasting` preserve supplied pointwise
lifts through native reversal, concatenation, reparameterization, reassociation,
constant-half contraction, cancellation and rotation. Their square descent uses
the actual `ThreeSideSquare.collapse`, including the full degree-zero loop and
an independent spectrum structure coordinate. These laws require the stated
path/surface lifts; they do not produce a lift for every native Bass track.

## Comparison with exact-category Q

For `E : Quillen.ExactStructure C`,
[`ofExactCategory E`](../../Quillen/Waldhausen/ExactCategory.lean) uses inflations
and isomorphisms as its cofibrations and weak equivalences. Its axioms follow
from the exact structure. A `F : Quillen.ExactFunctor E E'` has `F.waldhausenExact`,
with pushout preservation derived from additive exactness.

[`QuillenComparison.Equivalence`](../../Quillen/Waldhausen/QuillenComparison/Equivalence.lean)
constructs `deloopingHomotopyEquiv E` to `E.KSpace`. Its based zigzag gives
`comparisonKEquiv E n : (ofExactCategory E).K n ≃* E.K n`, with the original
`comparisonK E n` forward, for every `n` and without an equivalence premise.
`comparisonKEquiv_exactFunctor_naturality` commutes with Waldhausen
`KMap F.waldhausenExact n` and exact-category `F.KMap n` in their common universes.
See [ExactCategories.md](ExactCategories.md).

## Approximation and structural cylinder data

An approximation witness `h` for
[`HasApproximationProperty W V F`](../../Quillen/Waldhausen/Approximation/Basic.lean)
contains App1, reflection of weak equivalences, and the cofibration version of App2:
each `f : F.obj X ⟶ Y` factors as `F.map i ≫ p`, with `i : X ⟶ X'` a source
cofibration and `p : F.obj X' ⟶ Y` a target weak equivalence. Exactness is separate.

`HasApproximationProperty.KEquivGeneral h hF J n` requires
`[V.weq.HasTwoOutOfThreeProperty]` and
`J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)`.
The original `deloopingMap hF` is then a weak homotopy equivalence and the original
`KMap hF n` is bijective in every degree, including zero, and is the forward map.

[`JointData`](../../Quillen/Waldhausen/Fibration/Rows/JointFactorization.lean)
contains an exact arrow-to-extension functor, natural source and target injections
presenting a coproduct, and a coarse-weak projection factoring the original arrow.
This cylinder data is not inferred from Waldhausen axioms or App1/App2.
Approximation does not require the additional section identity below.

## Fibration and its connective tail

[`Fibration.NestedWeakEquivalences W`](../../Quillen/Waldhausen/Fibration/AcyclicSubcategory.lean)
specifies a coarse structure with the same cofibrations and chosen zero as `W`,
with `W.weq ≤ N.coarse.weq`. Its acyclic objects have a coarse-weak zero-to-object
map; their subcategory retains the fine weak class. `changeWeak_exact N` changes
only the weak class.

[`canonicalFiberMap N`](../../Quillen/Waldhausen/Fibration/CanonicalFiberMap.lean)
maps the acyclic S-delooping into the homotopy fiber of `changeWeakMap N`. Its
projection is the actual inclusion and its path is the reversed zero-to-inclusion
homotopy; construction does not assert a weak equivalence.

`canonicalFiberMap_isWeakHomotopyEquivalence_general` requires coarse two-out-of-three,
`he : Fibration.ExtensionAxiom N.coarse`, `D : Fibration.RowFactorization.JointData N`,
and `hs : Fibration.RowFactorization.SecondEndpointSection N D`.
The [extension axiom](../../Quillen/Waldhausen/Fibration/WeakEquivalenceCofiber.lean)
says weak source and quotient maps in a map of cofiber squares imply a weak middle map.
The [section condition](../../Quillen/Waldhausen/Fibration/Rows/SecondEndpoint.lean)
says the second injection followed by the joint cofibration and projection is the
target identity. This is additional to `JointData`. The theorem retains the original
map and full path for independent object and morphism universes.

Given a proof `h` that the original comparison is weak,
[`Fibration.LongExactSequence`](../../Quillen/Waldhausen/Fibration/LongExactSequence.lean)
defines `changeWeakConnectingHom N h n : N.coarse.K (n + 1) →* (acyclicStructure N).K n`
by the homotopy-fiber boundary, with all recurring range/kernel equalities for the
original K-maps. `changeWeak_KMap_zero_surjective_of_weak` gives surjectivity onto
`N.coarse.K 0` by the pointed-set tail and connected acyclic S-space. Positive
surjectivity separately requires injectivity of the preceding acyclic-inclusion
map. The sequence supplies no negative boundary.

### Prescribed loop-fiber normalization

For nested structures `N`, an object `A`, and `[HasZeroMorphisms C]`,
[`Fibration.canonicalFiberComponentEquiv N A`](../../Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean)
is a homotopy equivalence between fibers of the original localization loop map,
from the fiber over the constant loop to the fiber over `N.coarse.kZeroObjectLoop A`.
It uses the original loop/fiber transpose, left concatenation by the fine object
loop, and the actual identity-cofiber suffix path. `canonicalFiberComponentEquiv_object`
gives exactly the prescribed translation of the transposed object-loop point for
each `X : Fibration.AcyclicCategory N`.
The [fiber-square formula](../../Quillen/Waldhausen/Fibration/CanonicalFiberObjectSquare.lean)
reverses the zero-to-acyclic nerve time and retains the original object-loop time.

[`Structure.identityCofiberComponentEquiv_eq`](../../Quillen/Waldhausen/Fibration/IdentityCofiberNormalization.lean)
identifies the induced first homotopy-group normalization of the loop space with
the standard left-component normalization. It does not identify the entire
identity-cofiber and suffix-removal paths. The separate fibration theorem still
retains its hypotheses above. Scalar-boundary applications and their geometric
comparison questions are in [PerfectComplexes.md](PerfectComplexes.md).

## Dense cofinality and degree zero

The input `h` of type
[`Cofinality.DenseCofiberData W P`](../../Quillen/Waldhausen/Cofinality/DenseSubcategory.lean)
contains membership of zero, invariance along weak arrows, extension and quotient
closure for cofiber squares, and a complement `B` with `P (A ⨿ B)` for every `A`.
With `[HasBinaryCoproducts C]` these construct the dense full subcategory and grading.

With `D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W)`
and the corresponding `Fibration.RowFactorization.SecondEndpointSection`,
`h.inclusionKEquivGeneral D hs n` compares
the subcategory's `K (n + 1)` with `W.K (n + 1)` by inclusion.
`inclusion_KMap_injective_general` covers every degree. Separately,
`inclusion_KZero_exact_general` gives an injective K₀ inclusion, its range as the
kernel of change to `h.grading.nested.coarse`, and surjectivity onto that coarse
K₀ endpoint. K₀ inclusion surjectivity is not asserted. These original-map results
allow independent `u, v`.

## Bounded complexes and Gillet–Waldhausen

The general comparison takes `A : Type (max u v)` with `[Category.{v} A]` and
`[Abelian A]`. Its term property `P` has `[P.ContainsZero]`,
`[P.IsClosedUnderIsomorphisms]`, and
`[(Quillen.abelianExactStructure A).IsExtensionClosed P]`.
[`boundedTerms P`](../../Quillen/Waldhausen/GilletWaldhausen/BoundedTerms.lean)
consists of term-bounded cochain complexes with every term in `P`. The
[nested models](../../Quillen/Waldhausen/GilletWaldhausen/FibrationModels.lean)
share inherited admissible cofibrations and zero, with fine isomorphisms and
coarse quasi-isomorphisms.

`GilletWaldhausen.boundedTermsSingleCoarseKEquivGeneral P n` additionally requires
`[(Quillen.abelianExactStructure A).IsKernelClosed P]`. This is
[admissible kernel closure](../../Quillen/Resolution/Finite.lean): membership of the
middle and quotient of a conflation implies membership of the kernel, without
arbitrary admissible-subobject closure. The equivalence goes from the term category's
isomorphism-weak S-model to `(boundedTermsNested P).coarse.K n`, including `n = 0`,
with `KMap (boundedTermsSingle_coarseExact P 0) n` forward. This inserts the original
term as a single complex in cochain degree zero. The bounded-complex cylinder and
section data are constructed under these conditions.

## Classical K₀ and small-model transport

[`AlgebraicGrothendieck.Group W`](../../Quillen/Waldhausen/GrothendieckGroup/Basic.lean)
is the free abelian group on objects modulo the chosen-zero relation, equality
along weak arrows, and `[Q] = [B] + [D] - [A]` for every displayed cofibration
pushout `Q = B ⨿_A D`. Its universal grading is algebraic; identification with
homotopical K₀ is separate.

For `C : Type u` with `[SmallCategory C]`,
[`AlgebraicGrothendieck.grothendieckKZeroEquiv W`](../../Quillen/Waldhausen/GrothendieckComparison/Equivalence.lean)
has source `Multiplicative (Group W)` and target the original `W.K 0`. Its forward
`grothendieckToKZero W` uses the original object loops; its inverse is the realized
grading `kZeroToGrothendieck W`. Both inverse identities, original object classes,
and all-class exact-functor naturality are retained.
[`SmallWaldhausenCategory.grothendieckKZeroIso`](../../Quillen/Waldhausen/GrothendieckComparison/Functor.lean)
packages the natural isomorphism to `KFunctor 0`.

For independent object and morphism universes,
[`W.smallModel`](../../Quillen/Waldhausen/SmallModel/Basic.lean) uses `AsSmall` to lift
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
[`AlgebraicGrothendieck.ImageQuotient W F hF`](../../Quillen/Waldhausen/GrothendieckGroup/Image.lean)
is `AlgebraicGrothendieck.Group V` modulo the range of the original `AlgebraicGrothendieck.map W F hF`.
Its object grading `d := AlgebraicGrothendieck.imageQuotientGrading W F hF` defines a coarse structure
on the original target: weak arrows are those with equal quotient grades, while
the cofibrations and chosen zero are unchanged.

Supply `T : FunctorialFactorization V.smallModel`, a specified functorial
cofibration/weak-equivalence factorization in the fine target's small model.
[`imageQuotient_coarseKZeroValueMap_bijective`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotient.lean)
then identifies `d.coarseStructure.K 0` with the multiplicatively written algebraic image quotient
through the actual coarse value map. The
[exactness declarations](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientExact.lean)
`imageQuotient_changeWeakKMap_range_ker` and `imageQuotient_changeWeakKMap_surjective`
prove that the original changeWeak K₀ map is onto and its kernel is exactly
`(KMap hF 0).range`. These results use the original Grothendieck comparison and
its naturality; no assumed presentation or additional localization-fibration
premise replaces them. Object and morphism universes may differ as stated above.

[`imageQuotientConeMap W F hF`](../../Quillen/Waldhausen/GrothendieckComparison/ImageQuotientCone.lean)
is the unshifted cone descent for the original exact prespectrum map. Its
nullhomotopy reverses the specified zero-to-normalized-image transformation,
and its inclusion face is the original changeWeak prespectrum map.
With the same `T`, `imageQuotientConeMap_stable_zero_bijective` proves bijectivity
in stable degree zero. The proof uses the original connective spectrum's
cone/fiber comparison and vanishing in degree `-1`; the
[general cone-descent interface](../../Quillen/Topology/Prespectrum/ConeDescZeroComparison.lean)
retains these as explicit hypotheses. An all-degree stable-equivalence conclusion
additionally needs actual concentration of its source and target; it does not
follow from this degree-zero theorem alone.

Focused examples in [QuillenTest.CofiberObjectTrack](../../QuillenTest/CofiberObjectTrack.lean),
[QuillenTest.CofiberPrismComposition](../../QuillenTest/CofiberPrismComposition.lean), and
[QuillenTest.ImageQuotientKZeroExact](../../QuillenTest/ImageQuotientKZeroExact.lean) retain the
original faces, independent coordinates, and preimages under the original K-maps.

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
category and term closures. See [Scope.md](../reference/Scope.md) for remaining global
and geometric comparisons.
