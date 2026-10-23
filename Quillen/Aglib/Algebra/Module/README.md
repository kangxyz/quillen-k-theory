# Module constructions

`FiniteCoefficientRetract` constructs the actual retraction onto a finite
coefficient window when the split inclusion lands there; finite support alone
is insufficient over an arbitrary ring. [`Aglib.Algebra.Module.FiniteParametrix`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/FiniteParametrix.lean) constructs a finite
projective split kernel from the displayed finite defect factorizations and
projectivity hypotheses, without assuming Noetherianity.

[`Aglib.Algebra.Module.MatrixPresentation`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/MatrixPresentation.lean) realizes finite projective modules as actual idempotent
matrix images. [`Aglib.Algebra.Module.MatrixBaseChange`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Module/MatrixBaseChange.lean) retains their original splittings and the
coefficientwise matrix map, without a flatness hypothesis. `RightScalarExtension`
constructs balanced tensor extension for arbitrary unital rings using its
balanced biadditive universal property, preserving the order of multiplication.

These are ordinary module interfaces. Stable matrix classes and K-theory maps
remain downstream. The native finite-parametrix namespace is `Module`; matrix presentations and
base change use `Module.Projective`. Remaining local module extensions retain
their existing namespaces.

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.Algebra.Module.RightScalarExtension` | Literal noncommutative balanced right tensor and its universal properties |

## Scalar extension by its universal property

For `f : R →+* S`, `rightBaseChangeHomEquiv f P N` is an additive equivalence
between `Sᵐᵒᵖ`-linear maps from the actual change-of-rings object and
`f.op`-semilinear maps from `P` into any ambient target module `N`. Its forward
map is literally precomposition by `rightBaseChangeUnit f P`.
`rightBaseChangeLift`, its unit equation and uniqueness theorem, and
`rightBaseChange_existsUnique` express the same universal extension. The unit
and Hom equivalence are natural in the projective source and the target module.

The construction passes from finite-free coordinate extension in
`Algebra.Matrix.RightScalarExtension`, through idempotent images in
`Algebra.Category.ModuleCat.MatrixImageScalarExtension`, to the actual
finite-projective presentation equivalence. Source-ring, target-ring, and
ambient target-module universes may be independent in this algebraic interface.
The target need not be finite or projective. This does not assert an adjunction
within finite-projective subcategories: restriction of scalars need not
preserve finite projectives.

[`Consumer.RingScalarExtension`](../../../../examples/downstream/Consumer/RingScalarExtension.lean)
checks the literal unit, Hom map, uniqueness and naturality, including
noncommutative and zero-ring examples.

## Literal balanced tensor and the original scalar extension

`Quillen.Aglib.Algebra.Module.RightScalarExtension` defines `RightScalarExtension.Tensor`
as the literal quotient of `S ⊗[ℤ] M` by the balancing relations
`(f r * s) ⊗ m - s ⊗ (op r • m)`. It proves that the right-submodule relation
span equals the integer span, constructs pure tensors, and proves balanced
biadditive and right-module semilinear universal properties. Ring and module
carrier universes are independent; no commutativity or flatness is assumed.
[`Consumer.BalancedRightTensor`](../../../../examples/downstream/Consumer/BalancedRightTensor.lean)
checks the public universal-property interface.

`Quillen.Aglib.Algebra.Category.ModuleCat.RightScalarExtension` gives the actual
additive tensor functor, source naturality, identity and composition linear
equivalences, and the triple-composition equality `compEquiv_assoc` on literal
carriers. The original scalar-extension universal property constructs
`rightTensorBaseChangeEquiv`, with actual inverse maps. Its source naturality
and its agreement with the pre-existing `rightBaseChangeId` and
`rightBaseChangeComp` retain the original units. Rectangular-matrix naturality
and the explicit idempotent-image comparison are also proved.

The finite-projective tensor functor is exact because it preserves the actual
splittings of inherited conflations. It requires neither flatness nor
commutativity. `rightTensorBaseChangeExact_KMap` identifies its original
zero-normalized K-map with the unchanged `rightBaseChangeExact.KMap` in every
degree, within the original common-ring-universe K-map interface.

Raw tensor carriers and the general module functor have independent universes.
The original finite-projective source interface remains `Category.{u, u}` for
`R : Type u`; the mixed-ring-universe natural isomorphism explicitly lifts the
original target by `ModuleCat.uliftFunctor`. It does not make all carriers
definitionally equal or enlarge that existing finite-projective source scope.
Triple coherence is a proved equality on literal tensor carriers; categorical
ULift bookkeeping is not separately packaged as a pseudofunctor-coherence
structure. The older `rightBaseChangeTensorIso` concerns direct sum and is a
different comparison.

[`Consumer.BalancedTensorBaseChange`](../../../../examples/downstream/Consumer/BalancedTensorBaseChange.lean)
checks the lifted naturality square, original composition and all-degree K-map
identification. [`Consumer.FiniteProjectiveBaseChangeUnitCoherence`](../../../../examples/downstream/Consumer/FiniteProjectiveBaseChangeUnitCoherence.lean)
checks the original identity/composition units.
