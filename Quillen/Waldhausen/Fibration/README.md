# Fibration interfaces

## Fibration and its connective tail

[`Fibration.NestedWeakEquivalences W`](AcyclicSubcategory.lean)
specifies a coarse structure with the same cofibrations and chosen zero as `W`,
with `W.weq ≤ N.coarse.weq`. Its acyclic objects have a coarse-weak zero-to-object
map; their subcategory retains the fine weak class. `changeWeak_exact N` changes
only the weak class.

[`canonicalFiberMap N`](CanonicalFiberMap.lean)
maps the acyclic S-delooping into the homotopy fiber of `changeWeakMap N`. Its
projection is the actual inclusion and its path is the reversed zero-to-inclusion
homotopy; construction does not assert a weak equivalence.

`canonicalFiberMap_isWeakHomotopyEquivalence_general` requires coarse two-out-of-three,
`he : Fibration.ExtensionAxiom N.coarse`, `D : Fibration.RowFactorization.JointData N`,
and `hs : Fibration.RowFactorization.SecondEndpointSection N D`.
The [extension axiom](WeakEquivalenceCofiber.lean)
says weak source and quotient maps in a map of cofiber squares imply a weak middle map.
The [section condition](Rows/SecondEndpoint.lean)
says the second injection followed by the joint cofibration and projection is the
target identity. This is additional to `JointData`. The theorem retains the original
map and full path for independent object and morphism universes.

Given a proof `h` that the original comparison is weak,
[`Fibration.LongExactSequence`](LongExactSequence.lean)
defines `changeWeakConnectingHom N h n : N.coarse.K (n + 1) →* (acyclicStructure N).K n`
by the homotopy-fiber boundary, with all recurring range/kernel equalities for the
original K-maps. `changeWeak_KMap_zero_surjective_of_weak` gives surjectivity onto
`N.coarse.K 0` by the pointed-set tail and connected acyclic S-space. Positive
surjectivity separately requires injectivity of the preceding acyclic-inclusion
map. The sequence supplies no negative boundary.

## Prescribed loop-fiber normalization

For nested structures `N`, an object `A`, and `[HasZeroMorphisms C]`,
[`Fibration.canonicalFiberComponentEquiv N A`](CanonicalFiberComponentTranslation.lean)
is a homotopy equivalence between fibers of the original localization loop map,
from the fiber over the constant loop to the fiber over `N.coarse.kZeroObjectLoop A`.
It uses the original loop/fiber transpose, left concatenation by the fine object
loop, and the actual identity-cofiber suffix path. `canonicalFiberComponentEquiv_object`
gives exactly the prescribed translation of the transposed object-loop point for
each `X : Fibration.AcyclicCategory N`.
The [fiber-square formula](CanonicalFiberObjectSquare.lean)
reverses the zero-to-acyclic nerve time and retains the original object-loop time.

[`Structure.identityCofiberComponentEquiv_eq`](IdentityCofiberNormalization.lean)
identifies the induced first homotopy-group normalization of the loop space with
the standard left-component normalization. It does not identify the entire
identity-cofiber and suffix-removal paths. The separate fibration theorem still
retains its hypotheses above. Scalar-boundary applications and their geometric
comparison questions are in [perfect-complex guide](../../AlgebraicGeometry/PerfectComplexes/README.md).

## Spectrum comparison hypotheses

The fibration spectrum comparison retains coarse two-out-of-three,
`ExtensionAxiom`, the actual `JointData` and `SecondEndpointSection`.
Its endpoint supplies original K0 surjectivity. These data are not inferred
from a generic prespectrum fiber sequence; the
[prespectrum family](../../Topology/Prespectrum/README.md) owns that lower
stable topology.

## Original boundary and signed stable boundary

[LevelOneConnectingComparison](LevelOneConnectingComparison.lean) keeps the
original based fiber homeomorphism, canonical fiber map and geometric
connecting homomorphism at level one. Its square retains the complete
original acyclic null.

[StableConnectingComparison](StableConnectingComparison.lean) compares
`changeWeakConnectingHom` with the existing signed `stableFiberConnecting`
through `originalKStableEquiv`. The square has one explicit minus: the
original K-equivalence uses the structure map from level one to its first
stable stage. `originalKStableEquiv_connecting_sign` and its homomorphism
square retain the original canonical comparison and the degree cast
`((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1`.
`originalKStableEquiv_liftConnecting_sign` gives the same convention for
`stableFiberLiftConnecting` of the original arrows and specified null.

The statements include K₁ to K₀. They assume weakness of the original
canonical fiber map; an application may discharge that premise by the
fibration theorem above with its actual joint data and second-endpoint
section. The [perfect-complex boundary guide](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GeometricBoundary.md)
constructs its evaluation and whole-null comparisons before applying this
sign formula. These conventions do not identify a classical nonconnective
boundary.
