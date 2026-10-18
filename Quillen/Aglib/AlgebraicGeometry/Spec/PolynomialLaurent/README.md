# Polynomial and Laurent spectrum geometry

These leaves extend the native polynomial/Laurent spectrum interfaces while
retaining their actual ring maps, coefficient squares, coordinates and units.
`CoefficientSquares` gives the literal polynomial/Laurent coefficient pullbacks
and their two overlap squares. `OriginalCoordinate` retains the original
polynomial coordinate and Laurent restriction formulas. `AffinePlane` gives
the actual polynomial fiber square, its iterated-polynomial Spec isomorphism,
and both section coordinates. `AffineDiagonal`, `LaurentHyperbola`, and
`OppositeMixedEvaluation` retain the evaluation maps, actual kernels,
surjectivity and induced closed immersions over an arbitrary commutative ring.

`NaturalDiagram` retains polynomial/Laurent natural diagrams in the opposite
category of quasi-compact schemes. `UnitImage` records the original unit-image
identities; `Flat` retains coefficient flatness. `OpenPairs` and
`OpenPairZeroSection` retain arbitrary open-pair product geometry and its actual
zero-section interfaces. `ZeroSection` retains genuine zero-section projection
triangles. Their original additional hypotheses remain at the declarations.

`OpenPairInterchange` lifts the literal independent-variable swap to both entries
of the original open pair. It preserves the actual product projection and maps
of either fixed factor, hence both polynomial/Laurent charts. Only the ambient
entry is required compact; the fixed product legs are quasi-compact. Its current
consumer is the original supported Bass product-contraction transport.

`NativeCoordinates` gives the actual relative polynomial and Laurent schemes
over an arbitrary base scheme, the positive Laurent open immersion, and the
second-projection coordinate and Laurent unit. The coordinate pulls back to
the same forward unit; no quasi-compactness assumption is introduced.

[IndexSquare](IndexSquare.lean) forms the positive/inverse-chart square as
a genuine functor on all schemes in the opposite category. The common corner
is the actual scheme, and the two polynomial charts map to the original
Laurent corner. Independent products over the integer base give its
four-corner interchange isomorphism. The common-corner component is identity;
the other components retain the specified opposite swaps.
[IndexSquareFactor](IndexSquareFactor.lean) proves its projection and
positive/inverse factor-map equations. No compactness or quasi-separatedness
is required. The native `AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex`
namespace records these constructions; finite Bass cone and seed consumers
remain downstream.

Historic declaration namespaces are preserved. The actual projective-line
chart assembly, tautological and diagonal endpoints, and K/Bass model assembly
remain downstream.
