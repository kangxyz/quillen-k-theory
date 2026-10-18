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

The integral Spec-row interfaces retain the original coefficient algebra,
fixed scheme, projections and forward Laurent unit. Their hypotheses are
arbitrary objects over `Spec (CommRingCat.of (ULift.{u} ℤ))` and under
`CommRingCat.of (ULift.{u} ℤ)`, with their original morphisms; none adds
compactness or quasi-separatedness.

| Focused leaf | Native interface and result |
| --- | --- |
| [IntegerBaseSpecSquare](IntegerBaseSpecSquare.lean) | `AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec.specUnder`, `specSquareIso` and `specSquare` compare all four affine corners and both charts naturally; `nativeLaurentUnit_spec` preserves the original Laurent unit. |
| [IntegerBaseParameterRow](IntegerBaseParameterRow.lean) | `AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow.parameterRowIso` compares parameter-first products with the actual coefficient row; `parameterRowIso_scheme` and `rowIso_unit` retain scheme restriction and every global coefficient unit. |
| [IntegerBaseCanonicalRow](IntegerBaseCanonicalRow.lean) | `canonicalRowIso` and `canonicalParameterRowIso` use the literal canonical integer structure map, preserving both projections, coefficient/scheme arrows and arbitrary coefficient units. |
| [IntegerBaseLaurentParameter](IntegerBaseLaurentParameter.lean) | `laurentParameterIso` retains the whole Laurent fiber and parameter projection; `laurentParameterIso_unit` preserves the original coefficient `T` unit. |
| [IntegerBaseLaurentCoefficient](IntegerBaseLaurentCoefficient.lean) | `laurentParameterIso_coefficient` proves the complete original Laurent-projection square on the fixed-factor product. |

Each intended upstream module has the same mathematical suffix under
`Aglib.AlgebraicGeometry.Spec.PolynomialLaurent`. The product-row prerequisite
has its [own family owner](../../Products/README.md). The current application
consumers are the original global ambient/supported coefficient Models and
parameter Laurent tracks, beginning at
[GlobalParameterCoefficientModels](../../../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterCoefficientModels.lean).
Their finite Bass and localization comparisons remain downstream.

Historic declaration namespaces are preserved. The actual projective-line
chart assembly, tautological and diagonal endpoints, and K/Bass model assembly
remain downstream.
