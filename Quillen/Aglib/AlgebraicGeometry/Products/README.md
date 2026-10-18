# Independent scheme products over the integer base

These general candidates retain the original left-nested pullback objects
and arbitrary fixed structure maps to the integer base. Their declarations
use the native namespace `AlgebraicGeometry.Scheme.Products`, except for
the coefficient-row interfaces below. They require
neither compactness nor quasi-separatedness.

[IntegerBaseSwapUnits](IntegerBaseSwapUnits.lean) gives the actual scalar-unit
pullback formulas under either independent-factor swap and composition.
[IntegerBaseBraid](IntegerBaseBraid.lean) identifies the two literal three-swap
words on three factors. Both results use the specified product maps rather
than an implicitly associated or reordered product.

[IntegerBaseExternalFactor](IntegerBaseExternalFactor.lean) moves an external factor past
two internal factors. Its projection equation and swap square retain the
actual inverse two-swap transport and the reversed direction in the opposite
category. [IntegerBaseExternalTrack](IntegerBaseExternalTrack.lean) transports a genuine
natural transformation, and hence time slices of a natural homotopy, through
this square. That natural transformation is an input; the transport theorem
does not construct a specific scalar homotopy or independent two-time scalar
commutation law.

The current consumers are independent Laurent variables and the finite
double-cone Bass interchange. These product and external-track equations do
not themselves identify an externally chosen unit action on that cone
permutation. The arbitrary-scheme polynomial/Laurent index square is described
in the [adjacent family guide](../Spec/PolynomialLaurent/README.md).

[IntegerBaseCoefficientRow](IntegerBaseCoefficientRow.lean) compares the actual
coefficient fiber with the parameter-first product over
`Spec (CommRingCat.of (ULift.{u} ℤ))`. In the native namespace
`AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow`, `rowIso`
preserves both original projections and is natural in the fixed scheme and
coefficient algebra. `identityIso` identifies the identity-algebra product
with the fixed scheme by its actual second projection. The inputs are an
arbitrary scheme over this integer base and an arbitrary coefficient algebra
under its ring; no compactness or quasi-separatedness is required. The
intended upstream module is
`Aglib.AlgebraicGeometry.Products.IntegerBaseCoefficientRow`.

Its general row consumer is
[IntegerBaseParameterRow](../Spec/PolynomialLaurent/IntegerBaseParameterRow.lean).
The host
[GlobalParameterIdentityModels](../../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalParameterIdentityModels.lean)
uses the original projection to identify ambient and supported Models at the
integer parameter. Model, scalar-seed and localization conclusions remain in
that application.
