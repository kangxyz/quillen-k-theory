# Original scalar actions, products and signed boundaries

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.KTheory.LowDegreeScalarAction.IdentityAutomorphism` | Original K0-to-K1 and K1-to-K2 identity-natural-automorphism operations with both variable laws, actual track representatives and explicit consumer universes |
| `Quillen.KTheory.LowDegreeScalarAction.ScalarUnit`, `ExactNaturality` | Scalar-unit operations with both variable laws and actual original-KMap naturality, including SmallModels |
| `Quillen.KTheory.LowDegreeScalarAction.SerreBoundary` | Whole original Serre fiber/action square and signed connecting-map compatibility, including actual scalar-linear localization targets |
| `Quillen.KTheory.LowDegreeScalarAction.SmallModelBoundary` | Actual standard-model action transports and the original finite-module signed scalar-boundary formula |
| `Quillen.KTheory.LowDegreeScalarAction.ObjectClass` | Original object-class/cube calibration and upper field-module scalar determinant `(r^n)^-1`, including rank zero |
| `Quillen.KTheory.LowDegreeScalarAction.FieldSymbols`, `DvrSymbols` | Bilinear actual field unit products with tensor naturality; original localization/principal/fraction/local-DVR unit-unit boundary zero after explicit universe transport; the original all-field positive marking is supplied by Field.PositiveSymbolMarking |
| `Quillen.KTheory.LowDegreeScalarAction.UniverseNaturality` | Original universal-KMap operation/object naturality and canonical small-model universe transport of scalar actions and positive cubes, without linear instances on the models |
| `Quillen.KTheory.LowDegreeScalarAction.PrincipalUnitBoundary` | Original ordered unit/principal boundary equals the literal lower positive quotient scalar cube, for every Noetherian commutative ring at a regular element, including units and zero quotients |
| `Quillen.KTheory.LowDegreeScalarAction.DvrUnitBoundary` | Actual local-DVR ordered unit/uniformizer boundary equals the lower positive native residue cube; promotion and original determinant give the positive reduced unit, retaining canonical or supplied fraction fields and original restriction maps |

## Low-degree identity-automorphism operations

[`IdentityAutomorphism`](IdentityAutomorphism.lean)
defines original `E.K 0 →* E.K 1` and `E.K 1 →* E.K 2` operations for
`Aut (Id C)`. The group laws in both variables are proved, including identities.
The natural-automorphism laws use `C : Type (max u v)` and `Category.{v} C`,
covering native finite-module/projective categories and their upper SmallModel.
The actual Q-space action theorem supplies source additivity in degree zero.
Representative equations retain the original track-first cubes and their
degree-zero inverse relative to spatial-first normalization.
[`ScalarUnit`](ScalarUnit.lean)
instantiates these operations for actual scalar units and proves original-KMap
naturality, including chosen models without a linear-category instance.
[`ExactNaturality`](ExactNaturality.lean)
proves the whole normalized-Q homotopy square from ordinary componentwise
compatibility. The signed loop-shift and path-space boundary formulas are also
proved.
[`SerreBoundary`](SerreBoundary.lean)
proves the whole original Serre fiber/action square and the inverse-sign
connecting formula. Its
[`SmallModelBoundary`](SmallModelBoundary.lean)
transport gives the original finite-module scalar-boundary formula with no
model or formal-quotient linear instance.
[`ObjectClass`](ObjectClass.lean)
identifies the action on the original object class with `automorphismClass`,
hence the inverse positive cube. Its upper free rank-n field-module determinant
is `(r^n)^-1`, including rank zero.

The source-coordinate contraction formula in
[`SourceContractionBoundary`](../../Topology/HomotopyFiber/SourceContractionBoundary.lean)
and the whole cancellation prism in
[`NaturalTransformationLoopCancellation`](../../Topology/ClassifyingSpace/NaturalTransformationLoopCancellation.lean)
supply boundary geometry without assuming a calibration equation.
[`PrincipalRankOne`](../../Aglib/Algebra/Category/FGModuleCat/PrincipalRankOne.lean)
retains the literal multiplication/quotient maps and actual localized scalar
automorphism. Regularity supplies monicity; Noetherianity supplies the
categorical short-exact and conflation statements.
[`PrincipalObjectBoundary`](../../GTheory/FiniteModules/PrincipalObjectBoundary.lean)
now computes the original positive self-conflation cube boundary, including
zero cokernels. For a Noetherian commutative ring and regular `r`, the original
closed boundary of the actual localized rank-one cube is the original
quotient-ring rank-one object class, with positive sign.
[`UniverseNaturality`](UniverseNaturality.lean)
preserves actual scalar operations, object classes and positive cubes through
the original canonical model-universe comparison, with both smallness
hypotheses and no linear instances on the models.

[`FieldSymbols`](FieldSymbols.lean)
defines the original scalar-operation product on positive rank-one unit
classes and proves bilinearity and actual tensor-extension naturality.
[`DvrSymbols`](DvrSymbols.lean)
proves its unit-unit boundary is neutral for the original localization,
principal, fraction and local-DVR maps, explicitly lowering the upper model.
[`PrincipalUnitBoundary`](PrincipalUnitBoundary.lean)
computes the ordered unit/principal value: the original closed boundary of
the canonically lowered product is the literal lower positive rank-one
quotient scalar cube. The boundary inverse and object-class inverse cancel.
Only a Noetherian commutative ring and regular principal element are required;
units and the zero quotient are included.
[`DvrUnitBoundary`](DvrUnitBoundary.lean)
transports the ordered formula through the original local-DVR boundary square.
Its value is the positive lower native residue cube, and canonical promotion
followed by the original determinant gives the positive reduced unit. The
given-fraction-field version retains the exact original inverse restriction
map. The full marked Milnor comparison below supplies both ordered tame values.

## Same negative inverse and DVR boundaries

Import [MilnorNormalization](MilnorNormalization.lean). For a field `F : Type u`
with `CharZero F`, `milnorLowerModuleKTwoEquivCharZero` has the original upper
forward Milnor map followed by canonical same-category universe lowering.
`lowerModuleKTwoMilnorNegativeEquivCharZero` first promotes by that canonical
universe comparison and then applies the **same upper negative inverse**.
It equals minus the positive lower inverse and sends the original ordered lower
unit product to `-MilnorK.symbol ![a,b]`; the reversed ordered product has the
positive symbol value. Its inverse is minus the original lower forward map.

For a commutative Dedekind domain `R`, an actual height-one prime `p`,
`A = Localization.AtPrime p.asIdeal`, and its canonical fraction field `K`,
assume `CharZero K` and an irreducible uniformizer `π : A`. For every original
lower class `x : G K 2`, write `N(x)` for that same negative inverse.
`localDvrBoundary_raw_negativeNormalization` states that the **unchanged raw**
local boundary followed by the canonical original residue determinant is
`tame(-N(x))`. `localDvrBoundary_inverse_negativeNormalization` states that
its multiplicative inverse is `tame(N(x))`. The tame expression uses Aglib's
actual `MilnorK.twoEquiv` and the DVR data for the specified uniformizer.
The supplied-fraction-field versions retain its actual algebra and
`IsFractionRing` interface. These boundary statements require neither a residue
ring section nor `CharZero` on the residue field.

The raw ordered unit/uniformizer product has value the positive residue unit;
reversing the order inverts that value. Applying tame to `N` of the ordered
product gives the inverse residue unit. These are different normalizations of
the same actual maps; no sign is hidden by changing the unit product.

## Original affine unit-pair pullbacks

Import [SpecUnitPairNormalization](SpecUnitPairNormalization.lean). For a
Noetherian commutative ring `R`, a characteristic-zero field `L` in the same
universe and `f : R →+* L`, apply the original `Scheme.pullbackK` first and the
target's original `SpecUnitPairs.kToLowerG` second. The same lower normalization
has value `-MilnorK.symbol ![f(a),f(b)]` on the actual ordered scheme unit pair.
This concerns original K-pullback, not a nonflat coherent G-pullback.

The generic pullback for the actual local DVR has this formula for any given
characteristic-zero field algebra, including its canonical fraction field.
The **closed** pullback formula applies `N` to the residue field and therefore
explicitly requires `CharZero` of that residue field. This extra premise is
absent from the raw/inverse boundary determinant formulas above.

Unit-pair generation in [the DVR family](../../GTheory/DVR/README.md) still
requires an actual residue ring section. None of these normalizations asserts
generation for every nonsplit DVR or an arbitrary-DVR local Milnor presentation.

## Current normalization client

[Consumer.MilnorDvrNormalization](../../../examples/downstream/Consumer/MilnorDvrNormalization.lean)
checks the same `N` through canonical promotion, original raw boundaries,
integer Spec pullback and actual residue-section cancellation. The generic
boundary and the closed normalization retain their different hypotheses above.
