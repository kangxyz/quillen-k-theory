# Actual weak-cofibration comparison through Quillen A

## Exact categorical input

The original weak-arrow category is mathlib's `WideSubcategory weq`.
The original weak-cofibration category is `WideSubcategory (cof ⊓ weq)`.
The functor `TrivialCofibrations.inclusion cof weq` retains every original
object and underlying arrow literally. Multiplicativity supplies only the
actual category laws.

`CylinderData cof weq` records the actual middle functor, first inclusion,
projection and target inclusion. Its properties are the two literal
factorization/section identities, both endpoint cofibrations, weak projection,
and preservation of componentwise cofibration squares by the middle functor.
No contractibility, categorical equivalence, realization equivalence, or
fibration conclusion is an input. Coarse two-out-of-three derives weakness
of the first inclusion for a weak original arrow, of the second inclusion,
and of the middle map from its original right endpoint.

## Actual comma contraction

For a fixed original target Y, the comma category consists of original weak
arrows f:X→Y, with original weak-cofibration morphisms over Y. The original
middle projection T(f)→Y is again such an object. A comma morphism is sent
to the actual middle map of its original square (a,identity). Its cofibration
property follows from genuine middle-square preservation; its weak property
follows from the original weak projections and two-out-of-three.

The actual first and second endpoints give genuine comma natural maps
identity→T and constant(Y,id)→T. Their equations are precisely the two
recorded, and concretely proved, cylinder identities. The original endpoint
maps remain visible in the API. Realizing those two natural transformations
gives an actual contraction to the original identity-arrow vertex.

The existing proved Quillen-A theorem then gives
`inclusionClassifyingHomotopyEquiv`. Its forward map is exactly the original
inclusion's classifying-space map. The algebraic construction and comma
contraction allow independent object/hom universes. The Quillen-A endpoint
retains the existing implementation's common-universe `SmallCategory` scope.

## Genuine complex-row input

`Rows/TrivialCofibrationCylinder.lean` supplies the structural data from the
proved joint-cylinder factorization and proved second-endpoint section on
actual quotient rows. Its middle preserves genuine row cofibrations because
the original joint middle functor is exact on pointwise arrow cofibrations.
The complex instance retains all original identity-cone/biproduct maps.
Its target-section identity is proved directly, rather than inferred from
`JointData`, which only records the first endpoint identity.

## Mixed-model boundary

This comparison is intended to be applied after fixing the fine nerve degree:
objects are the actual fine-weak chains; horizontal maps are pointwise coarse
weak transformations, with the smaller class also pointwise cofibrations.
The separate exact transpose/model-identification and pointwise cylinder-lift
modules must prove that these are the original mixed nerves. The categorical
comparison does not pretend that the coarse cylinder projection is a fine
natural transformation, nor assert a diagonal fibration by itself.

## Verification

All four defining sources passed focused serial Lean checks warning-free.
The complete84-origin recursive audit (39 + 27 + 13 + 5) and18 actual-map
consumers also passed warning-free, with only the standard three axioms.
The driver is `audits/TrivialCofibrationComparisonAudit.lean`; its fixed84
guard was independently confirmed. The ordered frozen source
manifest is `logs/trivial-cofibration-comparison-sources.sha256`. Independent
review accepted all four fresh sources, fixed84 origins and22 strengthened
consumers warning-free, including full source/artifact/toolchain rehash.
No production source changed during review.
