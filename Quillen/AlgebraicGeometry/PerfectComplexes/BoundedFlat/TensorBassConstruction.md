# Tensor-rooted Bass construction and localization

The chosen model directly realizes the represented **left-[T]** Bass construction
of TT §§6.3–6.4 and proves the basic and auxiliary localization statements of
TT 7.4. The actual canonical homotopy-fiber lifts are stable equivalences under
the hypotheses below. This construction identification concerns the underlying
spectra, operations and null diagrams; a full multiplicative module API is
additional work.

The earlier `FineBassK.md` correction concerned the earlier facade alone. Its
historical conclusion was appropriate to that scope: Bass stability and group
comparisons did not by themselves identify the construction. The additional
results here certify the actual tensor input and its generated finite recursion;
they do not retroactively change the earlier proof or its evidence.

## Independent input

`ParameterTensorEvaluationRow.firstRow` is actual pullback followed by tensoring
with the rank-one unit row. `ParameterTensorCell.tensorCellCylinder`,
`tensorCellRealization`, and `tensorCell_succ/zero` expose its independent
realization, including the separate row, unit-action, and old-loop times.
The scalar is the actual `ParameterLaurentUnit.projectedLaurentScalar`, with the
forward T automorphism, not its inverse.

Module `ReturnedTensorFamily`: declaration
`ReturnedTensorConeRecognition.tensorFamily` uses the actual returned tensor Model,
evaluation inverse, unit and unitor comparison. Its naturality is proved.
Module `ReturnedTensorGenerators`: declaration
`ReturnedTensorConeRecognition.tensorFamilyReturnedPasting` retains the complete
tensor/evaluation prism. `coefficient_class` identifies that same scalar's
forward K1 class; it does not replace the all-input realization with group data.

## Independent recipe and uniform recursion

The generic declarations are in `Quillen.KTheory.Bass`:

- `ConeGeneratorRecognition`: `ConeGeneratorLaw` prescribes the target
  inclusion, upper/lower cone cylinders and overlap cylinder using only the four
  input cells and independent coordinates. Quotient elimination proves existence
  and uniqueness of the extension.
- Module `GeneratedTensorStep`: declaration
  `TensorGeneratedRecipe.GeneratorStep`: any extension satisfying those laws,
  followed by the fixed geometric index map, row strength, parameter looping and
  explicit loop/row inverse. It fixes all levels and actual successor endpoints;
  its definition does not refer to `iterateFamily` or a desired Track equality.
- Module `GeneratedTensorTrace`: declaration
  `TensorGeneratedRecipe.GeneratedTrace`: zero is typed cell identity;
  successor chooses a genuine next family with `GeneratorStep` and a residual
  trace on the transformed diagram.
- Module `GeneratedTensorTraceProof`: declaration
  `TensorGeneratedRecipe.iterateFamily_generated`: uniform induction in
  the initial diagram and all dependent row/family data constructs this trace.
  The successor invokes the induction hypothesis on BF with the actual step
  family and its proved properties, not merely on the original stage-zero data.

Module `ReturnedTensorGeneratedTrace`: declaration
`ReturnedTensorConeRecognition.tensor_generated_trace Q i` supplies the actual
scheme, tensor base, row and index data and targets the original
`strictifiedIteratedCell Q i`. No recognition certificate, trace or desired
comparison is a hypothesis. This is the formal generated-recipe witness.

`ReturnedTensorRecursiveRecognition` and `ReturnedTensorRecursiveCoordinates`
retain the actual left recursion, first-step level map, four-generator successor
uniqueness and positive/zero coordinate laws. They do not assert that differently
associated row transports are definitionally equal.

## Forward boundary and Omega-Sigma convention

The independently normalized tensor cell is followed by the original Laurent
cone boundary. `tensorStageBoundaryCurrentHomotopy` is a whole spectrum
homotopy to the current transition followed by the specified backward leg.
`ModelDiagramRowStabilizedTarget.unit_refinement` proves the exact suspension
unit/counit triangle; `ModelRowZigzagSequentialization.backward_eq` retains the
successor-object transport and looped row comparison. Its `backward_stable`
proves the actual stable equivalence. Thus the current system is recognized
through this specified roof, not a literal equality of operations. No sign is
inferred from a group-level boundary formula.

## Support, maps, canonical null and localization

Supported tensor rows and their exact evaluation return are constructed inside
the actual supported full subcategory. The supported forget rectangle and the
six basic/auxiliary normalized action compatibilities are already proved in
`ParameterTensorSupportedForgetRectangle` and `ParameterTensorPresentationActions`.
The forward's cone-source null and the localization acyclic support-to-open null
are distinct; the latter is preserved at every null time.

The existing spectrum-level, whole-null comparison is
current -> cone-normalized -> twisted <- iterated seed -> fine.
It is not a direct equality of current and fine towers, nor an arbitrary choice
of stable inverse. `ParameterFullFiberComparison`,
`ParameterIteratedTwistedFiber`, and `ParameterIteratedFullFiber` prove the basic
comparison; the auxiliary owners prove its supported counterpart.

Final exact entries:

- `ParameterFullCurrentNull.currentLift_integer_isStableEquivalence` in
  `ParameterCurrentFullFiber.lean`: an open immersion f:P->Q, compact P and Q,
  and quasi-separated Q.
- `ParameterAuxiliaryCurrentFiber.currentLift_integer_isStableEquivalence` in
  `ParameterAuxiliaryCurrentLocalization.lean`: the same hypotheses and an
  auxiliary open T in Q with `CompactSpace T`. The original closed-support
  intersection and its specified canonical null are retained.

These are stable equivalences of the specified homotopy-fiber lifts in every
signed degree, not levelwise homotopy equivalences. No affine or noetherian
hypothesis is introduced. `QuillenTest.TensorBassConstruction` and the downstream
consumer check the generated trace and these actual endpoints together.
The generic `LoopPrespectrum.stableFiberLongExactSequence` supplies the signed
connecting maps and exactness in every integer degree. The two fiber
identifications therefore give the long exact sequences of TT 7.4 as well.

## Scope of the TT 7.4 interpretation

The generator laws, transformed-diagram induction and specified stable roof
recognize the displayed represented tensor recipe of TT 6.3–6.4. Together with
the original-null fiber lifts above, they give basic and auxiliary localization
for this realization under the hypotheses of TT 7.4. This directly proves that
theorem's two localization statements. TT 6.4 permits equivalent homotopy-colimit
presentations, so this route does not require first choosing another point-set
tower and constructing a comparison to it. The source and exact
theorem locator are in the [comparison guide](../Development.md#classical-target-and-source).

The [prescribed raw implementation](../Development.md#comparison-with-the-prescribed-raw-point-set-implementation)
is a separate comparison target. A natural stable comparison to that tower,
its forward transitions, its entire canonical null and the required original
class/boundary conventions has not been constructed here. The generated trace
is a generation witness for the actual input family; it does not assert
uniqueness among arbitrary external towers or a full multiplicative module API.
Those separate goals do not qualify the TT 7.4 localization result above.

The [integration record](../../../../docs/evidence/TTTensorConstruction20261021.json)
keeps source, independent review and executable validation distinct.
