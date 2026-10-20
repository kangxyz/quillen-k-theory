# Row presentations and tensor comparisons

Row refinement gives a common target for independently constructed operations
without selecting an inverse to the row comparison. This family keeps the
forward cone and loop strengths, finite Model topology, input maps and whole
null homotopies. The [Bass guide](README.md) owns the finite Bass functor and
current/iterated-seed telescopes. The applications below use actual
`Scheme.{u}ᵒᵖ ⥤ Model.{u+1}` diagrams and specified Laurent tracks; a
generic presentation theorem does not construct those inputs.

## Refinement through cones, loops and Bass steps

[ModelDiagramRowRefinementNaturality](ModelDiagramRowRefinementNaturality.lean)
assembles the finite row comparisons into their original diagrams.
[DiagramConeRowStrength](DiagramConeRowStrength.lean) and
[DiagramConeRowStrengthHomotopy](DiagramConeRowStrengthHomotopy.lean) construct
the forward map from the cone of a refined row to the refinement of its
original cone. The quotient generators, source null and homotopy clocks are
retained, and the comparison triangle uses the original row map.
[DiagramBassRowStrength](DiagramBassRowStrength.lean) combines this map with
the explicit loop/row coordinate isomorphism, including the zero-level
coordinates. This construction does not require or assert stability of the
strength map.

[ModelDiagramRowStabilizedTarget](ModelDiagramRowStabilizedTarget.lean) uses
parameter looping of that computed cone refinement as its target. The
suspension counit followed by the original row comparison is stable, and its
unit triangle retains the successor transport. The zero space has three loop
coordinates; positive spaces have two. Separation, point HEP and finite
growth are proved on these actual spaces.

[DiagramRowInputNaturality](DiagramRowInputNaturality.lean) propagates a
supplied equivariant input transformation through spans, cones, loops and
finite iteration. [ModelDiagramRowInputNaturality](ModelDiagramRowInputNaturality.lean)
discharges that premise from genuine Model row naturality.
`ModelDiagramRowTargetInputNaturality` retains the actual counit/refinement
input square. These statements concern an input transformation as well as
coefficient-scheme naturality. The identity and composition owners keep their
original transports.

## Zigzags, sequentialization and ordinary colimits

A row presentation uses actual vertices `E_i`, targets `V_i` and legs

```text
E_i → V_i ← E_(i+1).
```

The sequentialization forms its stages from those specified legs. The
`ZigzagSequentialization` and `ZigzagSequentializationColimit` prespectrum
owners retain the resulting inclusions and cylinders and compare the
sequential construction with its ordinary-colimit presentation.
[ModelRowZigzagSequentialization](ModelRowZigzagSequentialization.lean)
discharges finite-growth and excision assumptions for the proper row targets.
Its `targetReplacementMap_stable` postcomposes both original legs with the
actual target replacement; `telescopeMap_stable` additionally requires a
whole factorization of the supplied forward leg through the original
current transition.

[SchemeTrackSequentialPresentation](SchemeTrackSequentialPresentation.lean)
applies this machinery to a strict Model diagram `M` and a specified track
`A`. The `Comparison`, `ComparisonStable`, `Initial` and `FiniteMap` owners
keep the actual current-telescope comparison and initial/finite inclusions.
`SchemeTrackSequentialInput`, `InputLaws` and `Diagram` retain actual input
maps; `Null`, `DiagramNull`, `NullTransport` and `LiftTransport` preserve
every time slice of a supplied equivariant null and its path-space lift.
`SchemeTrackSequentialTransport` and `ProofChoice` retain the stated track
equalities. These are interfaces for the chosen strict `M` and `A`, with
their stated factorization and null inputs.

## Tensor evaluation and the independent initial cell

The perfect-complex application begins with genuine tensor maps rather than
defining a cell by the desired telescope comparison.
[ParameterTensorEvaluationRow](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorEvaluationRow.lean),
`ParameterTensorModelComparison` and `ParameterTensorModelUnit` retain the
parameter coefficient map, actual tensor row, both chosen-zero
normalizations, and evaluation/unitor isomorphism. The unit square is proved
from these maps. `ParameterTensorRowPasting` supplies the complete
endpoint-relative first-S prism.

[ParameterTensorCell](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorCell.lean)
starts with the independently constructed tensor double cylinder. Its
realization retains row time, unit time and the level-zero input-loop
coordinate. `ParameterTensorInitialCell` compares it with the internal
ambient initial cell through original evaluation.
`ParameterTensorSupportedInitialCell` supplies the supported bridge from
the actual supported tensor/evaluation row. Its forgetful comparison uses
`TensorUnitSupportedCoefficientForget`; no injectivity of ambient support
forgetting is needed.

[ParameterTensorFirstBassCell](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorFirstBassCell.lean)
builds the first ambient Bass cell from the four initial corner cells, then
applies the cone index map, forward row strength and loop/row isomorphism.
The comparison is with the entire original first-Bass track after the row
comparison, with scheme-arrow naturality and both zero-level row coordinates.
`ParameterTensorIteratedCell` and `ParameterTensorSupportedIteratedCell`
iterate the original cone and parameter-loop operations before proving
equality with the original stage cells.

## Returned tensor action and the forward operation

[ParameterTensorReturnedForward](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedForward.lean)
defines `returnedNormalizedCupBoundary` by inverse-prefix normalization of
the actual returned first-S tensor cell, followed by the original Laurent
cone inclusion. `returnedNormalizedCupBoundaryHomotopy` compares this
operation with the independently normalized internal cell.
`returnedNormalizedForwardHomotopy` then compares it with
`SchemeModelRowSeed.forward` at stage zero. The supported construction is
in `ParameterTensorSupportedReturnedForward` and uses its own tensor row
and null.

[ParameterTensorReturnedStrictification](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedStrictification.lean)
and `ParameterTensorSupportedReturnedStrictification` first conjugate the
actual returned multiplication by the specified evaluation/unit/unitor
isomorphism, then apply the unchanged Bass recursion. Their
`strictifiedIteratedCell_eq` and `strictifiedNormalizedForward_eq` identify
the resulting cell and normalized forward at every finite stage.

The geometric input squares retain independent content.
`ParameterTensorRawInput` constructs the tensor square on the actual
parameter products and proves preservation of forward Laurent multiplication.
`ParameterTensorModelInputSquare` and `ParameterTensorReturnedInputSquare`
compare the Model and returned routes under genuine evaluation, with the
complete return-counit conjugation word.
`ParameterTensorSupportedInputRectangle` gives the corresponding supported
rectangle for every parameter arrow from the original product-pair square.
These source locators distinguish the actual evaluated tensor square from
ordinary naturality of a chosen strict Model map.

The concrete application supplies this action through all finite stages.
[ReturnedTensorGenerators](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ReturnedTensorGenerators.lean)
characterizes the actual inherited cone action on its four quotient generators.
`ReturnedTensorConeRecognition.tensorStageBoundaryCurrentHomotopy` in the
[module](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ReturnedTensorRecursiveRecognition.lean)
retains the whole tensor-action/boundary comparison at every stage.
[ReturnedTensorGeneratedTrace](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ReturnedTensorGeneratedTrace.lean)
instantiates the uniform generated recursion with the actual tensor family;
its declaration namespace is `Quillen.PerfectComplexes.ReturnedTensorConeRecognition`.
These data, the specified stable roof, and the support maps and whole
acyclicity null directly realize TT §§6.3–6.4 and prove original Theorem 7.4
for qcqs `X`, quasi-compact `U`, and auxiliary support with quasi-compact
complement, in every integer degree. The
[tensor Bass guide](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorBassConstruction.md)
records that realization. A full multiplicative API and comparison with
another prescribed raw point-set tower remain separate targets.

## Ambient, supported and auxiliary presentations

[ParameterTensorRowPresentation](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorRowPresentation.lean)
uses the independent tensor cells, original Laurent inclusion and whole
source null. `ParameterTensorNormalizedRowPresentation` uses the independently
normalized cell followed by the original boundary. Each has actual ambient
and supported current-telescope comparisons, stable at every scheme
parameter. The supported construction retains its open-immersion hypothesis.

[ParameterTensorPresentation](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorPresentation.lean)
and its `Diagram`, `Actions` and `ComparisonChoice` owners construct the
ordinary-colimit ambient and supported diagrams. Their comparison begins
at the actual current telescope, using the proved whole track equalities.
`ParameterTensorPresentationLocalization` defines `basicForget`,
`basicRestriction`, `basicNull` and their own `basicLift`.
`basicNull_comparison` preserves the original full-open null at exactly the
same time. For an open immersion `f : P ⟶ Q`, `basicLift` at the integer
parameter is stable when `P` and `Q` are compact and `Q` is quasi-separated.
Its projection is exactly `basicForget`.

For auxiliary `T : Q.Opens`, `ParameterAuxiliaryRowPresentation` and
`ParameterAuxiliaryNormalizedRowPresentation` retain the three supported
Models for the union open, `T`, and its inverse image in `P`. Their actual
enlargement and restriction squares compare all three current objects with
the corresponding presentations. The `RowPresentationNull` and
`NormalizedRowPresentationNull` owners descend the original finite nulls
along both forward and backward legs. Their cylinder formulas retain
independent telescope height and null time; their comparison equations keep
every value of the prescribed current null.

`ParameterAuxiliaryRowLocalization` and
[ParameterAuxiliaryNormalizedRowLocalization](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowLocalization.lean)
form the path-space lifts from those actual maps and nulls. Their whole
three-object squares give equivalence of stability with the original
current lift. At the integer parameter, and at the stated affine coefficient
parameters, stability requires the original open immersion, compact `P`,
`Q`, `T`, and quasi-separated `Q`. It holds in every signed degree. Original
negative classes and the positive geometric boundary, with its explicit
minus sign, are separate identified consumers in
[geometric connecting maps](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GeometricBoundary.md).

The source families describe these constructions and their hypotheses.
Their source and validation records belong to the
[global evidence registry](../../../docs/evidence/README.md#tt-source-and-validation-records).
