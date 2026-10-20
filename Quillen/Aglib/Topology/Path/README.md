# Path and homotopy candidates

These Mathlib-only helpers are intended for the corresponding
`Aglib.Topology.Path` modules. They keep native `Path` and `ContinuousMap`
namespaces and are temporarily imported through the focused leaves below
`Quillen.Aglib.Topology.Path`.
Their current consumers are the original coefficient Bass mixed routes,
carrier seams and seed comparison.

The ambient spaces need only their stated topologies. The pointwise evaluation
lemmas allow arbitrary functions; a continuous map is required where a path or
homotopy is actually mapped. Supplied path identities and homotopies remain
explicit inputs. The lemmas preserve the specified half-time concatenations,
reversals and endpoint casts.

| Module | Interface and mathematical use |
| --- | --- |
| [CarrierHalfPaths](CarrierHalfPaths.lean) | Reconstruct a continuous path from its two literal half slices, including the midpoint. |
| [EvaluationOperations](EvaluationOperations.lean) | Preserve arbitrary pointwise evaluation through literal path operations, homotopy pasting and the associator, with independent clocks. |
| [EvaluationFactorExtraction](EvaluationFactorExtraction.lean) | Recover the two evaluated factors of a prescribed concatenation and undo a reversal. |
| [HomotopyEvaluationTrans](HomotopyEvaluationTrans.lean) | Compare literal homotopy concatenations under two pointwise evaluation functions. |
| [HomotopyPathSlice](HomotopyPathSlice.lean) | Evaluate a homotopy slice through a given function while preserving path concatenation and reversal. |
| [MappedProjectionRectangle](MappedProjectionRectangle.lean) | Map a supplied projection rectangle, retaining its boundary paths and interior parameters. |
| [RetypedUnitComparison](RetypedUnitComparison.lean) | Transport a supplied unit comparison along specified whole movement paths, preserving its values. |
| [SpanReassociation](SpanReassociation.lean) | Reassociate the prescribed five paths through three literal associator stages with unchanged clocks. |
| [SpanReassociationNaturality](SpanReassociationNaturality.lean) | Recover those three evaluated stages from equality of their complete five-path target words. |
| [ThreeRadialSquares](ThreeRadialSquares.lean) | Paste three supplied radial squares into the literal two-piece comparison word, retaining all endpoint parentheses and half clocks. |
| [TwoSheetConjugation](TwoSheetConjugation.lean) | Construct the specified conjugation comparison with separately retained endpoints and whole boundary paths. |

`EvaluationOperations` owns the unchanged public operations
`Path.Evaluation.path_trans`, `path_symm`, `comparison_symm`, `comparison_trans`,
`comparison_hcomp`, and `transAssoc`. Their hypotheses allow an arbitrary evaluation
function; their statements retain the original half cuts and independent comparison
and path times. `NullWordEvaluation` remains the specialized straightening and
pasted-null word consumer and publicly imports this shared leaf. The five-path
`SpanReassociationNaturality` uses the same operations rather than private copies.

These candidates carry no assertion of upstream acceptance or of the geometric
Bass coherence supplied by their Quillen consumers.

`ThreeRadialSquaresEvaluation` preserves the complete original `ThreeRadialSquares.paste`
under an arbitrary evaluator satisfying its ten path and three whole-square equations.
It reuses `EvaluationOperations`; the polynomial cap Laurent-bottom recovery is its
application consumer. All reassociation, cancellation and endpoint-cast clocks remain literal.

`AssociatorEvaluationComparison` compares two evaluations of the exact three-path
associator from pointwise equality on each complete path. The target evaluation is
continuous; the source evaluation is arbitrary. Its current consumer is the original
carrier-square correction descent, which remains outside the candidate subtree.
