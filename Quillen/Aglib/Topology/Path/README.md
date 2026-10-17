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
| [EvaluationFactorExtraction](EvaluationFactorExtraction.lean) | Recover the two evaluated factors of a prescribed concatenation and undo a reversal. |
| [HomotopyEvaluationTrans](HomotopyEvaluationTrans.lean) | Compare literal homotopy concatenations under two pointwise evaluation functions. |
| [HomotopyPathSlice](HomotopyPathSlice.lean) | Evaluate a homotopy slice through a given function while preserving path concatenation and reversal. |
| [MappedProjectionRectangle](MappedProjectionRectangle.lean) | Map a supplied projection rectangle, retaining its boundary paths and interior parameters. |
| [RetypedUnitComparison](RetypedUnitComparison.lean) | Transport a supplied unit comparison along specified whole movement paths, preserving its values. |
| [TwoSheetConjugation](TwoSheetConjugation.lean) | Construct the specified conjugation comparison with separately retained endpoints and whole boundary paths. |

These candidates carry no assertion of upstream acceptance or of the geometric
Bass coherence supplied by their Quillen consumers.
