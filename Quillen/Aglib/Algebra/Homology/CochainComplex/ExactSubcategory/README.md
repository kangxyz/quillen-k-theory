# Bounded complexes in exact full subcategories

These leaves retain actual integer-indexed cochain complexes in an abelian
category, strict term bounds, bounded termwise and bounded acyclic object
properties, and their inherited exact structures. Zero/repleteness and
extension hypotheses are retained where those structures need them.

`AcyclicCycles`, `CyclesExact`, and `CycleEvaluationSequence` use native cycle
objects and their actual short exact maps. Kernel closure is required for
cycle membership and the smart-truncation constructions. `TruncationMaps`,
`AcyclicTruncation`, `TruncationFunctor`, `TruncationExact`, `QuotientExact`,
`TruncationTransformations`, `TruncationCoherence`, and `AdjacentTruncation`
retain the canonical smart truncations, natural maps, actual cokernel boundary,
and exactness. `IdentityDisk` and `TruncationLayer` retain the original two-term
disks and actual layer comparisons.

`BoundedStrata`, `FixedBounds`, `FiniteCycleBounds`, `FiniteCycleFiltration`, and
`FiniteCycleEvaluation` preserve explicit term intervals and their cycle/disk
functors. The corresponding `StupidTruncation*`, `BoundedTermsStrata`, and
`FiniteTerm*` leaves retain brutal truncations and single-term layers; these do
not require kernel closure or claim preservation of quasi-isomorphisms.
`SingleInsertion` and `BoundedTermsAcyclic` retain ordinary exact inclusions.

No common bound on all complexes is added. Original namespaces and maps remain;
Waldhausen structures, cofibration-sequence packaging, S-grid coverage and K
formulas stay downstream.
