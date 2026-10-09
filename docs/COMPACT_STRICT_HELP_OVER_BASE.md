# Actual strict compact HELP over the displayed base

## Frozen endpoint

`logs/strict-over-base-sources.sha256` freezes seven sources:

- `HomotopyLifting/VariableTime`
- `HomotopyLifting/Stationary`
- `HomotopyLifting/ParallelLifts`
- `HomotopyLifting/OverBaseCorrection`
- `HomotopyLifting/CubeDuration`
- `HELP/ContractibleTestOverBase`
- `HomotopyLifting/CubeOverBase`

They construct actual vertical comparison homotopies. Ordinary contracted
HELP is not treated as if it were already fiberwise.

## Exact hypotheses and conclusion

Two original maps `p:E→B` and `q:F→B` have genuine Hurewicz homotopy lifting.
The original `f:E→F` lies over their common base. Its original strict-fiber
maps have full compact HELP. The test pair is compact, has actual HEP, has
a displayed contraction of its target, and has a continuous duration whose
zero locus is exactly the image of its inclusion.

`strictHELP_over_contracted_test` extends the given boundary map exactly.
The extension's projection is exactly the prescribed base coordinate
`q ∘ b`. Its actual comparison homotopy to `b` is vertical at every time and
is constant at the original prescribed boundary value on the entire boundary.

The cube specialization supplies all test hypotheses from the actual lifted
finite cube, its canonical whole boundary and the original contraction.
Its duration is the product of `xᵢ(1−xᵢ)` in the original coordinates. Its
zero locus is exactly the entire boundary. The empty product in degree zero
is one, correctly giving no boundary there. No nonemptiness or positive-degree
assumption is added.

## First correction: original base homotopy and boundary retained

For a compact family constant at a parameter, the tube lemma proves that
arbitrary selection of its compact coordinate is continuous at that parameter.
No Hausdorff or regularity hypothesis is placed on the target topology.

A base homotopy stationary where the duration vanishes is accelerated by
`min(t/d(x),1)`. The compact-family lemma proves continuity at `d(x)=0`.
Ordinary HLP lifts this accelerated homotopy. Evaluating the result at
`t·d(x)` recovers the original projected homotopy exactly. Where `d(x)=0`,
the lift stays at its original initial value. This construction does not
assume that an arbitrary HLP choice preserves constant paths.

Applied to the projection of an ordinary comparison homotopy, this restores
the displayed base map and retains every original boundary value.

## Second correction: actual vertical comparison with coherence

The original comparison and the image of the corrected source lift are two
lifts of the same actual base homotopy. Reverse the latter and follow the
former. Its projection is the explicit backtrack with time `|2t−1|`.

Contract the backtrack to its endpoint using
`1−(1−s)(1−|2t−1|)`. Stationary lifting with duration `t(1−t)d(x)` fixes both
path endpoints and the entire prescribed zero set. The resulting endpoint
comparison is vertical. `parallel_lifts_with_coherence` also exposes the
full two-parameter homotopy, its exact projected backtrack contraction, both
fixed endpoints and the fixed zero set. The coherence is the actual same
constructed lift, rather than an unrelated path-class witness.

## Verification boundary

The ordered final source check and exhaustive author-origin audit are recorded
in `logs/strict-over-base-initial.log`: all seven source checks, all 41 defining
origins recursively, and the initial 12 exact consumers passed warning-free.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The final fixed-41 audit
`audits/StrictOverBaseHELPAudit.lean` also passed all 13 consumers warning-free,
including the explicit degree-zero endpoint. Its clean terminal evidence is
`logs/strict-over-base-fixed41.log`; all frozen source hashes match. No umbrella source is changed.

## Remaining scope

This boundary proves strict-square HELP with a vertical comparison constant
on the whole prescribed boundary. Arbitrary nonconstant prescribed boundary
homotopies require a later actual fiberwise extension and vertical unpadding
argument. Those companion drafts are excluded here.

No whole-space fiberwise deformation is chosen on a noncompact path pullback.
The chart-compatible vertical mapping-path construction and global weak-
cartesian/diagonal fiber gluing remain subsequent work.
