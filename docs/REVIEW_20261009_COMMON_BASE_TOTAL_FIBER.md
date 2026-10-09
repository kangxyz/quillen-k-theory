# Independent review: common-base transport and original total-tail fibers

Accepted 2026-10-09 14:07:08 UTC.

The three complete sources in
`logs/common-base-total-fiber-sources.sha256` were read:
`Topology/HomotopyFiber/CommonBaseSquareTransport`,
`Waldhausen/Fibration/RelativeRows/TotalFiber`, and
`Waldhausen/Fibration/AllWeak/TotalFiberSquare`, under `Quillen`.

## Actual maps and exact scope

The common-base transport map is the genuine source-change map on homotopy
pullbacks, after the displayed projection equality. It keeps the parameter
and complete outer path unchanged and applies the given fiber-model map to
the source. Its weakness follows from the established weak source-change
theorem. The strict projection and fiber-transition squares identify the
original model-square comparison with the original common-base comparison
composed with its fiber-model map. Two explicit weak fiber-model inputs and
actual weak-equivalence cancellation prove the original square comparison
weak. Those two inputs remain hypotheses of this general transport theorem;
no global relative realization fiber comparison is supplied or inferred.

The relative total-tail construction uses the actual original double-S zero
vertex and its realization point. The already proved ordinal split-fiber
tail identity gives a literally constant simplicial total tail. Its realized
comparison lands in the actual original homotopy fiber with precisely the
original source point and an entirely constant path. The original relative
zero maps to the actual constant-path zero of this fiber. These definitions
and identities require only the displayed nested weak-equivalence structure.
They make no weak-equivalence claim for the total-tail comparison.

The all-weak ordinary double-S inclusion is the realization of the actual
previously proved diagonal isomorphism and hence a genuine homeomorphism.
Its original zero is preserved. The original relative inclusion and tails
commute strictly with this exact base homeomorphism. The resulting map on
homotopy fibers uses the original relative source map and postcomposes the
entire stored path with the actual ordinary inclusion. The square with both
original constant-path total-tail comparisons and the original acyclic
inclusion is strict, including the stored paths and chosen zero points.
No coarse two-out-of-three or global-fiber theorem is needed for this square.

The topology and diagonal constructions retain their stated common-universe
scope. No cross-universe realization identification is hidden in the review.

## Independent verification

A separate first-path overlay excluded all three target artifact families
and freshly compiled the frozen sources in order. The fixed recursive
source-origin audit passed **41 = 10 + 15 + 16** declarations with only
`propext`, `Classical.choice`, and `Quot.sound`. All **33 consumers** passed,
including the 23 authored tests and ten additional checks of complete path
values, original source/projection identities, both homeomorphism inverse
laws, the inverse chosen-zero law, and the original transition composition.

- Audit: `audits/CommonBaseTotalFiberIndependentAudit.lean`
- Preparation: `logs/prepare-common-base-total-fiber-independent.py`
- Replay: `logs/verify-common-base-total-fiber-independent.sh`
- Evidence: `logs/common-base-total-fiber-independent-20261009`

The full audit and consumer import closure contains **3,876 prerequisite
sources** and **17,474 artifacts**. Their hashes, the three target source
hashes and project/toolchain pins agree before and after. All imported target
artifacts are fresh regular files at the first search path. The source
replay and audit are warning-free. A review-only import path typo prevented
the initial preparation; it was corrected before the successful fresh
replay. No production source was edited.

This independently accepted batch is outside the frozen 12:10 archive.
The global relative-tail weak comparisons, mixed weak gluing, Waldhausen
fibration, and Gillet–Waldhausen theorem remain separate open obligations.
