# Quillen performance cases

Return to the [performance lookup](../PERFORMANCE.md).
The shared methods are maintained in Aglib:
[conversion boundaries](https://github.com/kangxyz/aglib/blob/main/docs/performance/conversion-boundaries.md),
[shared constructions](https://github.com/kangxyz/aglib/blob/main/docs/performance/shared-constructions.md),
[instances and universes](https://github.com/kangxyz/aglib/blob/main/docs/performance/instances-and-universes.md).
These cases retain their original Lean 4.34.1 and dependency conditions.

## Vector-bundle instance inference

The former `VectorBundle.Basic` repeatedly inferred sheafification and locally
bijective classes on over-sites. Finite-type transport through an isomorphism
also rebuilt the unchanged finite generator witness. The repair bound the
existing universal proof instances locally and passed the witness directly;
the local basis, cover and generators agreed by `rfl`.

Three matched unprofiled module compilations used the same strict options,
compiler and compiled dependencies:

| Run | Before (s) | After (s) |
| --- | ---: | ---: |
| 1 | 17.790 | 11.470 |
| 2 | 16.455 | 11.820 |
| 3 | 17.084 | 11.155 |
| Median | 17.084 | 11.470 |

The observed median reduction was 32.9% for that module. Separate instrumented
runs located changes in individual proof bodies; those numbers include profiler
overhead. Neither result establishes a whole-library speedup. Future
performance comparisons, when requested, need their own matching conditions;
ordinary edits do not repeat these measurements.
[Original observation and limits](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#vector-bundle-instance-inference).

## Shared seed-factorization statements

The four supported/ambient seed-factorization declarations in
[CoefficientSupportedBassSeedStable](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassSeedStable.lean)
compiled, but the pinned linter's `checkType` exhausted its ordinary budget
on their types. Its full transparency meant local irreducibility did not hide
the concrete expressions.

The retained types instantiate shared transparent properties
`LaurentSeed.Track.SeedStableFactorization` and `SeedStableFormula`, parameterized
by the actual functor, Laurent track and natural seed. Original seeds, cone
inclusions, shifts and hypotheses remain. The recorded four application types
and five generic interfaces passed the pinned type check at its default budget.
This is scoped checker evidence, not a module-speed comparison.
[Original source and historical validation scope](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#stable-seed-factorization-types).

The client's audits, controls and replay mentioned in that old checkpoint
remain historical scope; they do not define current validation.

## Evaluation and node transports

In [GlobalBassEvaluationInputSeedEvaluationUnitNative](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedEvaluationUnitNative.lean),
`original_level` timed out while comparing concrete level maps. Direct and
pointwise reflexivity, and merely naming the endpoint type, were insufficient.
The repair first compared the whole relative homotopies, transported their
equality generically, then took the level map.

In [GlobalBassEvaluationInputSeedRawUnit](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedRawUnit.lean),
naming inner equalities moved the failure to outer isomorphism congruence.
Giving the existing comparison isomorphism an explicit type before composing
the equalities restored default-budget compilation.

For [BassProjectionFourEdgeTargetOverlapReanchor](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassProjectionFourEdgeTargetOverlapReanchor.lean),
specializing finite-parameter naturality over the full 31-node carrier failed
at 200,000 and in a 400,000 trial. The retained proof transported the whole
dependent-node family over abstract Model arrows, fixed the original finite
index and equations, then evaluated. The 18-node polynomial anchor in
[GlobalRawBassInputCompositionTerminalColumns](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputCompositionTerminalColumns.lean)
used a whole-functor transport lemma over the original equality transports and
composition isomorphism. Both retained no heartbeat override.

[SupportedRawPullbackCoherence](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedRawPullbackCoherence.lean)
retained the original ambient comparison under the faithful forgetful functor,
with a reflexive object equation and explicit projection simplifications.
These are proof-typing repairs with unchanged original data, maps and
hypotheses, not an identified universal conversion mechanism or measured
speedup.

The existing [integration record](../evidence/TTCheckpointIntegration20261019.json)
and [continuation record](../evidence/TTCheckpointContinuation20261019.json)
identify sources and native results. Their old control/client requirements
are part of those dated records; the current contributor guide owns practice.

## Retained finite allowances

A recorded passing allowance is different from an optimization:

- `mixedDeformationMap` failed at 200,000 and 400,000 and passed with its
  declaration-local 800,000 allowance.
- `normalizedMixedMap` failed at 540,000 and passed at 550,000. The latter is
  the smallest tested passing allowance, not a proved minimum.
- The `pre_total_anchor` Model-arrow/functor conversion retained a documented
  local 400,000 allowance after 200,000 failed. No minimality was claimed.

No accepted default-budget optimization was recorded for these boundaries.
Keep their mathematical and finite-budget conditions; use the current
[contributor policy](../../CONTRIBUTING.md#typechecking-performance) for
an explicitly requested investigation.
[Mixed-cylinder record](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#mixed-cylinder-naturality),
[evaluation-unit record](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#evaluation-unit-comparison-proofs).

## Historical hardlink workaround

At the old Aglib pin `2c34f185`, the observer rejected ctime changes on shared
artifacts after successful checks. In one idle task-owned workspace, private
reflinks retained bytes, ownership, permissions, mtime, traces and pins. The
unchanged final entry then passed its recorded checks and 89,314-declaration
axiom audit with no new Lean frontends. The measured XFS quota still charged
reflink allocation, so this workaround needed quota headroom.
[Exact old-pin result](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#shared-cache-metadata-during-final-checks).

The current shared observer rechecks native content for ctime-only changes;
see [the common lesson](https://github.com/kangxyz/aglib/blob/main/docs/performance/build-and-check-costs.md#distinguish-cache-observer-and-checker-failures)
and [toolkit owner](https://github.com/kangxyz/aglib/blob/main/scripts/README.md).
Private-reflink conversion is not routine preparation.

Common cache transport, resource profiles and generated-entry handling belong
to Aglib's current operating owners. The [complete earlier Quillen guide](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md)
remains recoverable. Its historical stage lists do not add current checks.
