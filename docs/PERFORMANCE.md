# Typechecking performance

Use focused imports and explicit mathematical interfaces when extending the
library. Proof iteration may use a temporary finite declaration-local budget
to establish correctness. Before adopting the proof, restore the standard
200,000 budget or settle a necessary finite local increase with an adjacent
explanation, then recompile the module. Keep package defaults unchanged and
retain a finite limit. Targeted profiling helps settle the retained budget;
the [contributor guide](../CONTRIBUTING.md) gives the pinned profiling command.
This development reference records measurements and resource requirements;
mathematical interfaces and hypotheses belong to the [source-family guides](../Quillen/README.md).

## Vector-bundle instance inference

An October 2026 profile of the former `VectorBundle.Basic` module
identified repeated inference of sheafification and locally bijective classes
on over-sites. Finite-type transport through an isomorphism also reconstructed
the finiteness of an unchanged generator index.

The profiled change bound the existing universal proof instances locally
and passed the existing finite-index witness directly. The transported local
basis, its cover and generators agreed with the previous construction by `rfl`.
Declaration types, maps and mathematical hypotheses are unchanged.

Three matched unprofiled compilations used Lean 4.34.1, the committed mathlib
revision, identical strict options and the same compiled dependencies:

| Complete module | Before | After |
| --- | --- | --- |
| Run 1 | 17.790 s | 11.470 s |
| Run 2 | 16.455 s | 11.820 s |
| Run 3 | 17.084 s | 11.155 s |
| Median | 17.084 s | 11.470 s |

The observed median reduction is 32.9% for this module. These elapsed times
include imports and output serialization. Background contention and machine
state affect timings; they do not establish a whole-library speedup.

Separate instrumented runs located the finite-type proof body at 4.797 s
before and 0.049 s after the change, and the finite-free proof at 1.487 s and
0.170 s. The data construction itself did not improve. Instrumented timings
include profiler overhead and are not interchangeable with plain runs.

Strict source checks and a semantic comparison passed. The comparison used
unchanged source, setup and dependency hashes throughout the measured batch.
Future changes should repeat a matched comparison rather than treating these
numbers as a performance requirement.

## Mixed-cylinder naturality

The outer naturality proof of
[`mixedDeformationMap`](../Quillen/Waldhausen/Additivity/DeformationMap.lean)
normalizes nested interval and grid reindexings. Under the pinned compiler,
the unchanged declaration exhausts both 200,000 and 400,000 heartbeats and
passes strict compilation with its local 800,000-heartbeat allowance.
The allowance applies to this declaration; its construction and proofs are
unchanged. This records a compilation resource requirement. A speed improvement
for this declaration remains open.

The chosen-zero variant
[`normalizedMixedMap`](../Quillen/Waldhausen/Additivity/NormalizedDeformationMap.lean)
also retains its original construction and proofs. Its outer naturality
requires a declaration-local 550,000-heartbeat allowance: strict compilation
fails at 540,000 and passes at 550,000. This is the smallest tested passing
allowance. Factoring the naturality proof did not produce an accepted
default-budget optimization; no speed improvement is claimed for this change.

## Stable seed factorization types

The four supported and ambient seed-factorization theorems in
[`CoefficientSupportedBassSeedStable`](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassSeedStable.lean)
compiled at the earlier `adbfc33d` snapshot, while the pinned declaration
linter's `checkType` exhausted the default 200,000 heartbeats on their types.
That checker uses complete transparency when revalidating stored types, so
local irreducibility does not shield the concrete expressions.

Their statements now instantiate the shared transparent properties
`LaurentSeed.Track.SeedStableFactorization` and `SeedStableFormula`, defined
for an arbitrary functor, actual Laurent track and supplied natural seed.
The original supported and ambient seeds, cone inclusions, parameter shifts
and hypotheses are retained. All four original propositions, their direct
consumers and the original functor/seed data pass kernel reduction checks.
The four application types and five generic interfaces pass the pinned
`checkType` at the unchanged default budget. This is a bounded checker result;
no whole-module timing improvement is claimed.

At the `f521b87e` checkpoint, the complete local native
`bash scripts/check.sh --ci --rehash` route passed:
91 script tests, the library/test build, declaration and text-style lint,
58,560 project declarations in the root axiom audit, and the independent
client build and its 462-declaration audit. That run reused native cache artifacts.
CI axiom audits select the capped Lean executable explicitly because Lake can
prepend its native toolchain directory to `PATH`; the observed audit command
retains `-j2 -M12800`, the 13824 MiB group RSS cutoff and one frontend.
Additional independent local kernel replays are outside this CI route.

## Evaluation-unit comparison proofs

The `original_level` proof in
[`GlobalBassEvaluationInputSeedEvaluationUnitNative`](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedEvaluationUnitNative.lean)
compares the complete level maps of the original evaluation-unit pasting and
its inner relative homotopy. With Lean 4.34.1 and the pinned dependencies,
the incoming proof exhausted the kernel's default 200,000-heartbeat budget.
Direct and pointwise reflexivity encountered the same failure. Merely naming
the inner homotopy's endpoint type did not resolve it.

The retained proof first establishes equality of the whole relative
homotopies, then applies a generic equality transport before taking the level
map. The inner constructor body, public statements, maps and independent
clocks are unchanged. Its explicit endpoint type is definitionally equivalent
to the inferred type. A fresh module compilation passed at the default
200,000 budget and the unchanged 12,800 MiB frontend limit.

The `evaluation_unit` proof in
[`GlobalBassEvaluationInputSeedRawUnit`](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedRawUnit.lean)
separately exhausted the default budget during elaboration of a nested
isomorphism congruence. Naming the inner equalities alone moved the timeout to
the outer congruence. Explicitly typing the existing comparison isomorphism
before composing those equalities restored default-budget compilation. This
also preserves every public statement and data construction.

The private `pre_total_anchor` in
[`GlobalBassEvaluationInputSeedCornerNodes`](../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedCornerNodes.lean)
joins the original complete corner anchors. Its proof now isolates the source
transport equality, propagates it by congruence, and supplies the original
Model arrows to generic reassociation. The whole prefix and suffix equalities
retain the specified scheme-square and strict-composition transports.

The remaining conversion between the Model-arrow and functor presentations
uses a documented, declaration-local 400,000-heartbeat allowance. The tested
200,000 budget failed and 400,000 passed; this is a settled finite allowance,
without a claim of minimality. Native compilation and the unchanged default
environment and text checks passed. All seven public declarations, including
their proofs, remain byte-identical to the incoming source.

These observations support factoring a large concrete equality before
projecting its data and giving a large comparison an explicit local type.
They do not establish a general cause for expensive conversion or a measured
speedup. The [integration evidence record](evidence/TTCheckpointIntegration20261019.json)
identifies the incoming sources,
repaired sources and successful native runs. Reproduce with the pinned
environment and the linked modules as build targets.
