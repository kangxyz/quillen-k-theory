> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#evaluation-unit-comparison-proofs) · [Context](original-context.md) · [Case index](README.md) · [Previous record](stable-seed-factorization-types.md) · [Next record](full-node-overlap-reanchoring.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Evaluation-unit comparison proofs

The `original_level` proof in
[`GlobalBassEvaluationInputSeedEvaluationUnitNative`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedEvaluationUnitNative.lean)
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
[`GlobalBassEvaluationInputSeedRawUnit`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedRawUnit.lean)
separately exhausted the default budget during elaboration of a nested
isomorphism congruence. Naming the inner equalities alone moved the timeout to
the outer congruence. Explicitly typing the existing comparison isomorphism
before composing those equalities restored default-budget compilation. This
also preserves every public statement and data construction.

The private `pre_total_anchor` in
[`GlobalBassEvaluationInputSeedCornerNodes`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationInputSeedCornerNodes.lean)
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
speedup. The [integration evidence record](../evidence/TTCheckpointIntegration20261019.json)
identifies the incoming sources,
repaired sources and successful native runs. Reproduce with the pinned
environment and the linked modules as build targets.

