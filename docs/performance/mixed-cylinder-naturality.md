> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#mixed-cylinder-naturality) · [Context](original-context.md) · [Case index](README.md) · [Previous record](vector-bundle-instance-inference.md) · [Next record](stable-seed-factorization-types.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Mixed-cylinder naturality

The outer naturality proof of
[`mixedDeformationMap`](../../Quillen/Waldhausen/Additivity/DeformationMap.lean)
normalizes nested interval and grid reindexings. Under the pinned compiler,
the unchanged declaration exhausts both 200,000 and 400,000 heartbeats and
passes strict compilation with its local 800,000-heartbeat allowance.
The allowance applies to this declaration; its construction and proofs are
unchanged. This records a compilation resource requirement. A speed improvement
for this declaration remains open.

The chosen-zero variant
[`normalizedMixedMap`](../../Quillen/Waldhausen/Additivity/NormalizedDeformationMap.lean)
also retains its original construction and proofs. Its outer naturality
requires a declaration-local 550,000-heartbeat allowance: strict compilation
fails at 540,000 and passes at 550,000. This is the smallest tested passing
allowance. Factoring the naturality proof did not produce an accepted
default-budget optimization; no speed improvement is claimed for this change.

