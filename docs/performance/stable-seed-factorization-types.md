> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#stable-seed-factorization-types) · [Context](original-context.md) · [Case index](README.md) · [Previous record](mixed-cylinder-naturality.md) · [Next record](evaluation-unit-comparison-proofs.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Stable seed factorization types

The four supported and ambient seed-factorization theorems in
[`CoefficientSupportedBassSeedStable`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportedBassSeedStable.lean)
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

