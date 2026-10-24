> Preserved original record. [Original source](https://github.com/kangxyz/quillen-k-theory/blob/778bbb81b9fb449e49452a98ea0f8b0c26e6fdb5/docs/PERFORMANCE.md#vector-bundle-instance-inference) · [Context](original-context.md) · [Case index](README.md) · [Previous record](generated-import-entries.md) · [Next record](mixed-cylinder-naturality.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

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

