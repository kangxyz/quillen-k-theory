# Original single/change-of-weak K-map identification

Two new modules expose an actual map triangle, without asserting a
Gillet–Waldhausen equivalence or assuming fibration.

`Waldhausen/GilletWaldhausen/SingleQuasiComparison.lean` proves that the same
original single-complex functor in every degree is exact into the bounded
termwise-P Waldhausen model with genuine quasi-isomorphisms. Its canonical
public normalized KMap is exactly the fine single KMap followed by the
actual identity change-of-weak-equivalences KMap from `boundedTermsNested`.
The triangle holds in every original K-group, including K₀.

The hypotheses are an abelian category, the honest compatible mixed
universe `A : Type (max u v)` with `Category.{v} A`, and P containing zero,
replete, and extension-closed. Kernel closure, projectivity, a K-equivalence,
or a fibration conclusion is not required.

`PerfectComplexes/SingleComparison.lean` identifies the actual scheme
models on an arbitrary scheme: bounded termwise finite-locally-free is
definitionally the existing strict-perfect predicate; the previously
constructed vector-bundle inclusion is the same original degree-zero single
functor. Therefore the existing `vectorBundleSComparison` is exactly the
coarse single KMap, and its actual fine/change-of-weak triangle is proved.
No noetherianity, regularity, resolution property, or global projectivity is
added. The audit also checks the previously public `vectorBundleToStrictKMap`
with its original Q/S conversion retained.

Both source files compile without warnings or errors. The actual-map,
weak-class, K₀, arbitrary-scheme and public-Q/S-map consumers are in
`audits/GilletWaldhausenSingleComparisonAudit.lean`. Its final fixed8 recursive
source-origin audit and all consumers passed without warnings, errors, or
`sorryAx`; only `propext`, `Classical.choice`, and `Quot.sound` occur.

The frozen manifest is
`logs/gillet-waldhausen-single-comparison-checked-sources.sha256`, the terminal
raw audit is `logs/gillet-waldhausen-single-comparison-axioms.log`, and all
source and prior-boundary hashes are checked in
`logs/gillet-waldhausen-single-comparison-prior-hashes.log`. Artifact hashes
are in `logs/gillet-waldhausen-single-comparison-artifacts.sha256`.
No existing accepted source or umbrella is changed. Independent review passed; see
`docs/REVIEW_20261009_SINGLE_COMPARISON_TRIANGLE.md`. This pair was accepted
after the Euler checkpoint.
