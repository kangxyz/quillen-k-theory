# Structural exact-functor adapter and canonical Q/S naturality

The four sources in `logs/exact-functor-waldhausen-sources.sha256` construct
the ordinary Waldhausen exactness witness from a genuine Quillen exact functor.
No pushout-preservation conclusion is assumed.

`MatrixInflation` proves that adjoining an arbitrary component to an admissible
mono remains admissible, by actual cobase change and a graph kernel.
`FunctorPushout` identifies an actual pushout along i with the actual cokernel
sequence A → B⊞T → P having maps (i,−f) and (g,j). Its first map is admissible,
so the sequence is a conflation. Exactness maps it to a conflation, and the
canonical biproduct comparison recovers the original mapped square.

`Waldhausen/ExactFunctor` supplies all four structural exactness conditions,
allowing independent object and morphism universes for source and target.
`QuillenComparison/ExactNaturality` then specializes the independently reviewed
based comparison theorem to that constructed witness. The canonical Q/S
isomorphism commutes with the original Quillen and Waldhausen K-maps, in every
nonnegative degree, with no extra zero-equality or pushout-preservation input.
The K-map API uses a common object/hom universe pair.

All four sources compile warning/error-free. Their recursive all-origin audit
passes 17 declarations and consumers for the exact maps and universe scopes.
Only standard Lean logical foundations occur. Independent fresh-overlay review is accepted, including the fixed17-origin audit;
see `docs/REVIEW_20261009_EXACT_FUNCTOR_WALDHAUSEN.md`.
The frozen 05:00 archive does not contain these later sources.
