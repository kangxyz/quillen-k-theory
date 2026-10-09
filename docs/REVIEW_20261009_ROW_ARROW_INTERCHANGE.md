# Independent acceptance: actual row-arrow interchange

Accepted 2026-10-09 08:00 UTC. All eight complete source files were inspected,
freshly rebuilt in order into an isolated overlay, and checked with a fixed
139-origin recursive-axiom audit. Only propext, Classical.choice and Quot.sound
are allowed, including private/generated declarations. The final audit contains
all 33 authored concrete consumers and one additional bidirectional actual
transpose-cofibration consumer. Source hashes match before and after. Checks
are warning-free.

The generic arrow/diagram equivalence retains the original component arrows and
all natural transformations. Its two inverse identities are proved, rather
than an abstract equivalence being supplied. Pointwise-arrow quotient rows and
arrows of actual quotient rows are genuinely exact in both directions. The
cofibration comparisons use the actual pointwise pushouts and inherited row
conditions, with no assumed ambient cocompleteness.

For Reedy arrows, transposing two extension directions changes the relative
pushout calculation. The actual three-direction pushout interchange is proved
by its universal property. It yields the genuine transpose cofibration theorem
and exact involution on the original extension category. This is the substantive
cube calculation; no equivalent cube condition or target exactness is assumed.
The resulting Reedy-arrow/quotient-row equivalence retains every original
component and is exact in both directions.

The joint cylinder on actual rows is the composite of these genuine exact
functors and exact postcomposition with the original joint functor. The component
maps and all ordinal reindexing equations are proved literally. Concrete consumers
instantiate both isomorphism and quasi-isomorphism weak models on genuine complex
subcategories, under their stated cone/shift closure conditions. Independent
category object/hom universes are retained.

These results provide structural input to the relative S-construction. They do
not prove relative additivity, a change-of-weak-equivalence fibration, or a
Gillet–Waldhausen comparison.

Evidence: `logs/row-arrow-interchange-sources.sha256`,
`logs/row-arrow-independent-prehash.log`, `logs/row-arrow-independent-build.log`,
`logs/row-arrow-independent-final-fixed139.log`,
`logs/row-arrow-independent-posthash.log`, and
`audits/RowArrowInterchangeIndependentAudit.lean`. The fresh defining artifacts
in `/tmp/quillen-row-arrow-independent-0745` were first in LEAN_PATH; dependency
resolution was recorded. The audit's fixed origin counts are
26 + 3 + 19 + 2 + 26 + 2 + 51 + 10 = 139.
