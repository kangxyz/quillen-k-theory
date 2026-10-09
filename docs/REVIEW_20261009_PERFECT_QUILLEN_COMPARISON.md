# Independent review: public Scheme.K maps to perfect-complex K

Date: 2026-10-09 (UTC).
Source: `Quillen/PerfectComplexes/QuillenComparison.lean`.
Manifest: `logs/review-20261009-perfect-quillen-comparison-sources.sha256`.

## Semantic result

The construction uses exactly the public definition of Scheme.K. The proved
small-model Q-equivalence first passes to actual vector-bundle Q-theory. The
inverse of the proved canonical exact-category Q/S comparison then gives
`vectorBundleQSEquiv` to actual vector-bundle S-theory. Both realizations in the
model bridge live in the same universe; no cross-universe claim or new model
assumption is introduced.

The maps `vectorBundleToStrictKMap` and `vectorBundleToPerfectKMap` are literal
composites with the already-defined S-theory maps induced by placing a vector
bundle in complex degree zero. They exist in every natural-number K-degree;
“degree zero” refers to the complex inclusion, not a restriction to K₀.
Their compatibility with the existing strict-to-local map is equality of the
actual homomorphisms, by associativity of composition.

No equivalence to strict or locally perfect K-theory is asserted. In particular,
Gillet–Waldhausen and strict/local comparison remain separate results.

## Verification

Accepted. The exact-hash source compiled independently with its matching olean,
without warnings or errors, under compiler slot 2. The before/after manifest
checks passed.

`audits/Review20261009PerfectQuillenComparisonAudit.lean` recursively audited
all 33 declaration origins, including generated proof declarations. Only
`propext`, `Classical.choice` and `Quot.sound` occurred; the origin count is
frozen at 33. Arbitrary-universe examples verified the public source type,
S-theory equivalence, its exact small-model/Q/S formula, both strict/local map
formulas, and their exact commuting triangle. No implementation source was edited.

Logs: `logs/review-20261009-perfect-quillen-comparison-check.log` and
`logs/review-20261009-perfect-quillen-comparison-audit.log`.
