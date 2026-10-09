# Independent review: the literal cubical boundary

The original source contains 30 recursive origins. Its 16 original consumers
and two independent tests (original presentation bijectivity and uniqueness
of boundary-map descent) passed.

Injectivity of the relative-cylinder boundary map is proved by the genuine
side/cap pushout relations. Surjectivity of the pushout coproduct gives all
side/side, side/cap, and cap/cap cases. The mixed-cap cases use the actual
inequality of the interval endpoints. This proves injectivity of each
canonical iterated cubical boundary presentation inductively, including the
empty zero-dimensional boundary.

The actual boundary subtype is Hausdorff, and the presentation is compact.
The original continuous bijection therefore gives a genuine homeomorphism.
Its forward map is literally the original presentation, and the inverse
composed with that original map is exactly the boundary inclusion. The
homotopy extension property transfers through this homeomorphism from the
proved canonical presentation. Universe-lift removal preserves all boundary
coordinates and proves HEP for the literal unlifted inclusion as well.

Arbitrary boundary maps and their full prescribed homotopies descend through
the genuine homeomorphism. There is no choice of discontinuous preimages,
no HEP assumption on an arbitrary closed subset, and no global weak-cartesian
gluing consequence asserted here.

## Independent validation

Accepted 2026-10-09 11:07 UTC. The combined check rebuilt all three targets in
an excluded-target first-path overlay, checked fixed origin counts 15+9+30,
and compiled 35 concrete consumers. Recursive axiom collection found only
`propext`, `Classical.choice`, and `Quot.sound`. Source and prerequisite hashes
were unchanged before and after the check. No production source was changed.

Audit: `audits/ChainReplacementBoundaryIndependentAudit.lean`.
Script: `logs/verify-chain-boundary-independent.sh`.
Evidence: `logs/chain-boundary-independent-artifacts.sha256`.
The boundary is outside the immutable 10:55 version7 archive.
