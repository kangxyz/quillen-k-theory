# Independent acceptance: compact Hausdorff pushouts

Accepted 2026-10-09 07:00 UTC after complete source inspection, an isolated
fresh rebuild, exact-map consumers, a fixed recursive five-origin audit and
before/after source hashes. All final checks were warning-free.

The underlying topology is the actual categorical TopCat pushout. Compactness
is obtained from the surjection from the disjoint union of the two corners.
Hausdorffness follows when the attaching map is a closed embedding and the two
other corners are compact Hausdorff: compactness of the attaching object is
derived, the actual quotient map is closed, and its T1 target is Hausdorff.
No separation or compactness conclusion is supplied as an input hypothesis.
The weaker closed-map lemma needs only compactness of the attaching object and
Hausdorffness of the other corner. The general closed-surjection lemma allows
independent source/target universes.

Evidence: `audits/CompactHausdorffPushoutIndependentAudit.lean`,
`logs/compact-hausdorff-independent-*`, fresh artifacts in
`/tmp/quillen-compact-hausdorff-independent-0657`. All five source-origin
declarations, including generated/private declarations, depend only on
propext, Classical.choice and Quot.sound. Accepted source SHA256:
`bfe52d7e0b719de7bec028d42b82419b24cf14ef77e7d65ec3b35ff8ff42fad0`.

This is a topology foundation for the next finite-realization/product proof;
it is outside the already frozen 07:00 checkpoint boundary.
