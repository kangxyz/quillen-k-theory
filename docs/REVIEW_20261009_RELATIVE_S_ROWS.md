# Independent review: actual relative S-row diagram and split triangle

Accepted 2026-10-09 09:20 UTC. The exact three sources in
`logs/relative-rows-simplicial-sources.sha256` were read completely, freshly
rebuilt in an isolated overlay, and audited with a fixed 55-origin guard.
All 22 original-map consumers passed warning-free. Source hashes match and
only propext, Classical.choice and Quot.sound occur recursively.

The zero-first tail section duplicates the original initial vertex, preserves
the actual chosen zero, and is genuinely exact by the original inclusion and
ordinal restriction. Tail followed by this section is the original identity
in the stated direction. Its first object is genuinely zero; no outer
naturality of this degreewise section is asserted.

The outer relative and ordinary row diagrams use actual inner S-constructions.
Their structure maps, tail maps and zero-tail split inclusions are the original
exact-functor S-maps. Strict functor equalities prove the required outer
naturality and actual zero composite. The raw realization universe is explicitly
common; the structural tail section retains independent object/hom universes.

The first/tail map targets the genuine simplicial product. Both projections
and the original split-to-constant-vertex triangle are exact equalities. Inner
row path connectedness comes from the actual Waldhausen S-connectedness
result. No first/tail realization equivalence, global fiber theorem, or
unrestricted ordinary-product realization homeomorphism is claimed.

Evidence: `logs/relative-srows-independent-{prehash,build,audit,posthash}.log`;
`audits/RelativeRowsSimplicialIndependentAudit.lean`;
replay `logs/verify-relative-srows-independent.sh`.
