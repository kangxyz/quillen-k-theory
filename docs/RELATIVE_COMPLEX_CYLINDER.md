# Relative cofibrations of the actual complex cylinder

The source `Quillen/Waldhausen/Cylinder/RelativeComplex.lean` proves the
naturality of both joint endpoints and of their actual shifted-source quotient.
These are assembled into a genuine map of short exact sequences. Evaluation
in each degree and the existing explicit relative retraction show that the
relative endpoint pushout map is degreewise split whenever the source map is.
If both source and target maps are degreewise split, the actual middle-object
functor map is degreewise split too: it factors as a pushout of the biproduct
map followed by that relative map.

The construction works in every abelian category, with independent object and
morphism universes. It uses no comparison or fibration theorem. It does not yet
supply the quotient-membership proof needed to restrict these maps to an
arbitrary complex subcategory, or the strict zero-normalization condition of a
complete cylinder-functor contract.

The source compiled without warnings or errors. A recursive audit found all
12 source-origin declarations (including generated/private declarations) depend
only on `propext`, `Classical.choice`, and `Quot.sound`. Arbitrary-universe
consumers check the exact short-sequence maps and the actual cofibrations.
Independent fresh-overlay review accepted this scoped result; see
`docs/REVIEW_20261009_RELATIVE_CYLINDER.md`. Source manifest:
`logs/cylinder-relative-complex-sources.sha256`; check/audit logs share that stem.
