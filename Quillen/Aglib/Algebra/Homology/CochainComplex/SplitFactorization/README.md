# Actual split factorizations of cochain maps

For integer-indexed cochain complexes in an abelian category, the original map
`f : K ⟶ L` factors through `Cone(id K) ⊞ L`. The actual first map is split in
each degree; the actual projection is a chain homotopy equivalence.
`FactorizationQuotient` retains the quotient `Cone(-f)` and its degreewise
splittings; `FactorizationSign` and `FactorizationConeFunctor` retain the signed
comparison with `Cone(f)` and its functorial exact sequences.

The ordinary arrow and joint-endpoint functors, natural transformations,
relative pushout/cokernel sequences, additive change-of-category comparisons,
and zero-source isomorphisms retain their original maps. Relative exactness
keeps its stated mono or degreewise split-mono hypothesis. Cone/shift closure
is retained for subcategory membership and its restricted functors.

The original namespaces are preserved. [`Factorization`](Factorization.lean)
retains the split-complex factorization wrapper and imports
`Quillen.Waldhausen.SplitComplexes.Basic`; this leaf therefore also depends on
that application interface. General exact-subcategory wrappers, further
Waldhausen cofibration classes and K-theory endpoints retain their application owners.
