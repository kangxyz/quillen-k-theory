# Independent review: original Waldhausen K-map functoriality

Accepted 2026-10-09 06:39 UTC after full source inspection, fresh isolated
rebuild, fixed22 recursive-origin audit, actual-map consumers and matching
before/after source hashes. No warnings or nonstandard axioms remain.

The public KMap API now has identity, composition, actual zero-functor and
natural-isomorphism laws. More generally, any actual pointwise weak natural
transformation gives equality of the original KMap homomorphisms. Its concrete
conjugation by canonical zero rebasing produces an actual weak transformation
between strictly based functors. Zero-object uniqueness proves the constant
track of the existing nerve-direction homotopy. No chosen-zero equality is an
input to the general invariance theorem.

When a functor genuinely has a strict chosen-zero equality, the API also
identifies its original canonical KMap with the actual unmodified realization
piMap. Identity and composition are proved through exact S-map formulas and
this normalization compatibility. The zero functor's original simplicial and
realization maps are literally constant, so its KMap is the trivial group
homomorphism. No generic fundamental-group commutativity is used.

The independent audit includes arbitrary independent object/hom universes,
identity at n=0, actual composition, weak natural transformations, literal
constant maps, and genuine fixed-bound acyclic truncation endpoints. The lower
endpoint gives the zero map on that bounded stratum; the upper gives precisely
the original inclusion KMap. Neither says that the whole acyclic category has
trivial isomorphism-model K-theory.

Evidence: `audits/WaldhausenKMapIndependentAudit.lean` and
`logs/waldhausen-kmap-independent-*`. The fresh overlay is
`/tmp/quillen-kmap-independent-0635`; import-resolution evidence points to the
fresh source-origin artifact. Frozen source SHA256:
`26bbbdc2727a9bb10dd6a64ab0253711ef2e520ceb1e543befab1a47c6f709b4`.
Only propext, Classical.choice and Quot.sound occur recursively, including
private/generated helpers. This file is independent of the additivity layer.
