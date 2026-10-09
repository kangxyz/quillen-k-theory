# Independent review: original mixed-nerve transposition

Accepted on 2026-10-09. The four production sources remain unchanged; their
ordered hashes are in `logs/mixed-nerves-transpose-independent/sources.sha256`.

## Semantic findings

The original fine-chain category retains all natural transformations. Its
objects satisfy the actual fine weak-arrow condition, while horizontal
cofibration and coarse weak-arrow conditions are imposed separately and
pointwise. No Waldhausen structure on this full chain category is presumed.
The coarse-chain and coarse-cofibration-chain objects reuse the existing
`CoarseWeakChain` and `CofibrationWeakChain` definitions; their morphisms in
the original nerve direction are precisely the original pointwise fine maps.

The explicit transpositions and inverses merely exchange the two finite
indices. Every object, horizontal arrow and vertical arrow remains the
original component. The genuine object/morphism predicates are repackaged
from their original witnesses. Both inverse identities, both ordinal
naturalities, and the literal inclusion square are proved directly. The
bisimplicial and diagonal isomorphisms use those same maps and the existing
canonical diagonal-flip isomorphism. No comparison equivalence, cylinder,
saturation, extension axiom or fibration conclusion is an input. Object and
hom universes remain independent, with the simplicial universe displayed as
max(u,v).

## Fresh verification

All524 production lines were read, together with the category interfaces they
reuse. An isolated first-path overlay excluded every target artifact family
before rebuilding all four sources. No live compiled target or production
source was edited. The fresh builds and fixed179-origin recursive audit
(24+78+61+16) passed warning-free with only the standard three axioms.

All38 consumers passed: the author's30 plus eight independent checks of
unrestricted underlying natural transformations, exact inverse object and
arrow components, both ordinal naturalities, degree-zero inverse components,
and the literal original diagonal inclusion. Existing tests cover both
inclusion squares, original predicates, independent universes and both
inverse identities. All98 dependency source hashes and326 actual prerequisite
artifact hashes match, as do pre/post production hashes.

The fixed driver is `audits/MixedNervesTransposeIndependentAudit.lean`.
The reproducible excluded-target harness, actual import paths, build/audit
logs and hash evidence are in `logs/mixed-nerves-transpose-independent/`.
This acceptance concerns the literal presentation isomorphisms; the separate
cylinder comparison and prescribed diagonal evaluation are later endpoints.
