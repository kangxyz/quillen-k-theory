# Independent review: ordinary product weak equivalences

Accepted 2026-10-09 10:30 UTC. The frozen one-source boundary in
`logs/ordinary-weak-product-sources.sha256` was semantically inspected and
freshly compiled in an excluded-target overlay. The fixed-nine recursive
origin audit and 11 independent consumers passed warning-free. Only the
three standard Lean logical axioms occur in the recursive closures.

The new `homotopyProdMap` is literally the pair of original continuous
projection maps on `HomotopyGroup N`; the index type N and both factor
universes are independent. Its bijection pairs actual generalized loops and
actual full-boundary relative homotopies. Thus it covers the empty index
as well as positive dimensions. In positive dimensions it agrees
 definitionally with the established group-homomorphism product map.

Strict naturality is checked on quotient representatives. The actual product
map of two complete weak homotopy equivalences is then a complete weak
equivalence: the all-finite-degree bijections are transported through those
literal projection pairs, and original component paths are paired to prove
component surjectivity. Empty factors are included; the all-basepoint test
alone is not substituted for the complete weak property. The original left-
and right-factor map corollaries allow an arbitrary unchanged factor.

The independent consumers import the public library, expose both literal
projection coordinates and all-index bijectivity, explicitly test degree zero,
retain positive-degree agreement, test all finite homotopy maps of the
original product map and its component surjectivity, verify strict naturality,
and cover both untouched factors and an empty source factor. There is no
cartesian-pushout or weak-gluing conclusion in this endpoint.

Script: `logs/verify-ordinary-weak-product-independent.sh`.
Fresh first-`LEAN_PATH` overlay: `/tmp/quillen-weak-product-independent-1024`.
Audit: `audits/OrdinaryWeakProductIndependentAudit.lean`.
Logs: `logs/ordinary-weak-product-independent-{build,audit,prehash,posthash}.log`.
Evidence: `logs/ordinary-weak-product-independent-artifacts.sha256`.
The frozen source hash was checked before and after; the target artifact
family was excluded before rebuilding. This is outside the 09:45 archive.
