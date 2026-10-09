# Independent acceptance: the original realization-product comparison

Accepted 2026-10-09 07:28 UTC after complete source inspection, seven isolated
fresh source rebuilds, a fixed46 recursive-origin audit, exact original-map
consumers and before/after hashes. Final checks are warning-free.

Finite simplicial realizations are compact by their actual nondegenerate-simplex
cover. Their actual finite skeletal stages are Hausdorff by compact closed-cell
attachments. Compactness factors the identity through one genuine stage, and
its continuous injective factor transfers Hausdorffness to the original
realization. Thus local compactness is proved for finite factors, not assumed.

The actual realization-product comparison is injective: both points are first
represented over one common finite right subcomplex; comparison there is the
already proved finite-factor homeomorphism, and the actual subcomplex inclusion
is injective. Every compact-source map into the topological product lifts
continuously and exactly through the original comparison by finite support of
its second coordinate. An unrestricted ordinary-TopCat product homeomorphism
is neither assumed nor claimed.

A separate generic lemma proves all finite-dimensional based homotopy-set
bijections from injectivity and actual compact-source lifting. The original
boundary values and lifted homotopy endpoints are forced by injectivity; the
argument includes dimension zero. The actual product homotopy-group comparison
is proved directly using paired generalized loops and relative homotopies.
Its forward map is exactly the pair of ordinary projection homomorphisms, with
no commutativity assumption, including the fundamental group.

All 46 defining-module origins, including generated/private declarations, have
only propext, Classical.choice and Quot.sound as recursive axioms. Consumers
check unchanged finite-realization topologies, no finite-factor hypothesis on
the general comparison, the original based forward piMap, dimension-zero
homotopy-set bijectivity, and the original fundamental-group projections.

Evidence: `logs/realization-product-topology-sources.sha256`,
`logs/product-topology-independent-*`,
`audits/RealizationProductTopologyIndependentAudit.lean`; fresh artifacts in
`/tmp/quillen-product-topology-independent-0708` precede live artifacts in
LEAN_PATH. The canonical Waldhausen product K wrappers are a separate review.
