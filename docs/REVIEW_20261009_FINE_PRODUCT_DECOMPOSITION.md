# Independent review: original fine K-product and coarse projection

Accepted 2026-10-09 09:20 UTC. The source in
`logs/gillet-waldhausen-fine-product-checked-sources.sha256` passed complete
semantic inspection, fresh isolated compilation, fixed 34-origin recursive
axiom audit, and all 14 consumers (13 examples plus the actual scheme product
specialization), warning-free. Hashes match; only the three standard axioms occur.

The product homomorphism is literally the original acyclic-inclusion KMap
multiplied by the original degree-zero single-insertion KMap. Its bijectivity
is derived from the accepted global unique factorization, and MulEquiv.ofBijective
constructs the genuine group equivalence. No equivalence is assumed. All degrees
include K₀; kernel closure remains explicit for bijectivity and the equivalence.

The original coarse composite of acyclic inclusion is proved trivial using the
actual weak-natural-transformation nullhomotopy and exact identity-on-complexes
fiber-object identification. The normalized KMap composition and exact original
inclusion square retain the original maps. Therefore changing weak equivalences
after the product equivalence equals the original coarse single map on its
second coordinate. Null-composite and raw product formulas need no kernel closure.
Arbitrary scheme consumers use the proved finite-locally-free kernel closure and
original vectorBundleSComparison.

Coarse surjectivity/injectivity, fibration exactness and Gillet–Waldhausen are
still separate. This endpoint supplies their group algebra without assuming them.

Evidence: `logs/fine-product-independent-{prehash,build,audit,posthash}.log`;
`audits/GilletWaldhausenFineProductIndependentAudit.lean`;
replay `logs/verify-fine-product-independent.sh`.
