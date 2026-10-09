# Independent acceptance: literal Waldhausen K-group additivity

Accepted 2026-10-09 07:33 UTC after complete inspection, three fresh isolated
source builds over the independently checked canonical product K-equivalence,
a fixed32 recursive-origin audit, original-operation/map consumers and source
hash rechecks. Final checks are warning-free.

The actual binary coproduct is proved an exact functor from the genuine
product Waldhausen category. Its original K-map, transported by the original
projection K-equivalence, gives a group homomorphism from K×K to K. The two
actual zero embeddings and coproduct-unit natural isomorphisms prove its two
unit restrictions are the identity. Group algebra therefore identifies it
with the existing multiplication and proves that multiplication commutative,
including degree zero. No fundamental-group commutativity is assumed.

KCommGroup explicitly extends exactly the existing Group structure. The
original K-map of the sum functor is pointwise multiplication of the original
summand K-maps. The previously proved based structural additivity homotopy then
gives KMap(G)(x)=KMap(F)(x)*KMap(H)(x) in subobject-then-quotient order for every
genuine cofibration sequence F→G→H and every degree, including K₀.

The fixed32 audit checks all three source-origin modules, including generated
and private declarations, with only propext, Classical.choice and Quot.sound.
Consumers retain independent object/hom universes, the exact original Group
by rfl, explicit K₀ formulas, and the actual bounded-acyclic truncation sequence.

Evidence: `logs/waldhausen-kgroup-formula-sources.sha256`,
`logs/kgroup-formula-independent-*`,
`audits/WaldhausenKGroupFormulaIndependentAudit.lean`; fresh artifacts in
`/tmp/quillen-product-topology-independent-0708` are first in LEAN_PATH.
The Quillen K adapters and Grothendieck-presentation comparison are separate;
the latter is not established by commutativity or additivity alone.
