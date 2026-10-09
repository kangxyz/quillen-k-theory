# Independent review: coherent adjacent acyclic truncations

Accepted on 2026-10-09. All three frozen sources were read in full and rebuilt
warning-free into fresh isolated artifacts. The fixed-count recursive audit
passed all 341 declaration origins of the fifteen imported GW sources and
all exact-map/arbitrary-universe consumers. Only `propext`, `Classical.choice`,
and `Quot.sound` occur; pre/post source hashes match.

`TruncationCoherence.lean` proves the actual nested-truncation isomorphism for
n<m on arbitrary complexes in an abelian category, without acyclicity or
termwise-subcategory hypotheses. Its forward map is truncation of the original
upper inclusion, and compatibility with both original inclusions is proved.
The isomorphism lifts naturally to the inherited bounded acyclic category.

`AdjacentTruncation.lean` transports the already genuine internal truncation
conflation along that coherence isomorphism and the actual disk-layer
isomorphism. The resulting sequence is exactly
truncLE_n → truncLE_(n+1) → identityDisk_n(cycles_(n+1)).
Its structural cofibration-sequence contract is derived for both isomorphism
and quasi-isomorphism weak equivalences; no additivity statement is an input.
The first arrow composes to the original inclusion into the untruncated complex.

`FixedBounds.lean` defines actual strict term bounds. Closure under zero,
isomorphisms, extensions and finite products is proved, yielding an inherited
exact structure on each stratum. Below the lower bound, actual truncation is
naturally the zero functor. At or above the upper bound it is naturally the
actual inclusion, with the original truncation-inclusion forward map. These
are genuine functor endpoint isomorphisms, not assumed numerical vanishing.

No uniform bound on the whole category is assumed. Passage from fixed strata
to all bounded complexes, based additivity, fibration, and Gillet–Waldhausen
are separate obligations. These leaves are outside the delivered 05:00 archive.

Evidence:
- `logs/gw-coherence-independent-sources.sha256`
- `logs/gw-coherence-independent-check.log`
- `logs/gw-coherence-independent-audit.log`
- `logs/gw-coherence-independent-hashes.log`
- `audits/GilletWaldhausenCoherenceIndependentAudit.lean`

Manifest SHA256:
`91f64caaf692a6f2ad6682ccef2b36313a5bf76d34f139a3476ade59b3f25c41`.
