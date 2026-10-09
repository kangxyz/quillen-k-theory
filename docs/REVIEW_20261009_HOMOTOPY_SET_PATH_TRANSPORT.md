# Independent acceptance: actual all-degree basepoint transport

Accepted 2026-10-09 08:11 UTC. Complete source and dependency inspection,
isolated fresh rebuild, fixed28 recursive-origin audit, all19 actual-map
consumers, and before/after hashes passed without warnings. The only permitted
axioms are propext, Classical.choice and Quot.sound.

The free path space has the original compact-open topology. Evaluation at any
interval point is an actual homotopy equivalence: its inverse is the constant
path map, and the interval is explicitly contracted linearly to that point.
At the basepoint equal to the supplied path, the original endpoint-evaluation
homotopy-set maps are therefore bijective in every finite degree. Their actual
composite defines path transport. No based inverse, Whitehead upgrade, or
continuous family of chosen inverse maps is assumed.

Postcomposition of actual free paths gives strict evaluation squares. The
original homotopy-set maps commute exactly with transport. Consequently their
injectivity, surjectivity and bijectivity are invariant along a path in the
source. The pointed-set degree-zero case is checked explicitly, without using
a group law on π₀. Actual constant classes and transport along a constant path
are retained. Independent source/target universes remain explicit.

This is a basepoint-transport result, not a global realization fiber theorem.
It was accepted after the frozen08:05 boundary and is absent from that archive.

Evidence: `logs/path-transport-independent-sources.sha256`,
`logs/path-transport-independent-{prehash,deps,build,audit,posthash}.log`,
`audits/PathTransportIndependentAudit.lean`. The defining artifact was freshly
built in `/tmp/quillen-path-transport-independent-0807`, first in LEAN_PATH.
Frozen source SHA256:
`0aa1157296407af9f2b4aa5a69ac28f2bfc8e678a6842c23f00a82c1788df3f0`.
