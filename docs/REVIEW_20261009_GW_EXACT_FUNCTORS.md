# Independent review: exact acyclic cycle and truncation functors

Accepted 2026-10-09 05:24 UTC. This extends the earlier bounded-acyclic
algebra and functor reviews to seven source modules.

`CyclesExact` proves naturality of the actual differential-to-cycle map.
If the target complex is exact in degree n and the original chain map is epi
in degree n−1, its map on cycles in degree n is epi: its composite with the
source differential-to-cycles map equals a composite of epimorphisms.
Together with existing left exactness, this proves that cycles take a short
exact sequence to a short exact sequence when only its rightmost complex is
acyclic. The actual cycles functor is proved additive and restricts to an
actual `ExactFunctor` on bounded acyclic termwise-P complexes.

`TruncationExact` gives natural isomorphisms identifying the genuine truncation
with original terms below the boundary and actual cycles at the boundary.
Cancellation against the actual monomorphic truncation inclusion proves
additivity. Degreewise short exactness then proves exactness of the genuine
truncation functor; above the boundary the objects are zero. Its underlying
functor is definitionally the first projection of the previously checked
truncation-sequence functor. No exactness conclusion is supplied as a hypothesis.

Both new sources were read in full and independently recompiled into an isolated
artifact overlay, warning/error-free. The earlier five sources retain their
prior independent rebuilds. Hash checks before and after passed for all seven.
The fixed-count audit `audits/GilletWaldhausenExactIndependentAudit.lean` passed
all 140 imported source-origin declarations, including generated/private ones,
with only `propext`, `Classical.choice` and `Quot.sound`. Arbitrary-(u,v) consumers
checked the stronger right-acyclic short-exact statements and exact functor/map
identities. An arbitrary-scheme vector-bundle consumer also passed, using the
independently proved ambient kernel closure.

Evidence: `logs/gw-exact-independent-{check,audit,hashes}.log` and
`logs/gw-exact-independent-sources.sha256`, with manifest SHA-256
`a173ce84cd21cb785d94fe62171578e3ee4739faa40cd491729b511c292610c8`.

Exactness of the quotient functor, disk-layer identification, additivity,
change-of-weak-equivalences fibration and Gillet–Waldhausen itself remain separate
results. These seven modules are outside the frozen 05:00 archive boundary.
