# Independent review: original acyclic inclusion K-map injectivity

Accepted 2026-10-09 at08:44:52 UTC. The two frozen sources in `logs/gillet-waldhausen-inclusion-injective-checked-sources.sha256` passed full semantic review, fresh isolated rebuilds, the fixed12 recursive-origin audit and all16 consumers, with before/after source/dependency hashes matching. No implementation source or live artifact was modified by this review.

## Semantic review

- Finite injectivity uses the actual adjacent-cycle incidence formula for the original inclusion and term/cycle evaluation KMaps. The genuinely zero lower cycle initializes an induction that detects every cycle coordinate. The previously proved finite cycle equivalence then detects the original class. Empty intervals are handled using the proved zero-layer formula; K₀ is included.
- The finite/global and transition inclusion squares are derived from actual original exact-functor compositions via canonical `KMap_comp`. No target square or injectivity is assumed.
- Global injectivity first represents the original acyclic K-class at a genuine finite stage. Actual eventual-zero detection for the bounded-term target produces a later stage where the included class is one. The proved finite injectivity detects that later acyclic class, and the original global inclusion/transition compatibility returns the original class as one. Group cancellation gives injectivity.
- Kernel closure remains explicit in the injectivity endpoint, since actual cycles must belong to the object property. The purely functorial squares themselves do not need it. Zero containment, repleteness and extension closure are also explicit.
- The exact universe contract is `A : Type (max u v)` with `Category.{v} A`. This is inherited honestly from the mixed cycle-evaluation/insertion API. Arbitrary schemes instantiate it at the explicit levels `{u,u+1}` using the proved ambient finite-locally-free kernel closure.
- All object and chain-map inclusions are unchanged. The weak model is the original isomorphism model. This is not an identification with the coarse quasi-isomorphism model or a homotopy-fiber theorem.

## Verification

The isolated overlay is `logs/gillet-waldhausen-inclusion-injective-independent-20261009/`. It reuses the separately freshly rebuilt five coverage artifacts, with newly rebuilt target artifacts for both sources. `audits/GilletWaldhausenInclusionInjectiveIndependentAudit.lean` fixes **12 declaration origins** (8+4) and includes **16 consumers**: literal complexes and chain maps, original map squares without kernel closure, finite/global original KMap injectivity, empty intervals, K₀, and arbitrary-scheme specializations.

The fresh two-target and five coverage dependency paths are verified in `deps.log`; the coverage paths point to the separately accepted freshly rebuilt artifacts. Source checks and the final audit are warning-free, and recursively permit only `propext`, `Classical.choice`, and `Quot.sound`. Replay script: `logs/verify-gillet-waldhausen-inclusion-injective-independent.sh`.
