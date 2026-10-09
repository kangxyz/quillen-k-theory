# Independent review: actual based finite-stage K-coverage

Review scope is the five sources in `logs/gillet-waldhausen-based-coverage-checked-sources.sha256`. Accepted 2026-10-09 at08:42:25 UTC: the full semantic review, fresh five-source rebuild, fixed70 recursive-origin audit, all34 actual-map consumers, and before/after source/dependency hashes passed without warnings. No implementation source or live artifact was changed by this review.

## Semantic review

1. `BasedGroups` uses the actual filtered simplicial colimit, compact based-cube factorization and relative-boundary homotopy lifting. Compatible actual basepoints are the only additional data. It proves joint representation and eventual equality for all finite based homotopy sets, including dimension0, without a transition equivalence or realization-map injectivity premise. The positive-dimensional group versions retain the original `piMap`.
2. Both actual finite-stratum models use the tagged ambient chosen zero and exactly the inverse-image isomorphism class used by the original filtered S-diagram. The genuine stage and transition structures retain actual inflations and actual pushouts. The original inclusion and transition functors literally preserve those tagged zeros.
3. Exact identity functors compare these models with the original inherited isomorphism structures. Their canonical KMaps are inverse in the required direction by actual KMap composition and identity. Inclusion and transition transport squares use these actual exact identities; no comparison square is assumed.
4. Each coverage proof applies the proved actual S-colimit at the actual stage points and then transports through those identities. Statements retain the original public inclusion/transition KMaps. In particular a class mapping to one globally becomes one under a genuine later original transition; no categorywide uniform bound is asserted.
5. The concrete five-source scope is an abelian category with independent object/hom universes and a zero-containing, replete, extension-closed object property. No kernel closure is required. The small stage indexing copy is taken in the genuine S-set universe `max u v`; there is no raw cross-universe realization identification.

## Verification

Fresh artifacts and logs: `logs/gillet-waldhausen-based-coverage-independent-20261009/`. All unchanged dependency artifacts are linked into that isolated namespace, and all five target artifacts were rebuilt as regular files. `deps.log` records the five fresh first-path imports. The independent audit is `audits/GilletWaldhausenBasedCoverageIndependentAudit.lean`, with **34 actual-map, tagged-zero, arbitrary-universe and K₀ consumers**.

The narrow direct-import origin inventory contains **70** declarations (5+28+5+27+5), recursively permitting only `propext`, `Classical.choice`, and `Quot.sound`. This differs from the author's69 contribution to its large aggregate audit solely because the generated `Quillen.Waldhausen.KMap.congr_simp` is assigned to `BoundedTermsBasedStrata` in the narrow fresh import order. The same frozen sources are used; the extra generated declaration was also recursively audited. The initial fixed69 mismatch is preserved in `audit-initial-count69.log`, and the independent driver now fixes70.

The separate global-injectivity consequence and the change-of-weak-class fibration are outside these five sources.

The final successful audit is `audit.log`; `session.log` records both the original slot1 fresh rebuild and the fixed70 slot2 audit rerun. The fresh five-target paths are verified in `deps.log`. Replay script: `logs/verify-gillet-waldhausen-based-coverage-independent.sh`.
