# Independent review: exact K-equivalence and bounded-acyclic model

Accepted 2026-10-09, separately from the immutable 08:05 archive.

## Frozen scope and verification

The three sources in `logs/fibration-model-equivalence-sources.sha256` were read in full and freshly rebuilt into `logs/fibration-model-equivalence-independent-20261009/olean`. Unchanged dependencies were linked into that isolated namespace; the three reviewed artifacts are newly generated regular files. `deps.log` verifies the audit resolves all three reviewed modules to those fresh artifacts. No live source or artifact was changed by the review.

`audits/FibrationModelEquivalenceIndependentAudit.lean` checks exactly **37 declaration origins** (8 generic exact-equivalence, 22 concrete-model, 7 K-adapter), recursively allowing only `propext`, `Classical.choice`, and `Quot.sound`. Its **27 consumer examples** retain original functor/inverse KMaps, both inverse identities, concrete objects and chain maps, fine/coarse classes, genuine exactness and displayed pushouts, and the original inclusion K-map. All checks passed without warnings. Frozen sources and relevant dependency sources matched before and after.

Evidence: `logs/fibration-model-equivalence-independent-20261009/`; replay command: `bash logs/verify-fibration-model-equivalence-independent.sh` with the existing isolated dependency overlay.

## Semantic conclusions

- `KEquivOfExactEquivalence` uses a genuine categorical equivalence and genuinely exact functor and inverse. The inverse identities are derived from actual unit/counit natural isomorphisms via canonical `KMap_comp` and `KMap_eq_of_iso`. Forward and inverse are exactly the original KMaps.
- The generic statement has a common object universe for both categories and a common hom universe. It imposes no strict chosen-zero preservation. The concrete bounded-complex categories honestly meet this common realization-universe condition, including arbitrary underlying abelian-category object/hom universes.
- `boundedTermsNested` retains fine isomorphisms and coarse quasi-isomorphisms, with the same cofibration/zero data. The identity-on-complexes equivalence identifies actual bounded acyclic complexes with the actual coarse-acyclic full subcategory. Every original chain map and the original inclusion are retained.
- Cofibration preservation in the reverse direction is proved using the accepted actual inherited-inflation criterion. It is not inferred from categorical equivalence. That criterion derives the quotient's acyclicity from the actual short exact sequence, with no arbitrary cokernel-closure premise.
- Zero and pushout preservation legitimately use the actual equivalence, after cofibration preservation has been separately established. Fine weak maps remain isomorphisms.

This boundary identifies the two actual acyclic category models and their K-groups. The change-of-weak-equivalence homotopy-fiber theorem remains a separate open obligation.
