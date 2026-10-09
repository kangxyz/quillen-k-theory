# Independent review: public scheme K and vector-bundle Q-model

Accepted 2026-10-09 04:36 UTC, after source review and a separate Lean rerun.
This endpoint is newer than the delivered 04:11 checkpoint.

## Mathematical contract

`SchemeSheaf.smallVectorBundleKEquiv X n` is an equivalence from the existing
public `Scheme.K X n` to `(vectorBundleExactStructure X).K n`, for any scheme
and any nonnegative degree. Its forward map is definitionally the separately
named `smallVectorBundleKMap`, induced by the actual exact small-model functor,
canonically normalized at zero.

The underlying small-model category and actual vector-bundle category have
hom universes `u+1` and `u` respectively. Both Q-categories already have object
and hom universes `u+1`, because a Q-arrow contains an apex object. Thus both
realizations live in the same universe. No arbitrary cross-universe
realization identification is asserted.

The generic `commonAmbientKEquiv` assumes a categorical equivalence of the
actual Q-functor. At the scheme endpoint this is supplied by the existing
proved exact small-model equivalence, which lifts admissible spans and
reflects the exact structure. It is not a hypothesized K-equivalence.
The based group equivalence uses the proved homotopy-fiber argument for an
ordinary homotopy equivalence whose forward map preserves the chosen point.
The inverse need not be assumed pointed.

## Independent checks

- Read both implementation modules and the small-model Q-equivalence,
  canonical rebasing and based-homotopy equivalence dependencies.
- Rebuilt the exact two-module closure with `lake --rehash`: 2,849 jobs.
- Reran a standalone recursive source-origin audit: all 34 declarations,
  including generated ones, use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Arbitrary-universe consumers check the original and small Q-category
  universes, actual KSpace universes, public endpoint, exact forward map,
  its bijectivity, and definitional agreement with the existing exact-functor
  K-map where the parameter ranges overlap.
- Source hashes matched before and after the independent rerun.

Sources: `Quillen/KTheory/Map/CommonAmbient.lean` and
`Quillen/Scheme/Comparison/SmallVectorBundleK.lean`.
Manifest: `logs/small-vector-bundle-k-sources.sha256`.
Consumer/audit: `audits/SmallVectorBundleKIndependentAudit.lean`.
Evidence: `logs/small-vector-bundle-independent-{build,audit,hashes}.log`.

This resolves the size-model alignment needed by the forthcoming geometric
Q/S comparison. It does not prove Q/S, Gillet–Waldhausen, strict/local
comparison, or TT localization.

## Public integration checks

The working public root rebuilt successfully (4,022 jobs). The independent
path-dependency consumer rebuilt successfully (3,998 jobs), and all 79 of its
declarations passed recursive standard-axiom checking. Its initial harness
needed the same local `Abelian.hasFiniteBiproducts` instance used by the
existing scheme consumer; only that harness was corrected. The retained
initial diagnostic is `logs/model-alignment-downstream-initial-diagnostic.log`.
Final evidence is `logs/model-alignment-{public-build,downstream-build,downstream-audit}.log`.
