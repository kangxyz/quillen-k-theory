# Global regular-scheme vector-bundle K = G

## Contract

The target is the original canonical `Quillen.Scheme.KToG X n`, induced by
inclusion of actual finite locally free sheaves into actual coherent sheaves.
The final comparison is in every nonnegative degree. Its hypotheses are:

- `Quillen.Scheme.IsRegular X`: X is locally noetherian and every actual
  structure-sheaf stalk is a regular local ring.
- `CompactSpace X`: quasi-compactness. Together with local noetherianity,
  this is the ordinary noetherian-scheme hypothesis.
- `Quillen.Scheme.HasResolutionProperty X`: every coherent sheaf is the
  quotient of an actual finite locally free sheaf.

The resolution-property predicate does **not** assume finite resolutions,
finite projective dimension, a uniform length bound, or any K-equivalence.
`hasResolutionProperty_iff_sheaf_epi` proves it is exactly the ordinary
ambient sheaf-epimorphism formulation. No vector bundle is assumed
projective in the global sheaf or global coherent category.

The regularity predicate does **not** use a homological definition:
`isRegular_iff_affineCharts` proves the actual stalk definition equivalent
to regularity of every actual affine chart ring. The proof uses open-immersion
stalk isomorphisms and the spectrum stalk/localization isomorphism.
`isRegular_spec_iff` identifies scheme regularity on Spec R with mathlib's
`IsRegularRing R`.

There is no finite Krull-dimension assumption. Every resolution bound depends
on the particular coherent sheaf. The theorem does not claim regularity
alone implies the resolution property. It does not replace vector-bundle
K-theory with perfect-complex K-theory.

## Construction

1. `VectorBundle/Locality.lean` transports actual finite local bases through
   the open-subscheme/over-site equivalence and composes their covering data.
   Jointly surjective open immersions, hence genuine affine covers, detect
   finite local freeness.
2. `Regular/KernelClosure.lean` proves kernel closure of coherent vector
   bundles by restricting actual short exact sequences to affine charts,
   applying finite-projective module kernel closure, and descending local
   freeness. This does not assert global splitting.
3. `Regular/ResolutionProperty.lean` constructs the actual coherent kernel
   of each vector-bundle quotient. Every noetherian affine scheme satisfies
   the resolution property by finite free module covers and the tilde
   equivalence, independently of regularity.
4. `Regular/AffineChartDimension.lean` uses actual restriction, the affine
   coherent/finite-module equivalence, and ambient module projective
   dimension. A bundle restricts to a projective module on each chart, so
   every chosen global coherent syzygy drops its chart dimension by one.
5. `Regular/ChartBounds.lean` uses the proved objectwise finite projective
   dimension theorem for regular affine rings. On a finite affine cover,
   the maximum of the bounds for one sheaf is finite.
6. `Regular/GlobalResolution.lean` iterates the actual global vector-bundle
   covers and coherent kernels. At bound zero the remaining sheaf is locally
   free on every chart and hence globally a vector bundle. The resulting
   finite resolution retains each actual conflation and its original target.
7. `Regular/GlobalComparison.lean` supplies these resolutions and kernel
   closure to the proved Quillen resolution theorem via the existing canonical
   small-model comparison. No new comparison map is substituted.

## Canonicality and affine consistency

- `KToG_regular_resolutionProperty_bijective` proves bijectivity of the
  existing comparison itself.
- `KToGRegularEquiv_toMonoidHom` is proved by `rfl`.
- `KToGRegularEquiv_restrict` retains actual geometric open restriction.
- `KToGRegularEquiv_spec` identifies the resulting equivalence on Spec R
  with the independently constructed `KToGRegularAffineEquiv R n`.

## Primary references

- Stacks Project, [Regular schemes, 28.9](https://stacks.math.columbia.edu/tag/02IR),
  especially the stalk and all-affine characterizations.
- Stacks Project, [The resolution property, 36.36](https://stacks.math.columbia.edu/tag/0F85),
  definition and its coherent-sheaf formulation on noetherian schemes.
- Stacks Project, [The resolution property and perfect complexes, 36.37](https://stacks.math.columbia.edu/tag/0F8D),
  for the geometric finite-resolution principle. The implementation above
  proves the sheaf case directly by affine projective dimension and kernels;
  it does not assume the derived-category result.
- Weibel, [The K-book, Chapter V](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf),
  Resolution Theorem 3.1, for the exact-category comparison.

## Verification

All eight source modules passed focused Lean checks. The declaration-closure
audit `audits/GlobalRegularResolutionAudit.lean` passed with exit code 0:
**83 declarations across all eight modules, using only standard Lean axioms**.
It checks every declaration whose source is one of the eight modules listed
in the source manifest and rejects axioms other than `propext`,
`Classical.choice`, and `Quot.sound`. It includes explicit endpoint examples
for the ordinary hypotheses, actual finite towers, definitionally unchanged
forward map, and agreement with the independent affine equivalence.

Focused check logs and the source SHA-256 manifest are stored under
`logs/global-regular-20261009/`. Parent-level independent review and aggregate
library verification are distinct from these focused checks.

Frozen source-manifest fingerprint (SHA-256 of
`logs/global-regular-20261009/sources.sha256`):

`b81f9540d535dd0f94533a8d2f15149ae5604e65a841823acfd3cc50c98da87c`

The final source-token audit passed. The aggregate layout check recorded an
unrelated concurrent change to
`Quillen/CategoryTheory/ExactCategory/SpecialFractions.lean`; the parent owns
its reconciliation. No global-RP source failed a layout/import check.
