# Actual based finite-stage K-coverage

## Five-source structural boundary

- `Topology/FilteredRealization/BasedGroups.lean` proves jointly surjective
  original finite homotopy maps and eventual equality/one detection for an
  actual filtered simplicial colimit with strictly compatible actual points.
  The proof reuses actual compact based-cube factorization and relative
  boundary homotopy lifting. No transition equivalence or realization-map
  injectivity is assumed.
- `BoundedTermsBasedStrata.lean` and `BoundedAcyclicBasedStrata.lean` give
  genuine Waldhausen structures on the existing symmetric bound strata,
  using precisely the raw filtered diagram's inverse-image isomorphisms and
  the tagged ambient chosen zero. Original transition and inclusion functors
  retain these zero objects literally. Original exact identity functors
  relate these models to the original inherited isomorphism models. The
  commuting original public KMaps and identity inverse are proved.
- `BoundedTermsKCoverage.lean` and `BoundedAcyclicKCoverage.lean` apply the
  proved filtered simplicial colimit to those actual points and transport
  the conclusions through the exact identities. Their statements use the
  original canonical public KMaps of the original inherited models.

For both bounded terms and bounded acyclic terms, the APIs are
`boundedTerms_KMap_jointlySurjective`, `boundedTerms_KMap_eq_eventually`,
`boundedTerms_KMap_eq_one_eventually`, and the corresponding names with
`boundedAcyclic`.

Every global K-class comes from one genuine symmetric finite-term stratum.
Two original classes from one stage with equal global images have equal
images under an actual later transition KMap. In particular, any stage class
with global image one becomes one in a later stage. These are all degrees,
including K₀, and are not a categorywide uniform-bound assertion.

For these five modules A is an abelian category with independent object and
hom universes. P contains zero, is replete, and is extension-closed. Kernel
closure, projectivity, a stagewise K-equivalence, or fibration is not required.

## Separate two-source injectivity consequence

`FiniteCycleInclusion.lean` uses the accepted actual adjacent-cycle incidence,
the genuinely zero lower cycle, and the actual finite cycle equivalence to
prove `finiteAcyclicTermsInclusion_KMap_injective` for every specified finite
interval, including empty intervals. It detects cycles recursively from the
original term coordinates; it does not assume the inclusion is zero.

`AcyclicInclusionInjective.lean` proves the actual finite/global inclusion
squares and transition squares on original KMaps. Actual stage representation
and eventual-zero detection then reduce the global kernel to one of these
proved finite kernels. The endpoint is
`boundedAcyclicTermsInclusion_KMap_injective P k`: the original inclusion of
bounded acyclic termwise-P complexes into bounded termwise-P complexes is
injective on the original isomorphism-model K-group in every degree,
including K₀.

These two modules additionally require the proved structural kernel closure
of P and the explicit compatible mixed universe `A : Type (max u v)` with
`Category.{v} A`. Arbitrary schemes specialize using the already proved
ambient finite-locally-free kernel closure and explicit levels `{u,u+1}`.
No fibration or global graded equivalence is an input. The quasi-isomorphism
model and the actual change-of-weak-equivalences fibration remain separate.

## Verification

The five-source manifest is
`logs/gillet-waldhausen-based-coverage-checked-sources.sha256`.
All five focused builds are warning-free. The separate two-source consequence also builds warning-free, with manifest
`logs/gillet-waldhausen-inclusion-injective-checked-sources.sha256`.
The combined actual-map and source-origin audit is `audits/GilletWaldhausenBasedCoverageAudit.lean`, with raw log
`logs/gillet-waldhausen-based-coverage-axioms.log`; its terminal fixed1022 counter passed, all consumers passed, and the raw log
has no warnings, errors, or `sorryAx`. Only `propext`, `Classical.choice`,
and `Quot.sound` occur recursively. New coverage5 contributes 69 origins
(5+27+5+27+5), and injectivity2 contributes 12 (8+4). The actual
arbitrary-scheme theorem consumer also has exactly those standard axioms.
All seven and the previously frozen forty source hashes match. Independent coverage5 review passed fresh5 rebuilding, a fixed70
narrow-import audit and 34 strengthened exact-map/zero/universe/K₀ consumers.
The difference from the aggregate69 attribution is the generated
`KMap.congr_simp`, attributed to `BoundedTermsBasedStrata` only in the narrow
import order; both checks audit its actual dependencies. The report is
`docs/REVIEW_20261009_GW_BASED_COVERAGE.md`. Independent injectivity2 review also passed fresh2 rebuilding, fixed12
origins and 16 strengthened actual-map/empty-interval/K₀/arbitrary-scheme
consumers. Its report is `docs/REVIEW_20261009_GW_INCLUSION_INJECTIVITY.md`.
