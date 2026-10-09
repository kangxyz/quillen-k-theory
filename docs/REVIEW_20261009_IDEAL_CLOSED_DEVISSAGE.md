# Independent review: arbitrary-ideal affine closed G-localization

Reviewed 2026-10-09, independently of the proof author. No proof source was changed.

## Checked mathematical contract

For a commutative noetherian ring `R` and **any** ideal `I`, the closed scheme is the actual `Spec(R/I)` and its morphism to `Spec R` is the actual quotient-induced closed immersion. The open term is the actual complement of `V(I)`; this open need not be affine. The result concerns the existing upper-universe public scheme G-groups, in every nonnegative degree, with the surjective G₀ tail.

The closed map on G-groups is induced by actual sheaf pushforward. The open map is the existing restriction map. The boundary is the existing supported-localization boundary transported through the proved closed-support equivalence. Neither a K/G equivalence nor comma-category contractibility is assumed in the endpoint's hypotheses.

## Semantic checks

- Restriction along `R → R/I` is explicitly constructed, fully faithful, exact, and essentially surjective onto precisely the I-annihilated finite modules. Its coherent-sheaf counterpart is constructed using actual sheaf pushforward and the proved global-sections comparison square.
- The I-annihilated category is not incorrectly declared Serre. The source explicitly separates it from the larger category of modules annihilated by a power of I.
- Actual stalk support gives the radical-annihilator criterion. Noetherian finite generation of I then supplies an objectwise uniform ideal-power bound. There is no exponent uniform over all coherent objects.
- Finite central-operator dévissage constructs genuine image filtrations. Refinement splices actual short exact sequences using pullbacks. The support representation proves the finite-generator predicate is exactly annihilation by all of I.
- Separately, `idealPowerFiltration` constructs the actual recursive `IM → M → M/IM` tower. The finite coherent-sheaf filtration is transported through the genuine affine equivalence, and its endpoint is identified with the original sheaf by the unit isomorphism.
- The annihilated equivalence is factored through the compatible small supported category. `closedSupportGEquiv_pushforward` and `closedSupportedGEquiv_pushforward` retain the original canonical pushforward map, including the exact-structure and small-model normalizations.
- All three adjacent exactness statements and G₀ surjectivity are transported from the proved global supported localization sequence. No arbitrary isomorphism is substituted for the actual pushforward or restriction.
- `Scheme.AffineClosedGTheory` is a thin facade over these checked statements and retains the actual closed/open schemes and canonical maps.

This implements the affine arbitrary-ideal case. It does not assert arbitrary nonaffine closed-immersion dévissage.

## Verification evidence

Exact source scope: `Devissage/{FiltrationRefinement,FiniteCentralFamily,FiltrationFunctor}`, `GTheory/FiniteModules/{IdealClosedSupport,IdealPowerFiltration}`, `Scheme/Coherent/ClosedImmersion/{IdealPushforward,IdealSupport,IdealSupportDevissage,IdealDevissage,IdealLocalization,IdealPowerFiltration}`, and `Scheme/AffineClosedGTheory`.

- Independent focused build: `logs/ideal-closed-independent-build.log` (3676 jobs, successful).
- Full exact-source-module dependency audits, including generated declarations and private helpers: `audits/IdealClosedDevissageIndependentAudit.lean`, `audits/AffineClosedPublicIndependentAudit.lean`.
- Audit logs: `logs/ideal-closed-independent-all-axioms.log`, `logs/affine-closed-public-independent-axioms.log`.
- Source fingerprints: `logs/ideal-closed-independent-sources.sha256`.
- The repository source-token audit also passed.

Final acceptance: **passed**. The main audit checks **357 declarations in 11 modules**; the public facade audit checks **10 declarations**. All depend only on `propext`, `Classical.choice`, and `Quot.sound`. All 12 source fingerprints matched after the checks. Manifest SHA-256: `600d71df3c710dc2ad22d979a4c3344c019e2897064695714961a86a479d71b9`.

Per-module counts: FiltrationRefinement 11; FiniteCentralFamily 9; FiltrationFunctor 4; module IdealClosedSupport 53; module IdealPowerFiltration 14; coherent IdealPushforward 69; IdealSupport 18; IdealSupportDevissage 31; IdealDevissage 79; IdealLocalization 61; coherent IdealPowerFiltration 8; public AffineClosedGTheory 10. No mathematical correctness blocker was found in the reviewed scope.
