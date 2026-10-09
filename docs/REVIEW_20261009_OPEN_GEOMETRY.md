# Independent review: K-to-G comparison and general-open geometry

Review date: 2026-10-09 (UTC), finalized at 01:58. Toolchain: Lean 4.34.0.

## Verdict and scope

- **Accepted:** `Scheme/Comparison/AffineFinite.lean` and `Scheme/Comparison/KToG.lean`. They prove the genuine finite-vector-bundle-to-coherent-sheaf comparison map, including naturality under actual geometric open restriction.
- **No K=G equivalence is claimed or inferred.** Constructing the exact inclusion and its K-map does not prove a resolution theorem or an isomorphism on K-groups.
- **Accepted open geometry:** all thirteen frozen modules through `AffineSectionsGlobal` and `AffineSectionsEquivalence`, with a 3086-job targeted build, direct source elaboration of every module, and 60 named declaration axiom checks. Actual quasicoherent pushforward is proved for every quasi-compact open immersion, with the locally-noetherian-target corollary. An independent consumer discharges the earlier conditional fullness hypothesis with this theorem. `Fullness.lean` additionally passes its 3085-job target build, direct-source check, and cumulative 63-declaration audit. The actual support-quotient functor is therefore unconditionally full, faithful, and exact.
- **Still separate:** coherent extension of arbitrary objects, essential surjectivity, the actual general-open quotient equivalence, and the associated global localization sequence.
- This review does not modify mathematical source files, umbrella imports, existing audit scripts, integration roots, or publication state. Its only writes are this report and review-specific evidence under `logs/review-20261009/`.

## Reproducible verification

From the repository root, run:

```sh
bash logs/review-20261009/verify-k-to-g.sh
bash logs/review-20261009/verify-open-geometry.sh
bash logs/review-20261009/verify-open-fullness.sh
bash logs/review-20261009/verify-local-isomorphisms.sh
```

These scripts set the known shared Lean toolchain, build the exact targets, directly elaborate each reviewed mathematical source, compile an independent audit source, and run the recursive placeholder scanner. The logs record source SHA-256 hashes and the actual toolchain version. The checked proof dependencies must be a subset of `propext`, `Classical.choice`, and `Quot.sound`.

K-to-G evidence:

- `logs/review-20261009/k-to-g-validation.log`: target build (3110 jobs) and direct elaboration of both frozen source files; includes the initial independent harness's missing local biproduct-instance diagnostic.
- `logs/review-20261009/k-to-g-consumer-and-axioms.log`: corrected independent consumer and eight semantic-root axiom checks, all passing, followed by a passing recursive source-token audit.
- `logs/review-20261009/k-to-g-clean-verification.log`: clean end-to-end rerun, including all 27 named declarations in the two new modules, all passing.
- `logs/review-20261009/ReviewKToG20261009.lean`: reproducible consumer and full declaration audit.

The consumer explicitly checks the no-noetherian affine finite-type theorem, the unchanged underlying object and morphism of the inclusion, the definitional equality with the actual exact inclusion's `smallKMap`, and the pointwise open-restriction square. When spelling `smallKMap` explicitly it uses the repository's existing `attribute [local instance] Abelian.hasFiniteBiproducts` convention. The initial omission of this attribute was a review-harness issue, not a proof failure or a hidden mathematical hypothesis.

Open-geometry evidence:

- `logs/review-20261009/open-geometry-validation.log`: first nine frozen modules, all 49 named declarations, passing.
- `logs/review-20261009/open-geometry-all-validation.log`: all thirteen frozen modules, all 60 named declarations, direct-source checks, independent unconditional-fullness consumer, and recursive token audit, all passing.
- `logs/review-20261009/ReviewOpenGeometry20261009.lean`: exact source of the independent examples and 60 axiom queries.
- `logs/review-20261009/open-fullness-validation.log` and `ReviewOpenGeometryFullness20261009.lean`: the passing final check of the three unconditional declarations exported by `Fullness.lean`, including 63 cumulative axiom queries.

## K-to-G semantic review

### Affine finite sections

`finite_globalSections_of_localGenerators` tests the actual global-section module at principal localizations. For each point it refines the given local-generator cover to a contained principal affine open. The finite generators are transported through the genuine over-site/restriction equivalence and restricted without changing the finite index set.

On the principal affine, finite global generators give finite sections through the actual tilde equivalence. Quasicoherence identifies the original affine sheaf with the tilde of its global sections. The comparison with principal restriction is the existing proved `restrictionGlobalSections_isLocalized`, not an arbitrary replacement module.

The set of successful principal elements spans the unit ideal because their basic opens cover the spectrum. `Module.Finite.of_localizationSpan'` then descends finite generation. There is no globally free assumption, no noetherian hypothesis, and no assumption that every open is principal. The finite-type corollary obtains real local generators; the finite-locally-free corollary uses the already-established finite local basis predicate.

### Actual categories, exact structure, and map

`coherent_of_finiteLocallyFree` applies the affine result to every actual affine open chart. Its object-property conclusion is valid without noetherianity; the exact-category comparison uses locally noetherianity, as its statement declares.

`vectorBundleToCoherent` is `ObjectProperty.ιOfLE`. Its object and morphism maps leave the underlying module sheaf and map unchanged. The source conflations are all ambient sheaf short exact sequences, using the previously proved local-splitting extension closure. They are not artificially restricted to globally split sequences. The target exact structure is the ordinary abelian coherent-sheaf structure. `vectorBundleToCoherent_shortExact_iff` identifies the two via the actual ambient inclusion.

`schemeKToG` and public `Scheme.KToG` are definitionally the `smallKMap` of this actual exact inclusion. Both source and target are the already-proved genuine upper-universe small-model theories, rather than arbitrary groups identified by type aliases. No cross-universe comparison is hidden here.

### Naturality

Both sides restrict by the genuine geometric sheaf restriction. The underlying inclusion/restriction square commutes definitionally. The induced group-level equality follows from actual small-model composition and natural-isomorphism invariance. No naturality law is postulated as extra quotient data.

## Frozen general-open modules: semantic findings

### `Denominators.lean`

The support class is the genuine kernel of coherent restriction, already identified with ordinary stalk support in the complement. An actual coherent morphism is inverted precisely when its coherent kernel and cokernel belong to this support Serre class.

For maps agreeing over the open, the denominator is concretely `kernel.ι (f - g)`. Exact restriction makes this kernel inclusion an isomorphism over the open. Thus the equality/cancellation result is a geometric coherent-subsheaf witness, not a presumed fraction calculus or a fabricated localization witness.

### `Quotient.lean`

`CoherentSupportQuotient` is the constructed localization of the actual coherent category at those supported-Serre denominators. `quotientCoherentRestriction` is its universal lift of actual coherent restriction. Its factorization is a proved strict equality, with a corresponding natural isomorphism.

Faithfulness is proved on **all quotient morphisms** through the Serre class's actual left calculus of fractions. The reduction on original maps uses the coherent kernel denominator above; it does not merely prove injectivity for original maps and rename that faithfulness. Additivity and finite-limit/finite-colimit preservation descend through the actual Serre quotient. The image-support criterion concerns the actual coherent image sheaf.

This module deliberately does not prove fullness or essential surjectivity.

### `Subobjects.lean` and `QuasicoherentClosure.lean`

The finite-subobject argument explicitly requires the subobject to be quasicoherent. On a noetherian affine, global sections of a monomorphism are injective and a submodule of a finite module is finite. The global result checks every affine chart. There is no false claim that an arbitrary subobject in all module sheaves is coherent.

Quasicoherence is recognized by actual affine presentations and the affine-open cover. Closure under ambient finite limits and colimits is transported through exact affine restriction and the actual affine quasicoherent inclusion. The resulting kernel/cokernel theorems use no open-pushforward theorem and no quotient-equivalence assumption.

### `GraphFractions.lean`: accepted conditional reduction

The hypothesis is precisely coherent subobject extension, with compatibility of the actual inclusion after restriction. The proof extends the actual graph inside the coherent biproduct. Its first projection is invertible on the open, hence is an actual supported-Serre denominator; its second projection supplies the numerator. The induced fullness proof uses genuine quotient fractions.

The hypothesis remains visible in the theorem statement. This is not itself a proof of geometric extension or a localization equivalence.

### `SubobjectExtension.lean`: accepted conditional construction

For a coherent monomorphism `A → H|U`, the proposed extension is exactly the ambient sheaf kernel of the adjoint map

```text
H → j_* coker(A → H|U).
```

Restriction, the open-immersion adjunction counit, and the universal property of kernels identify its restriction with `A` and prove compatibility with the inclusion. Quasicoherence of that one pushforward is a visible input. Quasicoherent kernel closure plus the noetherian subobject lemma then prove the extension coherent.

The general pushforward-quasicoherence hypothesis in `quotientCoherentRestriction_full_of_quasicoherent_pushforward` is likewise explicit. It is not silently installed as an instance and is not confused with an unconditional global-open theorem.

### `FiniteApproximation.lean`

Finite sets of localized generators have finitely many chosen numerators. Their span gives a finitely generated submodule whose localization is the desired finite localized module or the specified finitely generated localized submodule. In the exact-submodule version, the reverse inclusion is proved by clearing the chosen denominators and using closure of the target submodule under scalars. The finite-family theorem takes a finite supremum of the chosen submodules.

These are genuine algebraic approximation results without noetherianity. They do not alone construct a global coherent subsheaf or a compatible global extension across multiple affine charts.

### `AffineSections.lean`: finite compact-cover and actual gluing

`ClearsDenominators` records both existence of local numerators and the torsion/uniqueness condition for **actual sheaf restriction**. Its localization equivalence also proves invertibility of the element on the intersected principal open.

For a finite cover, the proof first raises every local numerator to one common exponent. It then restricts their discrepancies to pairwise overlaps. These discrepancies vanish after localization, so the overlap torsion conditions kill them after further powers. A second common exponent makes all numerators agree on every overlap. Only then does the proof invoke the actual sheaf gluing axiom. It separately proves the global torsion statement by a finite maximum and sheaf separatedness.

For a compact open of an affine scheme, the basic-open basis supplies a genuinely finite cover. Pairwise overlaps are `D(g_i g_j)`; their required quasicoherence comes from contained principal-chart restrictions. The final theorem assumes quasicoherence only on the selected open. It does not require or infer quasicoherence on the ambient affine outside that open.

Thus the critical overlap correction is present, compactness is used exactly for the finite exponent bounds, and there is no circular assumption of quasicoherence of an open pushforward.

### `AffineSectionsPushforward.lean`

Section comparison maps are isomorphisms because the inverse-image opens are equal, with the actual pushforward presheaf formulas checked. Quasicoherence of restriction of an open pushforward back to its domain follows only from the genuine adjunction counit isomorphism and quasicoherence of the original sheaf.

This is valid without assuming that the pushforward is quasicoherent on the target. It is the needed non-circular input for the compact-affine pushforward argument, not the conclusion being smuggled into a helper.

### `AffineSectionsQuasicoherent.lean`: pushforward quasicoherence is a conclusion

Write `N = j_* F`. The restriction of `N` to the image of the open immersion is quasicoherent by the actual counit and the domain/image isomorphism. The compact-open section theorem therefore applies to `N` on that image without knowing that `N` is quasicoherent elsewhere.

The restriction maps from the ambient affine to the image, and from a principal open to its intersection with that image, are isomorphisms because their inverse-image opens agree. They identify the compact-open localization map with the actual affine-principal restriction map for `j_* F`. The standard affine localizing criterion then proves `j_* F` quasicoherent. Both numerator extension and torsion corollaries refer to actual pushforward sections and actual restriction maps.

### `AffineSectionsBaseChange.lean`: actual natural base change

The natural isomorphism compares `j_*` followed by restriction to an open chart with restriction to the true pullback followed by its pushforward. The general `j` need not be an open immersion in this auxiliary theorem; the chart morphism is open, so the pullback projection used for restriction is open.

The relevant adjunction unit is proved invertible sectionwise. The key equality says its image/preimage open is the original inverse-image chart open, using the actual pullback projection's open range. All remaining steps are the genuine pushforward composition/congruence isomorphisms and the open-restriction counit. Neither quasicoherence nor any localization equivalence is assumed.

### `AffineSectionsGlobal.lean`: unconditional geometric endpoint

For a quasi-compact open immersion `j`, its base change to every affine chart is quasi-compact. Because that chart is compact, the source of the base-changed morphism is compact, and its image is a compact open. The affine pushforward theorem applies. Actual open base change transports this quasicoherence to the chart restriction of `j_* M`, and proved affine-chart recognition finishes the global statement.

The locally-noetherian-target corollary uses the pre-existing theorem that an open immersion into a locally noetherian scheme is quasi-compact (mathlib `AlgebraicGeometry/Noetherian.lean`, lines 205–218). It does not silently replace local noetherianity by global noetherianity or require the entire target to be compact.

The independent consumer imports the new modules and derives quotient fullness directly from this actual theorem, without a caller-supplied pushforward-quasicoherence premise. Therefore the formerly conditional geometric premise really has been discharged.

### `AffineSectionsEquivalence.lean`: canonical section-localization equivalence

`localizationEquiv` is the actual localized-module universal equivalence for the proved restriction map. Its generator formula explicitly sends the localization image of a section to that section's genuine restriction. It is an `R`-linear equivalence in the declared universe, with the compact-open and restricted-quasicoherence hypotheses visible. No abstractly chosen isomorphism substitutes for the canonical map.

### `Fullness.lean`: unconditional exported subobject extension and fullness

All three named exports are accepted. `coherent_subobject_extension` supplies the previously explicit pushforward-quasicoherence input using the actual global theorem, with quasicoherence of the actual cokernel proved first. `coherent_exists_fraction` specializes the graph construction. The `quotientCoherentRestriction_full` instance similarly discharges its formerly conditional input. These statements contain no remaining geometric extension assumption and combine with the existing faithful exact quotient functor.

The codomain is still all coherent sheaves on the open, and the source is the genuine support quotient. Full faithfulness does not assert that every codomain object is in the essential image.

### `LocalIsomorphisms.lean`: actual stalk and cover recognition

Accepted independently after a 3086-job target build, direct source elaboration, and all three declaration axiom checks (standard axioms only). The criterion uses actual underlying abelian-group stalk maps. A sheaf map whose stalk maps are isomorphisms becomes an isomorphism of underlying sheaves, then of module presheaves, and finally of module sheaves via reflection. The open-restriction criterion transports through the actual natural stalk-comparison isomorphism. The covering-family theorem only assumes actual pointwise coverage; it needs no compactness or quasicoherence hypothesis.

Evidence: `logs/review-20261009/local-isomorphisms-validation.log` and `ReviewLocalIsomorphisms20261009.lean`.

## Explicitly not covered by this completed review

The developing modules `AffineApproximation.lean`, `GluingLocality.lean`, and `GluingSubobjects.lean`, and any later finite-affine-cover induction, coherent-object extension, essential-surjectivity, quotient-equivalence, or global localization-sequence modules are **not accepted by this report**. They require their own frozen-source semantic and kernel review. This completed report accepts the K-to-G comparison, the compact-open/QC-pushforward stack, actual quotient full faithfulness/exactness, and `LocalIsomorphisms.lean` only.

## Remaining boundary

At this reviewed stage, the general-open route still distinguishes:

1. The finite-cover affine section-localization theorem, proved above.
2. Quasicoherence of actual open pushforward, now proved from that theorem and actual open base change.
3. Coherent subobject extension and quotient fullness, now proved and exported unconditionally in the independently checked `Fullness.lean`.
4. Extension of arbitrary coherent objects, not supplied merely by subobject extension into an already-global coherent ambient object.
5. Essential surjectivity, the actual quotient equivalence / `IsLocalization` identification, and a consequent general-open localization sequence.

Neither K-to-G nor any reviewed conditional helper closes steps 4–5 by itself. A future accepted final theorem must discharge all geometric inputs and retain an explicit comparison with actual restriction and actual support.
