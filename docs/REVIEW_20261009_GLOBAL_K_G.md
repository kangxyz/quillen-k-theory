# Independent review: global K/G foundations and principal closed dévissage

Date: 2026-10-09. Lean 4.34.0, pinned mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict

No mathematical correctness blocker was found in the source reviewed below.
The new constructions meet the substantive semantic gates: actual sheaf
categories, actual ambient exactness, explicit universe bounds, and actual
canonical maps. The independent post-restructuring focused build and kernel audit passed.
The kernel audit checked 8480 imported project declarations, including private
helpers, and found only Lean's standard logical foundations.

Accepted source-level milestones:

1. An actual abelian coherent-sheaf category and G-groups for every locally
   noetherian scheme, with exact geometric open restriction and genuine
   stalk-support categories.
2. An actual exact category of finite locally free sheaves on every scheme,
   with all ambient short exact sequences, and its upper-universe Quillen
   K-groups.
3. Principal closed dévissage for finite-module G-theory, including the
   canonical closed-to-supported K-isomorphism and the complete connective
   principal closed/open sequence.

These conclusions do not include the general noetherian-scheme restriction
quotient, arbitrary vector-bundle pullback, a K/G equivalence, a cross-universe
comparison, or enhanced/nonconnective perfect-complex localization.

## 1. Coherence tests every affine chart

`CoherentSchemeAffineProperty.affineFiniteSheaf R` means actual
quasicoherence together with finite generation of the actual global-sections
module on `Spec R`. Its definition does not require `R` to be noetherian.
For a noetherian ring, `affineFiniteSheaf_eq_essImage` identifies this property
with the essential image of the existing actual coherent inclusion. Exactness
of that inclusion proves closure under ambient finite limits and colimits.

`CoherentSchemeGlobal.coherent X` tests this predicate on every actual open
immersion `Spec R → X`. No noetherianity condition filters the charts. In
particular, it is not a vacuous predicate imposed only on a selected class
of charts whose hypotheses might be impossible. Under `IsLocallyNoetherian X`,
`noetherian_affineChart` proves that each such ring is noetherian, by pulling
local noetherianity back along the open immersion and applying the affine
criterion.

Finite limits and colimits of coherent objects are tested after actual
restriction to each affine chart. Restriction preserves those limits and
colimits; the affine result then proves the global closure. Kernels and
cokernels are actual ambient kernels and cokernels. The resulting full
subcategory is genuinely abelian, and `coherent_shortExact_iff` identifies
its exact sequences precisely with short exact sequences of the underlying
module sheaves.

No assertion of closure under arbitrary subobjects of all module sheaves is
introduced. The coherent category is not incorrectly declared to be a Serre
subcategory of all sheaves.

The additional `CoherentSchemeGlobalPresentation` module proves the one-way
comparison with actual upstream finite presentation. A finite module has a
finite generating family, and noetherianity makes the kernel of its finite
free presentation finitely generated. These actual finite presentations are
transported from affine charts to the over-site using the restriction
composition isomorphisms and the actual structure-sheaf unit isomorphism of
the over-site equivalence. The family of all affine opens is an actual cover,
so `coherent_finitePresentation` constructs finite local presentation data.
Consequently the underlying sheaf is genuinely quasicoherent in the upstream
sense. The converse comparison is not silently asserted.

## 2. Global G-theory, exact open restriction, and support

`CoherentScheme.G X n` uses the standard abelian exact structure of that
actual full category. The model is explicitly `SmallModel.{u+1}` for a scheme
in `Scheme.{u}`. Its essential-smallness instance is legitimate at the actual
sheaf-object universe. It is not a proof of essential smallness in universe
`u`.

`coherent_restrict` composes affine charts and transports along the actual
restriction-composition isomorphism. `coherentRestriction` is the lift of
ordinary geometric sheaf restriction, and its composite with the full
inclusion is definitionally that underlying functor. Its finite-limit and
finite-colimit preservation are reflected by the target coherent inclusion.
Thus `coherentRestrictionExact` and `restrictionGMap` are the genuine exact
functor and canonical small-model K-map.

`coherentSupportedAway` means actual vanishing after restriction. It is
Serre inside the coherent category. `coherentRestriction_kernel_eq_support`
identifies the exact kernel, and `coherentSupportedAway_iff_support_subset`
identifies its ordinary stalk-support meaning. `SupportedG` therefore uses
an actual supported coherent category, again explicitly in universe `u+1`.

An exact restriction functor with the correct Serre kernel does not by itself
prove a Serre quotient equivalence. The general global coherent extension,
fullness/fraction, and quotient proofs remain outside these files.

## 3. Vector-bundle exactness is locally split, not globally split

`SchemeFiniteSheaves.IsFiniteLocallyFree` requires one covering family of
actual local bases with finite index types. The pointwise equivalence in
`VectorBundleLocalBases` uses that same finite-basis data; it does not weaken
the predicate to unrestricted local freeness.

`VectorBundleSheafEpi` proves that forgetting module structure to additive
sheaves preserves colimits, by using presheaf colimits and sheafification.
It then obtains local surjectivity of epimorphisms. It does not assume that
an epimorphism is surjective on sections of every fixed open.

`exists_finite_local_lifts` lifts a finite family of sections on a common
neighborhood. The neighborhood is intersected with the original open,
including for an empty family of basis elements. The free-sheaf universal
property turns these lifts into a local right inverse in
`exists_local_section_of_finite_basis`. Restriction to the site over an open
is exact, so `exists_local_splitting` proves local splitting of an actual
short exact sequence with finite locally free quotient.

`finiteLocallyFree_of_shortExact` chooses bases for both endpoints, shrinks
to their common neighborhood, obtains a local splitting, and constructs the
middle-term basis from the sum of the endpoint bases. This proves genuine
ambient extension closure. The `ExactSubcategory` adapter uses that closure
to prove the exact-category axioms, including admissible pushouts, pullbacks,
and composition; it does not demand arbitrary vector-bundle kernels or
cokernels.

Most decisively, `vectorBundleExactStructure_conflation` is the reflexive
identity between the chosen conflations and actual ambient sheaf short exact
sequences. There is no global splitting condition. No noetherianity,
quasi-compactness, separatedness, or regularity assumption is needed.

`VectorBundleKTheory.SchemeK` uses this exact category in the explicitly
chosen `u+1` small universe. Its small-model conflation theorem still tests
actual sheaf exactness. `schemeKToModuleSheafK` targets K-theory of all module
sheaves; the code explicitly does not rename that target coherent G-theory.
Independence of exact presentations in a common small universe is available
from `presentationKEquiv`. Equality of realizations across different
universes is not claimed.

### Actual open restriction of vector bundles

`VectorBundleRestriction` transports the local basis presentations through
exactly the continuous-site construction implementing geometric open
restriction. The free basis maps remain isomorphisms and the generator index
types are unchanged, so finite local freeness survives. Its general helper
requires the relevant continuous/cocontinuous site functor, left-adjoint
structure, and isomorphic structure-sheaf map; the geometric application
actually constructs and discharges those hypotheses for an open immersion.

`vectorBundleRestrict_comp_forget` is a reflexive identity with the actual
underlying geometric restriction. `vectorBundleExactRestrict` preserves the
inherited conflations by ambient sheaf exactness, and `schemeKRestrict` is its
canonical small-model K-map. These results are open-restriction statements;
they do not yet prove pullback along arbitrary scheme morphisms.

## 4. Principal closed dévissage is not a category equivalence with support

`FiniteModuleClosedSupport` uses the actual quotient ring
`ClosedRing f = R/(f)`. Its `closedRestriction` is the actual restriction of
scalars along the quotient map. Fully faithfulness recovers quotient-ring
linearity from R-linearity using the surjectivity of the quotient map.
Essential surjectivity onto killed objects constructs their actual quotient
module structure. Consequently `closedEquivalence` is an equivalence only
with finite modules killed by `f`.

Restriction of scalars is exact for the standard finite-module abelian
structures under the noetherian hypothesis. The killed subcategory is
abelian and its inclusion is exact. It is not claimed to be extension closed
or Serre in all finite R-modules: an extension can instead be killed by a
higher power of `f`.

`PrincipalSupportDevissage` proves a general statement for a natural
endomorphism of the identity on an abelian category. The killed-object
property contains zero and is closed under subobjects, quotients, and finite
products. The finite filtration uses actual image inclusions and cokernels.
On the image of the endomorphism, the vanishing exponent decreases by one;
the quotient by that image is killed. The exponent-zero case requires and
proves that the object is zero. No uniform exponent across all objects is
assumed.

For principal support, a fully faithful representation in finite R-modules
pulls back multiplication by `f`. The existing uniform annihilation theorem
for each finite supported module supplies its exponent. The resulting
`principalFiltrationHypothesis` discharges the genuine classical dévissage
hypothesis, and `principalDevissageKEquiv` applies the already proved
homotopical theorem in every nonnegative degree, including homotopical G₀.
Its forward homomorphism is exactly the canonical inclusion-induced K-map.

`ClosedAffineGDevissage` first transports quotient-ring restriction to the
chosen small models and proves an exact equivalence onto the killed support
objects. It then composes this equivalence with the proved dévissage
isomorphism. `closedSupportGEquiv_toMonoidHom` identifies the resulting
forward map with `closedSupportedKMap`, the actual closed-to-supported exact
functor's K-map. `closedSupportGEquiv_pushforward` proves compatibility with
the original canonical closed pushforward, including small-model and
zero-object normalizations.

The three range/kernel identities and final G₀ surjectivity are assembled in
`principalClosedLocalization_longExact`. The boundary is the existing
localization boundary followed by the inverse of the proved canonical
closed-to-supported isomorphism. Neither an arbitrary chosen group
isomorphism nor an unproved categorical equivalence with all supported
objects replaces this argument.

This endpoint is presently expressed in finite-module G-theory over
`R/(f)`, `R`, and `R[f⁻¹]`. Its closed map is actual quotient-ring restriction
of scalars. A formal comparison with the actual sheaf pushforward along
`Spec(R/(f)) → Spec R`, or transport into the new upper-universe global G,
is a further theorem. The already established affine-module/affine-sheaf
comparisons should not be taken as an implicit proof of that missing
closed-pushforward compatibility.

## Remaining scope gates

- Prove the converse from upstream finite presentation to global affine-local
  coherence, and compare with the earlier affine coherent category.
- Prove any desired smaller-universe essential smallness and cross-universe
  K comparison. The upper-universe definitions are valid without them.
- Prove the actual global coherent restriction quotient equivalence and its
  canonical localization sequence for the intended noetherian schemes.
- Compare vector bundles on an affine with finite projective modules, and
  establish arbitrary-morphism vector-bundle pullback and its coherence.
- Construct the actual vector-bundle-to-coherent exact inclusion before
  claiming a K-to-G comparison. Resolution equivalences need further
  hypotheses and proof.
- Prove geometric closed-pushforward compatibility and general ideal-power
  dévissage separately from the principal finite-module endpoint.
- Keep perfect complexes, derived/proper pushforward, nonconnective tails,
  and perfect-localization comparisons separate.

## Verification evidence

After the coordinated library relocation restored consistent canonical-module
and compatibility-import caches, the independent focused build of
`CoherentSchemeGlobalRestriction`, `VectorBundleRestriction`, and
`ClosedAffineGDevissage` completed successfully with **3595 jobs**. Its
warnings were linter/style diagnostics, not proof errors.

The independent combined kernel audit explicitly printed dependencies for the
central category, exactness, universe-bound, support, local-splitting,
restriction, nilpotent-filtration, canonical-map, and long-exact-sequence
endpoints. It additionally traversed **8480 imported project declarations,
including private helpers**, rejecting every dependency except `propext`,
`Classical.choice`, and `Quot.sound`. It passed. The recursive source-token
audit also passed.

The supplemental finite-presentation module independently built successfully
with **3057 jobs**. Its separate kernel audit checked six explicit endpoints
and **1351 imported project declarations**, again with only `propext`,
`Classical.choice`, and `Quot.sound`. It passed.

The initial pre-relocation global/vector focused build had also passed with
3083 jobs. A subsequent audit and closed build crossed the library-migration
cache transition and were stopped. Those incomplete diagnostic logs are
retained, but are superseded by the successful final evidence above; they are
neither proof failures nor substitute verification.

Final evidence:

- `logs/global-k-g-independent-final-build-20261009.log`
- `logs/global-k-g-independent-full-audit-20261009.lean`
- `logs/global-k-g-independent-final-axioms-20261009.log`
- `logs/global-k-g-independent-final-source-token-audit-20261009.log`
- `logs/global-k-g-independent-source-hashes-20261009.json`
- `logs/global-k-g-independent-presentation-build-20261009.log`
- `logs/global-k-g-independent-presentation-audit-20261009.lean`
- `logs/global-k-g-independent-presentation-axioms-20261009.log`

The source hashes cover the reviewed canonical modules and their compatibility
imports. Names used in the review remain available through those compatibility
imports; implementation files now also live under the hierarchical public
library layout.

These focused checks do not replace the integrator's final aggregate build
and aggregate declaration audit after all subsequent modules and public
imports are settled. Only this review and its audit inputs/logs were written
by the reviewer. Implementation sources were not changed. No publication was
performed.

## Import-path update

This review predates the canonical-only cleanup. References to compatibility
imports describe the historical checked tree; those aliases have now been
removed. Current source paths are recorded in `module-migration.json` and the
canonical implementations retain the reviewed proof bodies.
