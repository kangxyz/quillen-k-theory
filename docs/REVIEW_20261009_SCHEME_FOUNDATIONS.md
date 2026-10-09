# Independent review: scheme foundations

Date: 2026-10-09. Reviewed against Lean 4.34.0 and pinned mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict and accepted scope

No mathematical correctness blocker was found in the checked foundation
modules below. The affine G-groups genuinely use coherent sheaves on
`Spec R`, their ambient sheaf exact sequences, and actual small models. They
are not K-groups of all module sheaves under a different name.

This is an affine/noetherian G-theory foundation milestone. It does not yet
prove vector-bundle K-theory, G-localization for open subschemes, non-affine
coherent closure, or a perfect-complex localization theorem.

## Semantic checks

### Exact equivalences, Q, and zero-based K-maps

`ExactEquivalence.ofEquivalence` defines a conflation precisely when its
image under the actual forward equivalence is a conflation. Kernel and
cokernel properties are reflected through that equivalence. Admissible
pushouts and pullbacks are transported using preserved universal properties;
they are not extra assumptions in a purported equivalence result.

In `ExactEquivalenceKTheory`, Q-faithfulness pulls back the apex isomorphism
of two spans. Q-fullness chooses an actual preimage of the span apex, pulls
back both legs, and uses the explicitly required reflection of inflation
and deflation. Essential surjectivity uses actual object isomorphisms.
Thus `mapQ_isEquivalence_of_equivalence` has genuine constructive content.

`KEquivOfMapQIsEquivalence` is `MulEquiv.ofBijective` applied to the existing
`KMap`. Its forward-map theorem is reflexive equality. The homotopy
equivalence is for the zero-normalized Q-functor, and
`KMap_bijective_of_homotopyEquiv` checks the actual zero-basepoint equality.
There is no replacement by a freely chosen isomorphism or an unproved
strictly based inverse.

### Size and exact structures on small models

`SmallModelExact` uses mathlib's `SmallModel.{w} C`, whose objects and
morphisms are both in universe `w`, under the explicit
`EssentiallySmall.{w} C` hypothesis. The additive and exact structures and
the two comparison functors come from the actual categorical equivalence.
`SmallModelAbelian` proves that transporting a standard abelian exact
structure yields the standard abelian exact structure of the small model.

`presentationKEquiv` proves independence between presentations in a common
small universe, with precisely the comparison functor's canonical K-map as
its forward map. This is not a comparison of the small realization with a
larger raw realization. No such cross-universe topological comparison is
claimed. The affine smallness proof ultimately uses finite modules
represented by quotients of finite free modules, rather than a hidden
essential-smallness assumption for all sheaves.

### Actual sheaf restriction and stalk support

`SchemeSheafExact` uses the actual `Scheme.Modules` category and actual
`Scheme.Modules.restrictFunctor` along an open immersion. Restriction has
the requisite two adjoint descriptions, hence is additive and exact.
Its kernel is a genuine Serre class. The actual restriction functor is a
localization because its pushforward right adjoint is fully faithful.
This is explicitly an ambient all-module-sheaf result.

`SchemeSheafSupport` defines ordinary support by nonzero underlying
abelian-group stalks, proves that all stalks vanish exactly for zero sheaves,
and identifies vanishing under restriction with support disjoint from the
open image. It makes no false assertion that arbitrary sheaf support is
closed.

`SchemeAffineSupport` compares actual tilde-sheaf stalk support with
module-theoretic support using the localized stalk maps. Finite generation
then gives closed support. `SchemeLocalSupport` proves the open-cover
criterion and the finite affine-local-module corollary. Its local module
hypotheses are substantive; global coherence is not silently supplied by
the theorem.

### Coherent affine sheaves and ambient exactness

`CoherentSchemeModules` proves that finite modules over a noetherian ring
are closed under subobjects, quotients, and extensions, using actual module
finite generation. `CoherentSchemeSheaves` uses actual quasicoherent
`O_(Spec R)`-module sheaves and mathlib's tilde/global-sections equivalence.
Its coherent subcategory is the inverse image of finite modules.

The Serre assertion is in quasicoherent sheaves, not in all module sheaves.
Arbitrary subsheaves of coherent sheaves need not be quasicoherent, so that
distinction is essential and is respected here.

`CoherentSchemeExact` closes the important ambient-exactness gate. It proves
that tilde preserves monomorphisms from injectivity of localized module
maps, combines this with its left-adjoint structure, and uses the actual
tilde/global-sections counit to prove exactness of the quasicoherent
inclusion. The coherent inclusion is consequently exact.
`affineCoherent_shortExact_iff` proves preservation and reflection of
short exact sequences by the actual inclusion into all sheaves. Thus the
exact structure defining affine G-theory is the desired geometric one.

`SchemeFiniteSheaves` uses one and the same local basis family with finite
index sets. It derives finite presentation using empty relation sets,
and supplies isomorphism invariance and finite-free/zero examples. It does
not install an unjustified split exact structure on vector bundles.
`CoherentSchemePresentation` proves that the affine coherent objects are
finitely presented sheaves via finite generators and relations. This is a
one-way comparison; the converse and general-scheme identification are not
asserted.

### Actual affine G-theory and support G-groups

`CoherentSchemeGTheory.AffineG R n` is the K-group of the small model of
actual affine coherent sheaves with the exact structure above.
`RingG R n` is the corresponding finite-module construction. The exact
global-sections equivalence, transported to these small models, gives
`affineGEquiv`. Its forward homomorphism is definitionally
`affineGToRingG`, the canonical `smallKMap`.

`CoherentSchemeSupport` defines supported coherent objects by applying
actual open restriction to their actual underlying sheaves. Exactness
proves that this is a Serre class in coherent sheaves. Its support is closed
and lies in the complement of the open image. The associated supported
G-group is formed from a genuine small model of this full abelian category.
Defining that group alone does not supply a localization sequence.

### Actual finite-module localization quotient

`FiniteModuleLocalization` restricts mathlib's scalar-localization functor
to actual finitely generated modules. Exactness and the torsion-kernel Serre
property are proved. `FiniteModuleLocalizationEssentialSurjectivity`
descends a finite localized module by taking the original-ring span of
finitely many generators; no noetherian hypothesis is needed for this step.

For a noetherian source ring, `FiniteModuleLocalizationQuotient` constructs
the comparison from the actual Serre quotient using the universal
localization lift. Fullness clears a single scalar denominator in a map
between localized finite modules. Faithfulness clears a denominator in an
equality, then uses the calculus of fractions. Finite presentation is
derived from noetherianity rather than assumed as the desired quotient.

The resulting `functor_isLocalization` and `quotientEquivalence` have only
the stated ring and multiplicative-set hypotheses. `quotientFunctor_fac`
is an equality with the original scalar-localization functor, and
`quotientEquivalence_fac` is its induced natural isomorphism. This is a
genuine algebraic quotient theorem, not a structure carrying a requested
equivalence as data.

## Remaining acceptance gates

1. Before describing a principal-open G-localization theorem, compare the
   actual finite-module localization functor with actual sheaf restriction
   along `Spec R_f -> Spec R`, including the canonical K-maps and support
   category. The algebraic quotient theorem alone does not prove this
   geometric compatibility.
2. Applying the completed Serre K-localization theorem to finite modules
   requires its actual small-model quotient/comparison transport. A
   quotient equivalence alone does not yet supply the canonical LES.
3. General noetherian schemes still require coherent closure and geometric
   restriction-quotient results proved by local-to-global methods.
4. Vector-bundle K-theory still requires closure and the inherited nonsplit
   exact structure, essential smallness, and the finite-projective affine
   comparison. A finite-locally-free predicate is not that endpoint.
5. Open restriction preserving the finite-sheaf predicates is not among the
   declarations reviewed in this foundation snapshot.
6. Perfect-complex/nonconnective localization and K/G comparison remain
   separate results. No all-sheaf theorem or connective abelian K0 tail is
   substituted for them.

These are scope gates, not defects in the theorems already proved.

## Verification evidence

Independent focused builds succeeded for the exact-equivalence/small-model,
ambient-sheaf, coherent-affine, affine-G, affine-support, and finite-module
quotient modules. The initial foundation build completed 2919 jobs, the
ambient-exactness build 2854 jobs, and the affine-G/quotient build 2955 jobs.
The finite-sheaf/presentation/local-support build completed 2886 jobs, and
the supported-coherent-category build completed 2931 jobs. Warnings seen
were style-only linter suggestions.

The first independent kernel audit checked 1243 imported project declarations,
including private helpers, and found only `propext`, `Classical.choice`, and
`Quot.sound`. It explicitly printed dependencies of the exact transport,
canonical K equivalence, small-model comparison, actual restriction
localization, support criterion, affine equivalence, smallness, and ambient
short-exactness theorem. The final expanded audit checked **1383 imported
project declarations**, including private helpers, with the same three
standard logical foundations and no unsupported assumptions. Its additional
explicit checks cover the canonical affine G-equivalence, the finite
presentation comparison, finite local freeness, local closed support, the
actual finite-module quotient, and the supported coherent Serre class.

Evidence files:

- `logs/scheme-independent-foundation-build-20261009.log`
- `logs/scheme-independent-ambient-exact-build-20261009.log`
- `logs/scheme-independent-affine-build-20261009.log`
- `logs/scheme-independent-finite-sheaf-build-20261009.log`
- `logs/scheme-independent-coherent-support-build-20261009.log`
- `logs/scheme-independent-foundation-axioms-20261009.log`
- `logs/scheme-independent-full-axioms-20261009.log`
- `logs/scheme-independent-audit-input-20261009.lean.txt`
- `logs/scheme-independent-source-hashes-20261009.json`
- `logs/scheme-independent-source-token-audit-20261009.log`

The source-token audit also passed. These focused checks do not replace the
integrator's final aggregate build and aggregate declaration audit after
all imports and subsequent changes are settled. No Lean source was changed
as part of this review.
