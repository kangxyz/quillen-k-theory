# Scheme K/G infrastructure audit

Pinned dependency: mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
Lean 4.34.0. This audit concerns the dependency actually checked out in this
project, not an assumed future API.

## Available geometric objects

- `AlgebraicGeometry.Scheme.Modules` is the actual category of sheaves of
  modules over a scheme's structure sheaf. Mathlib supplies its abelian
  structure, all limits and colimits, and its Grothendieck-abelian structure.
- For `X : Scheme.{u}`, its objects live in `Type (u + 1)` and its morphisms
  in `Type u`. These levels must not be silently identified.
- `Scheme.Modules.restrictFunctor j` is actual restriction along an open
  immersion. Its adjunction to pushforward and the isomorphism between
  restriction after pushforward and the identity are already available.
- `Scheme.Modules.restrictStalkNatIso` identifies restriction stalks with the
  original stalks at image points.
- `SheafOfModules.IsQuasicoherent` uses local presentations by sums of the
  structure sheaf. `SheafOfModules.IsFinitePresentation` requires locally
  finite generators and relations. The latter implies quasi-coherence and
  finite type; isomorphism invariance is proved upstream.
- `SheafOfModules.IsLocallyFree` is present. It allows arbitrary rank and is
  therefore not by itself the category for ordinary vector-bundle K-theory.
  `LocalGeneratorsData.IsFiniteType` supplies the extra local finiteness.
- `AlgebraicGeometry.Modules.Tilde` proves the actual equivalence of modules
  over a commutative ring and quasi-coherent sheaves on its affine spectrum.
- `IsLocallyNoetherian` and `IsNoetherian` scheme predicates are present.

Relevant upstream files are `AlgebraicGeometry/Modules/{Sheaf,Tilde}.lean`,
`Algebra/Category/ModuleCat/Sheaf/{Generators,Quasicoherent,LocallyFree}.lean`,
and `AlgebraicGeometry/Noetherian.lean`.

## Gaps that must be proved rather than assumed

The pinned dependency does not provide a coherent module-sheaf predicate and
its abelian category on a general noetherian scheme, or the finite-locally-free
exact category together with extension closure. Nor does it supply the
coherent restriction quotient theorem or the closed-support coherent
devissage hypotheses as ready-to-use theorem instances.

Finite presentation is not simply being renamed coherence on arbitrary
schemes. Likewise the category of all module sheaves is not being renamed
scheme K-theory or G-theory. A noetherian affine construction must use actual
quasi-coherent sheaves and finite modules, and a global construction must
supply the necessary local-to-global proofs.

The completed `Quillen.Localization.Serre.LocalizationTheorem` is stated for
`C : Type u` with `Category.{u} C`. The core `ExactStructure.K` definition
already allows independent object and morphism universes, but this does not
by itself generalize the full localization endpoint. Scheme-category
applications require a checked size/transport step (or a generalized
endpoint), and statements about essential smallness in the scheme universe
require their own proof. Raising to a larger ambient universe is distinct
from proving essential smallness at the original universe.

## Concrete first scheme modules

`Quillen.Scheme.Sheaf.Exact` uses the actual ambient module-sheaf categories and
open restriction. It supplies:

- the standard exact structure with conflations precisely short exact
  sequences and admissible maps precisely monomorphisms/epimorphisms;
- the additive exact restriction functor;
- `supportedAway j`, the object property that restriction along `j` is zero;
- its Serre-class property and the short-exact-sequence membership criterion;
- the actual ambient restriction functor as the Serre localization by that
  property, using the fully faithful pushforward right adjoint;
- the characterization of maps inverted by restriction through kernels and
  cokernels supported away from the open.

`Quillen.Scheme.Sheaf.Support` identifies this vanishing condition with ordinary
stalk support disjoint from the image of the open immersion and proves that support under restriction
is exactly its inverse image. No closedness claim is made for the support of
an arbitrary module sheaf.

`Quillen.Scheme.Sheaf.AffineSupport` proves that the stalk support of the actual
associated sheaf `tilde M` equals `Module.support R M`. It deduces closedness
for finite modules and for actual quasi-coherent affine sheaves with finite
global-section modules, using the canonical `fromTildeΓ` isomorphism.

`Quillen.Scheme.Sheaf.LocalSupport` proves that support closedness is local on any
scheme open cover, then obtains closed support whenever an actual affine
open cover has quasi-coherent restrictions with finite global-section
modules. This uses substantive local module finiteness conditions, not a
field assuming closedness. Identification with every formulation of the
general `SheafOfModules.IsFiniteType` condition is not asserted.

`Quillen.Scheme.VectorBundle.Basic` develops actual finite-presentation and finite
locally-free sheaves, including the common finite local-trivialization data,
zero/free examples, isomorphism invariance, and the full subcategories. It
does not assume extension closure as a replacement for proving it.

These ambient and finite-object modules are input to scheme G/K theory. They
are not a completed scheme G-localization sequence or a theorem for perfect
complex K-theory. In particular, no general connective K0-surjectivity claim
for perfect-complex localization follows from the abelian endpoint.

## Verification

Checked ambient/support builds:

- `SchemeSheafExact`: 2547 jobs, `logs/scheme-sheaf-exact-build.log`.
- `SchemeSheafSupport`: 2564 jobs, `logs/scheme-sheaf-support-build.log`.
- `SchemeAffineSupport`: 2676 jobs, `logs/scheme-affine-support-build.log`.
- `SchemeLocalSupport`: 2677 jobs, `logs/scheme-local-support-build.log`.
- `SchemeFiniteSheaves`: 2551 jobs, `logs/scheme-finite-sheaves-build.log`.
- Five-module aggregate: `logs/scheme-five-foundations-build.log`.
- The initial upstream scheme dependency build completed 2635 jobs in
  `logs/scheme-mathlib-dependencies.log`.

Fifteen ambient and affine declarations were checked with `#print axioms` in
`logs/scheme-ambient-axioms.log`; they use only `propext`, `Classical.choice`,
and `Quot.sound`. Two additional local-support checks are in
`logs/scheme-local-support-axioms.log`, and five finite-sheaf checks plus
default-transparency instance smoke tests are in
`logs/scheme-finite-sheaves-axioms-smoke.log`. They also use only these
standard axioms. No `sorry`, `admit`, `axiom`, or `opaque` declaration is
introduced in the five scheme modules. Aggregate library integration is
reported separately by the integrating task.
