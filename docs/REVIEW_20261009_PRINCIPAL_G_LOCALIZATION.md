# Independent review: principal-open G-localization

Date: 2026-10-09. Lean 4.34.0; mathlib pinned at
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict

No mathematical correctness blocker was found in the reviewed principal-open
supported G-localization theorem. It is a theorem about actual coherent sheaves
on a noetherian affine scheme, their actual geometric restriction, and the
actual supported coherent category. It is not merely a conditional quotient
adapter or an all-module-sheaf theorem relabelled as G-theory.

For a commutative noetherian ring `R` and any `r : R`,
`CoherentScheme.principal_localization_longExact` proves all three recurring
image-equals-kernel positions in nonnegative degrees for

`... -> G_(n+1)(Spec R[1/r]) -> G_n^Z(Spec R) -> G_n(Spec R) -> G_n(Spec R[1/r]) -> ...`,

where `Z` is the complement of the image of the actual principal-open
immersion. The explicit low-degree theorem
`principal_localization_GZero_tail` ends in the surjective map
`G_0(Spec R) -> G_0(Spec R[1/r]) -> 0`.

There is no regularity, reducedness, non-zero-divisor, nonzero-element,
pre-assumed K-equivalence, filtration, or Theorem B comparison hypothesis
in this geometric endpoint. All actual localization assumptions in the
generic adapters are discharged by the proved restriction quotient theorem.

## Semantic checks

### Actual target and canonical K-maps

`SerreLocalizationTarget.targetLift` is constructed by the localization
universal property. `targetLift_fac` is a strict equality with the original
localization functor, and `targetLift_isEquivalence` is a theorem of the actual
localization property. It is not a free field carrying the desired equivalence.

The induced `targetKEquiv` has precisely the quotient-lift `KMap` as its forward
map. `targetKEquiv_comp_quotientKMap` uses strict factorization and proved
zero-based K-functoriality to identify the transported quotient map with the
original localization map. `actualConnectingHom` transports the genuine
path-space boundary through this constructed equivalence. Its comparison with
the path-space boundary is explicit. Thus all three exactness positions and
the terminal K0 surjection retain the intended maps.

### Finite-module G-localization

`AffineGLocalization.smallFunctor` is exactly the small-model functor of the
actual scalar-localization exact functor. Its localization property is
transported from the previously proved finite-module Serre quotient using
actual categorical equivalences, with the required comparison natural
isomorphism constructed from their unit.

`smallTorsion_iff` identifies its objects with represented finite modules
killed by actual scalar localization. For powers of an element,
`smallTorsion_powers_iff_uniform` identifies them with modules annihilated by
one uniform power. It does not identify those modules with modules annihilated
by the element itself.

The identity-induced equivalence between transported and standard abelian
exact structures preserves the original localization `smallKMap` by
`smallKMap_comparison`. `FiniteModuleGLocalization.localization_longExact`
therefore applies to the actual finite-module G-groups and their original
localization map, at every stated degree and at K0.

### Actual sheaf restriction and localization square

`CoherentSchemeRestriction.principalOpen` is the actual morphism
`Spec R[1/r] -> Spec R` induced by the localization algebra map.
`affinePrincipalRestriction` is a lift of the actual sheaf restriction
functor into the coherent full subcategory. Its composite with underlying
sheaf inclusion equals actual geometric restriction by `rfl` in
`affinePrincipalRestriction_comp_inclusion`.

The localization/restriction comparison is proved first on actual modules.
Sections of the restricted associated sheaf form a localized module via the
actual map to sections on the principal open. Its linear localization
isomorphism is proved natural on module maps. The actual tilde/global-sections
equivalence then gives `affinePrincipalRestrictionSquare` for finite-module
valued functors. Preservation of coherence is derived from that isomorphism
and finite generation after scalar localization; it is not assumed.

`CoherentSchemeRestrictionExact` obtains exactness by reflection through the
fully faithful exact inclusion into ambient module sheaves.
`principalRestriction_kernel_eq_support` identifies its kernel with
`affineSupportedAway`, already defined using actual underlying sheaf
restriction. The quotient property is then transported through the proved
natural square from actual finite-module localization. No target quotient or
K-theory comparison remains as an input to the geometric theorem.

### Sizes, exact structures, and the supported term

The original finite-module and affine coherent-sheaf categories have objects
in `Type (u+1)` and morphisms in `Type u`. Their actual `SmallModel.{u}`
presentations have objects and morphisms in `Type u`; the G-groups in the
principal theorem also inhabit `Type u`. The supported full subcategory of
the small source is itself `u`-small. The generic transport permits different
original category and morphism universes while using a common explicitly
chosen small universe. No comparison between raw realizations in different
universes is silently used.

`SmallModelLocalization` conjugates the actual functor by the genuine
small-model equivalences and proves the kernel/quotient comparison. Its
`standardKEquiv` is induced by the identity exact functor between the two
proved-equal abelian exact structures. `SmallModelGLocalization` transports
exactness along those comparisons without replacing the given `F.smallKMap`.
The supported inclusion is the canonical full-subcategory inclusion followed
by the inverse identity-exact-structure comparison.

`CoherentSchemePrincipalSupport.principalSmallSupport_iff` identifies small
supported objects with actual supported coherent sheaves represented by them.
Combining it with `affineSupportedAway_iff_support_subset` gives ordinary
underlying-sheaf stalk support contained in the principal-open complement;
this combined statement was independently compiled in the audit.

The two supported presentations are kept distinct. `PrincipalSupportedG` is K
of the support full subcategory of the chosen small coherent model; the earlier
`SupportedAffineG` is SmallK of the original supported coherent category.
`principalSmallSupportEquivalence` is an actual categorical equivalence, whose
forward functor commutes with actual coherent inclusion definitionally.
`principalSupportComparison` supplies the additive exact comparison between
the two small presentations. `principalSupportedGEquiv` has exactly that
comparison's canonical K-map as its forward homomorphism, checked independently
by `rfl`. The endpoint uses the explicitly named `PrincipalSupportedG`; it
never silently equates the two aliases or asserts an unproved equality of
raw inclusion maps across them.

### Geometric endpoint and low degrees

`principalRestrictionGMap` is definitionally the original
`affinePrincipalRestrictionExact.smallKMap`. The final module directly
instantiates the proved generic small-model sequence with that exact functor.
Its quotient and finite-limit/colimit instances are the proved geometric ones.
The boundary and supported inclusion are the same ones used in every
exactness position and in the explicit G0 tail.

The K0 endpoint concerns the genuine homotopical K0 defined by the project.
It follows from the canonical localization comparison on pi0 and connectedness
of BQ, through the previously proved Serre theorem. It does not assume an
identification with the algebraic Grothendieck group or a separate K0
commutativity theorem.

## Scope boundaries

1. This is principal-open localization for a noetherian affine scheme.
   General open subschemes and general noetherian schemes still require their
   own coherent quotient and local-to-global results.
2. The support term is supported coherent G-theory. Replacing it with
   `G(R/(r))`, or with coherent sheaves on a closed subscheme, requires the
   separate closed-support equivalence and dévissage theorem. Those are not
   included in this accepted result or this review snapshot.
3. This does not prove vector-bundle K-theory, perfect-complex localization,
   K/G comparison, or a nonconnective negative-degree extension.
4. The actual natural restriction/localization square has been checked.
   This review does not promote it to a separate, unproved general naturality
   theorem for all localization sequences or all maps of Serre pairs.

## Verification evidence

The independent core focused build passed **3444 jobs**. The final focused
build of generic small-model transport and geometric principal localization
passed **3446 jobs**. Reported warnings were style-only linters.

The core kernel audit inspected **7986 imported project declarations**,
including private helpers, and allowed only `propext`, `Classical.choice`, and
`Quot.sound`. The final expanded audit inspected **8108 imported project declarations**,
including private helpers, with the same three permitted logical foundations
and no unsupported assumptions.
Explicit declaration type prints check the endpoint assumptions and universes.
The final audit also compiles the definitional canonical restriction-map
identity, the supported-presentation equivalence's forward-map identity,
ordinary sheaf-support characterization, and small-universe G-group types.
The source-token audit passed with no proof placeholders or custom assumptions.

Evidence files:

- `logs/principal-g-independent-core-build-20261009.log`
- `logs/principal-g-independent-geometric-build-20261009.log`
- `logs/principal-g-independent-core-axioms-20261009.log`
- `logs/principal-g-independent-final-axioms-20261009.log`
- `logs/principal-g-independent-core-audit-input-20261009.lean.txt`
- `logs/principal-g-independent-final-audit-input-20261009.lean.txt`
- `logs/principal-g-independent-source-hashes-20261009.json`
- `logs/principal-g-independent-source-token-audit-20261009.log`

No project Lean source was edited by this reviewer. These focused checks do
not replace the integrator's aggregate build and declaration audit after
final imports and any subsequent modifications. No publication was performed.
