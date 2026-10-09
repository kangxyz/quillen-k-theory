# Independent review: public K-map coherence and affine/global scheme APIs

Date: 2026-10-09. Lean 4.34.0, pinned mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict and scope

No mathematical correctness blocker was found in the nine implementation files
reviewed below. The APIs use actual exact functors, actual sheaves and ordinary
stalk support. Natural-isomorphism invariance fixes the genuine zero basepoint;
affine restriction covers every affine open immersion; and every K-theory
comparison stays within its explicitly selected realization universe.

The initial six-file independent build and final combined kernel audit passed.
The latter includes all three principal-localization additions and checked
8267 imported project declarations. This is
a focused mathematical/API review, not a replacement for the library worker's
full migration-integrity and standalone-consumer checks. Compatibility-path checks
were part of the historical review; those wrappers have since been removed.

The earlier global coherent/vector-bundle foundations and principal closed
finite-module dévissage are reviewed in
[REVIEW_20261009_GLOBAL_K_G.md](REVIEW_20261009_GLOBAL_K_G.md). Two former scope
items from that review are now resolved here: the global/affine coherent-category
comparison, and the principal-open localization sequence expressed in the
existing upper-universe global G-groups. General non-affine localization and the
converse from arbitrary upstream local finite presentation remain separate.

## 1. Natural isomorphisms preserve the original canonical K-map

Source: `Quillen/KTheory/Map/NaturalIso.lean`.

`mapQ_iso_naturality` compares genuine admissible spans. The common comparison
span has apex `F(s.apex)`, left leg `F(s.l)`, and right leg
`F(s.r) ≫ e.app Y`. Its two identifications with composite Q-morphisms use actual
pullback squares. One square uses an identity leg; the other uses the component
isomorphism at the original apex and the naturality of `e` on the left leg.
The right-leg equality uses naturality on `s.r`. The result therefore descends
to the actual quotient Q-category and is not a newly postulated Q-map.

`mapQIso` has components exactly `qIsoOfIso (e.app X)`. The natural comparison
of normalized functors conjugates this isomorphism with the two actual rebasing
isomorphisms. `rebaseFunctorNatIso_hom_base` explicitly keeps the object transports
and proves the component equals `eqToHom` when the supplied base isomorphisms
are compatible.

For exact functors the compatibility is proved by uniqueness of morphisms to
the original zero object, after reducing the Q-isomorphism composition to the
underlying original-category isomorphisms. It does not assert that the zero
vertex is a zero object of Q or that arbitrary Q morphisms to it are unique.

`normalizedQIso_hom_base` is precisely the identity-at-the-base input required by
`classifyingSpaceNaturalTransformationBasedHomotopy`. Its realized homotopy is
fixed at `EC.kBasepoint` and has value `ED.kBasepoint` there at every time.
`KMap_eq_of_natIso` applies actual based homotopy invariance to the continuous
maps defining the existing `F.KMap n` and `G.KMap n`. No unbased-homotopy shortcut,
conjugacy-only statement, or replacement K-map is used; degree zero is included.

## 2. Strict laws on actual chosen small-model K-maps

Source: `Quillen/CategoryTheory/SmallModel/Functoriality.lean`.

The underlying descended functor is the existing construction
`equivSmallModel(C).inverse ⋙ F ⋙ equivSmallModel(D).functor`.
`smallModelIdIso` uses the actual counit. `smallModelCompIso` inserts the actual
unit of the intermediate equivalence, mapped by G and the target equivalence;
its naturality proof is the mapped naturality of that unit.
`smallModelNatIso` is ordinary whiskering on both sides.

The preceding based natural-isomorphism theorem turns these comparisons into
`smallKMap_id`, `smallKMap_comp`, and `smallKMap_eq_of_natIso` for exactly the
existing `smallKMap`. The original categories may have different object and
morphism universes. They are all required to be essentially small in the same
explicit universe `w`, and all realization-level arguments happen there.
There is no equality between realizations in different universes and no
assumption that the chosen categorical small models are strictly functorial.

## 3. Finite global generators, without false global-sections exactness

Source: `Quillen/Scheme/Coherent/Affine/FinitePresentation.lean`.

`finite_globalSections_of_generatingSections` starts with actual quasicoherence
and a finite global generating family, hence an epimorphism from the finite free
sheaf. The canonical `fromTildeΓ` isomorphism and `tildeFinsupp` turn this into an
epimorphism between actual tilde sheaves. Fullness obtains the module map, and
faithfulness reflects its epimorphism. Module-category epimorphisms are
surjective, so the target is a quotient of a finite free module.

The proof never declares global sections exact on all module sheaves and never
infers global surjectivity from an arbitrary sheaf epimorphism. The essential
quasicoherence hypotheses are present. The presentation corollary uses a global
presentation and finite generators, without requiring a finite relation family.
It does not promote an arbitrary local finite-presentation witness to a finite
global presentation.

Conversely, a finite set generating the actual global-sections module supplies
a presentation of its tilde sheaf; the full kernel is allowed as the relation
index set. Only the generating family is required to be finite. Transport along
`fromTildeΓ` gives actual finite global generating sections of the original
sheaf. These statements correctly do not require noetherianity.

`affineFiniteSheaf_restrict` works for any open immersion `Spec S → Spec R`.
It maps the finite generating family using actual geometric restriction,
colimit preservation, and the structure-sheaf unit isomorphism. The index type
is unchanged. Quasicoherence survives restriction, so the preceding theorem
gives finite S-global-sections. There is no principal-open assumption or claim
that every affine open is a localization at a single element or multiplicative
subset.

## 4. Actual global/affine category and low-universe G comparisons

Sources: `Quillen/Scheme/Coherent/Affine/Comparison.lean` and
`Quillen/Scheme/Coherent/Affine/ComparisonGTheory.lean`.

`coherent_spec_iff` evaluates the all-affine-chart predicate on the identity
chart in one direction and invokes the arbitrary-affine-open theorem in the
other. This object-property result holds over every ring. Under noetherianity,
`coherentAffineEquivalence` identifies the existing global coherent category
with the existing affine coherent category. Both directions retain the actual
underlying sheaf and every morphism; unit and counit are reflexive.
`coherentAffineEquivalence_comp_inclusion` verifies this directly.

Both exact comparison functors preserve the standard abelian conflations.
They do not impose splitness or change the ambient notion of sheaf exactness.
The actual equivalence with finite modules proves essential smallness of the
global affine category in the base ring's universe `u`.

`SpecG R n` explicitly forms `SmallK.{u}` of this global coherent category.
`specGToAffineG` is the exact identity-on-sheaves comparison's original
`smallKMap`. Its Q-equivalence is proved from categorical equivalence and
reflection of admissible monomorphisms/epimorphisms for the actual abelian
structures. `specGAffineEquiv` therefore has exactly this canonical forward map.
The further `specGRingEquiv_toMonoidHom` is precisely the composite with actual
affine global sections. This does not identify `SpecG` with generic
`G (Spec R)`, which was defined using `SmallK.{u+1}`.

## 5. Ordinary closed stalk support on any scheme

Source: `Quillen/Scheme/Coherent/ClosedSupport.lean`.

`isClosed_support_of_coherent` assumes the actual all-affine-chart predicate,
not global noetherianity, quasi-compactness or separatedness. On each affine
chart it uses finite global sections and quasicoherence to obtain ordinary
closed stalk support, with the proved support/restriction identity.
At every point outside the global support, an affine chart supplies an open
neighborhood outside that support; the chart map is an actual open embedding.
Thus the complement is open. The specialized `coherent_support_isClosed`
applies this to objects of the existing coherent category. No new surrogate
support predicate is introduced.

## 6. Principal localization on the existing upper-universe global G-groups

Sources: `Quillen/Scheme/Coherent/PrincipalRestriction.lean`,
`PrincipalSupport.lean`, and `PrincipalLocalization.lean`.

`coherentPrincipalRestrictionSquare` is reflexive on underlying sheaves and
morphisms. The proved affine categorical localization is transported through
actual source and target category equivalences. The kernel-localization
instance is then rewritten using the proved identity with
`coherentSupportedAway`. Exactness alone is not mistaken for a localization
universal property.

`coherentPrincipalSmallRestriction` explicitly fixes `SmallModel.{u+1}`.
Its kernel consists exactly of represented actual coherent sheaves vanishing
on the open. `coherentPrincipalSmallSupportEquivalence` realizes this as an
actual equivalence with the existing `SupportedCoherent` category. The support
comparison starts from that category's `u+1` small model and lands in the
compatible kernel subcategory in the same universe. Exactness and reflection
of admissible monos/epis are proved before applying the canonical K-equivalence
construction.

`globalPrincipalInclusionGMap` uses the canonical exact support-presentation
comparison followed by the generic small-model inclusion map.
`globalPrincipalConnectingHom` uses the existing localization boundary followed
by the inverse of that same comparison. The support equivalence is induced by
specified categorical equivalences, not an arbitrary group isomorphism.
These files do not separately expose an equality with the smallKMap of a newly
bundled direct global-support inclusion; their stated definition uses the
explicit canonical presentation comparison.

All generic small-model localization calls are explicitly instantiated at
`u+1`. In particular the ambient-to-open map in the theorem is literally the
pre-existing `restrictionGMap (principalOpen R r)`, and the other terms are the
pre-existing global `G` and `SupportedG` definitions. The low-universe affine
G-equivalence is not used to cast or identify these groups.

`global_principal_localization_longExact` proves all three range/kernel
positions and surjectivity of that actual G-zero restriction. The separately
stated low-degree tail uses the same homotopical G-zero, rather than substituting
a Grothendieck presentation. This is the principal-open sequence on an affine
noetherian scheme; neither arbitrary non-affine open localization nor geometric
closed-immersion pushforward compatibility follows from this result alone.

## Remaining boundaries

- Generic common-small-universe functoriality does not establish cross-universe
  realization invariance.
- Finite global generators/global presentations do not settle the converse from
  arbitrary upstream local finite presentation to the all-affine-chart predicate.
- Principal affine global G-localization is now proved. General noetherian-scheme
  coherent extension and quotient/localization remain additional work.
- Closed-support objects are not identified with sheaves killed by the ideal
  itself; geometric closed-pushforward comparison and general ideal-power
  dévissage remain distinct from the sequence reviewed here.
- These additions do not supply arbitrary-morphism vector-bundle pullback,
  a K/G equivalence, or nonconnective/perfect-complex localization.

## Independent verification evidence

- Focused build of the original six endpoints passed: **3082 jobs**. It also
  rebuilt the canonical `Scheme.Coherent.Affine.ComparisonGTheory` path after
  its final move. Warnings were linter/style messages, not proof failures.
- The initial focused audit printed 34 named endpoint dependency lists and
  traversed **1479 imported project declarations**, including private helpers.
  Only `propext`, `Classical.choice` and `Quot.sound` were allowed and found.
- Compiled direct-consumer examples exercised mixed original universes for all
  three smallKMap laws, finite global sections without noetherianity, arbitrary
  affine-open restriction, closed support without global noetherianity, the
  low-universe `SpecG` type, and the exact composite comparison map.
- The final combined audit adds 17 principal-localization endpoints plus direct
  examples of the existing public upper-universe restriction and its G-zero
  surjectivity. It passed and traversed **8267 imported project declarations**,
  including private helpers; all 51 named endpoints and the complete traversal
  used only the three standard logical foundations listed above.
- Recursive source-token audit passed. Source SHA-256 records cover all nine
  reviewed implementation files and are checked for subsequent changes.

Evidence files:

- `logs/public-api-independent-build-20261009.log`
- `logs/public-api-independent-audit-20261009.lean`
- `logs/public-api-independent-axioms-20261009.log`
- `logs/public-api-independent-final-axioms-20261009.log`
- `logs/public-api-independent-source-token-audit-20261009.log`
- `logs/public-api-independent-source-hashes-20261009.json`

No implementation source was edited by this review, and nothing was published.
